class ahb_monitor extends uvm_monitor;

    ahb_config cfg;

    // Analysis port for individual beats
    uvm_analysis_port#(ahb_sequence_item) beat_ap;
    // Analysis port for completed burst transactions
    uvm_analysis_port#(ahb_burst_transaction) burst_ap;

    `uvm_component_utils(ahb_monitor)

    // Internal pipeline register for address phase
    protected ahb_sequence_item addr_phase_tr;
    protected bit addr_phase_valid = 0;

    // FSM for burst collection
    typedef enum {IDLE, IN_BURST} state_e;
    state_e state = IDLE;
    ahb_burst_transaction burst_tr;
    int beats_left;
    hburst_e active_burst_type;
    bit [31:0] start_addr;

    function new(string name = "ahb_monitor", uvm_component parent = null);
        super.new(name, parent);
        beat_ap = new("beat_ap", this);
        burst_ap = new("burst_ap", this);
    endfunction

    virtual task run_phase(uvm_phase phase);
        forever begin
            @(cfg.vif.monitor_cb);

            // -----------------------------------------------------------------
            // -- Data Phase Processing
            // -- Combine address (from last cycle) with data (from this cycle)
            // -----------------------------------------------------------------
            if (addr_phase_valid && cfg.vif.monitor_cb.HREADY) begin
                ahb_sequence_item complete_beat = addr_phase_tr;
                addr_phase_valid = 0; // Consume the address phase

                if (complete_beat.HWRITE) begin
                    complete_beat.HWDATA = cfg.vif.monitor_cb.HWDATA;
                end else begin
                    complete_beat.HRDATA = cfg.vif.monitor_cb.HRDATA;
                end
                
                process_complete_beat(complete_beat);
            end

            // -----------------------------------------------------------------
            // -- Address Phase Processing
            // -- Capture the start of a new transfer
            // -----------------------------------------------------------------
            if (cfg.vif.monitor_cb.HSELx && cfg.vif.monitor_cb.HTRANS inside {NONSEQ, SEQ}) begin
                if (addr_phase_valid) begin
                    `uvm_error("AHB_PROTOCOL_ERROR", "New transfer started before previous data phase completed (HREADY was low)")
                end
                addr_phase_tr = ahb_sequence_item::type_id::create("addr_phase_tr");
                addr_phase_tr.HADDR  = cfg.vif.monitor_cb.HADDR;
                addr_phase_tr.HWRITE = cfg.vif.monitor_cb.HWRITE;
                addr_phase_tr.HWSTRB = cfg.vif.monitor_cb.HWSTRB;
                addr_phase_tr.HPROT  = cfg.vif.monitor_cb.HPROT;

                assert($cast(addr_phase_tr.HSIZE , cfg.vif.monitor_cb.HSIZE));
                assert($cast(addr_phase_tr.HBURST, cfg.vif.monitor_cb.HBURST));
                assert($cast(addr_phase_tr.HTRANS, cfg.vif.monitor_cb.HTRANS));
                addr_phase_valid = 1;
            end
        end
    endtask

    virtual protected task process_complete_beat(ahb_sequence_item beat);
        // Publish every complete beat
        `uvm_info("BEAT_COLLECTED", $sformatf("Beat collected: %s", beat.sprint()), UVM_HIGH)
        beat_ap.write(beat);

        // Process the beat in the context of the burst FSM
        case (state)
            IDLE: begin
                if (beat.HTRANS == SEQ) begin
                    `uvm_error("AHB_PROTOCOL_ERROR", $sformatf("Illegal SEQ transfer detected at address %h while not in a burst. A burst must start with a NONSEQ transfer.", beat.HADDR))
                    return;
                end

                if (beat.HBURST == SINGLE) begin
                    ahb_burst_transaction single_beat_burst = new("single_beat_burst");
                    single_beat_burst.beats.push_back(beat);
                    `uvm_info("BURST_COMPLETE", $sformatf("SINGLE beat burst complete: %s", single_beat_burst.sprint()), UVM_MEDIUM)
                    burst_ap.write(single_beat_burst);
                end else begin // Start of a multi-beat burst
                    `uvm_info("FSM_STATE_CHANGE", $sformatf("IDLE -> IN_BURST. Burst of type %s started at addr %h.", beat.HBURST.name(), beat.HADDR), UVM_MEDIUM)
                    burst_tr = new("burst_tr");
                    burst_tr.beats.push_back(beat);
                    beats_left = get_burst_length(beat.HBURST) - 1;
                    active_burst_type = beat.HBURST;
                    start_addr = beat.HADDR;
                    state = IN_BURST;
                end
            end

            IN_BURST: begin
                if (beat.HTRANS != SEQ) begin
                    `uvm_error("AHB_PROTOCOL_ERROR", $sformatf("Burst started at %h of type %s terminated unexpectedly with HTRANS=%s when %0d beats are left", 
                                                                start_addr, active_burst_type.name(), beat.HTRANS.name(), beats_left))
                    burst_ap.write(burst_tr); // Publish partial burst
                    state = IDLE;
                    // TODO: Re-process the current beat as a new transaction if it was NONSEQ
                    return;
                end
                

                burst_tr.beats.push_back(beat);
                beats_left--;

                if (beats_left <= 0) begin
                    `uvm_info("BURST_COMPLETE", $sformatf("Burst of type %s complete. %s", active_burst_type.name(), burst_tr.sprint()), UVM_MEDIUM)
                    burst_ap.write(burst_tr);
                    `uvm_info("FSM_STATE_CHANGE", "IN_BURST -> IDLE.", UVM_MEDIUM)
                    state = IDLE;
                end
            end
        endcase
    endtask

    function uvm_analysis_port#(ahb_sequence_item) get_item_collected_port();
        return beat_ap;
    endfunction

endclass
