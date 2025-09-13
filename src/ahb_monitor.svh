class ahb_monitor extends uvm_monitor;

    ahb_config cfg;

    // Analysis port for individual beats
    uvm_analysis_port#(ahb_sequence_item) beat_ap;
    // Analysis port for completed burst transactions
    uvm_analysis_port#(ahb_burst_transaction) burst_ap;

    `uvm_component_utils(ahb_monitor)

    // FSM state definition
    typedef enum {IDLE, IN_BURST} state_e;
    state_e state = IDLE;

    // Burst collection variables
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
            if (cfg.vif.monitor_cb.HREADY && (cfg.vif.monitor_cb.HTRANS inside {NONSEQ, SEQ})) begin
                collect_and_process_beat();
            end
        end
    endtask

    virtual protected task collect_and_process_beat();
        ahb_sequence_item beat;

        // 1. Collect the raw beat data from the bus interface
        beat = ahb_sequence_item::type_id::create("beat");
        beat.HADDR = cfg.vif.monitor_cb.HADDR;
        beat.HWRITE = cfg.vif.monitor_cb.HWRITE;
        beat.HSIZE = cfg.vif.monitor_cb.HSIZE;
        beat.HTRANS = cfg.vif.monitor_cb.HTRANS;
        beat.HWSTRB = cfg.vif.monitor_cb.HWSTRB;
        beat.HBURST = cfg.vif.monitor_cb.HBURST;
        beat.HPROT = cfg.vif.monitor_cb.HPROT;

        if (beat.HWRITE) begin
            beat.HWDATA = cfg.vif.monitor_cb.HWDATA;
        end else begin
            // For reads, data is valid on the next edge.
            @(cfg.vif.monitor_cb);
            beat.HRDATA = cfg.vif.monitor_cb.HRDATA;
        end

        // 2. Publish the single beat
        beat_ap.write(beat);

        // 3. Process the beat in the context of the FSM
        case (state)
            IDLE: begin
                if (beat.HTRANS == SEQ) begin
                    `uvm_error("AHB_PROTOCOL_ERROR", "SEQ transfer outside of a burst sequence")
                    return;
                end

                // NONSEQ transfer starts a new transaction
                if (beat.HBURST == SINGLE) begin
                    ahb_burst_transaction single_beat_burst = new("single_beat_burst");
                    single_beat_burst.beats.push_back(beat);
                    burst_ap.write(single_beat_burst);
                end else begin // Start of a multi-beat burst
                    burst_tr = new("burst_tr");
                    burst_tr.beats.push_back(beat);
                    beats_left = get_burst_length(beat.HBURST) - 1;
                    active_burst_type = beat.HBURST;
                    start_addr = beat.HADDR;
                    state = IN_BURST;
                end
            end

            IN_BURST: begin
                // Protocol checks
                if (beat.HTRANS != SEQ) begin
                    `uvm_error("AHB_PROTOCOL_ERROR", $sformatf("Burst started at %h of type %s terminated unexpectedly with HTRANS=%s", start_addr, active_burst_type.name(), beat.HTRANS.name()))
                    burst_ap.write(burst_tr); // Publish partial burst
                    state = IDLE;
                    // TODO: Re-process the current beat as a new transaction if it was NONSEQ
                    return;
                end
                if (beat.HBURST != active_burst_type) begin
                     `uvm_error("AHB_PROTOCOL_ERROR", $sformatf("HBURST changed mid-burst at address %h", beat.HADDR))
                end

                // Add beat to the burst transaction
                burst_tr.beats.push_back(beat);
                beats_left--;

                if (beats_left <= 0) { // Use <= to handle undefined length bursts gracefully for now
                    burst_ap.write(burst_tr);
                    state = IDLE;
                end
            end
        endcase
    endtask

    // Helper function to get burst length from HBURST enum
    function int get_burst_length(hburst_e burst);
        case(burst)
            SINGLE: return 1;
            INCR4, WRAP4: return 4;
            INCR8, WRAP8: return 8;
            INCR16, WRAP16: return 16;
            INCR: return -1; // Indicate undefined length
            default: return 1;
        endcase
    endfunction

endclass