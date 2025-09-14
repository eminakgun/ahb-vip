
class ahb_driver extends uvm_driver#(ahb_sequence_item);

    ahb_config cfg;

    // A simple memory model for the subordinate
    logic [31:0] mem [255:0];

    int beats_left = 0;

    `uvm_component_utils(ahb_driver)

    function new(string name = "ahb_driver", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual task run_phase(uvm_phase phase);
        if (cfg.agent_type == MANAGER) begin
            init_manager();
            manager_get_put_loop();
        end else begin // SUBORDINATE
            init_subordinate();
            subordinate_run_phase();
        end
    endtask

    virtual protected task init_manager();
        cfg.vif.HWRITE <= 0;
        cfg.vif.HADDR <= 0;
        cfg.vif.HWDATA <= '0; 
        cfg.vif.HTRANS <= IDLE;
        cfg.vif.HBURST <= SINGLE;
        cfg.vif.HMASTLOCK <= '0; 
        cfg.vif.HPROT <= '0; 
        cfg.vif.HSIZE <= '0;
        cfg.vif.HWSTRB <= '0;
    endtask

    virtual protected task init_subordinate();
        cfg.vif.HRDATA <= '0;
        cfg.vif.HREADYOUT <= '0;
        cfg.vif.HRESP <= '0;
    endtask

    // This is the main manager loop based on the get/put pattern.
    virtual task manager_get_put_loop();
        forever begin
            seq_item_port.get(req);
            `uvm_info(get_type_name(), $sformatf("DRV_START: Received req of %0d ID\n%s", 
                                        req.get_transaction_id(), req.sprint()), UVM_MEDIUM)
            assert($cast(rsp, req.clone()));
            rsp.set_id_info(req);
            drive_transfer(rsp);
        end
    endtask

    // This task orchestrates the pipelined transfer.
    virtual task drive_transfer(ahb_sequence_item rsp);
        `uvm_info(get_type_name(), $sformatf("DRV_START: Starting transfer for req of %0d ID\n%s", 
                                              rsp.get_transaction_id(), rsp.sprint()), UVM_MEDIUM)
        // Drive the address phase for this transaction
        drive_address_phase(rsp);

        // if first beat of a burst
        if (rsp.HTRANS == NONSEQ && is_burst(rsp.HBURST))
            beats_left = get_burst_length(rsp.HBURST);

        // Fork a process to handle the data phase and completion
        fork
            begin
                // Data phase for the transaction begins on the next clock edge.
                @(cfg.vif.manager_cb);
                `uvm_info(get_type_name(), $sformatf("DATA_PHASE: Starting data phase of %0d ID", 
                                                        rsp.get_transaction_id()), UVM_MEDIUM)

                if (cfg.vif.manager_cb.HBURST == SINGLE) begin
                    cfg.vif.manager_cb.HTRANS <= IDLE;
                end
                else if (is_burst(rsp.HBURST)) begin
                    --beats_left;
                    if (rsp.HTRANS != INCR && beats_left == 0) begin // if not undefined length burst
                        cfg.vif.manager_cb.HTRANS <= IDLE;
                    end
                end

                // Drive write data during the data phase.
                drive_data_phase(rsp);

                // Wait for the subordinate to signal it can complete the transfer.
                // This loop finishes on the clock edge where HREADY is high.
                do begin
                    @(cfg.vif.manager_cb);
                end while (cfg.vif.manager_cb.HREADY != 1'b1);
                `uvm_info(get_type_name(), $sformatf("DATA_PHASE: Captured READY of %0d ID", 
                                        rsp.get_transaction_id()), UVM_MEDIUM)

                // Capture read data.
                if (!rsp.HWRITE) begin
                    `uvm_info(get_type_name(), $sformatf("DRV_READ: Reading HRDATA from VIF: 0x%0h", cfg.vif.manager_cb.HRDATA), UVM_MEDIUM)
                    rsp.HRDATA = cfg.vif.manager_cb.HRDATA;
                    `uvm_info(get_type_name(), $sformatf("DRV_READ: Captured HRDATA in rsp: 0x%0h", rsp.HRDATA), UVM_MEDIUM)
                end
                `uvm_info(get_type_name(), $sformatf("DRV_DONE: Sending response:\n%s", rsp.sprint()), UVM_MEDIUM)
                seq_item_port.put(rsp); // signal to calling sequence
            end
        join_none
    endtask

    virtual protected task drive_address_phase(ahb_sequence_item item);
        @(cfg.vif.manager_cb);
        cfg.vif.manager_cb.HADDR <= item.HADDR;
        cfg.vif.manager_cb.HWRITE <= item.HWRITE;
        cfg.vif.manager_cb.HSIZE <= item.HSIZE;
        cfg.vif.manager_cb.HTRANS <= item.HTRANS;
        cfg.vif.manager_cb.HBURST <= item.HBURST;
        cfg.vif.manager_cb.HPROT <= 4'b0011;
    endtask

    virtual protected task drive_data_phase(ahb_sequence_item item);
        if (item.HWRITE) begin
            cfg.vif.manager_cb.HWDATA <= item.HWDATA;
        end
    endtask
    
    virtual task subordinate_run_phase();
        logic data_phase_active = 0;
        logic [31:0] data_phase_HADDR;
        logic data_phase_HWRITE;

        // Initialize outputs to a safe state
        cfg.vif.subordinate_cb.HREADYOUT <= 1'b1;
        cfg.vif.subordinate_cb.HRESP     <= 1'b0;
        cfg.vif.subordinate_cb.HRDATA    <= 'z;

        forever begin
            @(cfg.vif.subordinate_cb);

            //==================================================================
            // Data Phase Stage (for transfer captured in the previous cycle)
            //==================================================================
            if (data_phase_active) begin
                if (data_phase_HWRITE) begin
                    // On a write, sample the write data from the bus
                    mem[data_phase_HADDR[7:0]] <= cfg.vif.subordinate_cb.HWDATA;
                end
                // For a read, HRDATA was already driven in the previous cycle (address phase)
            end

            //==================================================================
            // Address Phase Stage (for transfer starting in the current cycle)
            //==================================================================
            if (cfg.vif.subordinate_cb.HSELx && cfg.vif.subordinate_cb.HTRANS inside {NONSEQ, SEQ}) begin
                // A new transfer is starting. Capture its details for the data phase next cycle.
                data_phase_active = 1;
                data_phase_HADDR  = cfg.vif.subordinate_cb.HADDR;
                data_phase_HWRITE = cfg.vif.subordinate_cb.HWRITE;

                // Set response for the current transfer (zero wait states)
                cfg.vif.subordinate_cb.HREADYOUT <= 1'b1;
                cfg.vif.subordinate_cb.HRESP     <= 1'b0; // OKAY

                if (!data_phase_HWRITE) begin // This is a read transfer
                    // Fetch data and drive it onto HRDATA. It will be valid for the manager to sample next cycle.
                    cfg.vif.subordinate_cb.HRDATA <= mem[data_phase_HADDR[7:0]];
                end else begin
                    // Stop driving HRDATA during write transfers
                    cfg.vif.subordinate_cb.HRDATA <= 'z;
                end
                //seq_item_port.put(rsp);
            end else begin
                // No new transfer is starting.
                data_phase_active = 0;
                cfg.vif.subordinate_cb.HREADYOUT <= 1'b1;
                cfg.vif.subordinate_cb.HRDATA    <= 'z; // Stop driving HRDATA
            end
        end
    endtask

endclass
