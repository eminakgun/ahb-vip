
class ahb_driver extends uvm_driver#(ahb_sequence_item);

    ahb_config cfg;

    // A simple memory model for the subordinate
    logic [31:0] mem [255:0];

    `uvm_component_utils(ahb_driver)

    function new(string name = "ahb_driver", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual task run_phase(uvm_phase phase);
        if (cfg.is_active == UVM_PASSIVE) return;

        drive_idle();

        if (cfg.agent_type == MANAGER) begin
            manager_get_put_loop(phase);
        end else begin // SUBORDINATE
            subordinate_run_phase(phase);
        end
    endtask

    // This is the main manager loop based on the get/put pattern.
    virtual task manager_get_put_loop(uvm_phase phase);
        forever begin
            ahb_sequence_item req, rsp;
            seq_item_port.get(req);
            drive_transfer(req, rsp);
        end
    endtask

    // This task orchestrates the pipelined transfer.
    virtual task drive_transfer(input ahb_sequence_item req, output ahb_sequence_item rsp);
        assert($cast(rsp, req.clone()));

        // Drive the address phase for this transaction
        drive_address_phase(rsp);

        // Fork a process to handle the data phase and completion
        fork
            begin
                // Data phase for the transaction begins on the next clock edge.
                @(cfg.vif.manager_cb);

                // Drive write data during the data phase.
                drive_data_phase(rsp);

                // Wait for the subordinate to signal it can complete the transfer.
                // This loop finishes on the clock edge where HREADY is high.
                do begin
                    @(cfg.vif.manager_cb);
                end while (cfg.vif.manager_cb.HREADY == 1'b0) 

                // Capture read data.
                if (!rsp.HWRITE) begin
                    rsp.HRDATA = cfg.vif.manager_cb.HRDATA;
                end
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

    virtual protected task drive_idle();
        @(cfg.vif.manager_cb);
        cfg.vif.manager_cb.HTRANS <= IDLE;
        cfg.vif.manager_cb.HADDR <= 0;
        cfg.vif.manager_cb.HWRITE <= 0;
        cfg.vif.manager_cb.HBURST <= SINGLE;
    endtask

    virtual task subordinate_run_phase(uvm_phase phase);
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
            end else begin
                // No new transfer is starting.
                data_phase_active = 0;
                cfg.vif.subordinate_cb.HREADYOUT <= 1'b1;
                cfg.vif.subordinate_cb.HRDATA    <= 'z; // Stop driving HRDATA
            end
        end
    endtask

endclass
