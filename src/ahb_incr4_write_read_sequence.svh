class ahb_incr4_write_read_sequence extends uvm_sequence#(ahb_sequence_item);

    `uvm_object_utils(ahb_incr4_write_read_sequence)

    rand bit[31:0] start_addr;
    rand bit[31:0] write_data[4];
    bit[31:0] read_data[4];
    htrans_e htrans;

    constraint c_addr { 
        start_addr inside {[32'h0:32'hF0]}; 
    }

    function new(string name = "ahb_incr4_write_read_sequence");
        super.new(name);
    endfunction

    virtual task body();
        // 1. INCR4 Write Burst
        `uvm_info(get_type_name(), "Starting INCR4 Write Burst", UVM_MEDIUM)
        for (int i = 0; i < 4; i++) begin
            req = ahb_sequence_item::type_id::create("req");
            start_item(req);
            htrans = (i == 0) ? NONSEQ : SEQ;
            if(!req.randomize() with {
                HWRITE == 1'b1;
                HTRANS == htrans;
                HBURST == INCR4;
                HADDR == start_addr + (i * 4); // since hsize = word 
                HSIZE == HSIZE_WORD;
                HWDATA == write_data[i];
            }) `uvm_error("RNDFAIL", "Write randomize failed")
            `uvm_info(get_type_name(), $sformatf("Sending %0dth beat of burst write request to addr %h...", 
                                                    i, req.HADDR), UVM_MEDIUM)
            finish_item(req);
            
        end
        //repeat(4) get_response(rsp);
        for (int i = 0; i < 4; i++) begin
            get_response(rsp);
            `uvm_info(get_type_name(), $sformatf("Got response:\n%s", rsp.sprint()), UVM_MEDIUM)
        end

        // 2. INCR4 Read Burst
        `uvm_info(get_type_name(), "Starting INCR4 Read Burst", UVM_MEDIUM)
        for (int i = 0; i < 4; i++) begin
            req = ahb_sequence_item::type_id::create("req");
            start_item(req);
            htrans = (i == 0) ? NONSEQ : SEQ;
            if (!req.randomize() with {
                HWRITE == 1'b0;
                HTRANS == htrans;
                HBURST == INCR4;
                HADDR == start_addr + (i * 4); // since hsize = word 
                HSIZE == HSIZE_WORD;
            }) `uvm_error("RNDFAIL", "Read randomize failed")
            `uvm_info(get_type_name(), $sformatf("Sending %0dth beat of burst read request to addr %h...", 
                                                    i, req.HADDR), UVM_MEDIUM)
            finish_item(req);
        end
        
        for (int i = 0; i < 4; i++) begin
            get_response(rsp);
            read_data[i] = rsp.HRDATA;
            `uvm_info(get_type_name(), $sformatf("Got response:\n%s", rsp.sprint()), UVM_MEDIUM)
        end

        // 3. Verification
        `uvm_info(get_type_name(), "Verifying data...", UVM_MEDIUM)
        for (int i = 0; i < 4; i++) begin
            if (read_data[i] != write_data[i]) begin
                `uvm_error(get_type_name(), $sformatf("Data mismatch at index %0d: Wrote %0h, Read %0h", i, write_data[i], read_data[i]))
            end
        end
        `uvm_info(get_type_name(), "Data verification complete.", UVM_MEDIUM)

    endtask

endclass
