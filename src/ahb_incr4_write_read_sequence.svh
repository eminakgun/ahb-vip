class ahb_incr4_write_read_sequence extends uvm_sequence#(ahb_sequence_item);

    `uvm_object_utils(ahb_incr4_write_read_sequence)

    rand bit[31:0] start_addr;
    rand bit[31:0] write_data[4];
    bit[31:0] read_data[4];

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
            `uvm_do_with(req, {
                HWRITE == 1'b1;
                HTRANS == (i == 0) ? NONSEQ : SEQ;
                HBURST == INCR4;
                HADDR == start_addr + (i * 4);
                HSIZE == HSIZE_WORD;
                HWDATA == write_data[i];
            })
        end

        // 2. INCR4 Read Burst
        `uvm_info(get_type_name(), "Starting INCR4 Read Burst", UVM_MEDIUM)
        for (int i = 0; i < 4; i++) begin
            `uvm_do_with(req, {
                HWRITE == 1'b0;
                HTRANS == (i == 0) ? NONSEQ : SEQ;
                HBURST == INCR4;
                HADDR == start_addr + (i * 4);
                HSIZE == HSIZE_WORD;
            })
            read_data[i] = req.HRDATA;
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
