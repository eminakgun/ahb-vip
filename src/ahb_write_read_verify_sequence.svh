class ahb_write_read_verify_sequence extends uvm_sequence#(ahb_sequence_item);

    `uvm_object_utils(ahb_write_read_verify_sequence)

    rand uvm_reg_addr_t addr;
    rand uvm_reg_data_t wr_data;

    function new(string name = "ahb_write_read_verify_sequence");
        super.new(name);
    endfunction

    virtual task body();
        // 1. Send a single WRITE transaction
        `uvm_info(get_type_name(), $sformatf("Sending single write request to addr %h...", addr), UVM_MEDIUM)
        start_item(req);
        if (!req.randomize() with {
            HWRITE == 1'b1;
            HTRANS == NONSEQ;
            HBURST == SINGLE;
            HADDR == local::addr;
            HWDATA == local::wr_data;
            HSIZE == HSIZE_WORD;
        }) `uvm_error("RNDFAIL", "Write randomize failed")
        finish_item(req);
        // Consume the response to prevent response queue overflow
        get_response(rsp);

        // 2. Send a single READ transaction to the same address
        `uvm_info(get_type_name(), $sformatf("Sending single read request to addr %h to verify...", addr), UVM_MEDIUM)
        start_item(req);
        if (!req.randomize() with {
            HWRITE == 1'b0;
            HTRANS == NONSEQ;
            HBURST == SINGLE;
            HADDR == local::addr;
            HSIZE == HSIZE_WORD;
        }) `uvm_error("RNDFAIL", "Read randomize failed")
        finish_item(req);
        // Get the response for the read transaction
        get_response(rsp);

        // 3. Verify the read data from the second response
        `uvm_info(get_type_name(), $sformatf("Read back data: %h", rsp.HRDATA), UVM_MEDIUM)
        if (rsp.HRDATA == wr_data) begin
            `uvm_info(get_type_name(), $sformatf("SUCCESS: Read data %h matches written data %h.", rsp.HRDATA, wr_data), UVM_LOW)
        end else begin
            `uvm_error(get_type_name(), $sformatf("FAILURE: Read data %h does not match written data %h", rsp.HRDATA, wr_data))
        end
    endtask

endclass
