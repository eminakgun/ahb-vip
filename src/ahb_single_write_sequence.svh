class ahb_single_write_sequence extends uvm_sequence#(ahb_sequence_item);

    `uvm_object_utils(ahb_single_write_sequence)

    function new(string name = "ahb_single_write_sequence");
        super.new(name);
    endfunction

    virtual task body();
        // 1. Send a single WRITE transaction
        `uvm_info(get_type_name(), "Starting single write request...", UVM_MEDIUM)
        start_item(req);
        if (!req.randomize() with {
            HWRITE == 1'b1;
            HTRANS == NONSEQ;
            HBURST == SINGLE;
            HADDR == 32'h10;
            HWDATA == 32'hDEADBEEF;
            HSIZE == HSIZE_WORD;
        }) `uvm_error("RNDFAIL", "Write randomize failed")
        finish_item(req);
        // Must get the response that the driver sends via put()
        get_response(rsp);

        // 2. Send a single READ transaction to the same address
        `uvm_info(get_type_name(), "Starting single read request to verify...", UVM_MEDIUM)
        start_item(req);
        if (!req.randomize() with {
            HWRITE == 1'b0;
            HTRANS == NONSEQ;
            HBURST == SINGLE;
            HADDR == 32'h10;
            HSIZE == HSIZE_WORD;
        }) `uvm_error("RNDFAIL", "Read randomize failed")
        finish_item(req);
        // Get the response for the read transaction
        get_response(rsp);

        // 3. Verify the read data from the second response
        `uvm_info(get_type_name(), $sformatf("Read back data: %h", rsp.HRDATA), UVM_MEDIUM)
        if (rsp.HRDATA == 32'hDEADBEEF) begin
            `uvm_info(get_type_name(), "SUCCESS: Read data matches written data.", UVM_LOW)
        end else begin
            `uvm_error(get_type_name(), $sformatf("FAILURE: Read data %h does not match written data %h", rsp.HRDATA, 32'hDEADBEEF))
        end
    endtask

endclass
