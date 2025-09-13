class ahb_single_read_sequence extends uvm_sequence#(ahb_sequence_item);

    `uvm_object_utils(ahb_single_read_sequence)

    function new(string name = "ahb_single_read_sequence");
        super.new(name);
    endfunction

    virtual task body();
        `uvm_info(get_type_name(), "Sending single read request...", UVM_MEDIUM)
        start_item(req);
        if (!req.randomize() with {
            HWRITE == 1'b0;
            HTRANS == NONSEQ;
            HBURST == SINGLE;
            HADDR == 32'h20;
            HSIZE == HSIZE_WORD;
        }) `uvm_error("RNDFAIL", "Read randomize failed")
        finish_item(req);
        // Consume the response. Data is in rsp.HRDATA if needed.
        get_response(rsp);
    endtask

endclass
