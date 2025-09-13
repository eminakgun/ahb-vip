class ahb_single_write_sequence extends uvm_sequence#(ahb_sequence_item);

    `uvm_object_utils(ahb_single_write_sequence)

    function new(string name = "ahb_single_write_sequence");
        super.new(name);
    endfunction

    virtual task body();
        `uvm_info(get_type_name(), "Sending single write request...", UVM_MEDIUM)
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
        // Consume the response to prevent response queue overflow, but do not check it.
        get_response(rsp);
    endtask

endclass
