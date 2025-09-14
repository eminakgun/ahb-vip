class ahb_write_read_verify_sequence extends uvm_sequence#(ahb_sequence_item);
    `uvm_object_utils(ahb_write_read_verify_sequence)

    bit [31:0] addr;
    bit [31:0] wr_data;
    bit [31:0] rd_data;

    rand int iter = 0;

    constraint c_iter {
        iter inside {[1:10]};
    }

    function new(string name = "ahb_write_read_verify_sequence");
        super.new(name);
    endfunction

    virtual task body();
        `uvm_info(get_type_name(), $sformatf("Iteration count: %0d", iter), UVM_MEDIUM)
        repeat(iter) begin
            // 1. Send a single WRITE transaction
            begin
                ahb_sequence_item wr_req = ahb_sequence_item::type_id::create("wr_req");
                start_item(wr_req);
                if (!wr_req.randomize() with {
                    HWRITE == 1'b1;
                    HTRANS == NONSEQ;
                    HBURST == SINGLE;
                    HSIZE == HSIZE_WORD;
                }) `uvm_error("RNDFAIL", "Write randomize failed")
                `uvm_info(get_type_name(), $sformatf("Sending single write request to addr %h...", wr_req.HADDR), UVM_MEDIUM)
                finish_item(wr_req);

                // save write addr and data to compare later
                addr = wr_req.HADDR; 
                wr_data = wr_req.HWDATA;

                // Consume the response to prevent response queue overflow
                get_response(rsp);
            end

            // 2. Send a single READ transaction to the same address
            `uvm_info(get_type_name(), $sformatf("Sending single read request to addr %h to verify...", addr), UVM_MEDIUM)
            begin
                ahb_sequence_item rd_req = ahb_sequence_item::type_id::create("rd_req");
                start_item(rd_req);
                if (!rd_req.randomize() with {
                    HWRITE == 1'b0;
                    HTRANS == NONSEQ;
                    HBURST == SINGLE;
                    HADDR == addr;
                    HSIZE == HSIZE_WORD;
                }) `uvm_error("RNDFAIL", "Read randomize failed")
                finish_item(rd_req);

                // Get the response for the read transaction
                get_response(rsp);
                rd_data = rsp.HRDATA;
            end

            // 3. Verify the read data from the second response
            `uvm_info(get_type_name(), $sformatf("Read back data: %h", rsp.HRDATA), UVM_MEDIUM)
            if (rd_data == wr_data) begin
                `uvm_info(get_type_name(), $sformatf("SUCCESS: Read data %h matches written data %h.", rsp.HRDATA, wr_data), UVM_LOW)
            end else begin
                `uvm_error(get_type_name(), $sformatf("FAILURE: Read data %h does not match written data %h", rsp.HRDATA, wr_data))
            end
        end
        
    endtask

endclass
