class coverage_collector extends uvm_subscriber#(ahb_sequence_item);

    `uvm_component_utils(coverage_collector)

    // Transaction item to be sampled
    ahb_sequence_item tr;

    // Covergroup for basic AHB transfer properties
    covergroup ahb_transfer_cg;
        option.per_instance = 1;

        // Cover HTRANS
        cp_htrans: coverpoint tr.HTRANS {
            bins idle    = {IDLE};
            bins busy    = {BUSY};
            bins nonseq  = {NONSEQ};
            bins seq     = {SEQ};
        }

        // Cover HBURST
        cp_hburst: coverpoint tr.HBURST {
            bins single  = {SINGLE};
            bins incr4   = {INCR4};
            // TODO: Add other burst types as they are supported
        }

        // Cover HSIZE
        cp_hsize: coverpoint tr.HSIZE {
            bins size_byte    = {HSIZE_BYTE};
            bins size_hword   = {HSIZE_HWORD};
            bins size_word    = {HSIZE_WORD};
        }

        // Cover HWRITE
        cp_hwrite: coverpoint tr.HWRITE {
            bins write = {1'b1};
            bins read  = {1'b0};
        }
    endgroup

    function new(string name = "coverage_collector", uvm_component parent = null);
        super.new(name, parent);
        ahb_transfer_cg = new();
    endfunction

    // The write method is called by the analysis port to sample the transaction
    function void write(ahb_sequence_item t);
        this.tr = t;
        ahb_transfer_cg.sample();
        `uvm_info("COVERAGE", $sformatf("Sampled transaction: %s", t.sprint()), UVM_HIGH)
    endfunction

    function void report_phase(uvm_phase phase);
        super.report_phase(phase);
        `uvm_info("COVERAGE_REPORT", $sformatf("AHB Transfer Coverage: %3.2f%%", ahb_transfer_cg.get_inst_coverage()), UVM_LOW)
    endfunction

endclass
