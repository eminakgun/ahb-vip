class ahb_burst_transaction extends uvm_object;

    // Array of individual beats that form the burst
    ahb_sequence_item beats[];

    `uvm_object_utils(ahb_burst_transaction)

    function new(string name = "ahb_burst_transaction");
        super.new(name);
    endfunction

    // Override sprint to show the number of beats
    function string sprint(uvm_printer printer = null);
        sprint = $sformatf("Burst with %0d beats", beats.size());
    endfunction

endclass
