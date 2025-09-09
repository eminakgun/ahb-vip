
class ahb_monitor extends uvm_monitor;

    virtual ahb_if vif;

    // Analysis port
    local uvm_analysis_port#(ahb_sequence_item) item_collected_port;

    // UVM factory registration
    `uvm_component_utils(ahb_monitor)

    // Constructor
    function new(string name = "ahb_monitor", uvm_component parent = null);
        super.new(name, parent);
        item_collected_port = new("item_collected_port", this);
    endfunction

    // Run phase
    virtual task run_phase(uvm_phase phase);
        // Sample signals here
    endtask

    function uvm_analysis_port#(ahb_sequence_item) get_item_collected_port();
        return item_collected_port;
    endfunction

endclass
