
class ahb_driver extends uvm_driver#(ahb_sequence_item);

    virtual ahb_if vif;

    // UVM factory registration
    `uvm_component_utils(ahb_driver)

    // Constructor
    function new(string name = "ahb_driver", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    // Run phase
    virtual task run_phase(uvm_phase phase);
        forever begin
            seq_item_port.get_next_item(req);
            // Drive signals here
            seq_item_port.item_done();
        end
    endtask

endclass
