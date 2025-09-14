class single_write_test extends base_test;

    `uvm_component_utils(single_write_test)

    function new(string name = "single_write_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual task run_phase(uvm_phase phase);
        ahb_single_write_sequence seq;

        phase.raise_objection(this);

        // Create and start the sequence
        seq = ahb_single_write_sequence::type_id::create("seq");
        seq.start(env.manager_agent.sequencer);
        
        // Add a small delay to let the transfer complete
        #100ns;

        phase.drop_objection(this);
    endtask

endclass
