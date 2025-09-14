class single_read_test extends base_test;

    `uvm_component_utils(single_read_test)

    function new(string name = "single_read_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual task run_phase(uvm_phase phase);
        ahb_single_read_sequence seq;

        phase.raise_objection(this);

        // Create and start the sequence
        seq = ahb_single_read_sequence::type_id::create("seq");
        seq.start(env.manager_agent.sequencer);

        #100ns;

        phase.drop_objection(this);
    endtask

endclass
