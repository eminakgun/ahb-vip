class write_read_verify_test extends base_test;

    `uvm_component_utils(write_read_verify_test)

    function new(string name = "write_read_verify_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual task run_phase(uvm_phase phase);
        ahb_write_read_verify_sequence seq;

        phase.raise_objection(this);

        // Create and start the sequence
        seq = ahb_write_read_verify_sequence::type_id::create("seq");
        // Let the sequence choose a random address and data
        assert(seq.randomize());
        seq.start(env.manager_agent.sequencer);

        #200ns;

        phase.drop_objection(this);
    endtask

endclass
