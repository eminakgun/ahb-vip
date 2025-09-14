class incr4_write_read_test extends base_test;

    `uvm_component_utils(incr4_write_read_test)

    function new(string name = "incr4_write_read_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual task run_phase(uvm_phase phase);
        ahb_incr4_write_read_sequence seq;

        phase.raise_objection(this);

        seq = ahb_incr4_write_read_sequence::type_id::create("seq");
        assert(seq.randomize());
        seq.start(env.manager_agent.sequencer);

        #200ns; // Longer delay for the burst

        phase.drop_objection(this);
    endtask

endclass
