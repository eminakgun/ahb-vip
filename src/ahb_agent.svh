


class ahb_agent extends uvm_agent;

    // Components
    ahb_sequencer   sequencer;
    ahb_driver      driver;
    ahb_monitor     monitor;

    uvm_analysis_port#(ahb_sequence_item) ap;

    // Configuration
    ahb_config cfg;

    // UVM factory registration
    `uvm_component_utils(ahb_agent)

    // Constructor
    function new(string name = "ahb_agent", uvm_component parent = null);
        super.new(name, parent);
        ap = new("ap", this);
    endfunction

    // Build phase
    function void build_phase(uvm_phase phase);

        uvm_config_db#(ahb_config)::get(this, "", "cfg", cfg);

        monitor = ahb_monitor::type_id::create("monitor", this);
        monitor.cfg = cfg;

        if (cfg.is_active == UVM_ACTIVE) begin
            driver = ahb_driver::type_id::create("driver", this);
            driver.cfg = cfg;
            sequencer = ahb_sequencer::type_id::create("sequencer", this);
        end
    endfunction

    // Connect phase
    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        monitor.get_item_collected_port().connect(ap);
        if (cfg.is_active == UVM_ACTIVE) begin
            driver.seq_item_port.connect(sequencer.seq_item_export);
        end
    endfunction

endclass
