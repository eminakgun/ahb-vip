
class ahb_env extends uvm_env;
    `uvm_component_utils(ahb_env)

    // Components
    ahb_agent manager_agent;
    ahb_agent subordinate_agent;
    ahb_scoreboard scoreboard;

    // Configuration objects
    ahb_config manager_cfg;
    ahb_config subordinate_cfg;

    // Constructor
    function new(string name = "ahb_env", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    // Build phase
    function void build_phase(uvm_phase phase);

        // Set config objects for agents from env properties
        uvm_config_db#(ahb_config)::set(this, "manager_agent", "cfg", manager_cfg);
        uvm_config_db#(ahb_config)::set(this, "subordinate_agent", "cfg", subordinate_cfg);

        manager_agent = ahb_agent::type_id::create("manager_agent", this);
        subordinate_agent = ahb_agent::type_id::create("subordinate_agent", this);

        // Create scoreboard
        scoreboard = ahb_scoreboard::type_id::create("scoreboard", this);

    endfunction

    // Connect phase - connect agents to scoreboard
    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        
        // Connect manager agent's analysis port to scoreboard
        manager_agent.ap.connect(scoreboard.mgr_export);
        
        // Connect subordinate agent's analysis port to scoreboard (optional)
        // subordinate_agent.ap.connect(scoreboard.sub_export);
    endfunction

endclass
