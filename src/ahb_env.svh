
class ahb_env extends uvm_env;

    // Components
    ahb_agent manager_agent;
    ahb_agent subordinate_agent;
    ahb_config manager_cfg;
    ahb_config subordinate_cfg;
    // scoreboard placeholder

    // UVM factory registration
    `uvm_component_utils(ahb_env)

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

    endfunction

endclass
