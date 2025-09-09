
import uvm_pkg::*;
`include "uvm_macros.svh"
import ahb_pkg::*;

class base_test extends uvm_test;

    // Components
    ahb_env env;

    // Configuration objects
    virtual ahb_if manager_vif;
    virtual ahb_if subordinate_vif;
    ahb_config manager_cfg;
    ahb_config subordinate_cfg;

    // UVM factory registration
    `uvm_component_utils(base_test)

    // Constructor
    function new(string name = "base_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);

        env = ahb_env::type_id::create("env", this);

        // Get VIFs from config_db (set by tb_top)
        if (!uvm_config_db#(virtual ahb_if)::get(this, "", "manager_if", manager_vif))
            `uvm_fatal(get_full_name(), "Manager VIF not found in config_db")
        if (!uvm_config_db#(virtual ahb_if)::get(this, "", "subordinate_if", subordinate_vif))
            `uvm_fatal(get_full_name(), "Subordinate VIF not found in config_db")

        // Create config objects for agents
        manager_cfg = ahb_config::type_id::create("manager_cfg");
        subordinate_cfg = ahb_config::type_id::create("subordinate_cfg");

        // Set VIFs in config objects
        manager_cfg.vif = manager_vif;
        subordinate_cfg.vif = subordinate_vif;

        // Assign config objects to env properties
        env.manager_cfg = manager_cfg;
        env.subordinate_cfg = subordinate_cfg;

    endfunction

endclass
