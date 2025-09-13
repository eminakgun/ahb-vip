
class ahb_config extends uvm_object;

    // Properties
    uvm_active_passive_enum is_active = UVM_ACTIVE;
    agent_type_e agent_type = MANAGER;
    virtual ahb_if vif;

    // UVM factory registration
    `uvm_object_utils(ahb_config)

    // Constructor
    function new(string name = "ahb_config");
        super.new(name);
    endfunction

endclass
