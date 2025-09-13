
class ahb_monitor extends uvm_monitor;

    ahb_config cfg;

    // Analysis port
    local uvm_analysis_port#(ahb_sequence_item) item_collected_port;

    `uvm_component_utils(ahb_monitor)

    function new(string name = "ahb_monitor", uvm_component parent = null);
        super.new(name, parent);
        item_collected_port = new("item_collected_port", this);
    endfunction

    virtual task run_phase(uvm_phase phase);
        forever begin
            @(cfg.vif.monitor_cb);
            if (cfg.vif.monitor_cb.HREADY && (cfg.vif.monitor_cb.HTRANS inside {NONSEQ, SEQ})) begin
                collect_transfer();
            end
        end
    endtask

    virtual protected task collect_transfer();
        ahb_sequence_item item = ahb_sequence_item::type_id::create("item");
        item.HADDR = cfg.vif.monitor_cb.HADDR;
        item.HWRITE = cfg.vif.monitor_cb.HWRITE;
        item.HSIZE = cfg.vif.monitor_cb.HSIZE;
        item.HTRANS = cfg.vif.monitor_cb.HTRANS;
        item.HWSTRB = cfg.vif.monitor_cb.HWSTRB;
        item.HBURST = cfg.vif.monitor_cb.HBURST;
        item.HPROT = cfg.vif.monitor_cb.HPROT;

        if (item.HWRITE) begin
            item.HWDATA = cfg.vif.monitor_cb.HWDATA;
        end else begin
            // For a read, data is available on the next cycle
            @(cfg.vif.monitor_cb);
            item.HRDATA = cfg.vif.monitor_cb.HRDATA;
        end

        `uvm_info("collect_transfer", $sformatf("Collected: %s", item.sprint()), UVM_HIGH)
        item_collected_port.write(item);
    endtask

    function uvm_analysis_port#(ahb_sequence_item) get_item_collected_port();
        return item_collected_port;
    endfunction

endclass
