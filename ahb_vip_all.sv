// --- Start of file: src/ahb_if.sv ---

// AHB Interface
interface ahb_if#(
    parameter int ADDR_WIDTH = 32,
    parameter int DATA_WIDTH = 32
) (
    input logic HCLK,
    input logic HRESETn
);

    // Global signals
    logic [ADDR_WIDTH-1:0] HADDR;
    logic [2:0] HBURST;
    logic HMASTLOCK;
    logic [3:0] HPROT;
    logic [2:0] HSIZE;
    logic [1:0] HTRANS;
    logic [DATA_WIDTH-1:0] HWDATA;
    logic [DATA_WIDTH/8-1:0] HWSTRB;
    logic HWRITE;

    // Subordinate signals
    logic [DATA_WIDTH-1:0] HRDATA;
    logic HREADYOUT;
    logic HRESP;
    logic HSELx;

    // Manager signals
    logic HREADY;

    // Modports
    modport manager (
        output HADDR,
        output HBURST,
        output HMASTLOCK,
        output HPROT,
        output HSIZE,
        output HTRANS,
        output HWDATA,
        output HWSTRB,
        output HWRITE,
        input HRDATA,
        input HREADY,
        input HRESP
    );

    modport subordinate (
        input HADDR,
        input HBURST,
        input HMASTLOCK,
        input HPROT,
        input HSIZE,
        input HTRANS,
        input HWDATA,
        input HWSTRB,
        input HWRITE,
        input HSELx,
        output HRDATA,
        output HREADYOUT,
        output HRESP
    );

    modport monitor (
        input HCLK,
        input HRESETn,
        input HADDR,
        input HBURST,
        input HMASTLOCK,
        input HPROT,
        input HSIZE,
        input HTRANS,
        input HWDATA,
        input HWSTRB,
        input HWRITE,
        input HRDATA,
        input HREADY,
        input HRESP,
        input HSELx
    );

    // Manager Clocking Block
    clocking manager_cb @(posedge HCLK);
        default input #1step output #1ns;
        output HADDR, HBURST, HMASTLOCK, HPROT, HSIZE, HTRANS, HWDATA, HWSTRB, HWRITE;
        input HRDATA, HREADY, HRESP;
    endclocking

    // Subordinate Clocking Block
    clocking subordinate_cb @(posedge HCLK);
        default input #1step output #1ns;
        input HADDR, HBURST, HMASTLOCK, HPROT, HSIZE, HTRANS, HWDATA, HWSTRB, HWRITE, HSELx;
        output HRDATA, HREADYOUT, HRESP;
    endclocking

    // Monitor Clocking Block
    clocking monitor_cb @(posedge HCLK);
        default input #1step output #1ns;
        input HADDR, HBURST, HMASTLOCK, HPROT, HSIZE, HTRANS, HWDATA, HWSTRB, HWRITE, HRDATA, HREADY, HRESP, HSELx;
    endclocking

    // SVA: Check that HBURST remains stable throughout a burst transfer.
    a_hburst_stable: assert property (@(posedge HCLK) (HREADY && HTRANS == SEQ) |=> $stable(HBURST)) 
        else $error("SVA Error: HBURST changed value mid-burst.");

 endinterface

endinterface

// --- End of file: src/ahb_if.sv ---

// --- Start of file: src/ahb_pkg.sv (flattened) ---
package ahb_pkg;

    import uvm_pkg::*;

    `include "uvm_macros.svh"


// HTRANS values
typedef enum logic [1:0] {
    IDLE   = 2'b00,
    BUSY   = 2'b01,
    NONSEQ = 2'b10,
    SEQ    = 2'b11
} htrans_e;

// HBURST values
typedef enum logic [2:0] {
    SINGLE = 3'b000,
    INCR   = 3'b001,
    WRAP4  = 3'b010,
    INCR4  = 3'b011,
    WRAP8  = 3'b100,
    INCR8  = 3'b101,
    WRAP16 = 3'b110,
    INCR16 = 3'b111
} hburst_e;

// Agent type
typedef enum { MANAGER, SUBORDINATE } agent_type_e;

// HSIZE values
typedef enum logic [2:0] {
    HSIZE_BYTE   = 3'b000,
    HSIZE_HWORD  = 3'b001,
    HSIZE_WORD   = 3'b010,
    HSIZE_4_WORD = 3'b011,
    HSIZE_8_WORD = 3'b100,
    HSIZE_16_WORD = 3'b101,
    HSIZE_32_WORD = 3'b110,
    HSIZE_64_WORD = 3'b111
} hsize_e;



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




class ahb_sequence_item extends uvm_sequence_item;

    // Properties
    rand bit [31:0] HADDR;
    rand bit HWRITE;
    rand bit [31:0] HWDATA;
    rand bit [31:0] HRDATA;
    rand bit [3:0] HWSTRB;
    rand htrans_e HTRANS;
    rand hsize_e HSIZE;
    rand hburst_e HBURST;

    // UVM factory registration
    `uvm_object_utils_begin(ahb_sequence_item)
        `uvm_field_int(HADDR, UVM_ALL_ON)
        `uvm_field_int(HWRITE, UVM_ALL_ON)
        `uvm_field_int(HWDATA, UVM_ALL_ON)
        `uvm_field_int(HRDATA, UVM_ALL_ON | UVM_READONLY)
        `uvm_field_int(HWSTRB, UVM_ALL_ON)
        `uvm_field_enum(htrans_e, HTRANS, UVM_ALL_ON)
        `uvm_field_enum(hsize_e, HSIZE, UVM_ALL_ON)
        `uvm_field_enum(hburst_e, HBURST, UVM_ALL_ON)
    `uvm_object_utils_end

    // Constructor
    function new(string name = "ahb_sequence_item");
        super.new(name);
    endfunction

    // Constraints
    constraint c_valid_transfer {
        HTRANS inside {IDLE, BUSY, NONSEQ, SEQ};
        HSIZE inside {HSIZE_BYTE, HSIZE_HWORD, HSIZE_WORD};
        HBURST inside {SINGLE, INCR4}; // For now
    }

endclass


class ahb_burst_transaction extends uvm_object;

    // Array of individual beats that form the burst
    ahb_sequence_item beats[];

    `uvm_object_utils(ahb_burst_transaction)

    function new(string name = "ahb_burst_transaction");
        super.new(name);
    endfunction

    // Override sprint to show the number of beats
    function string sprint(uvm_printer printer = null);
        sprint = $sformatf("Burst with %0d beats", beats.size());
    endfunction

endclass


class ahb_single_write_sequence extends uvm_sequence#(ahb_sequence_item);

    `uvm_object_utils(ahb_single_write_sequence)

    function new(string name = "ahb_single_write_sequence");
        super.new(name);
    endfunction

    virtual task body();
        `uvm_info(get_type_name(), "Sending single write request...", UVM_MEDIUM)
        start_item(req);
        if (!req.randomize() with {
            HWRITE == 1'b1;
            HTRANS == NONSEQ;
            HBURST == SINGLE;
            HADDR == 32'h10;
            HWDATA == 32'hDEADBEEF;
            HSIZE == HSIZE_WORD;
        }) `uvm_error("RNDFAIL", "Write randomize failed")
        finish_item(req);
        // Consume the response to prevent response queue overflow, but do not check it.
        get_response(rsp);
    endtask

endclass


class ahb_single_read_sequence extends uvm_sequence#(ahb_sequence_item);

    `uvm_object_utils(ahb_single_read_sequence)

    function new(string name = "ahb_single_read_sequence");
        super.new(name);
    endfunction

    virtual task body();
        `uvm_info(get_type_name(), "Sending single read request...", UVM_MEDIUM)
        start_item(req);
        if (!req.randomize() with {
            HWRITE == 1'b0;
            HTRANS == NONSEQ;
            HBURST == SINGLE;
            HADDR == 32'h20;
            HSIZE == HSIZE_WORD;
        }) `uvm_error("RNDFAIL", "Read randomize failed")
        finish_item(req);
        // Consume the response. Data is in rsp.HRDATA if needed.
        get_response(rsp);
    endtask

endclass


class ahb_write_read_verify_sequence extends uvm_sequence#(ahb_sequence_item);

    `uvm_object_utils(ahb_write_read_verify_sequence)

    rand uvm_reg_addr_t addr;
    rand uvm_reg_data_t wr_data;

    function new(string name = "ahb_write_read_verify_sequence");
        super.new(name);
    endfunction

    virtual task body();
        // 1. Send a single WRITE transaction
        `uvm_info(get_type_name(), $sformatf("Sending single write request to addr %h...", addr), UVM_MEDIUM)
        start_item(req);
        if (!req.randomize() with {
            HWRITE == 1'b1;
            HTRANS == NONSEQ;
            HBURST == SINGLE;
            HADDR == local::addr;
            HWDATA == local::wr_data;
            HSIZE == HSIZE_WORD;
        }) `uvm_error("RNDFAIL", "Write randomize failed")
        finish_item(req);
        // Consume the response to prevent response queue overflow
        get_response(rsp);

        // 2. Send a single READ transaction to the same address
        `uvm_info(get_type_name(), $sformatf("Sending single read request to addr %h to verify...", addr), UVM_MEDIUM)
        start_item(req);
        if (!req.randomize() with {
            HWRITE == 1'b0;
            HTRANS == NONSEQ;
            HBURST == SINGLE;
            HADDR == local::addr;
            HSIZE == HSIZE_WORD;
        }) `uvm_error("RNDFAIL", "Read randomize failed")
        finish_item(req);
        // Get the response for the read transaction
        get_response(rsp);

        // 3. Verify the read data from the second response
        `uvm_info(get_type_name(), $sformatf("Read back data: %h", rsp.HRDATA), UVM_MEDIUM)
        if (rsp.HRDATA == wr_data) begin
            `uvm_info(get_type_name(), $sformatf("SUCCESS: Read data %h matches written data %h.", rsp.HRDATA, wr_data), UVM_LOW)
        end else begin
            `uvm_error(get_type_name(), $sformatf("FAILURE: Read data %h does not match written data %h", rsp.HRDATA, wr_data))
        end
    endtask

endclass


class ahb_incr4_write_read_sequence extends uvm_sequence#(ahb_sequence_item);

    `uvm_object_utils(ahb_incr4_write_read_sequence)

    rand bit[31:0] start_addr;
    rand bit[31:0] write_data[4];
    bit[31:0] read_data[4];

    function new(string name = "ahb_incr4_write_read_sequence");
        super.new(name);
        constraint c_addr { start_addr inside {[32'h0:32'hF0]}; }
    endfunction

    virtual task body();
        // 1. INCR4 Write Burst
        `uvm_info(get_type_name(), "Starting INCR4 Write Burst", UVM_MEDIUM)
        for (int i = 0; i < 4; i++) begin
            `uvm_do_with(req, {
                HWRITE == 1'b1;
                HTRANS == (i == 0) ? NONSEQ : SEQ;
                HBURST == INCR4;
                HADDR == start_addr + (i * 4);
                HSIZE == HSIZE_WORD;
                HWDATA == write_data[i];
            })
        end

        // 2. INCR4 Read Burst
        `uvm_info(get_type_name(), "Starting INCR4 Read Burst", UVM_MEDIUM)
        for (int i = 0; i < 4; i++) begin
            `uvm_do_with(req, {
                HWRITE == 1'b0;
                HTRANS == (i == 0) ? NONSEQ : SEQ;
                HBURST == INCR4;
                HADDR == start_addr + (i * 4);
                HSIZE == HSIZE_WORD;
            })
            read_data[i] = req.HRDATA;
        end

        // 3. Verification
        `uvm_info(get_type_name(), "Verifying data...", UVM_MEDIUM)
        for (int i = 0; i < 4; i++) begin
            if (read_data[i] != write_data[i]) begin
                `uvm_error(get_type_name(), $sformatf("Data mismatch at index %0d: Wrote %0h, Read %0h", i, write_data[i], read_data[i]))
            end
        end
        `uvm_info(get_type_name(), "Data verification complete.", UVM_MEDIUM)

    endtask

endclass



class ahb_sequencer extends uvm_sequencer#(ahb_sequence_item);

    // UVM factory registration
    `uvm_component_utils(ahb_sequencer)

    // Constructor
    function new(string name = "ahb_sequencer", uvm_component parent = null);
        super.new(name, parent);
    endfunction

endclass



class ahb_driver extends uvm_driver#(ahb_sequence_item);

    ahb_config cfg;

    // A simple memory model for the subordinate
    logic [31:0] mem [255:0];

    `uvm_component_utils(ahb_driver)

    function new(string name = "ahb_driver", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual task run_phase(uvm_phase phase);
        if (cfg.is_active == UVM_PASSIVE) return;

        drive_idle();

        if (cfg.agent_type == MANAGER) begin
            manager_get_put_loop(phase);
        end else begin // SUBORDINATE
            subordinate_run_phase(phase);
        end
    endtask

    // This is the main manager loop based on the get/put pattern.
    virtual task manager_get_put_loop(uvm_phase phase);
        forever begin
            ahb_sequence_item req, rsp;
            seq_item_port.get(req);
            drive_transfer(req, rsp);
        end
    endtask

    // This task orchestrates the pipelined transfer.
    virtual task drive_transfer(input ahb_sequence_item req, output ahb_sequence_item rsp);
        assert($cast(rsp, req.clone()));

        // Drive the address phase for this transaction
        drive_address_phase(rsp);

        // Fork a process to handle the data phase and completion
        fork
            begin
                // Data phase for the transaction begins on the next clock edge.
                @(cfg.vif.manager_cb);

                // Drive write data during the data phase.
                drive_data_phase(rsp);

                // Wait for the subordinate to signal it can complete the transfer.
                // This loop finishes on the clock edge where HREADY is high.
                do begin
                    @(cfg.vif.manager_cb);
                end while (cfg.vif.manager_cb.HREADY == 1'b0) 

                // Capture read data.
                if (!rsp.HWRITE) begin
                    rsp.HRDATA = cfg.vif.manager_cb.HRDATA;
                end
                seq_item_port.put(rsp); // signal to calling sequence
            end
        join_none
    endtask

    virtual protected task drive_address_phase(ahb_sequence_item item);
        @(cfg.vif.manager_cb);
        cfg.vif.manager_cb.HADDR <= item.HADDR;
        cfg.vif.manager_cb.HWRITE <= item.HWRITE;
        cfg.vif.manager_cb.HSIZE <= item.HSIZE;
        cfg.vif.manager_cb.HTRANS <= item.HTRANS;
        cfg.vif.manager_cb.HBURST <= item.HBURST;
        cfg.vif.manager_cb.HPROT <= 4'b0011;
    endtask

    virtual protected task drive_data_phase(ahb_sequence_item item);
        if (item.HWRITE) begin
            cfg.vif.manager_cb.HWDATA <= item.HWDATA;
        end
    endtask

    virtual protected task drive_idle();
        @(cfg.vif.manager_cb);
        cfg.vif.manager_cb.HTRANS <= IDLE;
        cfg.vif.manager_cb.HADDR <= 0;
        cfg.vif.manager_cb.HWRITE <= 0;
        cfg.vif.manager_cb.HBURST <= SINGLE;
    endtask

    virtual task subordinate_run_phase(uvm_phase phase);
        logic data_phase_active = 0;
        logic [31:0] data_phase_HADDR;
        logic data_phase_HWRITE;

        // Initialize outputs to a safe state
        cfg.vif.subordinate_cb.HREADYOUT <= 1'b1;
        cfg.vif.subordinate_cb.HRESP     <= 1'b0;
        cfg.vif.subordinate_cb.HRDATA    <= 'z;

        forever begin
            @(cfg.vif.subordinate_cb);

            //==================================================================
            // Data Phase Stage (for transfer captured in the previous cycle)
            //==================================================================
            if (data_phase_active) begin
                if (data_phase_HWRITE) begin
                    // On a write, sample the write data from the bus
                    mem[data_phase_HADDR[7:0]] <= cfg.vif.subordinate_cb.HWDATA;
                end
                // For a read, HRDATA was already driven in the previous cycle (address phase)
            end

            //==================================================================
            // Address Phase Stage (for transfer starting in the current cycle)
            //==================================================================
            if (cfg.vif.subordinate_cb.HSELx && cfg.vif.subordinate_cb.HTRANS inside {NONSEQ, SEQ}) begin
                // A new transfer is starting. Capture its details for the data phase next cycle.
                data_phase_active = 1;
                data_phase_HADDR  = cfg.vif.subordinate_cb.HADDR;
                data_phase_HWRITE = cfg.vif.subordinate_cb.HWRITE;

                // Set response for the current transfer (zero wait states)
                cfg.vif.subordinate_cb.HREADYOUT <= 1'b1;
                cfg.vif.subordinate_cb.HRESP     <= 1'b0; // OKAY

                if (!data_phase_HWRITE) begin // This is a read transfer
                    // Fetch data and drive it onto HRDATA. It will be valid for the manager to sample next cycle.
                    cfg.vif.subordinate_cb.HRDATA <= mem[data_phase_HADDR[7:0]];
                end else begin
                    // Stop driving HRDATA during write transfers
                    cfg.vif.subordinate_cb.HRDATA <= 'z;
                end
            end else begin
                // No new transfer is starting.
                data_phase_active = 0;
                cfg.vif.subordinate_cb.HREADYOUT <= 1'b1;
                cfg.vif.subordinate_cb.HRDATA    <= 'z; // Stop driving HRDATA
            end
        end
    endtask

endclass


class ahb_monitor extends uvm_monitor;

    ahb_config cfg;

    // Analysis port for individual beats
    uvm_analysis_port#(ahb_sequence_item) beat_ap;
    // Analysis port for completed burst transactions
    uvm_analysis_port#(ahb_burst_transaction) burst_ap;

    `uvm_component_utils(ahb_monitor)

    // Internal pipeline register for address phase
    protected ahb_sequence_item addr_phase_tr;
    protected bit addr_phase_valid = 0;

    // FSM for burst collection
    typedef enum {IDLE, IN_BURST} state_e;
    state_e state = IDLE;
    ahb_burst_transaction burst_tr;
    int beats_left;
    hburst_e active_burst_type;
    bit [31:0] start_addr;

    function new(string name = "ahb_monitor", uvm_component parent = null);
        super.new(name, parent);
        beat_ap = new("beat_ap", this);
        burst_ap = new("burst_ap", this);
    endfunction

    virtual task run_phase(uvm_phase phase);
        forever begin
            @(cfg.vif.monitor_cb);

            // -----------------------------------------------------------------
            // -- Data Phase Processing
            // -- Combine address (from last cycle) with data (from this cycle)
            // -----------------------------------------------------------------
            if (addr_phase_valid && cfg.vif.monitor_cb.HREADY) begin
                ahb_sequence_item complete_beat = addr_phase_tr;
                addr_phase_valid = 0; // Consume the address phase

                if (complete_beat.HWRITE) begin
                    complete_beat.HWDATA = cfg.vif.monitor_cb.HWDATA;
                end else begin
                    complete_beat.HRDATA = cfg.vif.monitor_cb.HRDATA;
                end
                
                process_complete_beat(complete_beat);
            end

            // -----------------------------------------------------------------
            // -- Address Phase Processing
            // -- Capture the start of a new transfer
            // -----------------------------------------------------------------
            if (cfg.vif.monitor_cb.HSELx && cfg.vif.monitor_cb.HTRANS inside {NONSEQ, SEQ}) begin
                if (addr_phase_valid) begin
                    `uvm_error("AHB_PROTOCOL_ERROR", "New transfer started before previous data phase completed (HREADY was low)")
                end
                addr_phase_tr = ahb_sequence_item::type_id::create("addr_phase_tr");
                addr_phase_tr.HADDR  = cfg.vif.monitor_cb.HADDR;
                addr_phase_tr.HWRITE = cfg.vif.monitor_cb.HWRITE;
                addr_phase_tr.HSIZE  = cfg.vif.monitor_cb.HSIZE;
                addr_phase_tr.HTRANS = cfg.vif.monitor_cb.HTRANS;
                addr_phase_tr.HWSTRB = cfg.vif.monitor_cb.HWSTRB;
                addr_phase_tr.HBURST = cfg.vif.monitor_cb.HBURST;
                addr_phase_tr.HPROT  = cfg.vif.monitor_cb.HPROT;
                addr_phase_valid = 1;
            end
        end
    endtask

    virtual protected task process_complete_beat(ahb_sequence_item beat);
        // Publish every complete beat
        `uvm_info("BEAT_COLLECTED", $sformatf("Beat collected: %s", beat.sprint()), UVM_HIGH)
        beat_ap.write(beat);

        // Process the beat in the context of the burst FSM
        case (state)
            IDLE: begin
                if (beat.HTRANS == SEQ) begin
                    `uvm_error("AHB_PROTOCOL_ERROR", $sformatf("Illegal SEQ transfer detected at address %h while not in a burst. A burst must start with a NONSEQ transfer.", beat.HADDR))
                    return;
                end

                if (beat.HBURST == SINGLE) begin
                    ahb_burst_transaction single_beat_burst = new("single_beat_burst");
                    single_beat_burst.beats.push_back(beat);
                    `uvm_info("BURST_COMPLETE", $sformatf("SINGLE beat burst complete: %s", single_beat_burst.sprint()), UVM_MEDIUM)
                    burst_ap.write(single_beat_burst);
                end else begin // Start of a multi-beat burst
                    `uvm_info("FSM_STATE_CHANGE", $sformatf("IDLE -> IN_BURST. Burst of type %s started at addr %h.", beat.HBURST.name(), beat.HADDR), UVM_MEDIUM)
                    burst_tr = new("burst_tr");
                    burst_tr.beats.push_back(beat);
                    beats_left = get_burst_length(beat.HBURST) - 1;
                    active_burst_type = beat.HBURST;
                    start_addr = beat.HADDR;
                    state = IN_BURST;
                end
            end

            IN_BURST: begin
                if (beat.HTRANS != SEQ) begin
                    `uvm_error("AHB_PROTOCOL_ERROR", $sformatf("Burst started at %h of type %s terminated unexpectedly with HTRANS=%s", start_addr, active_burst_type.name(), beat.HTRANS.name()))
                    burst_ap.write(burst_tr); // Publish partial burst
                    state = IDLE;
                    // TODO: Re-process the current beat as a new transaction if it was NONSEQ
                    return;
                end
                

                burst_tr.beats.push_back(beat);
                beats_left--;

                if (beats_left <= 0) begin
                    `uvm_info("BURST_COMPLETE", $sformatf("Burst of type %s complete. %s", active_burst_type.name(), burst_tr.sprint()), UVM_MEDIUM)
                    burst_ap.write(burst_tr);
                    `uvm_info("FSM_STATE_CHANGE", "IN_BURST -> IDLE.", UVM_MEDIUM)
                    state = IDLE;
                end
            end
        endcase
    endtask

    function int get_burst_length(hburst_e burst);
        case(burst)
            SINGLE: return 1;
            INCR4, WRAP4: return 4;
            INCR8, WRAP8: return 8;
            INCR16, WRAP16: return 16;
            INCR: return -1; // Undefined length
            default: return 1;
        endcase
    endfunction

endclass





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



endpackage// --- End of file: src/ahb_pkg.sv (flattened) ---

// --- Start of file: tests/base_test.sv ---

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
        manager_cfg.is_active = UVM_ACTIVE;
        manager_cfg.agent_type = MANAGER;

        subordinate_cfg.vif = subordinate_vif;
        subordinate_cfg.is_active = UVM_ACTIVE;
        subordinate_cfg.agent_type = SUBORDINATE;

        // Assign config objects to env properties
        env.manager_cfg = manager_cfg;
        env.subordinate_cfg = subordinate_cfg;

    endfunction

endclass

// --- End of file: tests/base_test.sv ---

// --- Start of file: tb_top.sv ---

`timescale 1ns / 1ps

module tb_top;

    // Clock and Reset Generation
    logic HCLK;
    logic HRESETn;

    initial begin
        HCLK = 0;
        forever #5 HCLK = ~HCLK; // 100 MHz clock
    end

    initial begin
        HRESETn = 0;
        #100; // Hold reset for 100ns
        HRESETn = 1;
    end

    // Instantiate AHB Interfaces
    ahb_if#(32, 32) manager_if(.HCLK(HCLK), .HRESETn(HRESETn));
    ahb_if#(32, 32) subordinate_if(.HCLK(HCLK), .HRESETn(HRESETn));

    // Instantiate the UVM testbench
    initial begin
        // Set interface handles to the config_db
        uvm_config_db#(virtual ahb_if)::set(null, "uvm_test_top", "manager_if", manager_if);
        uvm_config_db#(virtual ahb_if)::set(null, "uvm_test_top", "subordinate_if", subordinate_if);

        // Run the UVM test
        run_test("base_test");
    end

endmodule

// --- End of file: tb_top.sv ---

