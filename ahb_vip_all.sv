// ========================================
// Flattened SystemVerilog AHB VIP Package
// Generated automatically - do not edit
// ========================================

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

    // ===========================================================
    // Protocol Checkers
    // ===========================================================

    // SVA: Check that HBURST remains stable throughout a burst transfer.
    // SEQ    = 2'b11
    property p_hburst_stable
        @(posedge HCLK) disable iff(!HRESETn)
        (HREADY && HTRANS == 2'b11) |=> $stable(HBURST);
    endproperty
    a_hburst_stable: assert property (p_hburst_stable)
        else $error("SVA Error: HBURST changed value mid-burst.");

    // SVA: Check that second Cycle of HRESP should have HTRANS == IDLE to
    // cancel data phase of previous transaction
    property idle_on_err_p;
        @(posedge HCLK) disable iff(!HRESETn)
        (HRESP == 1) ##1 (HRESP == 1) |-> (HTRANS == 0);
    endproperty
    a_idle_on_error: assert property (idle_on_err_p)
        else $error("SVA Error: HBURST changed value mid-burst.");

    // SVA: Check that subordinates doesn't insert wait states for IDLE transfers
    property idle_okay_p;
        @(posedge HCLK) disable iff(!HRESETn)
        (HTRANS == 0) |=> (HRESP == 0);
    endproperty
    a_idle_on_error: assert property (idle_okay_p)
        else $error("SVA Error: HBURST changed value mid-burst.");

endinterface
// --- End of file: src/ahb_if.sv ---

// --- Start of file: src/ahb_pkg.sv (flattened) ---
package ahb_pkg;

    import uvm_pkg::*;

    `include "uvm_macros.svh"

  // --- Content from ahb_types.svh ---

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

function bit is_burst(hburst_e burst);
    return burst != SINGLE;
endfunction

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
  // --- End of ahb_types.svh ---

  // --- Content from ahb_config.svh ---

class ahb_config extends uvm_object;

    // Properties
    uvm_active_passive_enum is_active = UVM_ACTIVE;
    agent_type_e agent_type = MANAGER;
    virtual ahb_if vif;
    bit en_cov = 0;

    // UVM factory registration
    `uvm_object_utils(ahb_config)

    // Constructor
    function new(string name = "ahb_config");
        super.new(name);
    endfunction

endclass
  // --- End of ahb_config.svh ---


  // --- Content from ahb_sequence_item.svh ---

class ahb_sequence_item extends uvm_sequence_item;

    // Properties
    rand bit [31:0] HADDR;
    rand bit HWRITE;
    rand bit [31:0] HWDATA;
    rand bit [31:0] HRDATA;
    rand bit [3:0] HWSTRB;
    rand bit [3:0] HPROT;
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
        HBURST inside {SINGLE, INCR4}; // Only support single and incr4 burst for now
        soft (HSIZE == HSIZE_HWORD) -> HADDR % 16 == 0;
        soft (HSIZE == HSIZE_WORD) -> HADDR % 32 == 0;
    }

endclass
  // --- End of ahb_sequence_item.svh ---

  // --- Content from ahb_burst_transaction.svh ---
class ahb_burst_transaction extends uvm_object;

    // Array of individual beats that form the burst
    ahb_sequence_item beats[$];

    `uvm_object_utils(ahb_burst_transaction)

    function new(string name = "ahb_burst_transaction");
        super.new(name);
    endfunction

    // Override sprint to show the number of beats
    function string sprint(uvm_printer printer = null);
        sprint = $sformatf("Burst with %0d beats", beats.size());
    endfunction

endclass
  // --- End of ahb_burst_transaction.svh ---

  // --- Content from ahb_single_write_sequence.svh ---
class ahb_single_write_sequence extends uvm_sequence#(ahb_sequence_item);

    `uvm_object_utils(ahb_single_write_sequence)

    function new(string name = "ahb_single_write_sequence");
        super.new(name);
    endfunction

    virtual task body();
        `uvm_info(get_type_name(), "Sending single write request...", UVM_MEDIUM)
        req = ahb_sequence_item::type_id::create("req");
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
  // --- End of ahb_single_write_sequence.svh ---

  // --- Content from ahb_single_read_sequence.svh ---
class ahb_single_read_sequence extends uvm_sequence#(ahb_sequence_item);

    `uvm_object_utils(ahb_single_read_sequence)

    function new(string name = "ahb_single_read_sequence");
        super.new(name);
    endfunction

    virtual task body();
        `uvm_info(get_type_name(), "Sending single read request...", UVM_MEDIUM)
        req = ahb_sequence_item::type_id::create("req");
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
  // --- End of ahb_single_read_sequence.svh ---

  // --- Content from ahb_write_read_verify_sequence.svh ---
class ahb_write_read_verify_sequence extends uvm_sequence#(ahb_sequence_item);
    `uvm_object_utils(ahb_write_read_verify_sequence)

    bit [31:0] addr;
    bit [31:0] wr_data;
    bit [31:0] rd_data;

    rand int iter = 0;

    constraint c_iter {
        iter inside {[1:10]};
    }

    function new(string name = "ahb_write_read_verify_sequence");
        super.new(name);
    endfunction

    virtual task body();
        `uvm_info(get_type_name(), $sformatf("Iteration count: %0d", iter), UVM_MEDIUM)
        repeat(iter) begin
            // 1. Send a single WRITE transaction
            begin
                ahb_sequence_item wr_req = ahb_sequence_item::type_id::create("wr_req");
                start_item(wr_req);
                if (!wr_req.randomize() with {
                    HWRITE == 1'b1;
                    HTRANS == NONSEQ;
                    HBURST == SINGLE;
                    HSIZE == HSIZE_WORD;
                }) `uvm_error("RNDFAIL", "Write randomize failed")
                `uvm_info(get_type_name(), $sformatf("Sending single write request to addr %h...", wr_req.HADDR), UVM_MEDIUM)
                finish_item(wr_req);

                // save write addr and data to compare later
                addr = wr_req.HADDR; 
                wr_data = wr_req.HWDATA;

                // Consume the response to prevent response queue overflow
                get_response(rsp);
            end

            // 2. Send a single READ transaction to the same address
            `uvm_info(get_type_name(), $sformatf("Sending single read request to addr %h to verify...", addr), UVM_MEDIUM)
            begin
                ahb_sequence_item rd_req = ahb_sequence_item::type_id::create("rd_req");
                start_item(rd_req);
                if (!rd_req.randomize() with {
                    HWRITE == 1'b0;
                    HTRANS == NONSEQ;
                    HBURST == SINGLE;
                    HADDR == addr;
                    HSIZE == HSIZE_WORD;
                }) `uvm_error("RNDFAIL", "Read randomize failed")
                finish_item(rd_req);

                // Get the response for the read transaction
                get_response(rsp);
                rd_data = rsp.HRDATA;
            end

            // 3. Verify the read data from the second response
            `uvm_info(get_type_name(), $sformatf("Read back data: %h", rsp.HRDATA), UVM_MEDIUM)
            if (rd_data == wr_data) begin
                `uvm_info(get_type_name(), $sformatf("SUCCESS: Read data %h matches written data %h.", rsp.HRDATA, wr_data), UVM_LOW)
            end else begin
                `uvm_error(get_type_name(), $sformatf("FAILURE: Read data %h does not match written data %h", rsp.HRDATA, wr_data))
            end
        end
        
    endtask

endclass
  // --- End of ahb_write_read_verify_sequence.svh ---

  // --- Content from ahb_incr4_write_read_sequence.svh ---
class ahb_incr4_write_read_sequence extends uvm_sequence#(ahb_sequence_item);

    `uvm_object_utils(ahb_incr4_write_read_sequence)

    rand bit[31:0] start_addr;
    rand bit[31:0] write_data[4];
    bit[31:0] read_data[4];
    htrans_e htrans;

    constraint c_addr { 
        start_addr inside {[32'h0:32'hF0]}; 
    }

    function new(string name = "ahb_incr4_write_read_sequence");
        super.new(name);
    endfunction

    virtual task body();
        // 1. INCR4 Write Burst
        `uvm_info(get_type_name(), "Starting INCR4 Write Burst", UVM_MEDIUM)
        for (int i = 0; i < 4; i++) begin
            req = ahb_sequence_item::type_id::create("req");
            start_item(req);
            htrans = (i == 0) ? NONSEQ : SEQ;
            if(!req.randomize() with {
                HWRITE == 1'b1;
                HTRANS == htrans;
                HBURST == INCR4;
                HADDR == start_addr + (i * 4); // since hsize = word 
                HSIZE == HSIZE_WORD;
                HWDATA == write_data[i];
            }) `uvm_error("RNDFAIL", "Write randomize failed")
            `uvm_info(get_type_name(), $sformatf("Sending %0dth beat of burst write request to addr %h...", 
                                                    i, req.HADDR), UVM_MEDIUM)
            finish_item(req);
            
        end
        //repeat(4) get_response(rsp);
        for (int i = 0; i < 4; i++) begin
            get_response(rsp);
            `uvm_info(get_type_name(), $sformatf("Got response:\n%s", rsp.sprint()), UVM_MEDIUM)
        end

        // 2. INCR4 Read Burst
        `uvm_info(get_type_name(), "Starting INCR4 Read Burst", UVM_MEDIUM)
        for (int i = 0; i < 4; i++) begin
            req = ahb_sequence_item::type_id::create("req");
            start_item(req);
            htrans = (i == 0) ? NONSEQ : SEQ;
            if (!req.randomize() with {
                HWRITE == 1'b0;
                HTRANS == htrans;
                HBURST == INCR4;
                HADDR == start_addr + (i * 4); // since hsize = word 
                HSIZE == HSIZE_WORD;
            }) `uvm_error("RNDFAIL", "Read randomize failed")
            `uvm_info(get_type_name(), $sformatf("Sending %0dth beat of burst read request to addr %h...", 
                                                    i, req.HADDR), UVM_MEDIUM)
            finish_item(req);
        end
        
        for (int i = 0; i < 4; i++) begin
            get_response(rsp);
            read_data[i] = rsp.HRDATA;
            `uvm_info(get_type_name(), $sformatf("Got response:\n%s", rsp.sprint()), UVM_MEDIUM)
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
  // --- End of ahb_incr4_write_read_sequence.svh ---

  // --- Content from ahb_sequencer.svh ---

class ahb_sequencer extends uvm_sequencer#(ahb_sequence_item);

    // UVM factory registration
    `uvm_component_utils(ahb_sequencer)

    // Constructor
    function new(string name = "ahb_sequencer", uvm_component parent = null);
        super.new(name, parent);
    endfunction

endclass
  // --- End of ahb_sequencer.svh ---

  // --- Content from ahb_driver.svh ---

class ahb_driver extends uvm_driver#(ahb_sequence_item);

    ahb_config cfg;

    // A simple memory model for the subordinate
    logic [31:0] mem [255:0];

    int beats_left = 0;

    `uvm_component_utils(ahb_driver)

    function new(string name = "ahb_driver", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual task run_phase(uvm_phase phase);
        if (cfg.agent_type == MANAGER) begin
            init_manager();
            manager_get_put_loop();
        end else begin // SUBORDINATE
            init_subordinate();
            subordinate_run_phase();
        end
    endtask

    virtual protected task init_manager();
        cfg.vif.HWRITE <= 0;
        cfg.vif.HADDR <= 0;
        cfg.vif.HWDATA <= '0; 
        cfg.vif.HTRANS <= IDLE;
        cfg.vif.HBURST <= SINGLE;
        cfg.vif.HMASTLOCK <= '0; 
        cfg.vif.HPROT <= '0; 
        cfg.vif.HSIZE <= '0;
        cfg.vif.HWSTRB <= '0;
    endtask

    virtual protected task init_subordinate();
        cfg.vif.HRDATA <= '0;
        cfg.vif.HREADYOUT <= '0;
        cfg.vif.HRESP <= '0;
    endtask

    // This is the main manager loop based on the get/put pattern.
    virtual task manager_get_put_loop();
        forever begin
            seq_item_port.get(req);
            `uvm_info(get_type_name(), $sformatf("DRV_START: Received req of %0d ID\n%s", 
                                        req.get_transaction_id(), req.sprint()), UVM_MEDIUM)
            assert($cast(rsp, req.clone()));
            rsp.set_id_info(req);
            drive_transfer(rsp);
        end
    endtask

    // This task orchestrates the pipelined transfer.
    virtual task drive_transfer(ahb_sequence_item rsp);
        `uvm_info(get_type_name(), $sformatf("DRV_START: Starting transfer for req of %0d ID\n%s", 
                                              rsp.get_transaction_id(), rsp.sprint()), UVM_MEDIUM)
        // Drive the address phase for this transaction
        drive_address_phase(rsp);

        // if first beat of a burst
        if (rsp.HTRANS == NONSEQ && is_burst(rsp.HBURST))
            beats_left = get_burst_length(rsp.HBURST);

        // Fork a process to handle the data phase and completion
        fork
            begin
                // Data phase for the transaction begins on the next clock edge.
                @(cfg.vif.manager_cb);
                `uvm_info(get_type_name(), $sformatf("DATA_PHASE: Starting data phase of %0d ID", 
                                                        rsp.get_transaction_id()), UVM_MEDIUM)

                if (cfg.vif.manager_cb.HBURST == SINGLE) begin
                    cfg.vif.manager_cb.HTRANS <= IDLE;
                end
                else if (is_burst(rsp.HBURST)) begin
                    --beats_left;
                    if (rsp.HTRANS != INCR && beats_left == 0) begin // if not undefined length burst
                        cfg.vif.manager_cb.HTRANS <= IDLE;
                    end
                end

                // Drive write data during the data phase.
                drive_data_phase(rsp);

                // Wait for the subordinate to signal it can complete the transfer.
                // This loop finishes on the clock edge where HREADY is high.
                do begin
                    @(cfg.vif.manager_cb);
                end while (cfg.vif.manager_cb.HREADY != 1'b1);
                `uvm_info(get_type_name(), $sformatf("DATA_PHASE: Captured READY of %0d ID", 
                                        rsp.get_transaction_id()), UVM_MEDIUM)

                // Capture read data.
                if (!rsp.HWRITE) begin
                    `uvm_info(get_type_name(), $sformatf("DRV_READ: Reading HRDATA from VIF: 0x%0h", cfg.vif.manager_cb.HRDATA), UVM_MEDIUM)
                    rsp.HRDATA = cfg.vif.manager_cb.HRDATA;
                    `uvm_info(get_type_name(), $sformatf("DRV_READ: Captured HRDATA in rsp: 0x%0h", rsp.HRDATA), UVM_MEDIUM)
                end
                `uvm_info(get_type_name(), $sformatf("DRV_DONE: Sending response:\n%s", rsp.sprint()), UVM_MEDIUM)
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
    
    virtual task subordinate_run_phase();
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
                //seq_item_port.put(rsp);
            end else begin
                // No new transfer is starting.
                data_phase_active = 0;
                cfg.vif.subordinate_cb.HREADYOUT <= 1'b1;
                cfg.vif.subordinate_cb.HRDATA    <= 'z; // Stop driving HRDATA
            end
        end
    endtask

endclass
  // --- End of ahb_driver.svh ---

  // --- Content from ahb_monitor.svh ---
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
                addr_phase_tr.HWSTRB = cfg.vif.monitor_cb.HWSTRB;
                addr_phase_tr.HPROT  = cfg.vif.monitor_cb.HPROT;

                assert($cast(addr_phase_tr.HSIZE , cfg.vif.monitor_cb.HSIZE));
                assert($cast(addr_phase_tr.HBURST, cfg.vif.monitor_cb.HBURST));
                assert($cast(addr_phase_tr.HTRANS, cfg.vif.monitor_cb.HTRANS));
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
                    `uvm_error("AHB_PROTOCOL_ERROR", $sformatf("Burst started at %h of type %s terminated unexpectedly with HTRANS=%s when %0d beats are left", 
                                                                start_addr, active_burst_type.name(), beat.HTRANS.name(), beats_left))
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

    function uvm_analysis_port#(ahb_sequence_item) get_item_collected_port();
        return beat_ap;
    endfunction

endclass
  // --- End of ahb_monitor.svh ---

  // --- Content from ahb_coverage.svh ---
class coverage_collector extends uvm_subscriber#(ahb_sequence_item);
    `uvm_component_utils(coverage_collector)

    // Transaction item to be sampled
    ahb_sequence_item tr;

    // Covergroup for basic AHB transfer properties
    covergroup ahb_transfer_cg;
        option.per_instance = 1;

        // Cover HTRANS
        cp_htrans: coverpoint tr.HTRANS {
            bins idle    = {IDLE};
            bins busy    = {BUSY};
            bins nonseq  = {NONSEQ};
            bins seq     = {SEQ};
        }

        // Cover HBURST
        cp_hburst: coverpoint tr.HBURST {
            bins single  = {SINGLE};
            bins incr4   = {INCR4};
            // TODO: Add other burst types as they are supported
        }

        // Cover HSIZE
        cp_hsize: coverpoint tr.HSIZE {
            bins size_byte    = {HSIZE_BYTE};
            bins size_hword   = {HSIZE_HWORD};
            bins size_word    = {HSIZE_WORD};
        }

        // Cover HWRITE
        cp_hwrite: coverpoint tr.HWRITE {
            bins write = {1'b1};
            bins read  = {1'b0};
        }

        // Cover Address, with a few example bins
        cp_addr: coverpoint tr.HADDR {
            bins zero = {0};
            bins max  = {'1};
            bins addr[5] = {[0:'1]};
        }

        // Cover Write Data, with a few example bins
        cp_wdata: coverpoint tr.HWDATA iff (tr.HWRITE == 1) {
            bins zero = {0};
            bins max  = {'1};
            bins wdata[5] = {[0:'1]};
        }

        // Cover Read Data, with a few example bins
        cp_rdata: coverpoint tr.HRDATA iff (tr.HWRITE == 0) {
            bins zero = {0};
            bins max  = {'1};
            bins rdata[5] = {[0:'1]};
        }

        // Cross coverage for key control signals
        cross_rw_burst: cross cp_hwrite, cp_hburst;
        cross_rw_size: cross cp_hwrite, cp_hsize;
        cross_rw_xfer_type: cross cp_hwrite, cp_htrans;
        cross_rw_rdata_addr: cross cp_hwrite, cp_rdata, cp_addr {
            bins c3 = binsof(cp_hwrite.read);
        }
        cross_rw_wdata_addr: cross cp_hwrite, cp_wdata, cp_addr {
            bins c3 = binsof(cp_hwrite.write);
        }
    endgroup

    function new(string name = "coverage_collector", uvm_component parent = null);
        super.new(name, parent);
        ahb_transfer_cg = new();
    endfunction

    // The write method is called by the analysis port to sample the transaction
    function void write(ahb_sequence_item t);
        this.tr = t;
        ahb_transfer_cg.sample();
        `uvm_info("COVERAGE", $sformatf("Sampled transaction:\n%s", t.sprint()), UVM_HIGH)
    endfunction

    function void report_phase(uvm_phase phase);
        super.report_phase(phase);
        `uvm_info("COVERAGE_REPORT", $sformatf("AHB Transfer Coverage:%3.2f%%", ahb_transfer_cg.get_inst_coverage()), UVM_LOW)
    endfunction

endclass
  // --- End of ahb_coverage.svh ---

  // --- Content from ahb_agent.svh ---



class ahb_agent extends uvm_agent;

    // Components
    ahb_sequencer      sequencer;
    ahb_driver         driver;
    ahb_monitor        monitor;
    coverage_collector cov_collector;

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
        super.build_phase(phase);

        uvm_config_db#(ahb_config)::get(this, "", "cfg", cfg);

        monitor = ahb_monitor::type_id::create("monitor", this);
        monitor.cfg = cfg;

        if (cfg.en_cov) begin
            cov_collector = coverage_collector::type_id::create("cov_collector", this);
        end

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
        if (cfg.en_cov) begin
            monitor.get_item_collected_port().connect(cov_collector.analysis_export);
        end
        if (cfg.is_active == UVM_ACTIVE) begin
            driver.seq_item_port.connect(sequencer.seq_item_export);
        end
    endfunction

endclass
  // --- End of ahb_agent.svh ---

  // --- Content from ahb_scoreboard.svh ---
// ========================================
// AHB Scoreboard Implementation
// ========================================

class ahb_scoreboard extends uvm_scoreboard;
    
    `uvm_component_utils(ahb_scoreboard)
    
    // Analysis implementation macros for scoreboard
    `uvm_analysis_imp_decl(_mgr)
    `uvm_analysis_imp_decl(_sub)
    
    // Analysis imports to receive transactions
    uvm_analysis_imp_mgr#(ahb_sequence_item, ahb_scoreboard) mgr_export;
    uvm_analysis_imp_sub#(ahb_sequence_item, ahb_scoreboard) sub_export;
    
    // Internal memory model for expected data
    logic [31:0] expected_mem [logic [31:0]];
    
    
    // Statistics counters
    int write_count = 0;
    int read_count = 0;
    int read_match_count = 0;
    int read_mismatch_count = 0;
    int uninitialized_read_count = 0;
    
    // Configuration
    bit enable_memory_model = 1;  // Enable/disable memory modeling
    bit strict_checking = 1;      // Strict checking for uninitialized reads
    
    function new(string name = "ahb_scoreboard", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);

        mgr_export = new("mgr_export", this);
        sub_export = new("sub_export", this);

        // Get configuration if available
        if (!uvm_config_db#(bit)::get(this, "", "enable_memory_model", enable_memory_model))
            enable_memory_model = 1;
        if (!uvm_config_db#(bit)::get(this, "", "strict_checking", strict_checking))
            strict_checking = 1;
    endfunction
    
    // Receive transactions from manager agent
    virtual function void write_mgr(ahb_sequence_item tr);
        ahb_sequence_item cloned_tr;
        
        // Clone the transaction to avoid reference issues
        assert($cast(cloned_tr, tr.clone()));
        
        `uvm_info("SCOREBOARD_MGR", $sformatf("Received manager transaction:\n%s", 
                  cloned_tr.sprint()), UVM_HIGH)
        
        if (cloned_tr.HWRITE) begin
            process_write_transaction(cloned_tr);
        end else begin
            process_read_transaction(cloned_tr);
        end
    endfunction
    
    // Receive transactions from subordinate agent (if needed for additional validation)
    virtual function void write_sub(ahb_sequence_item tr);
        ahb_sequence_item cloned_tr;
        
        // Clone the transaction
        assert($cast(cloned_tr, tr.clone()));
        
        `uvm_info("SCOREBOARD_SUB", $sformatf("Received subordinate transaction:\n%s", 
                  cloned_tr.sprint()), UVM_HIGH)
        
        // Additional subordinate-side validation can be added here
        // For now, we primarily use manager-side transactions
    endfunction
    
    // Process write transactions
    virtual function void process_write_transaction(ahb_sequence_item tr);
        logic [31:0] aligned_addr;
        
        write_count++;
        
        // Calculate word-aligned address based on HSIZE
        aligned_addr = get_aligned_address(tr.HADDR, tr.HSIZE);
        
        if (enable_memory_model) begin
            // Update expected memory model
            case (tr.HSIZE)
                HSIZE_BYTE: begin
                    logic [7:0] byte_data = tr.HWDATA[7:0];
                    logic [1:0] byte_offset = tr.HADDR[1:0];
                    
                    // Read-modify-write for byte operations
                    if (expected_mem.exists(aligned_addr)) begin
                        expected_mem[aligned_addr][byte_offset*8 +: 8] = byte_data;
                    end else begin
                        expected_mem[aligned_addr] = 32'h0;
                        expected_mem[aligned_addr][byte_offset*8 +: 8] = byte_data;
                    end
                end
                
                HSIZE_HWORD: begin
                    logic [15:0] hword_data = tr.HWDATA[15:0];
                    logic hword_offset = tr.HADDR[1];
                    
                    // Read-modify-write for halfword operations
                    if (expected_mem.exists(aligned_addr)) begin
                        expected_mem[aligned_addr][hword_offset*16 +: 16] = hword_data;
                    end else begin
                        expected_mem[aligned_addr] = 32'h0;
                        expected_mem[aligned_addr][hword_offset*16 +: 16] = hword_data;
                    end
                end
                
                HSIZE_WORD: begin
                    // Full word write
                    expected_mem[aligned_addr] = tr.HWDATA;
                end
                
                default: begin
                    `uvm_warning("SCOREBOARD", $sformatf("Unsupported HSIZE: %s", tr.HSIZE.name()))
                end
            endcase
            
            `uvm_info("SCOREBOARD_WRITE", $sformatf("Write to addr 0x%08h (aligned: 0x%08h), data: 0x%08h, size: %s", 
                      tr.HADDR, aligned_addr, tr.HWDATA, tr.HSIZE.name()), UVM_MEDIUM)
        end
    endfunction
    
    // Process read transactions
    virtual function void process_read_transaction(ahb_sequence_item tr);
        logic [31:0] aligned_addr;
        logic [31:0] expected_data;
        logic [31:0] actual_data;
        logic [31:0] mask;
        bit address_initialized;
        
        read_count++;
        
        // Calculate word-aligned address
        aligned_addr = get_aligned_address(tr.HADDR, tr.HSIZE);
        actual_data = tr.HRDATA;
        
        if (enable_memory_model) begin
            address_initialized = expected_mem.exists(aligned_addr);
            
            if (address_initialized) begin
                expected_data = expected_mem[aligned_addr];
                
                // Extract the relevant portion based on HSIZE and address offset
                case (tr.HSIZE)
                    HSIZE_BYTE: begin
                        logic [1:0] byte_offset = tr.HADDR[1:0];
                        expected_data = (expected_data >> (byte_offset * 8)) & 32'h000000FF;
                        actual_data = actual_data & 32'h000000FF;
                        mask = 32'h000000FF;
                    end
                    
                    HSIZE_HWORD: begin
                        logic hword_offset = tr.HADDR[1];
                        expected_data = (expected_data >> (hword_offset * 16)) & 32'h0000FFFF;
                        actual_data = actual_data & 32'h0000FFFF;
                        mask = 32'h0000FFFF;
                    end
                    
                    HSIZE_WORD: begin
                        // Full word, no masking needed
                        mask = 32'hFFFFFFFF;
                    end
                    
                    default: begin
                        `uvm_warning("SCOREBOARD", $sformatf("Unsupported HSIZE: %s", tr.HSIZE.name()))
                        return;
                    end
                endcase
                
                // Compare expected vs actual data
                if (expected_data == actual_data) begin
                    read_match_count++;
                    `uvm_info("SCOREBOARD_PASS", $sformatf("READ MATCH - Addr: 0x%08h, Expected: 0x%08h, Actual: 0x%08h, Size: %s", 
                              tr.HADDR, expected_data, actual_data, tr.HSIZE.name()), UVM_MEDIUM)
                end else begin
                    read_mismatch_count++;
                    `uvm_error("SCOREBOARD_FAIL", $sformatf("READ MISMATCH - Addr: 0x%08h, Expected: 0x%08h, Actual: 0x%08h, Size: %s, Mask: 0x%08h", 
                               tr.HADDR, expected_data, actual_data, tr.HSIZE.name(), mask))
                end
                
            end else begin
                // Reading from uninitialized address
                uninitialized_read_count++;
                if (strict_checking) begin
                    `uvm_warning("SCOREBOARD_UNINIT", $sformatf("Reading from uninitialized address 0x%08h, data: 0x%08h, size: %s", 
                                 tr.HADDR, actual_data, tr.HSIZE.name()))
                end else begin
                    `uvm_info("SCOREBOARD_UNINIT", $sformatf("Reading from uninitialized address 0x%08h, data: 0x%08h, size: %s", 
                              tr.HADDR, actual_data, tr.HSIZE.name()), UVM_MEDIUM)
                end
            end
        end
    endfunction
    
    // Helper function to get properly aligned address based on access size
    virtual function logic [31:0] get_aligned_address(logic [31:0] addr, hsize_e size);
        case (size)
            HSIZE_BYTE:   return addr;                    // No alignment required for bytes
            HSIZE_HWORD:  return {addr[31:1], 1'b0};     // Halfword-aligned (clear bit 0)
            HSIZE_WORD:   return {addr[31:2], 2'b00};    // Word-aligned (clear bits [1:0])
            default:      return {addr[31:2], 2'b00};    // Default to word-aligned
        endcase
    endfunction
    
    // Report phase - print statistics
    virtual function void report_phase(uvm_phase phase);
        super.report_phase(phase);
        
        `uvm_info("SCOREBOARD_REPORT", "=== AHB Scoreboard Final Report ===", UVM_LOW)
        dump_memory_model();

        `uvm_info("SCOREBOARD_REPORT", $sformatf("Total Writes: %0d", write_count), UVM_LOW)
        `uvm_info("SCOREBOARD_REPORT", $sformatf("Total Reads: %0d", read_count), UVM_LOW)
        `uvm_info("SCOREBOARD_REPORT", $sformatf("Read Matches: %0d", read_match_count), UVM_LOW)
        `uvm_info("SCOREBOARD_REPORT", $sformatf("Read Mismatches: %0d", read_mismatch_count), UVM_LOW)
        `uvm_info("SCOREBOARD_REPORT", $sformatf("Uninitialized Reads: %0d", uninitialized_read_count), UVM_LOW)
        
        if (read_count > 0) begin
            real pass_rate = (real'(read_match_count) / real'(read_count)) * 100.0;
            `uvm_info("SCOREBOARD_REPORT", $sformatf("Read Pass Rate: %.2f%%", pass_rate), UVM_LOW)
        end
        
        `uvm_info("SCOREBOARD_REPORT", $sformatf("Memory Model Entries: %0d", expected_mem.size()), UVM_LOW)
        `uvm_info("SCOREBOARD_REPORT", "=== End of Report ===", UVM_LOW)
        
        // Final pass/fail determination
        if (read_mismatch_count == 0) begin
            `uvm_info("SCOREBOARD_RESULT", "SCOREBOARD: PASS - All read transactions matched expected data", UVM_LOW)
        end else begin
            `uvm_error("SCOREBOARD_RESULT", $sformatf("SCOREBOARD: FAIL - %0d read mismatches detected", read_mismatch_count))
        end
    endfunction
    
    // Optional: Function to manually check a specific address
    virtual function logic [31:0] get_expected_data(logic [31:0] addr);
        logic [31:0] aligned_addr = {addr[31:2], 2'b00};
        if (expected_mem.exists(aligned_addr)) begin
            return expected_mem[aligned_addr];
        end else begin
            `uvm_warning("SCOREBOARD", $sformatf("Address 0x%08h not found in memory model", addr))
            return 32'h0;
        end
    endfunction
    
    // Optional: Function to clear memory model (useful for tests)
    virtual function void clear_memory_model();
        expected_mem.delete();
        `uvm_info("SCOREBOARD", "Memory model cleared", UVM_MEDIUM)
    endfunction
    
    // Optional: Function to dump memory model contents
    virtual function void dump_memory_model();
        `uvm_info("SCOREBOARD", "=== Memory Model Dump ===", UVM_LOW)
        foreach (expected_mem[addr]) begin
            `uvm_info("SCOREBOARD", $sformatf("Addr: 0x%08h, Data: 0x%08h", addr, expected_mem[addr]), UVM_LOW)
        end
        `uvm_info("SCOREBOARD", "=== End Memory Model Dump ===", UVM_LOW)
    endfunction

endclass
  // --- End of ahb_scoreboard.svh ---

  // --- Content from ahb_env.svh ---

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
  // --- End of ahb_env.svh ---


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
        manager_cfg.en_cov = 1;

        subordinate_cfg.vif = subordinate_vif;
        subordinate_cfg.is_active = UVM_ACTIVE;
        subordinate_cfg.agent_type = SUBORDINATE;
        subordinate_cfg.en_cov = 0;

        // Assign config objects to env properties
        env.manager_cfg = manager_cfg;
        env.subordinate_cfg = subordinate_cfg;

    endfunction

endclass

// --- End of file: tests/base_test.sv ---

// --- Start of file: tests/incr4_write_read_test.sv ---
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

// --- End of file: tests/incr4_write_read_test.sv ---

// --- Start of file: tests/single_read_test.sv ---
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

// --- End of file: tests/single_read_test.sv ---

// --- Start of file: tests/single_write_test.sv ---
class single_write_test extends base_test;

    `uvm_component_utils(single_write_test)

    function new(string name = "single_write_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual task run_phase(uvm_phase phase);
        ahb_single_write_sequence seq;

        phase.raise_objection(this);

        // Create and start the sequence
        seq = ahb_single_write_sequence::type_id::create("seq");
        seq.start(env.manager_agent.sequencer);
        
        // Add a small delay to let the transfer complete
        #100ns;

        phase.drop_objection(this);
    endtask

endclass

// --- End of file: tests/single_write_test.sv ---

// --- Start of file: tests/write_read_verify_test.sv ---
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
        assert(seq.randomize());
        seq.start(env.manager_agent.sequencer);

        #200ns;

        phase.drop_objection(this);
    endtask

endclass

// --- End of file: tests/write_read_verify_test.sv ---

// --- Start of file: tb_top.sv ---

`timescale 1ns / 1ps

module tb_top;

    // Clock and Reset Generation
    logic HCLK;
    logic HRESETn = 1;

    initial begin
        HCLK = 0;
        forever #5 HCLK = ~HCLK; // 100 MHz clock
    end

    // Instantiate AHB Interfaces
    ahb_if#(32, 32) ahb_if(.HCLK(HCLK), .HRESETn(HRESETn));

    // Since there's no interconnect to decide which HREADY to route
    // and which subordinate to be selected,
    assign ahb_if.HREADY = ahb_if.HREADYOUT;
    assign ahb_if.HSELx = 1'b1;

    // Instantiate the UVM testbench
    initial begin
        $dumpfile("dump.vcd"); $dumpvars;
        $timeformat(-9, 2, " ns");

        // Set interface handles to the config_db
        uvm_config_db#(virtual ahb_if)::set(null, "uvm_test_top", "manager_if", ahb_if);
        uvm_config_db#(virtual ahb_if)::set(null, "uvm_test_top", "subordinate_if", ahb_if);

        // Run the UVM test
        run_test("incr4_write_read_test");
    end

endmodule

// --- End of file: tb_top.sv ---

