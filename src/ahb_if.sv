
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
    property p_hburst_stable;
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
    property idle_no_wait_p;
        @(posedge HCLK) disable iff(!HRESETn)
        (HTRANS == 0) |=> (HRESP == 0);
    endproperty
    a_idle_no_wait: assert property (idle_no_wait_p)
        else $error("SVA Error: HBURST changed value mid-burst.");

    property p_haddr_alignment;
        @(posedge HCLK)
        disable iff (!HRESETn)
        case (HSIZE)
            3'b000: 1'b1; // BYTE → no alignment required
            3'b001: HTRANS inside {[0:1]} |-> HADDR[0]    == 1'b0;       // HWORD      → 2-byte alignment
            3'b010: HTRANS inside {[0:1]} |-> HADDR[1:0]  == 2'b00;      // WORD       → 4-byte alignment
            3'b011: HTRANS inside {[0:1]} |-> HADDR[2:0]  == 3'b000;     // 4 WORD     → 8-byte alignment
            3'b100: HTRANS inside {[0:1]} |-> HADDR[3:0]  == 4'b0000;    // 8 WORD     → 16-byte alignment
            3'b101: HTRANS inside {[0:1]} |-> HADDR[4:0]  == 5'b00000;   // 16 WORD    → 32-byte alignment
            3'b110: HTRANS inside {[0:1]} |-> HADDR[5:0]  == 6'b000000;  // 32 WORD    → 64-byte alignment
            3'b111: HTRANS inside {[0:1]} |-> HADDR[6:0]  == 7'b0000000; // 64 WORD    → 128-byte alignment
            default: 1'b0; // Should never happen
        endcase
    endproperty
    a_haddr_alignment: assert property (p_haddr_alignment)
    else $error("SVA Error: HADDR is not aligned properly for HSIZE=%0d", HSIZE);
    

endinterface