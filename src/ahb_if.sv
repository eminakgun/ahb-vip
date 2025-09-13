
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
