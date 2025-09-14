
`timescale 1ns / 1ps

module tb_top;

    // Clock and Reset Generation
    logic HCLK;
    logic HRESETn;

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
        run_test("write_read_verify_test");
    end

endmodule
