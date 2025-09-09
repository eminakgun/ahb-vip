
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
