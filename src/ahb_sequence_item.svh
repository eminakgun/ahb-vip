
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
        HBURST inside {SINGLE, INCR4}; // For now
    }

endclass
