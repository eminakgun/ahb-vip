
class ahb_sequence_item extends uvm_sequence_item;

    // Properties
    rand bit [31:0] HADDR;
    rand bit HWRITE;
    rand bit [31:0] HWDATA;
    rand bit [3:0] HWSTRB;
    rand htrans_e HTRANS;
    rand hsize_e HSIZE;

    // UVM factory registration
    `uvm_object_utils_begin(ahb_sequence_item)
        `uvm_field_int(HADDR, UVM_ALL_ON)
        `uvm_field_int(HWRITE, UVM_ALL_ON)
        `uvm_field_int(HWDATA, UVM_ALL_ON)
        `uvm_field_int(HWSTRB, UVM_ALL_ON)
        `uvm_field_enum(htrans_e, HTRANS, UVM_ALL_ON)
        `uvm_field_enum(hsize_e, HSIZE, UVM_ALL_ON)
    `uvm_object_utils_end

    // Constructor
    function new(string name = "ahb_sequence_item");
        super.new(name);
    endfunction

    // Constraints
    constraint c_valid_transfer {
        // For now, only allow SINGLE transfers
        HTRANS inside {IDLE, BUSY, NONSEQ};
        HSIZE inside {HSIZE_BYTE, HSIZE_HWORD, HSIZE_WORD};
    }

endclass
