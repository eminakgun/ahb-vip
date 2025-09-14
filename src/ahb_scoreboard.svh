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