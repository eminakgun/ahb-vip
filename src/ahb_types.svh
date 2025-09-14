
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
