
// HTRANS values
typedef enum logic [1:0] {
    IDLE   = 2'b00,
    BUSY   = 2'b01,
    NONSEQ = 2'b10,
    SEQ    = 2'b11
} htrans_e;

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
