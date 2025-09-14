# AHB VIP Documentation

## Overview
This AHB VIP (Verification IP) is a comprehensive SystemVerilog UVM-based verification environment for verifying AHB (Advanced High-performance Bus) protocol compliance. The VIP supports both manager (master) and subordinate (slave) agents and provides comprehensive protocol checking, coverage collection, and transaction monitoring capabilities.

## 1. VIP Architecture

### 1.1 Block Diagram
```
┌─────────────────────────────────────────────────────────────────┐
│                        AHB VIP Environment                     │
├─────────────────────────────────────────────────────────────────┤
│  ┌─────────────────┐    ┌─────────┐    ┌─────────────────┐      │
│  │  Manager Agent  │    │   AHB   │    │ Subordinate     │      │
│  │                 │    │Interface│    │ Agent           │      │
│  │ ┌─────────────┐ │    │         │    │ ┌─────────────┐ │      │
│  │ │ Sequencer   │ │    │         │    │ │   Driver    │ │      │
│  │ └─────────────┘ │    │         │    │ │ (Memory     │ │      │
│  │ ┌─────────────┐ │    │         │    │ │  Model)     │ │      │
│  │ │   Driver    │ │<-->│  HCLK   │<-->│ └─────────────┘ │      │
│  │ └─────────────┘ │    │ HRESETn │    │ ┌─────────────┐ │      │
│  │ ┌─────────────┐ │    │ HADDR   │    │ │   Monitor   │ │      │
│  │ │   Monitor   │ │    │ HWRITE  │    │ └─────────────┘ │      │
│  │ └─────────────┘ │    │ HWDATA  │    │                 │      │
│  │ ┌─────────────┐ │    │ HRDATA  │    │                 │      │
│  │ │  Coverage   │ │    │ HREADY  │    │                 │      │
│  │ │ Collector   │ │    │ HRESP   │    │                 │      │
│  │ └─────────────┘ │    │ HSELx   │    │                 │      │
│  └─────────────────┘    │ HTRANS  │    └─────────────────┘      │
│           │             │ HBURST  │              │              │
│           │             │ HSIZE   │              │              │
│           │             │ etc...  │              │              │
│           │             └─────────┘              │              │
│           │                   │                  │              │
│           └───────────────────┼──────────────────┘              │
│                               │                                 │
│                    ┌─────────────────┐                          │
│                    │   Scoreboard    │                          │
│                    │                 │                          │
│                    │ Memory Model    │                          │
│                    │ Data Checking   │                          │
│                    │ Statistics      │                          │
│                    └─────────────────┘                          │
└─────────────────────────────────────────────────────────────────┘
```

### 1.2 Main Components

#### 1.2.1 AHB Manager Agent
- **Purpose**: Generates AHB transactions as a bus manager (master)
- **Key Features**:
  - Supports single transfers and INCR4 burst transfers
  - Configurable active/passive mode
  - Integrated sequencer for transaction generation
  - Coverage collection capability

#### 1.2.2 AHB Subordinate Agent
- **Purpose**: Responds to AHB transactions as a bus subordinate (slave)
- **Key Features**:
  - Simple memory model (256 entries)
  - Zero wait state responses
  - Supports word transfers
  - Automatic response generation

#### 1.2.3 AHB Monitor
- **Purpose**: Observes and collects AHB transactions for analysis
- **Key Features**:
  - Protocol compliance checking
  - Transaction collection and analysis
  - Burst transaction reconstruction
  - Pipelined transfer handling

#### 1.2.4 AHB Sequencer
- **Purpose**: Manages sequence execution for the manager agent
- **Key Features**:
  - Standard UVM sequencer functionality
  - Supports multiple sequence types
  - Transaction ordering and control

#### 1.2.5 AHB Scoreboard
- **Purpose**: Verifies data integrity and protocol compliance
- **Key Features**:
  - Memory model for expected data tracking
  - Read/write transaction verification
  - Statistical reporting
  - Configurable strict checking modes

### 1.3 Interface Signals
| Signal Name | Width | Direction | Description |
|-------------|-------|-----------|-------------|
| HCLK | 1 | Input | Bus clock |
| HRESETn | 1 | Input | Bus reset (active low) |
| HADDR | 32 | Manager→Subordinate | Address bus |
| HTRANS | 2 | Manager→Subordinate | Transfer type |
| HWRITE | 1 | Manager→Subordinate | Write enable |
| HSIZE | 3 | Manager→Subordinate | Transfer size |
| HBURST | 3 | Manager→Subordinate | Burst type |
| HPROT | 4 | Manager→Subordinate | Protection control |
| HWDATA | 32 | Manager→Subordinate | Write data bus |
| HWSTRB | 4 | Manager→Subordinate | Write strobe |
| HMASTLOCK | 1 | Manager→Subordinate | Master lock |
| HREADY | 1 | Subordinate→Manager | Transfer done |
| HRESP | 1 | Subordinate→Manager | Transfer response |
| HRDATA | 32 | Subordinate→Manager | Read data bus |
| HSELx | 1 | Decoder→Subordinate | Subordinate select |
| HREADYOUT | 1 | Subordinate→Decoder | Ready output |

### 1.4 Configuration Parameters
- **ADDR_WIDTH**: 32 - Address bus width in bits
- **DATA_WIDTH**: 32 - Data bus width in bits
- **agent_type**: MANAGER/SUBORDINATE - Configures agent as manager or subordinate
- **is_active**: UVM_ACTIVE/UVM_PASSIVE - Enable/disable driver functionality
- **en_cov**: 0/1 - Enable/disable coverage collection
- **enable_memory_model**: 1 - Enable scoreboard memory modeling
- **strict_checking**: 1 - Enable strict protocol checking


## 2. List of SVAs (SystemVerilog Assertions)

### 2.1 Protocol Compliance Assertions

#### 2.1.1 Burst Stability Assertion
- **SVA_AHB_001**: `a_hburst_stable`
  - **Description**: HBURST must remain stable throughout a burst transfer during sequential transfers
  - **Property**: 
  ```systemverilog
  property p_hburst_stable;
      @(posedge HCLK) disable iff(!HRESETn)
      (HREADY && HTRANS == 2'b11) |=> $stable(HBURST);
  endproperty
  a_hburst_stable: assert property (p_hburst_stable)
      else $error("SVA Error: HBURST changed value mid-burst.");
  ```

#### 2.1.2 Error Response Protocol
- **SVA_AHB_002**: `a_idle_on_error`
  - **Description**: Second cycle of error response should have HTRANS == IDLE to cancel data phase
  - **Property**: 
  ```systemverilog
  property idle_on_err_p;
      @(posedge HCLK) disable iff(!HRESETn)
      (HRESP == 1) ##1 (HRESP == 1) |-> (HTRANS == 0);
  endproperty
  a_idle_on_error: assert property (idle_on_err_p)
      else $error("SVA Error: HTRANS should be IDLE on second error cycle.");
  ```

#### 2.1.3 IDLE Transfer Handling
- **SVA_AHB_003**: `a_idle_no_wait`
  - **Description**: Subordinates must not insert wait states for IDLE transfers
  - **Property**: 
  ```systemverilog
  property idle_no_wait_p;
      @(posedge HCLK) disable iff(!HRESETn)
      (HTRANS == 0) |=> (HRESP == 0);
  endproperty
  a_idle_no_wait: assert property (idle_no_wait_p)
      else $error("SVA Error: Wait states inserted during IDLE transfer.");
  ```

#### 2.1.4 Address Alignment Checking
- **SVA_AHB_004**: `a_haddr_alignment`
  - **Description**: HADDR must be properly aligned based on HSIZE for NONSEQ and SEQ transfers
  - **Property**: 
  ```systemverilog
  property p_haddr_alignment;
      @(posedge HCLK) disable iff (!HRESETn)
      case (HSIZE)
          3'b000: 1'b1; // BYTE → no alignment required
          3'b001: HTRANS inside {[0:1]} |-> HADDR[0]    == 1'b0;       // HWORD      → 2-byte alignment
          3'b010: HTRANS inside {[0:1]} |-> HADDR[1:0]  == 2'b00;      // WORD       → 4-byte alignment
          3'b011: HTRANS inside {[0:1]} |-> HADDR[2:0]  == 3'b000;     // 4 WORD     → 8-byte alignment
          3'b100: HTRANS inside {[0:1]} |-> HADDR[3:0]  == 4'b0000;    // 8 WORD     → 16-byte alignment
          3'b101: HTRANS inside {[0:1]} |-> HADDR[4:0]  == 5'b00000;   // 16 WORD    → 32-byte alignment
          3'b110: HTRANS inside {[0:1]} |-> HADDR[5:0]  == 6'b000000;  // 32 WORD    → 64-byte alignment
          3'b111: HTRANS inside {[0:1]} |-> HADDR[6:0]  == 7'b0000000; // 64 WORD    → 128-byte alignment
          default: 1'b0;
      endcase
  endproperty
  a_haddr_alignment: assert property (p_haddr_alignment)
      else $error("SVA Error: HADDR is not aligned properly for HSIZE=%0d", HSIZE);
  ```

### 2.2 Protocol Monitoring Assertions

#### 2.2.1 Burst Sequence Monitoring
- **Monitor FSM Protocol Check**: Implemented in `ahb_monitor` class
  - **Description**: Validates proper burst sequencing (NONSEQ followed by SEQ transfers)
  - **Implementation**: FSM-based checking in monitor that detects illegal SEQ transfers outside burst context

## 3. Test Scenarios and Results

### 3.1 Test Environment Setup
- **Simulator**: QuestaSim or equivalent SystemVerilog simulator
- **Language**: SystemVerilog/UVM 1.2
- **Waveform Viewer**: ModelSim Wave or GTKWave (VCD output)

### 3.2 Basic Functionality Tests

| Test Name | Description | Status | Sequence Used | Notes |
|-----------|-------------|--------|------------|-------|
| single_write_test | Single write transaction (NONSEQ, SINGLE) | ✅ PASS |          ahb_single_write_sequence | Tests basic write functionality |
| single_read_test | Single read transaction (NONSEQ, SINGLE) | ✅ PASS |            ahb_single_read_sequence | Tests basic read functionality |
| write_read_verify_test | Write followed by read verification | ✅ PASS |           ahb_write_read_verify_sequence | Validates data integrity |
| incr4_write_read_test | INCR4 burst write followed by INCR4 burst read | ✅ PASS | ahb_incr4_write_read_sequence | Tests 4-beat incrementing burst |

### 3.3 Test Results Summary
- **Total Tests Run**: 4
- **Passed**: 4 (100%)
- **Failed**: 0 (0%)

## 4. Appendices

### 4.1 References
- ARM IHI 0033C AMBA AHB Protocol Specification Issue C
- SystemVerilog IEEE 1800-2017 Standard  
- UVM 1.2 User Guide