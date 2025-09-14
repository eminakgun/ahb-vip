## VIP Architecture & Infrastructure (Phase 0)

This phase establishes the core UVM structure. These items are prerequisites for implementing protocol-specific features.

*   [x] Define the AHB SystemVerilog `interface`
    *   Created a single `interface` file to encapsulate all AHB signals as defined in the specification.
    *   Used `modport` to define signal directions for Manager, Subordinate, and Monitor components.
    *   Parameterized the interface for key properties like `ADDR_WIDTH` and `DATA_WIDTH`.

*   [x] Create the Core Transaction/Sequence Item (`ahb_sequence_item`)
    *   Developed a `uvm_sequence_item` class to represent an AHB transfer.
    *   Included fields for essential properties: address, write/read direction, data, transfer type (`HTRANS`), and size (`HSIZE`).
    *   Added constraints for basic, valid transfers.
    *   **Refactored:** Renamed from `ahb_transfer` to `ahb_sequence_item`.

*   [x] Build the AHB Agent (`ahb_agent`)
    *   Created a standard `uvm_agent` that contains a sequencer, driver, and monitor.
    *   Included a configuration object (`ahb_config`) to control its behavior (e.g., `is_active`/`is_passive`, operating as a Manager or Subordinate).
    *   **Refactored:** Renamed `ahb_agent_config` to `ahb_config` and moved to `ahb_config.svh`.

*   [x] Implement Basic Agent Components
    *   **Sequencer (`ahb_sequencer`):** A standard `uvm_sequencer` parameterized with the `ahb_sequence_item` type.
    *   **Driver (`ahb_driver`):** Skeleton BFM (Bus Functional Model) that gets sequence items but doesn't yet drive signals.
    *   **Monitor (`ahb_monitor`):** Skeleton monitor with analysis ports that connects to the interface but doesn't yet sample signals.
    *   **Enhancement:** Monitor's `item_collected_port` is now private, connected to agent's public analysis port.

*   [x] Set up a Basic Test Environment (`ahb_env`)
    *   Created a `uvm_env` to instantiate the Manager and Subordinate agents.
    *   Included a simple scoreboard placeholder.
    *   Created a base test (`base_test`) to build the environment and configure the agents.
    *   **Enhancement:** Implemented robust VIF passing from `tb_top` -> `base_test` -> `ahb_env` -> `ahb_agent` -> `ahb_driver`/`ahb_monitor`.

---

## Core Infrastructure Enhancements

These are additional features and refactorings implemented to improve the VIP's structure and usability.

*   [x] Enum Type Definitions: Defined `HTRANS` and `HSIZE` enum types in `ahb_types.svh` for improved readability and type safety.
*   [x] Package Refactoring: Created `ahb_pkg.sv` to encapsulate all agent components and types, ensuring proper SystemVerilog package structure and facilitating single-file compilation.
*   [x] Top-Level Testbench (`tb_top.sv`): Implemented a top-level module to instantiate AHB interfaces, generate clock/reset, and initiate the UVM testbench.
*   [x] UVM Field Macro Correction: Corrected `uvm_field_int` to `uvm_field_enum` for enum-typed variables in `ahb_sequence_item`.
*   [x] Constructor Implementation: Ensured all UVM classes (`ahb_config`, `ahb_sequence_item`, `ahb_sequencer`, `ahb_driver`, `ahb_monitor`, `ahb_agent`, `ahb_env`, `base_test`) have appropriate constructors.
*   [x] `super.build_phase` Removal: Removed calls to `super.build_phase` in all UVM components as per specific user instruction.

---

## MVP Development (Phase 1)

The goal of the MVP is to verify basic, zero-wait-state, single and simple burst transfers correctly.

*   [x] Implement Basic Manager Driver Functionality
    *   Drive fundamental address and control signals: `HADDR`, `HWRITE`, `HSIZE`.
    *   Implement basic transfer types: `NONSEQ` for the first beat and `IDLE` for inactive cycles.
    *   Drive `HWDATA` for write transfers.
    *   Wait for `HREADY` to be HIGH before completing a transfer and starting the next one.

*   [x] Implement a Basic Subordinate "Memory Model" Driver
    *   Act as a simple memory: respond to transfers when its `HSELx` is asserted.
    *   On a read transfer, retrieve data and drive `HRDATA`.
    *   On a write transfer, sample `HWDATA` and store it.
    *   Always drive `HREADYOUT` HIGH (no wait states).
    *   Always drive `HRESP` as `OKAY`.

*   [x] Implement Basic Monitor Functionality
    *   On the rising edge of `HCLK`, sample the bus signals.
    *   Detect the start of a transfer when `HTRANS` is `NONSEQ` or `SEQ`.
    *   When `HREADY` is HIGH, capture the transfer details into an `ahb_transfer` object and write it to an analysis port.
    *   **Protocol Check:** Add an assertion to ensure the address phase and data phase are correctly pipelined (address phase of the current transfer occurs during the data phase of the previous one)[cite: 370].

*   [x] Implement Basic Burst Transfers
    *   [x] **Sequence Item:** Add a field for burst type (`HBURST`).
    *   [x] **Manager Driver:** Implement logic for a `SINGLE` transfer and a fixed-length incrementing burst (`INCR4`). This involves driving `HTRANS` as `NONSEQ` followed by `SEQ`.
    *   [x] **Subordinate Driver:** Must be able to handle a sequence of back-to-back transfers that form a burst.
    *   [x] **Monitor:** Identify and reconstruct full bursts.

*   [x] Create MVP-Level Tests
    *   [x] `test_single_read`: A single read to the Subordinate.
    *   [x] `test_single_write`: A single write to the Subordinate, verified with a read-back.
    *   [x] `test_write_read_verify`: A sequence writes a random value, reads it back, and verifies the data within the sequence.
    *   [x] `test_incr4_write_read`: Perform a 4-beat write burst, then read back the same locations to verify data integrity.
    *   [ ] `test_back_to_back_rw`: Sequences of multiple non-burst writes and reads.

*   [ ] VIP Enhancements
    *   [x] Add basic functional coverage collection.
    *   [x] Implement and connect a scoreboard for write/read verification.
    *   [ ] Refactor Subordinate driver to move memory model to the sequence level.
    *   [ ] Refactor `ahb_burst_transaction` to `ahb_burst_item`.

---

## Post-MVP Development (Phase 2)

This phase adds advanced features to make the VIP robust, comprehensive, and capable of verifying complex corner cases.

*   [ ] Implement Waited Transfers
    *   **Subordinate VIP:** Add logic and configuration to drive `HREADYOUT` LOW to insert wait states into transfers.
    *   **Manager VIP:** Ensure it holds address and control signals stable when `HREADY` is LOW.
    *   **Monitor:** Correctly handle waited transfers without erroneously capturing multiple transactions. Add protocol checks for illegal signal changes during wait states.

*   [ ] Implement Full Burst and Transfer Type Support
    *   Implement all burst types: `INCR8`, `INCR16`, `WRAP4`, `WRAP8`, `WRAP16`, and undefined-length `INCR`.
    *   Implement `BUSY` transfers, allowing the manager to insert idle cycles within a burst.
    *   **Protocol Check:** Add assertions to verify correct wrap address calculation and ensure managers do not cross 1KB boundaries on incrementing bursts.
    *   **Protocol Check:** Ensure fixed-length bursts are not terminated with a `BUSY` transfer.

*   [ ] Implement Subordinate Error Response
    *   **Subordinate VIP:** Add logic to generate a two-cycle `ERROR` response (`HRESP`=1, `HREADYOUT`=0, then `HREADYOUT`=1). This should be configurable and triggerable.
    *   **Manager VIP:** Add logic to properly handle an `ERROR` response, such as cancelling the rest of a burst by driving `HTRANS` to `IDLE`.
    *   **Monitor:** Correctly capture the `ERROR` response and check that it follows the two-cycle protocol.

*   [ ] Advanced Monitor Features
    *   [ ] Implement an FSM to detect and correctly sample full burst transfers.
    *   [ ] Add a second analysis port (`burst_ap`) to broadcast completed burst transactions. The original port will continue to broadcast individual beats.
    *   [ ] Implement protocol error-checking mechanisms (e.g., for illegal `HTRANS` transitions, `HBURST` changes during a burst, etc.).

*   [ ] Add Support for AHB5 Features
    *   **Write Strobes (`HWSTRB`):**
        *   [x] Added `HWSTRB` to the interface and transaction object.
        *   Update the Manager driver to control which byte lanes are valid during a write.
        *   Update the Subordinate memory model to respect the write strobes.
        *   Add coverage for sparse writes.
    *   [ ] Exclusive Transfers (`HEXCL`, `HMASTER`, `HEXOKAY`):
        *   Add the required signals to the interface and transaction object.
        *   Implement an "Exclusive Access Monitor" component in the test environment that tracks exclusive reads and determines the success/failure of exclusive writes.
        *   Update the Subordinate to route/generate the `HEXOKAY` response.
        *   Add protocol checks for all restrictions on exclusive transfers (e.g., must be single beat, address aligned).
    *   [ ] Secure Transfers (`HNONSEC`):
        *   Add `HNONSEC` to the interface and transaction class.
        *   Allow sequences to control the security level of a transfer.
    *   [ ] Protection Control & Memory Types (`HPROT`):
        *   Expand the `HPROT` field in the transaction object to its full 7-bit width.
        *   Add constraints and sequences to generate all valid memory type encodings.

*   [ ] Enhance Configurability and Usability
    *   **Data/Address Width:** Ensure all components (driver, monitor, transaction) are fully scalable based on the interface parameters.
    *   **Endianness:** Add a configuration parameter for endianness (`BE8` or `BE32`) and implement the correct byte-lane mapping logic in the driver and monitor based on the selected mode.
    *   **Callbacks:** Add UVM callbacks in the driver and monitor for advanced error injection and customized analysis.
    *   **Coverage:** Implement comprehensive functional coverage for all transaction fields (`HBURST`, `HSIZE`, `HPROT`, etc.), wait states, and response types.
    *   **Assertions:** Create a complete SystemVerilog Assertion (SVA) checker module for all protocol rules defined in the specification.