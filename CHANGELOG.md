# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [0.1.0] - 2025-09-09

### Added

-   **Phase 0: VIP Architecture & Infrastructure**
    -   Defined AHB SystemVerilog `interface`.
    -   Created Core Transaction/Sequence Item (`ahb_sequence_item`).
    -   Built AHB Agent (`ahb_agent`).
    -   Implemented Basic Agent Components (Sequencer, Driver, Monitor).
    -   Set up a Basic Test Environment (`ahb_env`).

-   **Core Infrastructure Enhancements**
    -   Defined `HTRANS` and `HSIZE` enum types.
    -   Refactored `ahb_pkg` for better organization and single-file compilation.
    -   Implemented Top-Level Testbench (`tb_top.sv`).
    -   Corrected UVM Field Macros (`uvm_field_enum`).
    -   Ensured all classes have appropriate constructors.
    -   Implemented robust VIF passing mechanism.
    -   Added `HWSTRB` to interface and transaction object (part of AHB5 features).
    -   Removed `super.build_phase` calls as per specific user instruction.
