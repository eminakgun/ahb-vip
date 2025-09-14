# **AHB-VIP Test Plan**

This document outlines the verification strategy for the AHB-VIP. The plan is divided into phases, with each phase building upon the previous one to incrementally verify the VIP's functionality.

### **Phase 0: Environment Sanity Verification**

*   **Goal:** Ensure all UVM components are instantiated correctly and connected without elaboration or run-time errors.
*   **Test:** `base_test`
*   **Method:** Compile the VIP and run the `base_test`. This test builds the environment with one manager and one subordinate agent and runs for a short duration. A successful run with no UVM errors verifies the basic testbench structure.
*   **Status:** **[COMPLETED]**

### **Phase 1: MVP Development Verification**

*   **Goal:** Verify basic, zero-wait-state, single and simple burst transfers.
*   **Tests:**
    1.  **`test_single_write`**:
        *   **Stimulus:** A sequence writes a single data word to a random address.
        *   **Status:** **[COMPLETED]**
    2.  **`test_single_read`**:
        *   **Stimulus:** A sequence reads a single data word from a random address.
        *   **Status:** **[COMPLETED]**
    3.  **`test_write_read_verify`**:
        *   **Stimulus:** A dedicated sequence writes a random value to a random address, then reads it back.
        *   **Checking:** The sequence compares the read-back data with the written data.
        *   **Status:** **[COMPLETED]**
    4.  **`test_incr4_write_read`**:
        *   **Stimulus:** A sequence performs a 4-beat `INCR4` write burst of random data to a random starting address. It then performs a 4-beat `INCR4` read burst from the same addresses.
        *   **Checking:** The sequence compares the read-back data with the original written data for all 4 beats. The advanced monitor will also be checked to ensure it correctly captures one single burst transaction containing four beats.
        *   **Status:** **[COMPLETED]**
    5.  **`test_back_to_back_rw`**:
        *   **Stimulus:** A sequence that performs multiple single write and read transfers back-to-back.
        *   **Checking:** Data integrity is maintained across multiple independent transfers.
        *   **Status:** **[NOT STARTED]**

### **Phase 1.6: Functional Coverage Verification**

*   **Goal:** Ensure that the functional coverage points are being sampled correctly.
*   **Tests:**
    1.  **`test_coverage_sampling`**:
        *   **Stimulus:** Run a variety of existing tests (e.g., `test_write_read_verify`, `test_incr4_write_read`) with coverage enabled in the test configuration.
        *   **Checking:** Verify from simulation logs or reports that the `ahb_transfer_cg` covergroup in the `coverage_collector` is being sampled. A coverage percentage greater than zero confirms success.
        *   **Status:** **[COMPLETED]**

### **Phase 2: Post-MVP Advanced Feature Verification**

*   **Goal:** Verify advanced features like wait states, all burst types, and error responses.
*   **Tests:**
    1.  **`test_waited_transfers`**:
        *   **Stimulus:** Configure the subordinate agent to randomly insert wait states. Re-run all Phase 1 tests.
        *   **Checking:** Verify data integrity remains correct. Protocol compliance during wait states will be checked by SVA in the interface.
        *   **Status:** **[NOT STARTED]**
    2.  **`test_all_burst_types`**:
        *   **Stimulus:** Create dedicated sequences for `WRAP4`, `INCR8`, `WRAP8`, `INCR16`, and `WRAP16` bursts. Each sequence will perform a write-then-read-back test.
        *   **Checking:** Data integrity checks within each sequence.
        *   **Status:** **[NOT STARTED]**
    3.  **`test_subordinate_error_response`**:
        *   **Stimulus:** Configure the subordinate to respond with an `ERROR` on a specific access. A sequence will then attempt to access that address.
        *   **Checking:** The manager driver must handle the `ERROR` response correctly (e.g., by aborting a burst). The monitor must correctly capture the two-cycle `ERROR` response.
        *   **Status:** **[NOT STARTED]**
