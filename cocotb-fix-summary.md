# Cocotb Test Runner Fix

## Issue Fixed

The CI pipeline was incorrectly using **`pytest`** to run cocotb tests instead of the proper **`cocotb`** test runner.

## Before (Incorrect)
```yaml
- name: Run ALU tests
  run: |
    cd verification/cocotb
    if [ -f test_alu.py ]; then
      python -m pytest test_alu.py -v  # ❌ Wrong runner!
    fi
```

## After (Correct)
```yaml
- name: Run ALU tests
  run: |
    cd verification/cocotb
    if [ -f test_alu.py ] && [ -f ../../rtl/core/alu.sv ]; then
      make test-alu  # ✅ Proper cocotb runner!
    fi
```

## Why This Matters

### Cocotb Tests Require Special Execution
- **Cocotb tests are NOT pytest tests** - they need hardware simulation
- **Need RTL compilation** with Verilator/other simulators  
- **Need proper signal bindings** between Python and SystemVerilog
- **Need async/await handling** for simulation timing

### The Correct Method
The project already has a proper `Makefile` in `verification/cocotb/` that uses:
```python
from cocotb_test.simulator import run
run(
    verilog_sources=['../../rtl/core/alu.sv'],
    toplevel='alu',
    module='test_alu',
    simulator='verilator',
    extra_args=['--trace', '--trace-structs']
)
```

## Tests Now Properly Run

### Individual Module Tests
- `make test-alu` - ALU functionality
- `make test-regfile` - Register file  
- `make test-instruction_memory` - Instruction memory
- `make test-data_memory` - Data memory
- `make test-fetch` - Fetch stage
- `make test-decode` - Decode stage

### Integration Tests  
- `make test-cpu-integration` - Full CPU integration

## Verification

To test a cocotb test manually:
```bash
cd verification/cocotb
make test-alu  # Runs actual hardware simulation
```

You should see:
- ✅ Verilator compilation output
- ✅ Cocotb test execution with timing
- ✅ VCD waveform generation
- ✅ Test pass/fail results

## Impact

- ✅ **Hardware tests now actually test hardware** (not just Python syntax)
- ✅ **Simulation errors properly caught** and fail CI
- ✅ **Follows SystemVerilog coding standards** with proper verification
- ✅ **Each module has corresponding cocotb test** as per project rules