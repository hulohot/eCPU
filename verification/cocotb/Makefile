# Cocotb Makefile for eCPU tests using cocotb_test.simulator

# Python executable
PYTHON ?= python3

# Common test parameters
SIMULATOR ?= verilator

# Test targets
.PHONY: test-alu test-regfile test-instruction_memory test-data_memory test-fetch test-decode test-execute test-memory_stage test-writeback test-hazard_unit

test-alu:
	@echo "Running ALU tests..."
	env -i PATH="/usr/local/bin:/usr/bin:/bin" PYTHONPATH="." \
	$(PYTHON) -c "\
from cocotb_test.simulator import run; \
run( \
    verilog_sources=['../../rtl/core/alu.sv'], \
    toplevel='alu', \
    module='test_alu', \
    simulator='$(SIMULATOR)', \
    extra_args=['--trace', '--trace-structs'] \
)"

test-regfile:
	@echo "Running register file tests..."
	env -i PATH="/usr/local/bin:/usr/bin:/bin" PYTHONPATH="." \
	$(PYTHON) -c "\
from cocotb_test.simulator import run; \
run( \
    verilog_sources=['../../rtl/core/regfile.sv'], \
    toplevel='regfile', \
    module='test_regfile', \
    simulator='$(SIMULATOR)', \
    extra_args=['--trace', '--trace-structs'] \
)"

test-instruction_memory:
	@echo "Running instruction memory tests..."
	env -i PATH="/usr/local/bin:/usr/bin:/bin" PYTHONPATH="." \
	$(PYTHON) -c "\
from cocotb_test.simulator import run; \
run( \
    verilog_sources=['../../rtl/memory/instruction_memory.sv'], \
    toplevel='instruction_memory', \
    module='test_instruction_memory', \
    simulator='$(SIMULATOR)', \
    extra_args=['--trace', '--trace-structs'] \
)"

test-data_memory:
	@echo "Running data memory tests..."
	env -i PATH="/usr/local/bin:/usr/bin:/bin" PYTHONPATH="." \
	$(PYTHON) -c "\
from cocotb_test.simulator import run; \
run( \
    verilog_sources=['../../rtl/memory/data_memory.sv'], \
    toplevel='data_memory', \
    module='test_data_memory', \
    simulator='$(SIMULATOR)', \
    extra_args=['--trace', '--trace-structs'] \
)"

test-fetch:
	@echo "Running fetch stage tests..."
	env -i PATH="/usr/local/bin:/usr/bin:/bin" PYTHONPATH="." \
	$(PYTHON) -c "\
from cocotb_test.simulator import run; \
run( \
    verilog_sources=['../../rtl/core/fetch.sv'], \
    toplevel='fetch', \
    module='test_fetch', \
    simulator='$(SIMULATOR)', \
    extra_args=['--trace', '--trace-structs'] \
)"

test-decode:
	@echo "Running decode stage tests..."
	env -i PATH="/usr/local/bin:/usr/bin:/bin" PYTHONPATH="." \
	$(PYTHON) -c "\
from cocotb_test.simulator import run; \
run( \
    verilog_sources=['../../rtl/core/decode.sv'], \
    toplevel='decode', \
    module='test_decode', \
    simulator='$(SIMULATOR)', \
    extra_args=['--trace', '--trace-structs'] \
)"

test-execute:
	@echo "Running execute stage tests..."
	env -i PATH="/usr/local/bin:/usr/bin:/bin" PYTHONPATH="." \
	$(PYTHON) -c "\
from cocotb_test.simulator import run; \
run( \
    verilog_sources=['../../rtl/core/execute.sv', '../../rtl/core/alu.sv'], \
    toplevel='execute', \
    module='test_execute', \
    simulator='$(SIMULATOR)', \
    extra_args=['--trace', '--trace-structs'] \
)"

test-memory_stage:
	@echo "Running memory stage tests..."
	env -i PATH="/usr/local/bin:/usr/bin:/bin" PYTHONPATH="." \
	$(PYTHON) -c "\
from cocotb_test.simulator import run; \
run( \
    verilog_sources=['../../rtl/core/memory.sv'], \
    toplevel='memory', \
    module='test_memory_stage', \
    simulator='$(SIMULATOR)', \
    extra_args=['--trace', '--trace-structs'] \
)"

test-writeback:
	@echo "Running writeback stage tests..."
	env -i PATH="/usr/local/bin:/usr/bin:/bin" PYTHONPATH="." \
	$(PYTHON) -c "\
from cocotb_test.simulator import run; \
run( \
    verilog_sources=['../../rtl/core/writeback.sv'], \
    toplevel='writeback', \
    module='test_writeback', \
    simulator='$(SIMULATOR)', \
    extra_args=['--trace', '--trace-structs'] \
)"

test-hazard_unit:
	@echo "Running hazard unit tests..."
	env -i PATH="/usr/local/bin:/usr/bin:/bin" PYTHONPATH="." \
	$(PYTHON) -c "\
from cocotb_test.simulator import run; \
run( \
    verilog_sources=['../../rtl/core/hazard_unit.sv'], \
    toplevel='hazard_unit', \
    module='test_hazard_unit', \
    simulator='$(SIMULATOR)', \
    extra_args=['--trace', '--trace-structs'] \
)"

clean:
	rm -rf __pycache__
	rm -rf .pytest_cache
	rm -rf sim_build

# Run all tests
test-all: test-alu test-regfile test-instruction_memory test-data_memory test-fetch test-decode test-execute test-memory_stage test-writeback test-hazard_unit 