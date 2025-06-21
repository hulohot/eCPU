# Cocotb Makefile for eCPU tests

# Remove oss-cad-suite from PATH to avoid conflicts, but keep everything else
export PATH := $(shell echo $$PATH | tr ':' '\n' | grep -v oss-cad-suite | tr '\n' ':' | sed 's/:$$//')

# Simulator to use
SIM ?= verilator

# Python executable (use the system python3 which has cocotb installed)
PYTHON_BIN ?= python3

# Top level module
TOPLEVEL ?= alu

# Test module
MODULE ?= test_alu

# Verilog sources
VERILOG_SOURCES ?= ../../rtl/core/alu.sv

# Cocotb configuration
COCOTB_REDUCED_LOG_FMT = 1
EXTRA_ARGS += --trace --trace-structs

# Include cocotb's make rules to take care of the simulator setup
include $(shell $(PYTHON_BIN) -c "import cocotb; print(cocotb.__path__[0])")/share/makefiles/Makefile.sim 