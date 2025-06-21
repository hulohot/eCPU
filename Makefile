# eCPU RISC-V RV32I Implementation Makefile
# ==================================================

# Project configuration
PROJECT_NAME = eCPU
TOP_MODULE = eCPU_top
RTL_DIR = rtl
TEST_DIR = verification
DOCS_DIR = docs
BUILD_DIR = build
SYNTH_DIR = synthesis

# Tool configuration
VERILATOR = verilator
YOSYS = yosys
NEXTPNR = nextpnr-ice40
ICEPACK = icepack
ICEPROG = iceprog
PYTHON = python3
COCOTB_TEST = cocotb-test

# iCEBreaker specific configuration
FPGA_PART = up5k
FPGA_PACKAGE = sg48
PCF_FILE = synthesis/icebreaker/icebreaker.pcf

# Source files
RTL_SOURCES = $(shell find $(RTL_DIR) -name "*.sv" -o -name "*.v")
CORE_SOURCES = $(wildcard $(RTL_DIR)/core/*.sv)
MEMORY_SOURCES = $(wildcard $(RTL_DIR)/memory/*.sv)
COMMON_SOURCES = $(wildcard $(RTL_DIR)/common/*.sv)

# Test files
COCOTB_TESTS = $(wildcard $(TEST_DIR)/cocotb/test_*.py)
UNIT_TESTS = $(wildcard $(TEST_DIR)/unit_tests/test_*.py)

# Build directories
$(BUILD_DIR):
	mkdir -p $(BUILD_DIR)

$(BUILD_DIR)/sim:
	mkdir -p $(BUILD_DIR)/sim

$(BUILD_DIR)/synth:
	mkdir -p $(BUILD_DIR)/synth

$(BUILD_DIR)/docs:
	mkdir -p $(BUILD_DIR)/docs

# ==================================================
# SIMULATION TARGETS
# ==================================================

.PHONY: sim-verilator sim-icarus sim-all
sim-verilator: $(BUILD_DIR)/sim
	@echo "Running Verilator simulation..."
	cd $(BUILD_DIR)/sim && \
	$(VERILATOR) --cc --exe --build -j 0 \
		-Wall -Wno-WIDTH -Wno-UNUSED \
		--top-module $(TOP_MODULE) \
		$(addprefix ../../,$(RTL_SOURCES)) \
		--trace --trace-structs

sim-icarus: $(BUILD_DIR)/sim
	@echo "Running Icarus Verilog simulation..."
	cd $(BUILD_DIR)/sim && \
	iverilog -g2012 -o $(TOP_MODULE).vvp \
		$(addprefix ../../,$(RTL_SOURCES))
	cd $(BUILD_DIR)/sim && vvp $(TOP_MODULE).vvp

sim-all: sim-verilator sim-icarus

# ==================================================
# COCOTB TESTING TARGETS
# ==================================================

.PHONY: test-alu test-regfile test-memory test-pipeline test-cpu test-all test-unit coverage

test-alu:
	@echo "Running ALU tests..."
	cd $(TEST_DIR)/cocotb && \
	env -i PATH="/usr/local/bin:/usr/bin:/bin" PYTHONPATH="." \
	$(PYTHON) -c "\
from cocotb_test.simulator import run; \
run( \
    verilog_sources=['../../rtl/core/alu.sv'], \
    toplevel='alu', \
    module='test_alu', \
    simulator='verilator', \
    extra_args=['--trace', '--trace-structs'] \
)"

test-regfile:
	@echo "Running register file tests..."
	cd $(TEST_DIR)/cocotb && \
	env -i PATH="/usr/local/bin:/usr/bin:/bin" PYTHONPATH="." \
	$(PYTHON) -c "\
from cocotb_test.simulator import run; \
run( \
    verilog_sources=['../../rtl/core/regfile.sv'], \
    toplevel='regfile', \
    module='test_regfile', \
    simulator='verilator', \
    extra_args=['--trace', '--trace-structs'] \
)"

test-memory:
	@echo "Running memory tests..."
	cd $(TEST_DIR)/cocotb && \
	$(PYTHON) -m pytest test_memory.py -v --tb=short

test-pipeline:
	@echo "Running pipeline tests..."
	cd $(TEST_DIR)/cocotb && \
	$(PYTHON) -m pytest test_pipeline.py -v --tb=short

test-cpu:
	@echo "Running CPU integration tests..."
	cd $(TEST_DIR)/cocotb && \
	$(PYTHON) -m pytest test_cpu.py -v --tb=short

test-compliance:
	@echo "Running RISC-V compliance tests..."
	cd $(TEST_DIR)/compliance && \
	$(PYTHON) run_compliance.py

test-unit: $(UNIT_TESTS)
	@echo "Running unit tests..."
	cd $(TEST_DIR)/unit_tests && \
	$(PYTHON) -m pytest . -v --tb=short

test-all: test-unit test-alu test-regfile test-memory test-pipeline test-cpu test-compliance

coverage:
	@echo "Generating coverage report..."
	cd $(TEST_DIR) && \
	$(PYTHON) -m pytest --cov=../$(RTL_DIR) --cov-report=html --cov-report=term

# ==================================================
# SYNTHESIS TARGETS
# ==================================================

.PHONY: synth-yosys synth-icebreaker synth-check synth-clean

synth-yosys: $(BUILD_DIR)/synth
	@echo "Running Yosys synthesis check..."
	cd $(BUILD_DIR)/synth && \
	$(YOSYS) -p "read_verilog $(addprefix ../../,$(RTL_SOURCES)); \
		hierarchy -top $(TOP_MODULE); \
		proc; opt; fsm; opt; memory; opt; \
		techmap; opt; \
		stat; \
		write_verilog $(TOP_MODULE)_synth.v"

synth-icebreaker: $(BUILD_DIR)/synth synth-yosys
	@echo "Synthesizing for iCEBreaker..."
	cd $(BUILD_DIR)/synth && \
	$(YOSYS) -p "read_verilog $(addprefix ../../,$(RTL_SOURCES)); \
		hierarchy -top $(TOP_MODULE); \
		synth_ice40 -top $(TOP_MODULE) -json $(TOP_MODULE).json"
	cd $(BUILD_DIR)/synth && \
	$(NEXTPNR) --$(FPGA_PART) --package $(FPGA_PACKAGE) \
		--json $(TOP_MODULE).json \
		--pcf ../../$(PCF_FILE) \
		--asc $(TOP_MODULE).asc
	cd $(BUILD_DIR)/synth && \
	$(ICEPACK) $(TOP_MODULE).asc $(TOP_MODULE).bin

synth-check: synth-yosys
	@echo "Synthesis check complete. See build/synth/$(TOP_MODULE)_synth.v"

synth-clean:
	rm -rf $(BUILD_DIR)/synth/*

# ==================================================
# FPGA PROGRAMMING TARGETS
# ==================================================

.PHONY: prog-icebreaker prog-flash

prog-icebreaker: synth-icebreaker
	@echo "Programming iCEBreaker..."
	$(ICEPROG) $(BUILD_DIR)/synth/$(TOP_MODULE).bin

prog-flash: synth-icebreaker
	@echo "Programming iCEBreaker flash..."
	$(ICEPROG) -S $(BUILD_DIR)/synth/$(TOP_MODULE).bin

# ==================================================
# FORMAL VERIFICATION TARGETS
# ==================================================

.PHONY: formal-alu formal-pipeline formal-all

formal-alu:
	@echo "Running formal verification on ALU..."
	cd $(TEST_DIR)/formal && \
	sby -f alu.sby

formal-pipeline:
	@echo "Running formal verification on pipeline..."
	cd $(TEST_DIR)/formal && \
	sby -f pipeline.sby

formal-all: formal-alu formal-pipeline

# ==================================================
# DOCUMENTATION TARGETS
# ==================================================

.PHONY: docs docs-clean docs-serve

docs: $(BUILD_DIR)/docs
	@echo "Building documentation..."
	@echo "Generating module documentation..."
	cd $(DOCS_DIR) && \
	$(PYTHON) ../scripts/gen_module_docs.py ../$(RTL_DIR) $(BUILD_DIR)/docs
	@echo "Converting markdown to HTML..."
	find $(DOCS_DIR) -name "*.md" -exec pandoc {} -o $(BUILD_DIR)/docs/{}.html -s --css=style.css \;

docs-clean:
	rm -rf $(BUILD_DIR)/docs/*

docs-serve: docs
	@echo "Serving documentation at http://localhost:8000"
	cd $(BUILD_DIR)/docs && $(PYTHON) -m http.server 8000

# ==================================================
# SOFTWARE TOOLCHAIN TARGETS
# ==================================================

.PHONY: toolchain-check bootloader examples

toolchain-check:
	@echo "Checking RISC-V toolchain..."
	@which riscv32-unknown-elf-gcc || echo "RISC-V GCC not found"
	@which riscv32-unknown-elf-objdump || echo "RISC-V objdump not found"
	@which riscv32-unknown-elf-objcopy || echo "RISC-V objcopy not found"

bootloader:
	@echo "Building bootloader..."
	$(MAKE) -C software/bootloader

examples:
	@echo "Building software examples..."
	$(MAKE) -C software/examples

# ==================================================
# UTILITY TARGETS
# ==================================================

.PHONY: clean lint format install-deps help status

clean:
	rm -rf $(BUILD_DIR)
	find . -name "*.pyc" -delete
	find . -name "__pycache__" -delete
	find . -name "*.vcd" -delete
	find . -name "*.fst" -delete
	find . -name "*.vvp" -delete

lint:
	@echo "Linting RTL files..."
	@echo "Running Verilator lint..."
	$(VERILATOR) --lint-only -Wall -Wno-WIDTH -Wno-UNUSED \
		--top-module $(TOP_MODULE) $(RTL_SOURCES)
	@echo "Linting Python files..."
	find $(TEST_DIR) -name "*.py" -exec python3 -m flake8 {} \;

format:
	@echo "Formatting Python files..."
	find $(TEST_DIR) -name "*.py" -exec python3 -m black {} \;
	find scripts -name "*.py" -exec python3 -m black {} \;

install-deps:
	@echo "Installing Python dependencies..."
	pip3 install cocotb cocotb-test pytest pytest-cov black flake8 pandas numpy
	@echo "Installing Verilator (if not present)..."
	@which verilator || echo "Please install Verilator manually"
	@echo "Installing Yosys toolchain (if not present)..."
	@which yosys || echo "Please install Yosys toolchain manually"

status:
	@echo "=== eCPU Project Status ==="
	@echo "RTL Sources: $(words $(RTL_SOURCES)) files"
	@echo "Core modules: $(words $(CORE_SOURCES)) files"
	@echo "Memory modules: $(words $(MEMORY_SOURCES)) files"
	@echo "Common modules: $(words $(COMMON_SOURCES)) files"
	@echo "Cocotb tests: $(words $(COCOTB_TESTS)) files"
	@echo "Unit tests: $(words $(UNIT_TESTS)) files"
	@echo ""
	@echo "Recent changes:"
	@git log --oneline -5 2>/dev/null || echo "No git history"

help:
	@echo "eCPU RISC-V RV32I Implementation"
	@echo "================================="
	@echo ""
	@echo "SIMULATION:"
	@echo "  sim-verilator    - Run Verilator simulation"
	@echo "  sim-icarus       - Run Icarus Verilog simulation"
	@echo "  sim-all          - Run all simulations"
	@echo ""
	@echo "TESTING:"
	@echo "  test-alu         - Run ALU tests"
	@echo "  test-regfile     - Run register file tests"
	@echo "  test-memory      - Run memory tests"
	@echo "  test-pipeline    - Run pipeline tests"
	@echo "  test-cpu         - Run CPU integration tests"
	@echo "  test-compliance  - Run RISC-V compliance tests"
	@echo "  test-unit        - Run unit tests"
	@echo "  test-all         - Run all tests"
	@echo "  coverage         - Generate coverage report"
	@echo ""
	@echo "SYNTHESIS:"
	@echo "  synth-yosys      - Synthesis check with Yosys"
	@echo "  synth-icebreaker - Synthesize for iCEBreaker"
	@echo "  synth-check      - Quick synthesis check"
	@echo "  synth-clean      - Clean synthesis outputs"
	@echo ""
	@echo "FPGA:"
	@echo "  prog-icebreaker  - Program iCEBreaker SRAM"
	@echo "  prog-flash       - Program iCEBreaker flash"
	@echo ""
	@echo "FORMAL VERIFICATION:"
	@echo "  formal-alu       - Formal verification of ALU"
	@echo "  formal-pipeline  - Formal verification of pipeline"
	@echo "  formal-all       - Run all formal verification"
	@echo ""
	@echo "DOCUMENTATION:"
	@echo "  docs             - Build documentation"
	@echo "  docs-clean       - Clean documentation"
	@echo "  docs-serve       - Serve documentation locally"
	@echo ""
	@echo "SOFTWARE:"
	@echo "  toolchain-check  - Check RISC-V toolchain"
	@echo "  bootloader       - Build bootloader"
	@echo "  examples         - Build software examples"
	@echo ""
	@echo "UTILITIES:"
	@echo "  clean            - Clean all build outputs"
	@echo "  lint             - Lint RTL and Python files"
	@echo "  format           - Format Python files"
	@echo "  install-deps     - Install dependencies"
	@echo "  status           - Show project status"
	@echo "  help             - Show this help"

# Default target
.DEFAULT_GOAL := help 