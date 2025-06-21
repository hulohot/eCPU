# eCPU (Ethan's CPU) - RISC-V RV32I Implementation Project

## Project Overview

Create a complete RISC-V RV32I CPU implementation with comprehensive verification, documentation, and toolchain support. The project should be production-ready with formal verification, synthesis support for SkyWater 130nm PDK, and extensive testing infrastructure.

## Core Requirements

### 1. CPU Architecture

ISA: RISC-V RV32I (base integer instruction set)
Pipeline: 3-stage pipeline (Fetch, Decode/Execute, Memory/Writeback)
Memory Architecture: Von Neumann (unified memory)
Memory Sizes:

Instruction/Data Memory: 64KB (parameterizable)
Register File: 32 x 32-bit registers


Bus Interface: Wishbone B4 compatible interface for extensibility

### 2. Verification Infrastructure

Primary Verification: cocotb-based testbenches in Python
Formal Verification: SymbiYosys integration with SVA properties
Compliance Testing: RISC-V compliance test suite integration
Coverage: Code coverage and functional coverage tracking
Testbench Generator: Automated test generation for:

Random instruction sequences
Directed corner cases
Memory access patterns
Pipeline hazard scenarios



### 3. Development Tools

HDL: SystemVerilog/Verilog
Simulation: Icarus Verilog or Verilator
Formal: SymbiYosys
Synthesis: Yosys for quick checks, OpenLane for full SkyWater 130 flow
Waveform Viewer: GTKWave with automatic VCD/FST generation
Build System: Makefile-based with clear targets

### 4. Features to Implement

Performance Counters:

Cycle counter
Instruction counter
Stall counter
Branch prediction statistics (if applicable)
Memory access statistics


Interrupt Support:

Timer interrupt
Software interrupt
External interrupt pin
Proper CSR (Control Status Register) implementation


Debug Features:

Instruction trace logging (PC, instruction, registers modified)
Breakpoint support
Single-step execution mode
Register and memory dump capabilities



### 5. Software Toolchain

Compiler: RISC-V GCC toolchain integration
Assembler/Linker: Custom linker scripts for memory layout
Program Loader: Simple bootloader/program loader
Runtime: Minimal C runtime (crt0.S)
Examples: Sample programs in C and assembly

### 6. Documentation Requirements

Create comprehensive documentation including:

Architecture Guide (docs/architecture.md):

Block diagrams
Pipeline stages explanation
Timing diagrams
Memory map


Verification Guide (docs/verification.md):

Test plan
Coverage goals
How to run tests
Adding new tests


User Guide (docs/user_guide.md):

Building the CPU
Running simulations
Synthesizing for FPGA/ASIC
Writing and running programs


Implementation Details (docs/implementation/):

Module-by-module documentation
Interface specifications
Design decisions and trade-offs



### 7. Project Structure

```
eCPU/
├── rtl/                    # RTL source files
│   ├── core/              # CPU core modules
│   │   ├── eCPU_top.sv
│   │   ├── fetch.sv
│   │   ├── decode.sv
│   │   ├── execute.sv
│   │   ├── memory.sv
│   │   ├── writeback.sv
│   │   ├── regfile.sv
│   │   ├── alu.sv
│   │   └── csr.sv
│   ├── memory/            # Memory modules
│   ├── peripherals/       # Future peripherals
│   └── common/            # Common modules (muxes, etc.)
├── verification/          # Verification files
│   ├── cocotb/           # cocotb testbenches
│   ├── formal/           # Formal verification
│   ├── compliance/       # RISC-V compliance tests
│   └── unit_tests/       # Unit tests for modules
├── software/             # Software toolchain
│   ├── bootloader/
│   ├── runtime/
│   ├── examples/
│   └── tools/           # Assembler, loader, etc.
├── synthesis/           # Synthesis scripts
│   ├── yosys/
│   └── openlane/
├── scripts/             # Build and utility scripts
├── docs/                # Documentation
├── tests/               # Integration tests
├── .github/             # CI/CD workflows
├── Makefile            # Top-level Makefile
└── TODO.md             # Comprehensive task list
```

### 8. CI/CD Pipeline

GitHub Actions workflow for:

RTL linting
Unit tests
Integration tests
Compliance tests
Synthesis checks
Documentation building
Coverage reports



### 9. Comprehensive TODO List

Create and maintain a TODO.md file with:

Task priorities (P0, P1, P2)
Task dependencies
Estimated effort
Assignment status
Completion status

Categories:

Core Implementation
Verification
Documentation
Toolchain
Optimization
Future Extensions

Implementation Strategy
Start by asking these clarifying questions:

Development Environment: What OS are you using? Do you have the RISC-V toolchain installed?
FPGA Target: Do you have a specific FPGA board for testing before ASIC synthesis?
Performance Goals: Any specific performance targets (MHz, CPI)?
Memory Interface: Should we implement caches in the future? If so, should the current design accommodate this?
Debugging Interface: Would you prefer JTAG or a simpler custom debug interface?
Peripheral Plans: What peripherals do you plan to add first? (UART, SPI, I2C, GPIO?)
Testing Priority: Should we prioritize certain instruction types or scenarios?
Branch Prediction: Should the 3-stage pipeline include simple branch prediction?

First Implementation Phase
Begin with:

Basic module structure and interfaces
Simple ALU and register file
Basic cocotb testbench framework
Minimal instruction support (ADD, SUB, LW, SW, BEQ)
Simple memory model
TODO list generation with parallel task identification

The implementation should be modular and well-commented from the start to facilitate parallel development by background agents.

## Key Design Principles

Modularity: Clear interfaces between all components
Testability: Every module should be independently testable
Extensibility: Easy to add new features without major refactoring
Documentation: Document as you code
Open Source: Use only open-source tools and libraries
