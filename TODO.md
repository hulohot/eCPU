# eCPU Project TODO List

This document tracks all tasks for the eCPU RISC-V RV32I implementation project.

**Priority Levels:**
- P0: Critical path items required for basic functionality  
- P1: Important features needed for complete implementation
- P2: Nice-to-have features and optimizations

**Status:**
- 🔴 Not Started
- 🟡 In Progress  
- 🟢 Complete
- ⚫ Blocked

## Phase 1: Core Infrastructure (P0)

### RTL Development
- [x] 🟢 **P0** Create basic ALU module (2-3 days)
  - Dependencies: None
  - Implements: ADD, SUB, AND, OR, XOR, SLT, SLL, SRL, SRA, LUI, COPY operations
  
- [x] 🟢 **P0** Create register file module (1-2 days)
  - Dependencies: None
  - 32 x 32-bit registers with dual read, single write ports
  
- [ ] 🔴 **P0** Create instruction fetch module (2-3 days)
  - Dependencies: Memory interface
  - PC generation, instruction memory interface
  
- [ ] 🔴 **P0** Create instruction decode module (3-4 days)
  - Dependencies: None
  - Instruction parsing, control signal generation
  
- [ ] 🔴 **P0** Create execute stage module (2-3 days)
  - Dependencies: ALU, Register file
  - ALU control, data forwarding logic
  
- [ ] 🔴 **P0** Create memory stage module (2-3 days)
  - Dependencies: Wishbone interface
  - Load/store operations, data memory interface
  
- [ ] 🔴 **P0** Create writeback stage module (1-2 days)
  - Dependencies: Execute, Memory stages
  - Result writeback to register file

### Memory System
- [ ] 🔴 **P0** Create instruction memory model (1-2 days)
  - Dependencies: None
  - Simple synchronous RAM model
  
- [ ] 🔴 **P0** Create data memory model (1-2 days)
  - Dependencies: None
  - Byte-addressable memory with word/halfword/byte access
  
- [ ] 🔴 **P0** Implement basic Wishbone interface (2-3 days)
  - Dependencies: None
  - Wishbone B4 classic interface for memory access

### Pipeline Infrastructure
- [ ] 🔴 **P0** Create pipeline registers (1-2 days)
  - Dependencies: None
  - IF/ID, ID/EX, EX/MEM pipeline registers
  
- [ ] 🔴 **P0** Implement hazard detection unit (3-4 days)
  - Dependencies: All pipeline stages
  - Data hazards, control hazards
  
- [ ] 🔴 **P0** Create forwarding unit (2-3 days)
  - Dependencies: Pipeline stages
  - Data forwarding to resolve hazards

## Phase 2: Instruction Set Implementation (P0-P1)

### Arithmetic Instructions
- [ ] 🔴 **P0** ADD, SUB, SLT, SLTU (1 day)
- [ ] 🔴 **P0** AND, OR, XOR (1 day)
- [ ] 🔴 **P0** SLL, SRL, SRA (1-2 days)
- [ ] 🔴 **P0** ADDI, SLTI, SLTIU (1 day)
- [ ] 🔴 **P0** ANDI, ORI, XORI (1 day)
- [ ] 🔴 **P0** SLLI, SRLI, SRAI (1 day)
- [ ] 🔴 **P0** LUI, AUIPC (1-2 days)

### Memory Instructions
- [ ] 🔴 **P0** LW, SW (2-3 days)
- [ ] 🔴 **P0** LB, LBU, LH, LHU (2-3 days)
- [ ] 🔴 **P0** SB, SH (1-2 days)

### Control Flow Instructions
- [ ] 🔴 **P0** BEQ, BNE (2-3 days)
- [ ] 🔴 **P0** BLT, BLTU, BGE, BGEU (2-3 days)
- [ ] 🔴 **P0** JAL, JALR (2-3 days)

### System Instructions
- [ ] 🟡 **P1** ECALL, EBREAK (1-2 days)
- [ ] 🟡 **P1** FENCE (1 day) - NOP implementation initially

## Phase 3: Verification Infrastructure (P0)

### Cocotb Testbenches
- [x] 🟢 **P0** ALU unit tests (2-3 days)
  - Dependencies: ALU module
  - Test all arithmetic and logical operations
  
- [x] 🟢 **P0** Register file unit tests (1-2 days)
  - Dependencies: Register file module
  - Test read/write operations, port conflicts
  
- [ ] 🔴 **P0** Memory model unit tests (1-2 days)
  - Dependencies: Memory modules
  - Test different access sizes, alignment
  
- [ ] 🔴 **P0** Pipeline integration tests (3-4 days)
  - Dependencies: All pipeline stages
  - Test instruction sequences, hazards
  
- [ ] 🔴 **P0** Instruction set compliance tests (2-3 days)
  - Dependencies: Full CPU implementation
  - RISC-V compliance test suite

### Test Infrastructure
- [x] 🟢 **P0** Automated test runner (1-2 days)
  - Dependencies: Cocotb tests
  - Makefile targets for all tests
  
- [ ] 🔴 **P0** Coverage collection (2-3 days)
  - Dependencies: Test infrastructure
  - Code and functional coverage
  
- [ ] 🟡 **P1** Random instruction generator (3-4 days)
  - Dependencies: ISA implementation
  - Generate random valid instruction sequences

## Phase 4: Advanced Features (P1)

### Branch Prediction
- [ ] 🟡 **P1** Simple branch predictor (3-4 days)
  - Dependencies: Control flow instructions
  - 2-bit saturating counter predictor
  
- [ ] 🟡 **P1** Branch target buffer (2-3 days)
  - Dependencies: Branch predictor
  - Cache recent branch targets

### CSR (Control Status Registers)
- [ ] 🟡 **P1** CSR register file (2-3 days)
  - Dependencies: None
  - Basic CSR implementation
  
- [ ] 🟡 **P1** Performance counters (2-3 days)
  - Dependencies: CSR registers
  - Cycle, instruction, stall counters
  
- [ ] 🟡 **P1** CSR instructions (1-2 days)
  - Dependencies: CSR register file
  - CSRRW, CSRRS, CSRRC and immediate variants

### Debug Features
- [ ] 🟡 **P1** Instruction trace logging (2-3 days)
  - Dependencies: Pipeline implementation
  - PC, instruction, register changes
  
- [ ] 🟡 **P1** Register/memory dump (1-2 days)
  - Dependencies: CPU implementation
  - Debug interface for state inspection

## Phase 5: Software Toolchain (P1-P2)

### Runtime Support
- [ ] 🟡 **P1** Basic C runtime (crt0.S) (2-3 days)
  - Dependencies: None
  - Stack setup, main() call
  
- [ ] 🟡 **P1** Linker script (1-2 days)
  - Dependencies: Memory map
  - Memory layout for programs
  
- [ ] 🟡 **P1** Simple bootloader (2-3 days)
  - Dependencies: UART peripheral
  - Program loading mechanism

### Example Programs
- [ ] 🟡 **P1** Assembly examples (1-2 days)
  - Dependencies: Assembler
  - Basic instruction demonstrations
  
- [ ] 🟡 **P1** C examples (1-2 days)
  - Dependencies: C runtime
  - Hello world, fibonacci, sorting
  
- [ ] 🟡 **P2** Benchmarks (2-3 days)
  - Dependencies: C examples
  - Dhrystone, CoreMark ports

## Phase 6: Synthesis & Hardware (P1-P2)

### FPGA Implementation
- [ ] 🟡 **P1** Yosys synthesis scripts (1-2 days)
  - Dependencies: RTL completion
  - Basic synthesis for timing check
  
- [ ] 🟡 **P1** Tang Nano 20K port (2-3 days)
  - Dependencies: Synthesis scripts
  - Pin constraints, clock configuration
  
- [ ] 🟡 **P2** iCEBreaker port (2-3 days)
  - Dependencies: Synthesis scripts
  - Alternative FPGA target
  
- [ ] 🟡 **P2** ULX3S port (2-3 days)
  - Dependencies: Synthesis scripts
  - High-performance FPGA target

### ASIC Preparation
- [ ] 🟡 **P2** OpenLane flow setup (3-4 days)
  - Dependencies: RTL completion
  - SkyWater 130nm PDK integration
  
- [ ] 🟡 **P2** Timing constraints (1-2 days)
  - Dependencies: OpenLane setup
  - SDC file creation

## Phase 7: Formal Verification (P2)

### Property Specification
- [ ] 🟡 **P2** ALU properties (2-3 days)
  - Dependencies: ALU implementation
  - Formal verification of arithmetic
  
- [ ] 🟡 **P2** Pipeline properties (3-4 days)
  - Dependencies: Pipeline implementation
  - Hazard handling, data integrity
  
- [ ] 🟡 **P2** ISA properties (4-5 days)
  - Dependencies: Full CPU
  - Instruction behavior verification

## Phase 8: Documentation (P1-P2)

### Technical Documentation
- [ ] 🟡 **P1** Architecture guide (3-4 days)
  - Dependencies: RTL implementation
  - Block diagrams, pipeline explanation
  
- [ ] 🟡 **P1** Verification guide (2-3 days)
  - Dependencies: Test infrastructure
  - Test plan, coverage goals
  
- [ ] 🟡 **P1** User guide (2-3 days)
  - Dependencies: Build system
  - Building, simulating, programming
  
- [ ] 🟡 **P2** Implementation details (3-4 days)
  - Dependencies: Full implementation
  - Module documentation, design decisions

### API Documentation
- [ ] 🟡 **P2** Module interfaces (1-2 days)
  - Dependencies: RTL modules
  - Automated interface documentation
  
- [ ] 🟡 **P2** Software API (1-2 days)
  - Dependencies: Software toolchain
  - Programming interface documentation

## Phase 9: Optimization & Extensions (P2)

### Performance Optimization
- [ ] 🟡 **P2** Pipeline optimization (3-4 days)
  - Dependencies: Performance analysis
  - Reduce stalls, improve throughput
  
- [ ] 🟡 **P2** Memory optimization (2-3 days)
  - Dependencies: Memory subsystem
  - Reduce memory access latency
  
- [ ] 🟡 **P2** Branch prediction tuning (2-3 days)
  - Dependencies: Branch predictor
  - Improve prediction accuracy

### Peripheral Extensions
- [ ] 🟡 **P2** UART controller (3-4 days)
  - Dependencies: Wishbone interface
  - Serial communication support
  
- [ ] 🟡 **P2** GPIO controller (2-3 days)
  - Dependencies: Wishbone interface
  - General purpose I/O
  
- [ ] 🟡 **P2** Timer/Counter (2-3 days)
  - Dependencies: Wishbone interface
  - Interrupt generation
  
- [ ] 🟡 **P2** SPI controller (3-4 days)
  - Dependencies: Wishbone interface
  - Serial peripheral interface

## Phase 10: Advanced Features (P2)

### Interrupt Support
- [ ] 🟡 **P2** Interrupt controller (3-4 days)
  - Dependencies: CSR implementation
  - Timer, software, external interrupts
  
- [ ] 🟡 **P2** Exception handling (2-3 days)
  - Dependencies: Interrupt controller
  - Illegal instruction, misaligned access

### Cache System (Future)
- [ ] 🟡 **P2** Instruction cache design (5-6 days)
  - Dependencies: Memory interface redesign
  - Simple direct-mapped cache
  
- [ ] 🟡 **P2** Data cache design (5-6 days)
  - Dependencies: Instruction cache
  - Write-through cache policy

## Current Sprint Planning

**Sprint 1 (Weeks 1-2): Core Infrastructure**
- ALU module
- Register file module  
- Basic memory models
- Unit test framework

**Sprint 2 (Weeks 3-4): Pipeline Foundation**
- Pipeline registers
- Hazard detection
- Basic instruction fetch/decode

**Sprint 3 (Weeks 5-6): Instruction Implementation**
- Arithmetic instructions
- Load/store instructions
- Basic control flow

**Sprint 4 (Weeks 7-8): Integration & Testing**
- Pipeline integration
- Comprehensive testing
- Bug fixes

## Progress Notes

**Completed (Jun 21, 2024):**
- ✅ ALU Module: Full RISC-V ALU with ADD, SUB, AND, OR, XOR, SLT, SLTU, SLL, SRL, SRA, LUI, COPY operations
- ✅ Register File: 32x32-bit registers with dual read ports, single write port, x0 hardwired to zero
- ✅ Comprehensive Cocotb Tests: 8 ALU tests + 7 register file tests, all passing
- ✅ Clean Testing Framework: Resolved Python version conflicts, working Makefile integration
- ✅ Proper SystemVerilog: Following coding standards with consistent signal naming

**Next Priority**: Memory system implementation (instruction/data memory models)

## Notes

- **Parallel Development**: Many RTL modules can be developed simultaneously
- **Test-Driven Development**: Write tests before implementing features where possible
- **Documentation**: Document interfaces and design decisions as you go
- **Tool Setup**: Ensure all developers have consistent toolchain setup

## Estimated Timeline

- **Phase 1-3 (Core + Verification)**: 8-10 weeks
- **Phase 4-5 (Advanced + Software)**: 6-8 weeks  
- **Phase 6-8 (Hardware + Docs)**: 4-6 weeks
- **Phase 9-10 (Optimization)**: 4-6 weeks

**Total Estimated Duration**: 22-30 weeks (5-7 months)

This timeline assumes 1-2 people working part-time. Adjust based on available resources and priorities. 