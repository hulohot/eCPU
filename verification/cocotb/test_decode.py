"""
test_decode.py - Cocotb testbench for decode module

Tests the decode module functionality:
- Instruction field extraction
- Control signal generation
- Immediate value generation
- Register file interface
- RISC-V RV32I instruction decoding

Author: Ethan
Date: 2024
"""

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, FallingEdge, Timer
from cocotb.binary import BinaryValue
import random


class DecodeTB:
    """Testbench for decode module"""
    
    def __init__(self, dut):
        self.dut = dut
        self.XLEN = 32
        self.ILEN = 32
        self.ADDR_WIDTH = 32
        
        # ALU operation definitions (matching decode.sv)
        self.ALU_ADD  = 0b0000
        self.ALU_SUB  = 0b0001
        self.ALU_AND  = 0b0010
        self.ALU_OR   = 0b0011
        self.ALU_XOR  = 0b0100
        self.ALU_SLT  = 0b0101
        self.ALU_SLTU = 0b0110
        self.ALU_SLL  = 0b0111
        self.ALU_SRL  = 0b1000
        self.ALU_SRA  = 0b1001
        self.ALU_LUI  = 0b1010
        self.ALU_COPY = 0b1011
        
    async def reset(self):
        """Reset the DUT"""
        self.dut.rst_i.value = 1
        self.dut.pc_i.value = 0
        self.dut.instr_i.value = 0
        self.dut.instr_valid_i.value = 0
        self.dut.stall_i.value = 0
        self.dut.rs1_data_i.value = 0
        self.dut.rs2_data_i.value = 0
        self.dut.rd_addr_wb_i.value = 0
        self.dut.rd_data_wb_i.value = 0
        self.dut.reg_write_wb_i.value = 0
        
        await RisingEdge(self.dut.clk_i)
        await RisingEdge(self.dut.clk_i)
        self.dut.rst_i.value = 0
        await RisingEdge(self.dut.clk_i)
        
    async def feed_instruction(self, pc, instruction, rs1_data=0x12345678, rs2_data=0x87654321):
        """Feed an instruction to the decode stage"""
        self.dut.pc_i.value = pc
        self.dut.instr_i.value = instruction
        self.dut.instr_valid_i.value = 1
        self.dut.rs1_data_i.value = rs1_data
        self.dut.rs2_data_i.value = rs2_data
        self.dut.stall_i.value = 0
        
        # Wait for pipeline register to capture the inputs
        await RisingEdge(self.dut.clk_i)
        
    def get_register_addresses(self, instruction):
        """Extract register addresses from instruction"""
        rs1 = (instruction >> 15) & 0x1F
        rs2 = (instruction >> 20) & 0x1F
        rd = (instruction >> 7) & 0x1F
        return rs1, rs2, rd


@cocotb.test()
async def test_decode_reset(dut):
    """Test decode module reset behavior"""
    
    tb = DecodeTB(dut)
    
    # Start clock
    cocotb.start_soon(Clock(dut.clk_i, 10, units="ns").start())
    
    dut._log.info("Testing decode module reset")
    
    # Reset
    await tb.reset()
    
    # Check initial state after reset
    assert dut.pc_o.value == 0, "PC output should be 0 after reset"
    assert dut.instr_o.value == 0, "Instruction output should be 0 after reset"
    assert dut.instr_valid_o.value == 0, "Instruction valid should be 0 after reset"
    assert dut.reg_write_o.value == 0, "Register write should be 0 after reset"
    assert dut.mem_read_o.value == 0, "Memory read should be 0 after reset"
    assert dut.mem_write_o.value == 0, "Memory write should be 0 after reset"


@cocotb.test()
async def test_decode_add_instruction(dut):
    """Test decoding of ADD instruction"""
    
    tb = DecodeTB(dut)
    
    # Start clock
    cocotb.start_soon(Clock(dut.clk_i, 10, units="ns").start())
    
    dut._log.info("Testing ADD instruction decode")
    
    # Reset
    await tb.reset()
    
    # ADD x1, x2, x3 = 0x003100b3
    # opcode=0110011, rd=1, funct3=000, rs1=2, rs2=3, funct7=0000000
    add_instr = 0x003100B3
    pc = 0x00001000
    
    await tb.feed_instruction(pc, add_instr)
    
    # Wait one more cycle for outputs to appear (pipeline register)
    await RisingEdge(dut.clk_i)
    
    # Check outputs
    assert dut.pc_o.value == pc, f"PC output mismatch: expected 0x{pc:08x}, got 0x{int(dut.pc_o.value):08x}"
    assert dut.instr_o.value == add_instr, f"Instruction output mismatch"
    assert dut.instr_valid_o.value == 1, "Instruction should be valid"
    assert dut.rs1_addr_o.value == 2, "rs1 address should be 2"
    assert dut.rs2_addr_o.value == 3, "rs2 address should be 3"
    assert dut.rd_addr_o.value == 1, "rd address should be 1"
    assert dut.alu_op_o.value == tb.ALU_ADD, f"ALU operation should be ADD, got {int(dut.alu_op_o.value)}"
    assert dut.reg_write_o.value == 1, "Register write should be enabled"
    assert dut.mem_read_o.value == 0, "Memory read should be disabled"
    assert dut.mem_write_o.value == 0, "Memory write should be disabled"
    assert dut.branch_o.value == 0, "Branch should be disabled"
    assert dut.jump_o.value == 0, "Jump should be disabled"


@cocotb.test()
async def test_decode_addi_instruction(dut):
    """Test decoding of ADDI instruction"""
    
    tb = DecodeTB(dut)
    
    # Start clock
    cocotb.start_soon(Clock(dut.clk_i, 10, units="ns").start())
    
    dut._log.info("Testing ADDI instruction decode")
    
    # Reset
    await tb.reset()
    
    # ADDI x1, x2, 100 = 0x06410093
    # opcode=0010011, rd=1, funct3=000, rs1=2, imm=100
    addi_instr = 0x06410093
    pc = 0x00001004
    
    await tb.feed_instruction(pc, addi_instr)
    
    # Wait one more cycle for outputs to appear (pipeline register)
    await RisingEdge(dut.clk_i)
    
    # Check outputs
    assert dut.alu_op_o.value == tb.ALU_ADD, "ALU operation should be ADD for ADDI"
    assert dut.reg_write_o.value == 1, "Register write should be enabled"
    assert dut.imm_o.value == 100, f"Immediate should be 100, got {int(dut.imm_o.value)}"
    assert dut.rs1_addr_o.value == 2, "rs1 address should be 2"
    assert dut.rd_addr_o.value == 1, "rd address should be 1"


@cocotb.test()
async def test_decode_load_instruction(dut):
    """Test decoding of load instructions"""
    
    tb = DecodeTB(dut)
    
    # Start clock
    cocotb.start_soon(Clock(dut.clk_i, 10, units="ns").start())
    
    dut._log.info("Testing load instruction decode")
    
    # Reset
    await tb.reset()
    
    # LW x1, 8(x2) = 0x00812083
    # opcode=0000011, rd=1, funct3=010, rs1=2, imm=8
    lw_instr = 0x00812083
    pc = 0x00001008
    
    await tb.feed_instruction(pc, lw_instr)
    
    # Wait one more cycle for outputs to appear (pipeline register)
    await RisingEdge(dut.clk_i)
    
    # Check outputs
    assert dut.alu_op_o.value == tb.ALU_ADD, "ALU operation should be ADD for address calculation"
    assert dut.reg_write_o.value == 1, "Register write should be enabled"
    assert dut.mem_read_o.value == 1, "Memory read should be enabled"
    assert dut.mem_write_o.value == 0, "Memory write should be disabled"
    assert dut.imm_o.value == 8, f"Immediate should be 8, got {int(dut.imm_o.value)}"
    assert dut.mem_size_o.value == 0b010, "Memory size should be word (010)"


@cocotb.test()
async def test_decode_store_instruction(dut):
    """Test decoding of store instructions"""
    
    tb = DecodeTB(dut)
    
    # Start clock
    cocotb.start_soon(Clock(dut.clk_i, 10, units="ns").start())
    
    dut._log.info("Testing store instruction decode")
    
    # Reset
    await tb.reset()
    
    # SW x3, 12(x2) = 0x00312623
    # opcode=0100011, imm[11:5]=0000000, rs2=3, rs1=2, funct3=010, imm[4:0]=01100
    sw_instr = 0x00312623
    pc = 0x0000100C
    
    await tb.feed_instruction(pc, sw_instr)
    
    # Wait one more cycle for outputs to appear (pipeline register)
    await RisingEdge(dut.clk_i)
    
    # Check outputs
    assert dut.alu_op_o.value == tb.ALU_ADD, "ALU operation should be ADD for address calculation"
    assert dut.reg_write_o.value == 0, "Register write should be disabled"
    assert dut.mem_read_o.value == 0, "Memory read should be disabled"
    assert dut.mem_write_o.value == 1, "Memory write should be enabled"
    assert dut.imm_o.value == 12, f"Immediate should be 12, got {int(dut.imm_o.value)}"
    assert dut.rs1_addr_o.value == 2, "rs1 address should be 2"
    assert dut.rs2_addr_o.value == 3, "rs2 address should be 3"


@cocotb.test()
async def test_decode_branch_instruction(dut):
    """Test decoding of branch instructions"""
    
    tb = DecodeTB(dut)
    
    # Start clock
    cocotb.start_soon(Clock(dut.clk_i, 10, units="ns").start())
    
    dut._log.info("Testing branch instruction decode")
    
    # Reset
    await tb.reset()
    
    # BEQ x1, x2, 8 = 0x00208463  
    # opcode=1100011, imm[12|10:5]=000000, rs2=2, rs1=1, funct3=000, imm[4:1|11]=0100, imm[0]=0
    beq_instr = 0x00208463
    pc = 0x00001010
    
    await tb.feed_instruction(pc, beq_instr)
    
    # Wait one more cycle for outputs to appear (pipeline register)
    await RisingEdge(dut.clk_i)
    
    # Check outputs
    assert dut.alu_op_o.value == tb.ALU_SUB, "ALU operation should be SUB for BEQ comparison"
    assert dut.reg_write_o.value == 0, "Register write should be disabled"
    assert dut.branch_o.value == 1, "Branch should be enabled"
    assert dut.jump_o.value == 0, "Jump should be disabled"
    assert dut.branch_type_o.value == 0b000, "Branch type should be BEQ (000)"
    assert dut.imm_o.value == 8, f"Branch offset should be 8, got {int(dut.imm_o.value)}"


@cocotb.test()
async def test_decode_jump_instruction(dut):
    """Test decoding of jump instructions"""
    
    tb = DecodeTB(dut)
    
    # Start clock
    cocotb.start_soon(Clock(dut.clk_i, 10, units="ns").start())
    
    dut._log.info("Testing jump instruction decode")
    
    # Reset
    await tb.reset()
    
    # JAL x1, 100 = 0x064000ef
    # opcode=1101111, rd=1, imm[20|10:1|11|19:12]=00000000000001100100
    jal_instr = 0x064000EF
    pc = 0x00001014
    
    await tb.feed_instruction(pc, jal_instr)
    
    # Wait one more cycle for outputs to appear (pipeline register)
    await RisingEdge(dut.clk_i)
    
    # Check outputs
    assert dut.alu_op_o.value == tb.ALU_ADD, "ALU operation should be ADD for return address"
    assert dut.reg_write_o.value == 1, "Register write should be enabled"
    assert dut.jump_o.value == 1, "Jump should be enabled"
    assert dut.branch_o.value == 0, "Branch should be disabled"
    assert dut.rd_addr_o.value == 1, "rd address should be 1"
    assert dut.imm_o.value == 100, f"Jump offset should be 100, got {int(dut.imm_o.value)}"


@cocotb.test()
async def test_decode_lui_instruction(dut):
    """Test decoding of LUI instruction"""
    
    tb = DecodeTB(dut)
    
    # Start clock
    cocotb.start_soon(Clock(dut.clk_i, 10, units="ns").start())
    
    dut._log.info("Testing LUI instruction decode")
    
    # Reset
    await tb.reset()
    
    # LUI x1, 0x12345 = 0x123450b7
    # opcode=0110111, rd=1, imm[31:12]=0x12345
    lui_instr = 0x123450B7
    pc = 0x00001018
    
    await tb.feed_instruction(pc, lui_instr)
    
    # Wait one more cycle for outputs to appear (pipeline register)
    await RisingEdge(dut.clk_i)
    
    # Check outputs
    assert dut.alu_op_o.value == tb.ALU_LUI, "ALU operation should be LUI"
    assert dut.reg_write_o.value == 1, "Register write should be enabled"
    assert dut.rd_addr_o.value == 1, "rd address should be 1"
    expected_imm = 0x12345000  # Upper 20 bits with lower 12 bits as 0
    assert dut.imm_o.value == expected_imm, f"Immediate should be 0x{expected_imm:08x}, got 0x{int(dut.imm_o.value):08x}"


@cocotb.test()
async def test_decode_immediate_sign_extension(dut):
    """Test immediate value sign extension"""
    
    tb = DecodeTB(dut)
    
    # Start clock
    cocotb.start_soon(Clock(dut.clk_i, 10, units="ns").start())
    
    dut._log.info("Testing immediate sign extension")
    
    # Reset
    await tb.reset()
    
    # ADDI x1, x2, -1 = 0xfff10093 (immediate = 0xfff = -1)
    addi_neg_instr = 0xFFF10093
    pc = 0x0000101C
    
    await tb.feed_instruction(pc, addi_neg_instr)
    
    # Wait one more cycle for outputs to appear (pipeline register)
    await RisingEdge(dut.clk_i)
    
    # Check that immediate is properly sign-extended to -1 (0xFFFFFFFF)
    expected_imm = 0xFFFFFFFF  # -1 sign-extended to 32 bits
    assert dut.imm_o.value == expected_imm, f"Immediate should be sign-extended to 0x{expected_imm:08x}, got 0x{int(dut.imm_o.value):08x}"


@cocotb.test()
async def test_decode_register_interface(dut):
    """Test register file interface"""
    
    tb = DecodeTB(dut)
    
    # Start clock
    cocotb.start_soon(Clock(dut.clk_i, 10, units="ns").start())
    
    dut._log.info("Testing register file interface")
    
    # Reset
    await tb.reset()
    
    # ADD x5, x10, x15 = 0x00f50ab3
    add_instr = 0x00F50AB3
    rs1_data = 0xAAAABBBB
    rs2_data = 0xCCCCDDDD
    
    await tb.feed_instruction(0x1000, add_instr, rs1_data, rs2_data)
    
    # Wait one more cycle for outputs to appear (pipeline register)
    await RisingEdge(dut.clk_i)
    
    # Check register addresses are correctly output
    assert dut.rs1_addr_o.value == 10, "rs1 address should be 10"
    assert dut.rs2_addr_o.value == 15, "rs2 address should be 15"
    
    # Check register data is correctly passed through
    assert dut.rs1_data_o.value == rs1_data, f"rs1 data should be 0x{rs1_data:08x}"
    assert dut.rs2_data_o.value == rs2_data, f"rs2 data should be 0x{rs2_data:08x}"


@cocotb.test()
async def test_decode_stall_behavior(dut):
    """Test decode behavior during pipeline stall"""
    
    tb = DecodeTB(dut)
    
    # Start clock
    cocotb.start_soon(Clock(dut.clk_i, 10, units="ns").start())
    
    dut._log.info("Testing stall behavior")
    
    # Reset
    await tb.reset()
    
    # Feed instruction normally
    add_instr = 0x003100B3
    await tb.feed_instruction(0x1000, add_instr)
    
    # Wait for outputs to appear
    await RisingEdge(dut.clk_i)
    
    # Save current outputs
    current_pc = int(dut.pc_o.value)
    current_instr = int(dut.instr_o.value)
    
    # Assert stall
    dut.stall_i.value = 1
    
    # Outputs should remain stable during stall
    for _ in range(5):
        await RisingEdge(dut.clk_i)
        assert dut.pc_o.value == current_pc, "PC should remain stable during stall"
        assert dut.instr_o.value == current_instr, "Instruction should remain stable during stall"
        assert dut.stall_o.value == 1, "Stall output should reflect stall input"
    
    # Release stall
    dut.stall_i.value = 0
    await RisingEdge(dut.clk_i)
    assert dut.stall_o.value == 0, "Stall output should be released" 