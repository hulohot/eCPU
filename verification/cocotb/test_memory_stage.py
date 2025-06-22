"""
test_memory_stage.py - Comprehensive tests for memory stage module

Tests the memory stage functionality including:
- Load/store operations with different sizes
- Wishbone protocol compliance
- Memory alignment and byte selection
- Pipeline register behavior
- Stall handling

Author: Ethan
Date: 2024
"""

import cocotb
from cocotb.triggers import RisingEdge, Timer
from cocotb.clock import Clock
from cocotb.binary import BinaryValue
import random

class MemoryTestbench:
    """Test harness for memory stage module"""
    
    def __init__(self, dut):
        self.dut = dut
        
    async def reset(self):
        """Reset the memory stage module"""
        self.dut.rst_i.value = 1
        self.dut.dmem_ack_i.value = 0
        self.dut.dmem_dat_i.value = 0
        self.dut.dmem_err_i.value = 0
        await RisingEdge(self.dut.clk_i)
        await RisingEdge(self.dut.clk_i)
        self.dut.rst_i.value = 0
        await RisingEdge(self.dut.clk_i)
        
    async def clock_edge(self):
        """Wait for rising edge of clock"""
        await RisingEdge(self.dut.clk_i)
        
    def set_inputs(self, pc=0, instr=0, instr_valid=1, rd_addr=0, alu_result=0, 
                   rs2_data=0, reg_write=0, mem_read=0, mem_write=0, mem_size=0, stall=0):
        """Set memory stage inputs"""
        self.dut.pc_i.value = pc
        self.dut.instr_i.value = instr
        self.dut.instr_valid_i.value = instr_valid
        self.dut.rd_addr_i.value = rd_addr
        self.dut.alu_result_i.value = alu_result
        self.dut.rs2_data_i.value = rs2_data
        self.dut.reg_write_i.value = reg_write
        self.dut.mem_read_i.value = mem_read
        self.dut.mem_write_i.value = mem_write
        self.dut.mem_size_i.value = mem_size
        self.dut.stall_i.value = stall
        
    def set_memory_response(self, ack=0, data=0, err=0):
        """Set memory response signals"""
        self.dut.dmem_ack_i.value = ack
        self.dut.dmem_dat_i.value = data
        self.dut.dmem_err_i.value = err

@cocotb.test()
async def test_memory_reset(dut):
    """Test memory stage reset behavior"""
    cocotb.log.info("Testing memory stage reset")
    
    tb = MemoryTestbench(dut)
    
    # Start clock
    cocotb.start_soon(Clock(dut.clk_i, 10, units="ns").start())
    
    # Apply reset
    await tb.reset()
    
    # Check reset values
    assert dut.pc_o.value == 0, f"PC output should be 0 after reset, got {dut.pc_o.value}"
    assert dut.instr_o.value == 0, f"Instruction output should be 0 after reset, got {dut.instr_o.value}"
    assert dut.instr_valid_o.value == 0, f"Instruction valid should be 0 after reset, got {dut.instr_valid_o.value}"
    assert dut.rd_addr_o.value == 0, f"Destination register should be 0 after reset, got {dut.rd_addr_o.value}"
    assert dut.alu_result_o.value == 0, f"ALU result should be 0 after reset, got {dut.alu_result_o.value}"
    assert dut.mem_data_o.value == 0, f"Memory data should be 0 after reset, got {dut.mem_data_o.value}"
    assert dut.reg_write_o.value == 0, f"Register write should be 0 after reset, got {dut.reg_write_o.value}"
    assert dut.stall_o.value == 0, f"Stall output should be 0 after reset, got {dut.stall_o.value}"

@cocotb.test()
async def test_memory_load_word(dut):
    """Test word load operation"""
    cocotb.log.info("Testing word load operation")
    
    tb = MemoryTestbench(dut)
    
    # Start clock
    cocotb.start_soon(Clock(dut.clk_i, 10, units="ns").start())
    
    await tb.reset()
    
    # Set up load word operation
    tb.set_inputs(pc=0x1000, alu_result=0x2000, mem_read=1, mem_size=2, 
                  rd_addr=5, reg_write=1)  # LW, mem_size=2 for word
    
    # Check Wishbone signals
    await tb.clock_edge()
    assert dut.dmem_cyc_o.value == 1, f"Cycle should be asserted for load"
    assert dut.dmem_stb_o.value == 1, f"Strobe should be asserted for load"
    assert dut.dmem_we_o.value == 0, f"Write enable should be 0 for load"
    assert dut.dmem_adr_o.value == 0x2000, f"Address should be 0x2000, got {dut.dmem_adr_o.value}"
    assert dut.dmem_sel_o.value == 0xF, f"Byte select should be 0xF for word, got {dut.dmem_sel_o.value}"
    
    # Simulate memory response
    tb.set_memory_response(ack=1, data=0xDEADBEEF)
    await tb.clock_edge()
    
    # Check pipeline register update
    assert dut.pc_o.value == 0x1000, f"PC should be propagated"
    assert dut.rd_addr_o.value == 5, f"Destination register should be propagated"
    assert dut.alu_result_o.value == 0x2000, f"ALU result should be propagated"
    assert dut.mem_data_o.value == 0xDEADBEEF, f"Memory data should be loaded, got {dut.mem_data_o.value}"
    assert dut.reg_write_o.value == 1, f"Register write should be propagated"

@cocotb.test()
async def test_memory_store_word(dut):
    """Test word store operation"""
    cocotb.log.info("Testing word store operation")
    
    tb = MemoryTestbench(dut)
    
    # Start clock
    cocotb.start_soon(Clock(dut.clk_i, 10, units="ns").start())
    
    await tb.reset()
    
    # Set up store word operation
    tb.set_inputs(pc=0x1004, alu_result=0x3000, rs2_data=0x12345678, 
                  mem_write=1, mem_size=2)  # SW, mem_size=2 for word
    
    # Check Wishbone signals
    await tb.clock_edge()
    assert dut.dmem_cyc_o.value == 1, f"Cycle should be asserted for store"
    assert dut.dmem_stb_o.value == 1, f"Strobe should be asserted for store"
    assert dut.dmem_we_o.value == 1, f"Write enable should be 1 for store"
    assert dut.dmem_adr_o.value == 0x3000, f"Address should be 0x3000, got {dut.dmem_adr_o.value}"
    assert dut.dmem_dat_o.value == 0x12345678, f"Data should be store value, got {dut.dmem_dat_o.value}"
    assert dut.dmem_sel_o.value == 0xF, f"Byte select should be 0xF for word, got {dut.dmem_sel_o.value}"
    
    # Simulate memory acknowledgment
    tb.set_memory_response(ack=1)
    await tb.clock_edge()
    
    # Check pipeline register update
    assert dut.pc_o.value == 0x1004, f"PC should be propagated"
    assert dut.alu_result_o.value == 0x3000, f"ALU result should be propagated"

@cocotb.test()
async def test_memory_load_byte(dut):
    """Test byte load operations"""
    cocotb.log.info("Testing byte load operations")
    
    tb = MemoryTestbench(dut)
    
    # Start clock
    cocotb.start_soon(Clock(dut.clk_i, 10, units="ns").start())
    
    await tb.reset()
    
    # Test LB (load byte signed) from offset 0
    tb.set_inputs(alu_result=0x2000, mem_read=1, mem_size=0, rd_addr=5, reg_write=1)  # LB
    await tb.clock_edge()
    
    assert dut.dmem_sel_o.value == 0x1, f"Byte select should be 0x1 for byte 0, got {dut.dmem_sel_o.value}"
    
    # Simulate memory response with byte in LSB position
    tb.set_memory_response(ack=1, data=0x000000FF)  # Negative byte (0xFF)
    await tb.clock_edge()
    
    # Should sign-extend to 0xFFFFFFFF
    assert dut.mem_data_o.value == 0xFFFFFFFF, f"Signed byte should extend to 0xFFFFFFFF, got {dut.mem_data_o.value}"
    
    # Test LBU (load byte unsigned) from offset 1
    tb.set_inputs(alu_result=0x2001, mem_read=1, mem_size=4, rd_addr=6, reg_write=1)  # LBU
    await tb.clock_edge()
    
    assert dut.dmem_sel_o.value == 0x2, f"Byte select should be 0x2 for byte 1, got {dut.dmem_sel_o.value}"
    
    # Simulate memory response with byte in second position
    tb.set_memory_response(ack=1, data=0x0000FF00)  # Byte 0xFF in position 1
    await tb.clock_edge()
    
    # Should zero-extend to 0x000000FF
    assert dut.mem_data_o.value == 0x000000FF, f"Unsigned byte should be 0x000000FF, got {dut.mem_data_o.value}"

@cocotb.test()
async def test_memory_store_byte(dut):
    """Test byte store operations"""
    cocotb.log.info("Testing byte store operations")
    
    tb = MemoryTestbench(dut)
    
    # Start clock
    cocotb.start_soon(Clock(dut.clk_i, 10, units="ns").start())
    
    await tb.reset()
    
    # Test SB (store byte) to offset 0
    tb.set_inputs(alu_result=0x3000, rs2_data=0x12345678, mem_write=1, mem_size=0)  # SB
    await tb.clock_edge()
    
    assert dut.dmem_sel_o.value == 0x1, f"Byte select should be 0x1 for byte 0, got {dut.dmem_sel_o.value}"
    assert dut.dmem_dat_o.value == 0x00000078, f"Store data should be 0x00000078, got {dut.dmem_dat_o.value}"
    
    # Test SB to offset 2
    tb.set_inputs(alu_result=0x3002, rs2_data=0x12345678, mem_write=1, mem_size=0)  # SB
    await tb.clock_edge()
    
    assert dut.dmem_sel_o.value == 0x4, f"Byte select should be 0x4 for byte 2, got {dut.dmem_sel_o.value}"
    assert dut.dmem_dat_o.value == 0x00780000, f"Store data should be 0x00780000, got {dut.dmem_dat_o.value}"

@cocotb.test()
async def test_memory_load_halfword(dut):
    """Test halfword load operations"""
    cocotb.log.info("Testing halfword load operations")
    
    tb = MemoryTestbench(dut)
    
    # Start clock
    cocotb.start_soon(Clock(dut.clk_i, 10, units="ns").start())
    
    await tb.reset()
    
    # Test LH (load halfword signed) from offset 0
    tb.set_inputs(alu_result=0x2000, mem_read=1, mem_size=1, rd_addr=5, reg_write=1)  # LH
    await tb.clock_edge()
    
    assert dut.dmem_sel_o.value == 0x3, f"Byte select should be 0x3 for halfword 0, got {dut.dmem_sel_o.value}"
    
    # Simulate memory response with halfword in LSB position
    tb.set_memory_response(ack=1, data=0x0000FFFF)  # Negative halfword
    await tb.clock_edge()
    
    # Should sign-extend to 0xFFFFFFFF
    assert dut.mem_data_o.value == 0xFFFFFFFF, f"Signed halfword should extend to 0xFFFFFFFF, got {dut.mem_data_o.value}"
    
    # Test LHU (load halfword unsigned) from offset 2
    tb.set_inputs(alu_result=0x2002, mem_read=1, mem_size=5, rd_addr=6, reg_write=1)  # LHU
    await tb.clock_edge()
    
    assert dut.dmem_sel_o.value == 0xC, f"Byte select should be 0xC for halfword 1, got {dut.dmem_sel_o.value}"
    
    # Simulate memory response with halfword in MSB position
    tb.set_memory_response(ack=1, data=0xFFFF0000)  # Halfword 0xFFFF in position 2-3
    await tb.clock_edge()
    
    # Should zero-extend to 0x0000FFFF
    assert dut.mem_data_o.value == 0x0000FFFF, f"Unsigned halfword should be 0x0000FFFF, got {dut.mem_data_o.value}"

@cocotb.test()
async def test_memory_store_halfword(dut):
    """Test halfword store operations"""
    cocotb.log.info("Testing halfword store operations")
    
    tb = MemoryTestbench(dut)
    
    # Start clock
    cocotb.start_soon(Clock(dut.clk_i, 10, units="ns").start())
    
    await tb.reset()
    
    # Test SH (store halfword) to offset 0
    tb.set_inputs(alu_result=0x3000, rs2_data=0x12345678, mem_write=1, mem_size=1)  # SH
    await tb.clock_edge()
    
    assert dut.dmem_sel_o.value == 0x3, f"Byte select should be 0x3 for halfword 0, got {dut.dmem_sel_o.value}"
    assert dut.dmem_dat_o.value == 0x00005678, f"Store data should be 0x00005678, got {dut.dmem_dat_o.value}"
    
    # Test SH to offset 2
    tb.set_inputs(alu_result=0x3002, rs2_data=0x12345678, mem_write=1, mem_size=1)  # SH
    await tb.clock_edge()
    
    assert dut.dmem_sel_o.value == 0xC, f"Byte select should be 0xC for halfword 1, got {dut.dmem_sel_o.value}"
    assert dut.dmem_dat_o.value == 0x56780000, f"Store data should be 0x56780000, got {dut.dmem_dat_o.value}"

@cocotb.test()
async def test_memory_misaligned_access(dut):
    """Test misaligned memory access handling"""
    cocotb.log.info("Testing misaligned access handling")
    
    tb = MemoryTestbench(dut)
    
    # Start clock
    cocotb.start_soon(Clock(dut.clk_i, 10, units="ns").start())
    
    await tb.reset()
    
    # Test misaligned halfword access (odd address)
    tb.set_inputs(alu_result=0x2001, mem_read=1, mem_size=1)  # LH from odd address
    await tb.clock_edge()
    
    # Should not generate memory access for misaligned access
    assert dut.dmem_cyc_o.value == 0, f"Cycle should not be asserted for misaligned access"
    assert dut.dmem_stb_o.value == 0, f"Strobe should not be asserted for misaligned access"
    
    # Test misaligned word access (non-aligned address)
    tb.set_inputs(alu_result=0x2002, mem_read=1, mem_size=2)  # LW from non-word-aligned address
    await tb.clock_edge()
    
    # Should not generate memory access for misaligned access
    assert dut.dmem_cyc_o.value == 0, f"Cycle should not be asserted for misaligned word access"
    assert dut.dmem_stb_o.value == 0, f"Strobe should not be asserted for misaligned word access"

@cocotb.test()
async def test_memory_wishbone_protocol(dut):
    """Test Wishbone protocol compliance"""
    cocotb.log.info("Testing Wishbone protocol compliance")
    
    tb = MemoryTestbench(dut)
    
    # Start clock
    cocotb.start_soon(Clock(dut.clk_i, 10, units="ns").start())
    
    await tb.reset()
    
    # Test that STB implies CYC
    tb.set_inputs(alu_result=0x2000, mem_read=1, mem_size=2)
    await tb.clock_edge()
    
    if dut.dmem_stb_o.value == 1:
        assert dut.dmem_cyc_o.value == 1, f"CYC must be asserted when STB is asserted"
    
    # Test address alignment (Wishbone addresses should be word-aligned)
    assert (dut.dmem_adr_o.value & 0x3) == 0, f"Wishbone address should be word-aligned, got {dut.dmem_adr_o.value}"
    
    # Test that WE is only asserted for stores
    tb.set_inputs(alu_result=0x2000, mem_read=1, mem_size=2)
    await tb.clock_edge()
    assert dut.dmem_we_o.value == 0, f"WE should be 0 for load operations"
    
    tb.set_inputs(alu_result=0x2000, mem_write=1, mem_size=2)
    await tb.clock_edge()
    assert dut.dmem_we_o.value == 1, f"WE should be 1 for store operations"

@cocotb.test()
async def test_memory_stall_behavior(dut):
    """Test pipeline stall behavior"""
    cocotb.log.info("Testing stall behavior")
    
    tb = MemoryTestbench(dut)
    
    # Start clock
    cocotb.start_soon(Clock(dut.clk_i, 10, units="ns").start())
    
    await tb.reset()
    
    # Set up initial values
    tb.set_inputs(pc=0x1000, instr=0x12345678, alu_result=0x2000, 
                  rd_addr=5, reg_write=1)
    await tb.clock_edge()
    
    # Store expected values
    expected_pc = int(dut.pc_o.value)
    expected_instr = int(dut.instr_o.value)
    expected_alu_result = int(dut.alu_result_o.value)
    
    # Apply stall
    tb.set_inputs(pc=0x2000, instr=0x87654321, alu_result=0x3000, 
                  rd_addr=10, stall=1)  # New inputs with stall
    await tb.clock_edge()
    
    # During stall, pipeline register should hold previous values
    assert dut.pc_o.value == expected_pc, f"PC should be held during stall"
    assert dut.instr_o.value == expected_instr, f"Instruction should be held during stall"
    assert dut.alu_result_o.value == expected_alu_result, f"ALU result should be held during stall"
    assert dut.stall_o.value == 1, f"Stall output should reflect stall input"
    
    # Release stall
    tb.set_inputs(stall=0)
    await tb.clock_edge()
    
    # Should now accept new values
    assert dut.pc_o.value == 0x2000, f"PC should update after stall release"
    assert dut.stall_o.value == 0, f"Stall output should be cleared"

@cocotb.test()
async def test_memory_no_operation(dut):
    """Test behavior when no memory operation is requested"""
    cocotb.log.info("Testing no memory operation")
    
    tb = MemoryTestbench(dut)
    
    # Start clock
    cocotb.start_soon(Clock(dut.clk_i, 10, units="ns").start())
    
    await tb.reset()
    
    # Set up non-memory operation (e.g., ALU operation)
    tb.set_inputs(pc=0x1000, alu_result=0x2000, rd_addr=5, reg_write=1,
                  mem_read=0, mem_write=0)  # No memory operation
    await tb.clock_edge()
    
    # Should not generate any memory accesses
    assert dut.dmem_cyc_o.value == 0, f"Cycle should not be asserted for non-memory operation"
    assert dut.dmem_stb_o.value == 0, f"Strobe should not be asserted for non-memory operation"
    assert dut.dmem_we_o.value == 0, f"Write enable should not be asserted for non-memory operation"
    
    # Pipeline registers should still update
    assert dut.pc_o.value == 0x1000, f"PC should be propagated"
    assert dut.alu_result_o.value == 0x2000, f"ALU result should be propagated"
    assert dut.rd_addr_o.value == 5, f"Destination register should be propagated"
    assert dut.reg_write_o.value == 1, f"Register write should be propagated" 