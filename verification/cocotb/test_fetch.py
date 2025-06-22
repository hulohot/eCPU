"""
test_fetch.py - Cocotb testbench for fetch module

Tests the fetch module functionality:
- PC generation and updating
- Instruction memory interface via Wishbone
- Branch/jump target handling
- Pipeline stall support
- Branch prediction interface
- Reset behavior

Author: Ethan
Date: 2024
"""

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, FallingEdge, Timer
from cocotb.binary import BinaryValue
import random


class FetchTB:
    """Testbench for fetch module"""
    
    def __init__(self, dut):
        self.dut = dut
        self.XLEN = 32
        self.ADDR_WIDTH = 32
        
    async def reset(self):
        """Reset the DUT"""
        self.dut.rst_i.value = 1
        self.dut.stall_i.value = 0
        self.dut.branch_taken_i.value = 0
        self.dut.branch_target_i.value = 0
        self.dut.bp_prediction_i.value = 0
        self.dut.bp_target_i.value = 0
        self.dut.imem_ack_i.value = 0
        self.dut.imem_dat_i.value = 0
        self.dut.imem_err_i.value = 0
        
        await RisingEdge(self.dut.clk_i)
        await RisingEdge(self.dut.clk_i)
        self.dut.rst_i.value = 0
        await RisingEdge(self.dut.clk_i)
        
    async def simulate_imem_response(self, instruction=0x00000013, delay=0, error=False):
        """Simulate instruction memory response"""
        # Wait for memory request
        while self.dut.imem_cyc_o.value == 0 or self.dut.imem_stb_o.value == 0:
            await RisingEdge(self.dut.clk_i)
            
        # Add delay if specified
        for _ in range(delay):
            await RisingEdge(self.dut.clk_i)
            
        # Provide response
        self.dut.imem_ack_i.value = 1 if not error else 0
        self.dut.imem_err_i.value = 1 if error else 0
        self.dut.imem_dat_i.value = instruction if not error else 0
        
        await RisingEdge(self.dut.clk_i)
        
        # Clear response
        self.dut.imem_ack_i.value = 0
        self.dut.imem_err_i.value = 0


@cocotb.test()
async def test_fetch_reset(dut):
    """Test fetch module reset behavior"""
    
    tb = FetchTB(dut)
    
    # Start clock
    cocotb.start_soon(Clock(dut.clk_i, 10, units="ns").start())
    
    dut._log.info("Testing fetch module reset")
    
    # Reset
    await tb.reset()
    
    # Check initial state
    assert dut.pc_o.value == 0, f"PC should be 0 after reset, got 0x{int(dut.pc_o.value):08x}"
    assert dut.imem_cyc_o.value == 1, "Memory cycle should be active after reset"
    assert dut.imem_stb_o.value == 1, "Memory strobe should be active after reset"
    assert dut.imem_we_o.value == 0, "Memory write should never be asserted"
    assert dut.imem_adr_o.value == 0, "Memory address should be PC (0)"
    assert int(dut.imem_sel_o.value) == 0xF, "Memory select should be full word"


@cocotb.test()
async def test_fetch_basic_operation(dut):
    """Test basic fetch operation without branches"""
    
    tb = FetchTB(dut)
    
    # Start clock
    cocotb.start_soon(Clock(dut.clk_i, 10, units="ns").start())
    
    dut._log.info("Testing basic fetch operation")
    
    # Reset
    await tb.reset()
    
    # Test sequence of instructions
    instructions = [0x00000013, 0x12345678, 0xDEADBEEF, 0xCAFEBABE]
    expected_pcs = [0x00000000, 0x00000004, 0x00000008, 0x0000000C]
    
    for i, (pc, instr) in enumerate(zip(expected_pcs, instructions)):
        # Check PC
        assert dut.pc_o.value == pc, f"PC mismatch at step {i}: expected 0x{pc:08x}, got 0x{int(dut.pc_o.value):08x}"
        
        # Simulate memory response
        cocotb.start_soon(tb.simulate_imem_response(instr))
        
        # Wait for response
        while dut.instr_valid_o.value == 0:
            await RisingEdge(dut.clk_i)
        
        # Check instruction output
        assert dut.instr_o.value == instr, f"Instruction mismatch: expected 0x{instr:08x}, got 0x{int(dut.instr_o.value):08x}"
        assert dut.instr_valid_o.value == 1, "Instruction should be valid"
        
        # Move to next cycle to let PC update
        await RisingEdge(dut.clk_i)


@cocotb.test()
async def test_fetch_branch_taken(dut):
    """Test fetch behavior when branch is taken"""
    
    tb = FetchTB(dut)
    
    # Start clock
    cocotb.start_soon(Clock(dut.clk_i, 10, units="ns").start())
    
    dut._log.info("Testing branch taken behavior")
    
    # Reset
    await tb.reset()
    
    # Set up branch signals
    branch_target = 0x00001000
    dut.branch_taken_i.value = 1
    dut.branch_target_i.value = branch_target
    
    # Wait for one clock edge to let branch take effect
    await RisingEdge(dut.clk_i)
    
    # Allow time for PC output to settle
    await Timer(1, units="ns")
    
    # Check that PC is updated to branch target
    assert dut.pc_o.value == branch_target, f"PC should jump to branch target 0x{branch_target:08x}, got 0x{int(dut.pc_o.value):08x}"
    
    # Clear branch signals  
    dut.branch_taken_i.value = 0


@cocotb.test()
async def test_fetch_branch_prediction(dut):
    """Test fetch behavior with branch prediction"""
    
    tb = FetchTB(dut)
    
    # Start clock
    cocotb.start_soon(Clock(dut.clk_i, 10, units="ns").start())
    
    dut._log.info("Testing branch prediction")
    
    # Reset
    await tb.reset()
    
    # Set up branch prediction signals
    predicted_target = 0x00002000
    dut.bp_prediction_i.value = 1
    dut.bp_target_i.value = predicted_target
    
    # Wait for one clock edge to let prediction take effect
    await RisingEdge(dut.clk_i)
    
    # Allow time for PC output to settle
    await Timer(1, units="ns")
    
    # Check that PC is updated to predicted target
    assert dut.pc_o.value == predicted_target, f"PC should jump to predicted target 0x{predicted_target:08x}, got 0x{int(dut.pc_o.value):08x}"
    
    # Clear prediction signals
    dut.bp_prediction_i.value = 0


@cocotb.test()
async def test_fetch_branch_priority(dut):
    """Test that branch_taken has priority over branch prediction"""
    
    tb = FetchTB(dut)
    
    # Start clock
    cocotb.start_soon(Clock(dut.clk_i, 10, units="ns").start())
    
    dut._log.info("Testing branch taken priority over prediction")
    
    # Reset
    await tb.reset()
    
    # Set both branch taken and prediction signals
    branch_target = 0x00001000
    predicted_target = 0x00002000
    
    dut.branch_taken_i.value = 1
    dut.branch_target_i.value = branch_target
    dut.bp_prediction_i.value = 1
    dut.bp_target_i.value = predicted_target
    
    # Wait for one clock edge to let signals take effect
    await RisingEdge(dut.clk_i)
    
    # Allow time for PC output to settle
    await Timer(1, units="ns")
    
    # Branch taken should have priority
    assert dut.pc_o.value == branch_target, f"branch_taken should have priority: expected 0x{branch_target:08x}, got 0x{int(dut.pc_o.value):08x}"
    
    # Clear signals
    dut.branch_taken_i.value = 0
    dut.bp_prediction_i.value = 0


@cocotb.test()
async def test_fetch_stall(dut):
    """Test fetch behavior during pipeline stall"""
    
    tb = FetchTB(dut)
    
    # Start clock
    cocotb.start_soon(Clock(dut.clk_i, 10, units="ns").start())
    
    dut._log.info("Testing pipeline stall")
    
    # Reset
    await tb.reset()
    
    # Complete first instruction fetch to get to a known state
    cocotb.start_soon(tb.simulate_imem_response(0x00000013))
    while dut.instr_valid_o.value == 0:
        await RisingEdge(dut.clk_i)
    
    # PC should be 4 after the first instruction
    await RisingEdge(dut.clk_i) 
    current_pc = int(dut.pc_o.value)
    
    # Assert stall - this should prevent memory access and PC updates
    dut.stall_i.value = 1
    
    # PC should not update during stall, memory should be inactive
    for _ in range(5):
        await RisingEdge(dut.clk_i)
        assert dut.pc_o.value == current_pc, f"PC should not change during stall: expected 0x{current_pc:08x}, got 0x{int(dut.pc_o.value):08x}"
        assert dut.imem_cyc_o.value == 0, "Memory cycle should be inactive during stall"
        assert dut.imem_stb_o.value == 0, "Memory strobe should be inactive during stall"
    
    # Release stall
    dut.stall_i.value = 0
    
    await RisingEdge(dut.clk_i)
    
    # Memory should become active again
    assert dut.imem_cyc_o.value == 1, "Memory cycle should be active after stall"
    assert dut.imem_stb_o.value == 1, "Memory strobe should be active after stall"
    
    # Simulate memory response to allow PC to advance
    cocotb.start_soon(tb.simulate_imem_response(0x22222222))
    while dut.instr_valid_o.value == 0:
        await RisingEdge(dut.clk_i)
    
    # Now PC should advance
    await RisingEdge(dut.clk_i)
    expected_pc = current_pc + 4
    assert dut.pc_o.value == expected_pc, f"PC should increment after stall: expected 0x{expected_pc:08x}, got 0x{int(dut.pc_o.value):08x}"


@cocotb.test()
async def test_fetch_memory_error(dut):
    """Test fetch behavior when memory error occurs"""
    
    tb = FetchTB(dut)
    
    # Start clock
    cocotb.start_soon(Clock(dut.clk_i, 10, units="ns").start())
    
    dut._log.info("Testing memory error handling")
    
    # Reset
    await tb.reset()
    
    # Simulate memory error
    cocotb.start_soon(tb.simulate_imem_response(0x00000000, delay=0, error=True))
    
    # Wait a few cycles
    for _ in range(5):
        await RisingEdge(dut.clk_i)
    
    # Check that instruction is not valid when error occurs
    assert dut.instr_valid_o.value == 0, "Instruction should not be valid when memory error occurs"


@cocotb.test()
async def test_fetch_wishbone_protocol(dut):
    """Test Wishbone protocol compliance"""
    
    tb = FetchTB(dut) 
    
    # Start clock
    cocotb.start_soon(Clock(dut.clk_i, 10, units="ns").start())
    
    dut._log.info("Testing Wishbone protocol compliance")
    
    # Reset
    await tb.reset()
    
    # Check Wishbone signals
    assert dut.imem_we_o.value == 0, "Write enable should always be 0 for instruction fetch"
    assert int(dut.imem_sel_o.value) == 0xF, "Byte select should be full word (0xF)"
    assert dut.imem_dat_o.value == 0, "Data output should be 0 for reads"
    
    # Check that strobe implies cycle
    await RisingEdge(dut.clk_i)
    if dut.imem_stb_o.value == 1:
        assert dut.imem_cyc_o.value == 1, "strobe should imply cycle"


@cocotb.test()
async def test_fetch_pc_alignment(dut):
    """Test that PC is always word-aligned"""
    
    tb = FetchTB(dut)
    
    # Start clock
    cocotb.start_soon(Clock(dut.clk_i, 10, units="ns").start())
    
    dut._log.info("Testing PC word alignment")
    
    # Reset
    await tb.reset()
    
    # Test multiple PC updates
    for i in range(10):
        # Simulate instruction response
        cocotb.start_soon(tb.simulate_imem_response(0x00000013))
        
        # Wait for response
        while dut.instr_valid_o.value == 0:
            await RisingEdge(dut.clk_i)
        
        # Check PC alignment
        pc_value = int(dut.pc_o.value)
        assert (pc_value & 0x3) == 0, f"PC not word-aligned: 0x{pc_value:08x}"
        
        await RisingEdge(dut.clk_i) 