"""
test_hazard_unit.py - Comprehensive tests for hazard unit module

Tests the hazard unit functionality including:
- Load-use hazard detection
- Data forwarding control for operands A and B
- Pipeline stall generation
- Register dependency tracking

Author: Ethan
Date: 2024
"""

import cocotb
from cocotb.triggers import RisingEdge, Timer
from cocotb.clock import Clock
from cocotb.binary import BinaryValue
import random

class HazardTestbench:
    """Test harness for hazard unit module"""
    
    def __init__(self, dut):
        self.dut = dut
        
    def set_inputs(self, rs1_addr_d=0, rs2_addr_d=0, rd_addr_e=0, mem_read_e=0, 
                   reg_write_e=0, rd_addr_m=0, reg_write_m=0):
        """Set hazard unit inputs"""
        self.dut.rs1_addr_d_i.value = rs1_addr_d
        self.dut.rs2_addr_d_i.value = rs2_addr_d
        self.dut.rd_addr_e_i.value = rd_addr_e
        self.dut.mem_read_e_i.value = mem_read_e
        self.dut.reg_write_e_i.value = reg_write_e
        self.dut.rd_addr_m_i.value = rd_addr_m
        self.dut.reg_write_m_i.value = reg_write_m

@cocotb.test()
async def test_hazard_no_dependencies(dut):
    """Test behavior when no dependencies exist"""
    cocotb.log.info("Testing no dependencies")
    
    tb = HazardTestbench(dut)
    
    # No dependencies - different registers
    tb.set_inputs(rs1_addr_d=1, rs2_addr_d=2, rd_addr_e=3, mem_read_e=0, 
                  reg_write_e=1, rd_addr_m=4, reg_write_m=1)
    
    await Timer(1, units="ns")  # Allow combinational settling
    
    # Should have no forwarding and no stalls
    assert dut.stall_o.value == 0, f"No stall should be generated, got {dut.stall_o.value}"
    assert dut.forward_a_o.value == 0, f"No forwarding for A should occur, got {dut.forward_a_o.value}"
    assert dut.forward_b_o.value == 0, f"No forwarding for B should occur, got {dut.forward_b_o.value}"

@cocotb.test()
async def test_hazard_load_use_detection(dut):
    """Test load-use hazard detection"""
    cocotb.log.info("Testing load-use hazard detection")
    
    tb = HazardTestbench(dut)
    
    # Test load-use hazard with rs1
    # Execute stage: LW x5, 0(x1) (loading into x5)
    # Decode stage: ADD x6, x5, x7 (using x5 immediately)
    tb.set_inputs(rs1_addr_d=5, rs2_addr_d=7, rd_addr_e=5, mem_read_e=1, 
                  reg_write_e=1, rd_addr_m=0, reg_write_m=0)
    
    await Timer(1, units="ns")
    
    assert dut.stall_o.value == 1, f"Load-use hazard should cause stall, got {dut.stall_o.value}"
    
    # Test load-use hazard with rs2
    # Execute stage: LW x10, 0(x1) (loading into x10)
    # Decode stage: ADD x6, x7, x10 (using x10 immediately)
    tb.set_inputs(rs1_addr_d=7, rs2_addr_d=10, rd_addr_e=10, mem_read_e=1, 
                  reg_write_e=1, rd_addr_m=0, reg_write_m=0)
    
    await Timer(1, units="ns")
    
    assert dut.stall_o.value == 1, f"Load-use hazard with rs2 should cause stall, got {dut.stall_o.value}"
    
    # Test load-use hazard with both rs1 and rs2
    # Execute stage: LW x15, 0(x1) (loading into x15)
    # Decode stage: ADD x6, x15, x15 (using x15 for both operands)
    tb.set_inputs(rs1_addr_d=15, rs2_addr_d=15, rd_addr_e=15, mem_read_e=1, 
                  reg_write_e=1, rd_addr_m=0, reg_write_m=0)
    
    await Timer(1, units="ns")
    
    assert dut.stall_o.value == 1, f"Load-use hazard with both operands should cause stall, got {dut.stall_o.value}"

@cocotb.test()
async def test_hazard_no_load_use_stall(dut):
    """Test cases where load-use stall should NOT occur"""
    cocotb.log.info("Testing no load-use stall cases")
    
    tb = HazardTestbench(dut)
    
    # Case 1: Execute stage is not a load instruction
    tb.set_inputs(rs1_addr_d=5, rs2_addr_d=7, rd_addr_e=5, mem_read_e=0, 
                  reg_write_e=1, rd_addr_m=0, reg_write_m=0)
    
    await Timer(1, units="ns")
    
    assert dut.stall_o.value == 0, f"Non-load instruction should not cause stall, got {dut.stall_o.value}"
    
    # Case 2: Execute stage doesn't write to register
    tb.set_inputs(rs1_addr_d=5, rs2_addr_d=7, rd_addr_e=5, mem_read_e=1, 
                  reg_write_e=0, rd_addr_m=0, reg_write_m=0)
    
    await Timer(1, units="ns")
    
    assert dut.stall_o.value == 0, f"Load without register write should not cause stall, got {dut.stall_o.value}"
    
    # Case 3: Execute stage writes to x0 (which is discarded)
    tb.set_inputs(rs1_addr_d=5, rs2_addr_d=7, rd_addr_e=0, mem_read_e=1, 
                  reg_write_e=1, rd_addr_m=0, reg_write_m=0)
    
    await Timer(1, units="ns")
    
    assert dut.stall_o.value == 0, f"Load to x0 should not cause stall, got {dut.stall_o.value}"
    
    # Case 4: Different registers (no dependency)
    tb.set_inputs(rs1_addr_d=5, rs2_addr_d=7, rd_addr_e=10, mem_read_e=1, 
                  reg_write_e=1, rd_addr_m=0, reg_write_m=0)
    
    await Timer(1, units="ns")
    
    assert dut.stall_o.value == 0, f"No register dependency should not cause stall, got {dut.stall_o.value}"

@cocotb.test()
async def test_hazard_forwarding_from_memory(dut):
    """Test data forwarding from memory stage"""
    cocotb.log.info("Testing forwarding from memory stage")
    
    tb = HazardTestbench(dut)
    
    # Test forwarding to rs1 (operand A)
    # Memory stage: ADD x5, x1, x2 (writing to x5)
    # Execute stage: SUB x6, x5, x7 (reading from x5)
    tb.set_inputs(rs1_addr_d=5, rs2_addr_d=7, rd_addr_e=6, mem_read_e=0, 
                  reg_write_e=1, rd_addr_m=5, reg_write_m=1)
    
    await Timer(1, units="ns")
    
    assert dut.forward_a_o.value == 1, f"Should forward from memory to A, got {dut.forward_a_o.value}"
    assert dut.forward_b_o.value == 0, f"Should not forward to B, got {dut.forward_b_o.value}"
    assert dut.stall_o.value == 0, f"Forwarding should resolve dependency without stall, got {dut.stall_o.value}"
    
    # Test forwarding to rs2 (operand B)
    # Memory stage: ADD x10, x1, x2 (writing to x10)
    # Execute stage: SUB x6, x7, x10 (reading from x10)
    tb.set_inputs(rs1_addr_d=7, rs2_addr_d=10, rd_addr_e=6, mem_read_e=0, 
                  reg_write_e=1, rd_addr_m=10, reg_write_m=1)
    
    await Timer(1, units="ns")
    
    assert dut.forward_a_o.value == 0, f"Should not forward to A, got {dut.forward_a_o.value}"
    assert dut.forward_b_o.value == 1, f"Should forward from memory to B, got {dut.forward_b_o.value}"
    assert dut.stall_o.value == 0, f"Forwarding should resolve dependency without stall, got {dut.stall_o.value}"
    
    # Test forwarding to both operands
    # Memory stage: ADD x15, x1, x2 (writing to x15)
    # Execute stage: SUB x6, x15, x15 (reading from x15 for both operands)
    tb.set_inputs(rs1_addr_d=15, rs2_addr_d=15, rd_addr_e=6, mem_read_e=0, 
                  reg_write_e=1, rd_addr_m=15, reg_write_m=1)
    
    await Timer(1, units="ns")
    
    assert dut.forward_a_o.value == 1, f"Should forward from memory to A, got {dut.forward_a_o.value}"
    assert dut.forward_b_o.value == 1, f"Should forward from memory to B, got {dut.forward_b_o.value}"
    assert dut.stall_o.value == 0, f"Forwarding should resolve dependencies without stall, got {dut.stall_o.value}"

@cocotb.test()
async def test_hazard_no_forwarding_cases(dut):
    """Test cases where forwarding should NOT occur"""
    cocotb.log.info("Testing no forwarding cases")
    
    tb = HazardTestbench(dut)
    
    # Case 1: Memory stage doesn't write to register
    tb.set_inputs(rs1_addr_d=5, rs2_addr_d=7, rd_addr_e=6, mem_read_e=0, 
                  reg_write_e=1, rd_addr_m=5, reg_write_m=0)
    
    await Timer(1, units="ns")
    
    assert dut.forward_a_o.value == 0, f"No forwarding when memory stage doesn't write, got {dut.forward_a_o.value}"
    assert dut.forward_b_o.value == 0, f"No forwarding when memory stage doesn't write, got {dut.forward_b_o.value}"
    
    # Case 2: Memory stage writes to x0 (which should be ignored)
    tb.set_inputs(rs1_addr_d=5, rs2_addr_d=7, rd_addr_e=6, mem_read_e=0, 
                  reg_write_e=1, rd_addr_m=0, reg_write_m=1)
    
    await Timer(1, units="ns")
    
    assert dut.forward_a_o.value == 0, f"No forwarding from x0, got {dut.forward_a_o.value}"
    assert dut.forward_b_o.value == 0, f"No forwarding from x0, got {dut.forward_b_o.value}"
    
    # Case 3: Different registers (no dependency)
    tb.set_inputs(rs1_addr_d=5, rs2_addr_d=7, rd_addr_e=6, mem_read_e=0, 
                  reg_write_e=1, rd_addr_m=10, reg_write_m=1)
    
    await Timer(1, units="ns")
    
    assert dut.forward_a_o.value == 0, f"No forwarding for different registers, got {dut.forward_a_o.value}"
    assert dut.forward_b_o.value == 0, f"No forwarding for different registers, got {dut.forward_b_o.value}"

@cocotb.test()
async def test_hazard_x0_special_cases(dut):
    """Test special handling of x0 register"""
    cocotb.log.info("Testing x0 register special cases")
    
    tb = HazardTestbench(dut)
    
    # Case 1: Decode stage reads from x0 (should never forward or stall)
    tb.set_inputs(rs1_addr_d=0, rs2_addr_d=0, rd_addr_e=5, mem_read_e=1, 
                  reg_write_e=1, rd_addr_m=10, reg_write_m=1)
    
    await Timer(1, units="ns")
    
    assert dut.stall_o.value == 0, f"Reading from x0 should not cause stall, got {dut.stall_o.value}"
    assert dut.forward_a_o.value == 0, f"Reading from x0 should not require forwarding, got {dut.forward_a_o.value}"
    assert dut.forward_b_o.value == 0, f"Reading from x0 should not require forwarding, got {dut.forward_b_o.value}"
    
    # Case 2: Memory stage writes to x0 (should not forward)
    tb.set_inputs(rs1_addr_d=5, rs2_addr_d=7, rd_addr_e=6, mem_read_e=0, 
                  reg_write_e=1, rd_addr_m=0, reg_write_m=1)
    
    await Timer(1, units="ns")
    
    assert dut.forward_a_o.value == 0, f"Writing to x0 should not enable forwarding, got {dut.forward_a_o.value}"
    assert dut.forward_b_o.value == 0, f"Writing to x0 should not enable forwarding, got {dut.forward_b_o.value}"

@cocotb.test()
async def test_hazard_complex_scenarios(dut):
    """Test complex hazard scenarios"""
    cocotb.log.info("Testing complex hazard scenarios")
    
    tb = HazardTestbench(dut)
    
    # Scenario 1: Load-use hazard takes precedence over forwarding
    # Memory stage: writing to x8
    # Execute stage: LW x5, 0(x1) (loading)
    # Decode stage: ADD x6, x5, x8 (uses both loaded register and forwarded register)
    tb.set_inputs(rs1_addr_d=5, rs2_addr_d=8, rd_addr_e=5, mem_read_e=1, 
                  reg_write_e=1, rd_addr_m=8, reg_write_m=1)
    
    await Timer(1, units="ns")
    
    # Should stall due to load-use hazard (rs1 dependency)
    assert dut.stall_o.value == 1, f"Load-use hazard should cause stall, got {dut.stall_o.value}"
    # Forwarding for rs2 should still be available
    assert dut.forward_b_o.value == 1, f"Should still forward to B when possible, got {dut.forward_b_o.value}"
    
    # Scenario 2: Multiple pipeline stages with dependencies
    # Memory stage: writing to x10
    # Execute stage: writing to x11 (non-load)
    # Decode stage: ADD x12, x10, x11 (depends on both stages)
    tb.set_inputs(rs1_addr_d=10, rs2_addr_d=11, rd_addr_e=11, mem_read_e=0, 
                  reg_write_e=1, rd_addr_m=10, reg_write_m=1)
    
    await Timer(1, units="ns")
    
    # Should forward from memory stage to rs1
    assert dut.forward_a_o.value == 1, f"Should forward from memory to A, got {dut.forward_a_o.value}"
    # No forwarding for rs2 (would need execute stage forwarding, not implemented)
    assert dut.forward_b_o.value == 0, f"No execute stage forwarding implemented, got {dut.forward_b_o.value}"
    # No stall needed
    assert dut.stall_o.value == 0, f"No load-use hazard, got {dut.stall_o.value}"

@cocotb.test()
async def test_hazard_forwarding_priorities(dut):
    """Test forwarding control values"""
    cocotb.log.info("Testing forwarding control values")
    
    tb = HazardTestbench(dut)
    
    # Test FORWARD_NONE (value 0)
    tb.set_inputs(rs1_addr_d=5, rs2_addr_d=7, rd_addr_e=6, mem_read_e=0, 
                  reg_write_e=1, rd_addr_m=10, reg_write_m=1)
    
    await Timer(1, units="ns")
    
    assert dut.forward_a_o.value == 0, f"FORWARD_NONE should be 0, got {dut.forward_a_o.value}"
    assert dut.forward_b_o.value == 0, f"FORWARD_NONE should be 0, got {dut.forward_b_o.value}"
    
    # Test FORWARD_MEM (value 1)
    tb.set_inputs(rs1_addr_d=5, rs2_addr_d=7, rd_addr_e=6, mem_read_e=0, 
                  reg_write_e=1, rd_addr_m=5, reg_write_m=1)
    
    await Timer(1, units="ns")
    
    assert dut.forward_a_o.value == 1, f"FORWARD_MEM should be 1, got {dut.forward_a_o.value}"
    
    # Test both forwarding controls can be set independently
    tb.set_inputs(rs1_addr_d=5, rs2_addr_d=7, rd_addr_e=6, mem_read_e=0, 
                  reg_write_e=1, rd_addr_m=5, reg_write_m=1)
    
    await Timer(1, units="ns")
    
    assert dut.forward_a_o.value == 1, f"Forward A should be 1, got {dut.forward_a_o.value}"
    assert dut.forward_b_o.value == 0, f"Forward B should be 0, got {dut.forward_b_o.value}"

@cocotb.test()
async def test_hazard_random_scenarios(dut):
    """Test random combinations of register dependencies"""
    cocotb.log.info("Testing random scenarios")
    
    tb = HazardTestbench(dut)
    
    # Run 100 random test cases
    for i in range(100):
        rs1_addr = random.randint(0, 31)
        rs2_addr = random.randint(0, 31)
        rd_addr_e = random.randint(0, 31)
        rd_addr_m = random.randint(0, 31)
        mem_read_e = random.randint(0, 1)
        reg_write_e = random.randint(0, 1)
        reg_write_m = random.randint(0, 1)
        
        tb.set_inputs(rs1_addr_d=rs1_addr, rs2_addr_d=rs2_addr, 
                      rd_addr_e=rd_addr_e, mem_read_e=mem_read_e, 
                      reg_write_e=reg_write_e, rd_addr_m=rd_addr_m, 
                      reg_write_m=reg_write_m)
        
        await Timer(1, units="ns")
        
        # Check stall logic
        expected_stall = (mem_read_e and reg_write_e and rd_addr_e != 0 and 
                         (rs1_addr == rd_addr_e or rs2_addr == rd_addr_e))
        
        assert dut.stall_o.value == expected_stall, \
            f"Test {i}: Stall mismatch - expected {expected_stall}, got {dut.stall_o.value}"
        
        # Check forwarding logic for operand A
        expected_forward_a = (reg_write_m and rd_addr_m != 0 and rd_addr_m == rs1_addr)
        assert dut.forward_a_o.value == (1 if expected_forward_a else 0), \
            f"Test {i}: Forward A mismatch - expected {expected_forward_a}, got {dut.forward_a_o.value}"
        
        # Check forwarding logic for operand B
        expected_forward_b = (reg_write_m and rd_addr_m != 0 and rd_addr_m == rs2_addr)
        assert dut.forward_b_o.value == (1 if expected_forward_b else 0), \
            f"Test {i}: Forward B mismatch - expected {expected_forward_b}, got {dut.forward_b_o.value}"

@cocotb.test()
async def test_hazard_edge_cases(dut):
    """Test edge cases and boundary conditions"""
    cocotb.log.info("Testing edge cases")
    
    tb = HazardTestbench(dut)
    
    # Edge case 1: All registers are x0
    tb.set_inputs(rs1_addr_d=0, rs2_addr_d=0, rd_addr_e=0, mem_read_e=1, 
                  reg_write_e=1, rd_addr_m=0, reg_write_m=1)
    
    await Timer(1, units="ns")
    
    assert dut.stall_o.value == 0, f"All x0 should not cause stall, got {dut.stall_o.value}"
    assert dut.forward_a_o.value == 0, f"All x0 should not cause forwarding, got {dut.forward_a_o.value}"
    assert dut.forward_b_o.value == 0, f"All x0 should not cause forwarding, got {dut.forward_b_o.value}"
    
    # Edge case 2: Maximum register numbers
    tb.set_inputs(rs1_addr_d=31, rs2_addr_d=31, rd_addr_e=31, mem_read_e=1, 
                  reg_write_e=1, rd_addr_m=31, reg_write_m=1)
    
    await Timer(1, units="ns")
    
    assert dut.stall_o.value == 1, f"Load-use with x31 should cause stall, got {dut.stall_o.value}"
    assert dut.forward_a_o.value == 1, f"Forward from x31 should work, got {dut.forward_a_o.value}"
    assert dut.forward_b_o.value == 1, f"Forward from x31 should work, got {dut.forward_b_o.value}"
    
    # Edge case 3: Same source and destination registers
    tb.set_inputs(rs1_addr_d=15, rs2_addr_d=15, rd_addr_e=15, mem_read_e=0, 
                  reg_write_e=1, rd_addr_m=15, reg_write_m=1)
    
    await Timer(1, units="ns")
    
    assert dut.stall_o.value == 0, f"Non-load dependency should not cause stall, got {dut.stall_o.value}"
    assert dut.forward_a_o.value == 1, f"Should forward to both operands, got {dut.forward_a_o.value}"
    assert dut.forward_b_o.value == 1, f"Should forward to both operands, got {dut.forward_b_o.value}" 