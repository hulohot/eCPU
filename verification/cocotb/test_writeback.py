"""
test_writeback.py - Comprehensive tests for writeback stage module

Tests the writeback stage functionality including:
- Data selection between ALU result and memory data
- Load instruction detection
- Register write control
- Signal propagation

Author: Ethan
Date: 2024
"""

import cocotb
from cocotb.triggers import RisingEdge, Timer
from cocotb.clock import Clock
from cocotb.binary import BinaryValue
import random

class WritebackTestbench:
    """Test harness for writeback module"""
    
    def __init__(self, dut):
        self.dut = dut
        
    async def reset(self):
        """Reset the writeback module"""
        self.dut.rst_i.value = 1
        await RisingEdge(self.dut.clk_i)
        await RisingEdge(self.dut.clk_i)
        self.dut.rst_i.value = 0
        await RisingEdge(self.dut.clk_i)
        
    async def clock_edge(self):
        """Wait for rising edge of clock"""
        await RisingEdge(self.dut.clk_i)
        
    def set_inputs(self, rd_addr=0, alu_result=0, mem_data=0, reg_write=0, instr=0):
        """Set writeback module inputs"""
        self.dut.rd_addr_i.value = rd_addr
        self.dut.alu_result_i.value = alu_result
        self.dut.mem_data_i.value = mem_data
        self.dut.reg_write_i.value = reg_write
        self.dut.instr_i.value = instr

@cocotb.test()
async def test_writeback_alu_result_selection(dut):
    """Test ALU result selection for non-load instructions"""
    cocotb.log.info("Testing ALU result selection")
    
    tb = WritebackTestbench(dut)
    
    # Start clock
    cocotb.start_soon(Clock(dut.clk_i, 10, units="ns").start())
    
    await tb.reset()
    
    # Test ADD instruction (opcode != 0x03 - not a load)
    add_instr = 0x00A58533  # Example ADD instruction
    tb.set_inputs(rd_addr=10, alu_result=0x12345678, mem_data=0xDEADBEEF, 
                  reg_write=1, instr=add_instr)
    await tb.clock_edge()
    
    # Should select ALU result for non-load instructions
    assert dut.rd_data_o.value == 0x12345678, f"Should select ALU result for ADD, got {dut.rd_data_o.value}"
    assert dut.rd_addr_o.value == 10, f"Destination register should be propagated, got {dut.rd_addr_o.value}"
    assert dut.reg_write_o.value == 1, f"Register write should be propagated, got {dut.reg_write_o.value}"
    
    # Test ADDI instruction
    addi_instr = 0x00A50513  # Example ADDI instruction (opcode 0x13)
    tb.set_inputs(rd_addr=5, alu_result=0x87654321, mem_data=0xCAFEBABE, 
                  reg_write=1, instr=addi_instr)
    await tb.clock_edge()
    
    # Should select ALU result for immediate instructions
    assert dut.rd_data_o.value == 0x87654321, f"Should select ALU result for ADDI, got {dut.rd_data_o.value}"
    assert dut.rd_addr_o.value == 5, f"Destination register should be 5, got {dut.rd_addr_o.value}"

@cocotb.test()
async def test_writeback_memory_data_selection(dut):
    """Test memory data selection for load instructions"""
    cocotb.log.info("Testing memory data selection")
    
    tb = WritebackTestbench(dut)
    
    # Start clock
    cocotb.start_soon(Clock(dut.clk_i, 10, units="ns").start())
    
    await tb.reset()
    
    # Test LW instruction (opcode 0x03)
    lw_instr = 0x00A52503  # Example LW instruction (opcode 0000011)
    tb.set_inputs(rd_addr=10, alu_result=0x12345678, mem_data=0xDEADBEEF, 
                  reg_write=1, instr=lw_instr)
    await tb.clock_edge()
    
    # Should select memory data for load instructions
    assert dut.rd_data_o.value == 0xDEADBEEF, f"Should select memory data for LW, got {dut.rd_data_o.value}"
    assert dut.rd_addr_o.value == 10, f"Destination register should be propagated, got {dut.rd_addr_o.value}"
    assert dut.reg_write_o.value == 1, f"Register write should be propagated, got {dut.reg_write_o.value}"
    
    # Test LB instruction (also opcode 0x03, different funct3)
    lb_instr = 0x00A50003  # Example LB instruction (opcode 0000011)
    tb.set_inputs(rd_addr=1, alu_result=0x11111111, mem_data=0xFFFFFFFF, 
                  reg_write=1, instr=lb_instr)
    await tb.clock_edge()
    
    # Should select memory data for all load instructions
    assert dut.rd_data_o.value == 0xFFFFFFFF, f"Should select memory data for LB, got {dut.rd_data_o.value}"
    assert dut.rd_addr_o.value == 1, f"Destination register should be 1, got {dut.rd_addr_o.value}"
    
    # Test LH instruction
    lh_instr = 0x00A51003  # Example LH instruction (opcode 0000011)
    tb.set_inputs(rd_addr=2, alu_result=0x22222222, mem_data=0x0000FFFF, 
                  reg_write=1, instr=lh_instr)
    await tb.clock_edge()
    
    # Should select memory data for halfword loads
    assert dut.rd_data_o.value == 0x0000FFFF, f"Should select memory data for LH, got {dut.rd_data_o.value}"
    assert dut.rd_addr_o.value == 2, f"Destination register should be 2, got {dut.rd_addr_o.value}"

@cocotb.test()
async def test_writeback_register_write_control(dut):
    """Test register write enable control"""
    cocotb.log.info("Testing register write control")
    
    tb = WritebackTestbench(dut)
    
    # Start clock
    cocotb.start_soon(Clock(dut.clk_i, 10, units="ns").start())
    
    await tb.reset()
    
    # Test with register write enabled
    add_instr = 0x00A58533  # ADD instruction
    tb.set_inputs(rd_addr=15, alu_result=0x12345678, reg_write=1, instr=add_instr)
    await tb.clock_edge()
    
    assert dut.reg_write_o.value == 1, f"Register write should be enabled, got {dut.reg_write_o.value}"
    assert dut.rd_addr_o.value == 15, f"Destination register should be 15, got {dut.rd_addr_o.value}"
    
    # Test with register write disabled (e.g., store instruction)
    sw_instr = 0x00A52023  # SW instruction (opcode 0100011)
    tb.set_inputs(rd_addr=0, alu_result=0x87654321, reg_write=0, instr=sw_instr)
    await tb.clock_edge()
    
    assert dut.reg_write_o.value == 0, f"Register write should be disabled for store, got {dut.reg_write_o.value}"
    assert dut.rd_addr_o.value == 0, f"Destination register should be 0 for store, got {dut.rd_addr_o.value}"

@cocotb.test()
async def test_writeback_instruction_types(dut):
    """Test various instruction types"""
    cocotb.log.info("Testing various instruction types")
    
    tb = WritebackTestbench(dut)
    
    # Start clock
    cocotb.start_soon(Clock(dut.clk_i, 10, units="ns").start())
    
    await tb.reset()
    
    # Test cases: (instruction, expected_data_source, description)
    test_cases = [
        # ALU result instructions (opcode != 0x03)
        (0x00A58533, "alu", "ADD instruction"),      # R-type: opcode 0110011
        (0x00A50513, "alu", "ADDI instruction"),    # I-type: opcode 0010011
        (0x000502B7, "alu", "LUI instruction"),     # U-type: opcode 0110111
        (0x00000517, "alu", "AUIPC instruction"),   # U-type: opcode 0010111
        (0x0000006F, "alu", "JAL instruction"),     # J-type: opcode 1101111
        (0x00050067, "alu", "JALR instruction"),    # I-type: opcode 1100111
        
        # Load instructions (opcode 0x03 - should use memory data)
        (0x00052503, "mem", "LW instruction"),      # I-type: opcode 0000011
        (0x00050003, "mem", "LB instruction"),      # I-type: opcode 0000011
        (0x00051003, "mem", "LH instruction"),      # I-type: opcode 0000011
        (0x00054003, "mem", "LBU instruction"),     # I-type: opcode 0000011
        (0x00055003, "mem", "LHU instruction"),     # I-type: opcode 0000011
    ]
    
    for i, (instr, expected_source, description) in enumerate(test_cases):
        alu_value = 0x1000 + i
        mem_value = 0x2000 + i
        
        tb.set_inputs(rd_addr=i+1, alu_result=alu_value, mem_data=mem_value, 
                      reg_write=1, instr=instr)
        await tb.clock_edge()
        
        if expected_source == "alu":
            expected_value = alu_value
            assert dut.rd_data_o.value == expected_value, \
                f"{description}: Should select ALU result {expected_value:08x}, got {dut.rd_data_o.value:08x}"
        else:  # "mem"
            expected_value = mem_value
            assert dut.rd_data_o.value == expected_value, \
                f"{description}: Should select memory data {expected_value:08x}, got {dut.rd_data_o.value:08x}"
        
        assert dut.rd_addr_o.value == (i+1), f"{description}: Destination register should be {i+1}"
        assert dut.reg_write_o.value == 1, f"{description}: Register write should be enabled"

@cocotb.test()
async def test_writeback_zero_register(dut):
    """Test behavior with x0 register (should still propagate signals)"""
    cocotb.log.info("Testing x0 register handling")
    
    tb = WritebackTestbench(dut)
    
    # Start clock
    cocotb.start_soon(Clock(dut.clk_i, 10, units="ns").start())
    
    await tb.reset()
    
    # Test writing to x0 (should propagate signals normally - register file will ignore)
    add_instr = 0x00A58033  # ADD x0, x10, x10
    tb.set_inputs(rd_addr=0, alu_result=0x12345678, mem_data=0xDEADBEEF, 
                  reg_write=1, instr=add_instr)
    await tb.clock_edge()
    
    # Writeback stage should still propagate the signals
    assert dut.rd_addr_o.value == 0, f"Should propagate x0 address, got {dut.rd_addr_o.value}"
    assert dut.rd_data_o.value == 0x12345678, f"Should propagate ALU result, got {dut.rd_data_o.value}"
    assert dut.reg_write_o.value == 1, f"Should propagate write enable, got {dut.reg_write_o.value}"

@cocotb.test()
async def test_writeback_combinational_behavior(dut):
    """Test that writeback is purely combinational (no clock dependency)"""
    cocotb.log.info("Testing combinational behavior")
    
    tb = WritebackTestbench(dut)
    
    # Start clock
    cocotb.start_soon(Clock(dut.clk_i, 10, units="ns").start())
    
    await tb.reset()
    
    # Test that output changes immediately with input changes (combinational)
    add_instr = 0x00A58533  # ADD instruction
    tb.set_inputs(rd_addr=5, alu_result=0x11111111, mem_data=0x22222222, 
                  reg_write=1, instr=add_instr)
    
    # Should change immediately without clock edge
    await Timer(1, units="ns")  # Small delay for propagation
    assert dut.rd_data_o.value == 0x11111111, f"ALU result should be selected immediately"
    assert dut.rd_addr_o.value == 5, f"Address should be propagated immediately"
    assert dut.reg_write_o.value == 1, f"Write enable should be propagated immediately"
    
    # Change to load instruction
    lw_instr = 0x00052503  # LW instruction
    tb.set_inputs(instr=lw_instr)
    
    # Should change immediately
    await Timer(1, units="ns")
    assert dut.rd_data_o.value == 0x22222222, f"Memory data should be selected immediately"

@cocotb.test()
async def test_writeback_random_operations(dut):
    """Test random combinations of inputs"""
    cocotb.log.info("Testing random operations")
    
    tb = WritebackTestbench(dut)
    
    # Start clock
    cocotb.start_soon(Clock(dut.clk_i, 10, units="ns").start())
    
    await tb.reset()
    
    # Run 50 random test cases
    for i in range(50):
        rd_addr = random.randint(0, 31)
        alu_result = random.randint(0, 0xFFFFFFFF)
        mem_data = random.randint(0, 0xFFFFFFFF)
        reg_write = random.randint(0, 1)
        
        # Generate random instruction (mix of load and non-load)
        if random.random() < 0.3:  # 30% chance of load instruction
            opcode = 0x03  # Load opcode
            funct3 = random.randint(0, 5)  # Various load types
            instr = (funct3 << 12) | opcode | (rd_addr << 7) | (random.randint(0, 31) << 15) | (random.randint(-2048, 2047) << 20)
            instr = instr & 0xFFFFFFFF
            expected_data = mem_data
        else:  # Non-load instruction
            opcode = random.choice([0x33, 0x13, 0x37, 0x17, 0x6F, 0x67])  # Various non-load opcodes
            instr = opcode | (rd_addr << 7) | (random.randint(0, 0xFFFFF) << 12)
            instr = instr & 0xFFFFFFFF
            expected_data = alu_result
        
        tb.set_inputs(rd_addr=rd_addr, alu_result=alu_result, mem_data=mem_data,
                      reg_write=reg_write, instr=instr)
        await tb.clock_edge()
        
        # Check outputs
        assert dut.rd_addr_o.value == rd_addr, f"Test {i}: Address should be {rd_addr}, got {dut.rd_addr_o.value}"
        assert dut.reg_write_o.value == reg_write, f"Test {i}: Write enable should be {reg_write}, got {dut.reg_write_o.value}"
        assert dut.rd_data_o.value == expected_data, f"Test {i}: Data should be {expected_data:08x}, got {dut.rd_data_o.value:08x}"

@cocotb.test()
async def test_writeback_edge_cases(dut):
    """Test edge cases and boundary conditions"""
    cocotb.log.info("Testing edge cases")
    
    tb = WritebackTestbench(dut)
    
    # Start clock
    cocotb.start_soon(Clock(dut.clk_i, 10, units="ns").start())
    
    await tb.reset()
    
    # Test with all zeros
    tb.set_inputs(rd_addr=0, alu_result=0, mem_data=0, reg_write=0, instr=0)
    await tb.clock_edge()
    
    assert dut.rd_addr_o.value == 0, f"Address should be 0"
    assert dut.reg_write_o.value == 0, f"Write enable should be 0"
    assert dut.rd_data_o.value == 0, f"Data should be 0"
    
    # Test with maximum values
    tb.set_inputs(rd_addr=31, alu_result=0xFFFFFFFF, mem_data=0xFFFFFFFF, 
                  reg_write=1, instr=0xFFFFFFFF)
    await tb.clock_edge()
    
    assert dut.rd_addr_o.value == 31, f"Address should be 31"
    assert dut.reg_write_o.value == 1, f"Write enable should be 1"
    # Data selection depends on instruction opcode
    
    # Test instruction with opcode exactly 0x03 (boundary case)
    boundary_instr = 0x00000003  # Minimal load instruction
    tb.set_inputs(rd_addr=15, alu_result=0x12345678, mem_data=0x87654321, 
                  reg_write=1, instr=boundary_instr)
    await tb.clock_edge()
    
    assert dut.rd_data_o.value == 0x87654321, f"Should select memory data for opcode 0x03" 