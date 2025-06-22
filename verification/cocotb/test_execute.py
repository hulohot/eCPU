"""
test_execute.py - Comprehensive tests for execute stage module

Tests the execute stage functionality including:
- ALU operations with forwarding
- Branch condition evaluation  
- Jump target calculation
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

class ExecuteTestbench:
    """Test harness for execute module"""
    
    def __init__(self, dut):
        self.dut = dut
        
    async def reset(self):
        """Reset the execute module"""
        self.dut.rst_i.value = 1
        await RisingEdge(self.dut.clk_i)
        await RisingEdge(self.dut.clk_i)
        self.dut.rst_i.value = 0
        await RisingEdge(self.dut.clk_i)
        
    async def clock_edge(self):
        """Wait for rising edge of clock"""
        await RisingEdge(self.dut.clk_i)
        
    def set_inputs(self, pc=0, instr=0, instr_valid=1, rs1_data=0, rs2_data=0, 
                   rd_addr=0, imm=0, alu_op=0, alu_src=0, reg_write=0, mem_read=0, mem_write=0,
                   mem_size=0, branch=0, jump=0, branch_type=0, stall=0,
                   forward_a=0, forward_b=0, alu_result_mem=0, rd_data_wb=0):
        """Set execute module inputs"""
        self.dut.pc_i.value = pc
        self.dut.instr_i.value = instr
        self.dut.instr_valid_i.value = instr_valid
        self.dut.rs1_data_i.value = rs1_data
        self.dut.rs2_data_i.value = rs2_data
        self.dut.rd_addr_i.value = rd_addr
        self.dut.imm_i.value = imm
        self.dut.alu_op_i.value = alu_op
        self.dut.alu_src_i.value = alu_src
        self.dut.reg_write_i.value = reg_write
        self.dut.mem_read_i.value = mem_read
        self.dut.mem_write_i.value = mem_write
        self.dut.mem_size_i.value = mem_size
        self.dut.branch_i.value = branch
        self.dut.jump_i.value = jump
        self.dut.branch_type_i.value = branch_type
        self.dut.stall_i.value = stall
        self.dut.forward_a_i.value = forward_a
        self.dut.forward_b_i.value = forward_b
        self.dut.alu_result_mem_i.value = alu_result_mem
        self.dut.rd_data_wb_i.value = rd_data_wb

@cocotb.test()
async def test_execute_reset(dut):
    """Test execute module reset behavior"""
    cocotb.log.info("Testing execute module reset")
    
    tb = ExecuteTestbench(dut)
    
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
    assert dut.reg_write_o.value == 0, f"Register write should be 0 after reset, got {dut.reg_write_o.value}"
    assert dut.mem_read_o.value == 0, f"Memory read should be 0 after reset, got {dut.mem_read_o.value}"
    assert dut.mem_write_o.value == 0, f"Memory write should be 0 after reset, got {dut.mem_write_o.value}"
    assert dut.stall_o.value == 0, f"Stall output should be 0 after reset, got {dut.stall_o.value}"

@cocotb.test()
async def test_execute_alu_operations(dut):
    """Test ALU operations without forwarding"""
    cocotb.log.info("Testing ALU operations")
    
    tb = ExecuteTestbench(dut)
    
    # Start clock
    cocotb.start_soon(Clock(dut.clk_i, 10, units="ns").start())
    
    await tb.reset()
    
    # Test ADD operation
    tb.set_inputs(pc=0x1000, instr=0x12345678, rs1_data=10, rs2_data=20, 
                  rd_addr=5, alu_op=0, reg_write=1)  # ALU_ADD = 0
    await tb.clock_edge()
    await tb.clock_edge()  # Wait additional cycle for pipeline register to update
    
    # Check ALU result is passed through pipeline register
    assert dut.alu_result_o.value == 30, f"ADD result should be 30, got {dut.alu_result_o.value}"
    assert dut.pc_o.value == 0x1000, f"PC should be passed through, got {dut.pc_o.value}"
    assert dut.rd_addr_o.value == 5, f"Destination register should be 5, got {dut.rd_addr_o.value}"
    assert dut.reg_write_o.value == 1, f"Register write should be 1, got {dut.reg_write_o.value}"
    
    # Test SUB operation
    tb.set_inputs(pc=0x1004, rs1_data=30, rs2_data=10, rd_addr=6, alu_op=1)  # ALU_SUB = 1
    await tb.clock_edge()
    await tb.clock_edge()  # Wait additional cycle for pipeline register to update
    
    assert dut.alu_result_o.value == 20, f"SUB result should be 20, got {dut.alu_result_o.value}"
    assert dut.rd_addr_o.value == 6, f"Destination register should be 6, got {dut.rd_addr_o.value}"

@cocotb.test()
async def test_execute_forwarding(dut):
    """Test data forwarding logic"""
    cocotb.log.info("Testing data forwarding")
    
    tb = ExecuteTestbench(dut)
    
    # Start clock
    cocotb.start_soon(Clock(dut.clk_i, 10, units="ns").start())
    
    await tb.reset()
    
    # Test forwarding from memory stage (forward_a = 1)
    tb.set_inputs(rs1_data=10, rs2_data=20, alu_op=0, forward_a=1, 
                  alu_result_mem=100)  # Forward from memory stage
    await tb.clock_edge()
    await tb.clock_edge()  # Wait additional cycle for pipeline register to update
    
    # Should use forwarded value (100) instead of rs1_data (10)
    assert dut.alu_result_o.value == 120, f"Forwarded ADD should be 120 (100+20), got {dut.alu_result_o.value}"
    
    # Test forwarding from writeback stage (forward_b = 2)
    tb.set_inputs(rs1_data=10, rs2_data=20, alu_op=0, forward_b=2, 
                  rd_data_wb=200)  # Forward from writeback stage
    await tb.clock_edge()
    await tb.clock_edge()  # Wait additional cycle for pipeline register to update
    
    # Should use forwarded value (200) instead of rs2_data (20)
    assert dut.alu_result_o.value == 210, f"Forwarded ADD should be 210 (10+200), got {dut.alu_result_o.value}"

@cocotb.test()
async def test_execute_branch_evaluation(dut):
    """Test branch condition evaluation"""
    cocotb.log.info("Testing branch evaluation")
    
    tb = ExecuteTestbench(dut)
    
    # Start clock
    cocotb.start_soon(Clock(dut.clk_i, 10, units="ns").start())
    
    await tb.reset()
    
    # Test BEQ (branch equal) - should be taken when rs1 == rs2
    tb.set_inputs(pc=0x1000, rs1_data=10, rs2_data=10, imm=0x100, 
                  branch=1, branch_type=0, alu_op=1)  # BEQ, SUB to set zero flag
    await tb.clock_edge()
    
    assert dut.branch_taken_o.value == 1, f"BEQ should be taken when operands are equal"
    assert dut.branch_target_o.value == 0x1100, f"Branch target should be PC + imm = 0x1100, got {dut.branch_target_o.value}"
    
    # Test BEQ - should not be taken when rs1 != rs2
    tb.set_inputs(pc=0x1000, rs1_data=10, rs2_data=20, imm=0x100, 
                  branch=1, branch_type=0, alu_op=1)  # BEQ, SUB to clear zero flag
    await tb.clock_edge()
    
    assert dut.branch_taken_o.value == 0, f"BEQ should not be taken when operands are different"
    
    # Test BNE (branch not equal) - should be taken when rs1 != rs2
    tb.set_inputs(pc=0x1000, rs1_data=10, rs2_data=20, imm=0x100, 
                  branch=1, branch_type=1, alu_op=1)  # BNE, SUB to clear zero flag
    await tb.clock_edge()
    
    assert dut.branch_taken_o.value == 1, f"BNE should be taken when operands are different"

@cocotb.test()
async def test_execute_jump_operations(dut):
    """Test jump instruction handling"""
    cocotb.log.info("Testing jump operations")
    
    tb = ExecuteTestbench(dut)
    
    # Start clock
    cocotb.start_soon(Clock(dut.clk_i, 10, units="ns").start())
    
    await tb.reset()
    
    # Test JAL (jump and link) - target = PC + imm
    tb.set_inputs(pc=0x1000, imm=0x200, jump=1, alu_op=0)  # JAL
    await tb.clock_edge()
    
    assert dut.branch_taken_o.value == 1, f"JAL should always be taken"
    assert dut.branch_target_o.value == 0x1200, f"JAL target should be PC + imm = 0x1200, got {dut.branch_target_o.value}"
    
    # Test JALR (jump and link register) - target = rs1 + imm
    tb.set_inputs(pc=0x1000, rs1_data=0x2000, imm=0x100, jump=1, alu_op=11)  # JALR (ALU_COPY)
    await tb.clock_edge()
    
    assert dut.branch_taken_o.value == 1, f"JALR should always be taken"
    assert dut.branch_target_o.value == 0x2100, f"JALR target should be rs1 + imm = 0x2100, got {dut.branch_target_o.value}"

@cocotb.test()
async def test_execute_immediate_operations(dut):
    """Test immediate operations (ALU operand selection)"""
    cocotb.log.info("Testing immediate operations")
    
    tb = ExecuteTestbench(dut)
    
    # Start clock
    cocotb.start_soon(Clock(dut.clk_i, 10, units="ns").start())
    
    await tb.reset()
    
    # Test immediate operation (ADDI) - should use immediate instead of rs2
    tb.set_inputs(rs1_data=10, rs2_data=999, imm=50, alu_op=0, alu_src=1)  # ADD with immediate source
    await tb.clock_edge()
    await tb.clock_edge()  # Wait additional cycle for pipeline register to update
    
    # Should use immediate (50) instead of rs2_data (999) 
    # Expected: 10 + 50 = 60
    assert dut.alu_result_o.value == 60, f"ADDI should be 60 (10+50), got {dut.alu_result_o.value}"

@cocotb.test()
async def test_execute_memory_operations(dut):
    """Test memory operation signal propagation"""
    cocotb.log.info("Testing memory operations")
    
    tb = ExecuteTestbench(dut)
    
    # Start clock
    cocotb.start_soon(Clock(dut.clk_i, 10, units="ns").start())
    
    await tb.reset()
    
    # Test load operation
    tb.set_inputs(pc=0x1000, rs1_data=0x2000, imm=0x100, alu_op=0, alu_src=1,
                  mem_read=1, mem_size=2, rd_addr=5, reg_write=1)  # Load word
    await tb.clock_edge()
    await tb.clock_edge()  # Wait additional cycle for pipeline register to update
    
    assert dut.alu_result_o.value == 0x2100, f"Load address should be rs1 + imm = 0x2100, got {dut.alu_result_o.value}"
    assert dut.mem_read_o.value == 1, f"Memory read should be propagated"
    assert dut.mem_size_o.value == 2, f"Memory size should be propagated"
    
    # Test store operation
    tb.set_inputs(pc=0x1004, rs1_data=0x3000, rs2_data=0xDEADBEEF, imm=0x200, 
                  alu_op=0, alu_src=1, mem_write=1, mem_size=2)  # Store word
    await tb.clock_edge()
    await tb.clock_edge()  # Wait additional cycle for pipeline register to update
    
    assert dut.alu_result_o.value == 0x3200, f"Store address should be rs1 + imm = 0x3200, got {dut.alu_result_o.value}"
    assert dut.rs2_data_o.value == 0xDEADBEEF, f"Store data should be propagated"
    assert dut.mem_write_o.value == 1, f"Memory write should be propagated"

@cocotb.test()
async def test_execute_stall_behavior(dut):
    """Test pipeline stall behavior"""
    cocotb.log.info("Testing stall behavior")
    
    tb = ExecuteTestbench(dut)
    
    # Start clock
    cocotb.start_soon(Clock(dut.clk_i, 10, units="ns").start())
    
    await tb.reset()
    
    # Set up initial values
    tb.set_inputs(pc=0x1000, instr=0x12345678, rs1_data=10, rs2_data=20, 
                  rd_addr=5, alu_op=0, reg_write=1)
    await tb.clock_edge()
    await tb.clock_edge()  # Wait for pipeline register to update
    
    # Store expected values
    expected_pc = int(dut.pc_o.value)
    expected_instr = int(dut.instr_o.value)
    expected_alu_result = int(dut.alu_result_o.value)
    
    # Apply stall
    tb.set_inputs(pc=0x2000, instr=0x87654321, rs1_data=100, rs2_data=200, 
                  rd_addr=10, alu_op=1, stall=1)  # New inputs with stall
    await tb.clock_edge()
    
    # During stall, pipeline register should hold previous values
    assert dut.pc_o.value == expected_pc, f"PC should be held during stall"
    assert dut.instr_o.value == expected_instr, f"Instruction should be held during stall"
    assert dut.alu_result_o.value == expected_alu_result, f"ALU result should be held during stall"
    assert dut.stall_o.value == 1, f"Stall output should reflect stall input"
    
    # Release stall with the new inputs
    tb.set_inputs(pc=0x2000, instr=0x87654321, rs1_data=100, rs2_data=200, 
                  rd_addr=10, alu_op=1, stall=0)  # Same inputs but stall=0
    await tb.clock_edge()
    await tb.clock_edge()  # Wait for pipeline register to update
    
    # Should now accept new values
    assert dut.pc_o.value == 0x2000, f"PC should update after stall release"
    assert dut.stall_o.value == 0, f"Stall output should be cleared"

@cocotb.test()
async def test_execute_random_operations(dut):
    """Test random combinations of operations"""
    cocotb.log.info("Testing random operations")
    
    tb = ExecuteTestbench(dut)
    
    # Start clock
    cocotb.start_soon(Clock(dut.clk_i, 10, units="ns").start())
    
    await tb.reset()
    
    # Run 20 random test cases
    for i in range(20):
        pc = random.randint(0x1000, 0xFFFF) & 0xFFFFFFFC  # Word-aligned
        rs1_data = random.randint(0, 0xFFFFFFFF)
        rs2_data = random.randint(0, 0xFFFFFFFF)
        imm = random.randint(-2048, 2047)  # 12-bit signed immediate
        alu_op = random.randint(0, 11)
        rd_addr = random.randint(1, 31)  # Avoid x0
        
        tb.set_inputs(pc=pc, rs1_data=rs1_data, rs2_data=rs2_data, 
                      imm=imm, alu_op=alu_op, rd_addr=rd_addr, reg_write=1)
        await tb.clock_edge()
        await tb.clock_edge()  # Wait additional cycle for pipeline register to update
        
        # Basic checks - values should be propagated
        assert dut.pc_o.value == pc, f"PC should be propagated for test {i}"
        assert dut.rd_addr_o.value == rd_addr, f"Destination register should be propagated for test {i}"
        assert dut.reg_write_o.value == 1, f"Register write should be propagated for test {i}"
        
        # ALU result should be valid (not X or Z)
        alu_result = dut.alu_result_o.value
        assert alu_result.is_resolvable, f"ALU result should be valid for test {i}, got {alu_result}" 