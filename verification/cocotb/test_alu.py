"""
test_alu.py - Cocotb tests for ALU module

Tests all arithmetic and logical operations for the eCPU ALU.

Author: Ethan
Date: 2024
"""

import cocotb
from cocotb.triggers import Timer
from cocotb.result import TestFailure
import random


class ALUOp:
    """ALU operation codes"""
    ADD = 0b0000
    SUB = 0b0001
    AND = 0b0010
    OR = 0b0011
    XOR = 0b0100
    SLT = 0b0101
    SLTU = 0b0110
    SLL = 0b0111
    SRL = 0b1000
    SRA = 0b1001
    LUI = 0b1010
    COPY = 0b1011


@cocotb.test()
async def test_alu_add(dut):
    """Test ALU addition operation"""
    dut._log.info("Testing ALU ADD operation")
    
    test_cases = [
        (0x00000000, 0x00000000, 0x00000000),
        (0x00000001, 0x00000001, 0x00000002),
        (0x12345678, 0x87654321, 0x99999999),
        (0xFFFFFFFF, 0x00000001, 0x00000000),  # Overflow case
        (0x7FFFFFFF, 0x00000001, 0x80000000),  # Sign change
    ]
    
    for a, b, expected in test_cases:
        dut.operand_a_i.value = a
        dut.operand_b_i.value = b
        dut.alu_op_i.value = ALUOp.ADD
        
        await Timer(1, units="ns")
        
        result = dut.result_o.value.integer
        assert result == expected, f"ADD failed: {a:08x} + {b:08x} = {result:08x}, expected {expected:08x}"
        
        # Test zero flag
        zero_expected = (result == 0)
        assert dut.zero_o.value == zero_expected, f"Zero flag incorrect for {result:08x}"


@cocotb.test()
async def test_alu_sub(dut):
    """Test ALU subtraction operation"""
    dut._log.info("Testing ALU SUB operation")
    
    test_cases = [
        (0x00000000, 0x00000000, 0x00000000),
        (0x00000002, 0x00000001, 0x00000001),
        (0x12345678, 0x12345678, 0x00000000),
        (0x00000000, 0x00000001, 0xFFFFFFFF),  # Underflow
        (0x80000000, 0x00000001, 0x7FFFFFFF),  # Sign change
    ]
    
    for a, b, expected in test_cases:
        dut.operand_a_i.value = a
        dut.operand_b_i.value = b
        dut.alu_op_i.value = ALUOp.SUB
        
        await Timer(1, units="ns")
        
        result = dut.result_o.value.integer
        assert result == expected, f"SUB failed: {a:08x} - {b:08x} = {result:08x}, expected {expected:08x}"


@cocotb.test()
async def test_alu_logical(dut):
    """Test ALU logical operations (AND, OR, XOR)"""
    dut._log.info("Testing ALU logical operations")
    
    test_cases = [
        (0xF0F0F0F0, 0x0F0F0F0F),
        (0xAAAAAAAA, 0x55555555),
        (0x12345678, 0x87654321),
        (0xFFFFFFFF, 0x00000000),
    ]
    
    for a, b in test_cases:
        # Test AND
        dut.operand_a_i.value = a
        dut.operand_b_i.value = b
        dut.alu_op_i.value = ALUOp.AND
        await Timer(1, units="ns")
        expected_and = a & b
        assert dut.result_o.value.integer == expected_and, f"AND failed: {a:08x} & {b:08x}"
        
        # Test OR
        dut.alu_op_i.value = ALUOp.OR
        await Timer(1, units="ns")
        expected_or = a | b
        assert dut.result_o.value.integer == expected_or, f"OR failed: {a:08x} | {b:08x}"
        
        # Test XOR
        dut.alu_op_i.value = ALUOp.XOR
        await Timer(1, units="ns")
        expected_xor = a ^ b
        assert dut.result_o.value.integer == expected_xor, f"XOR failed: {a:08x} ^ {b:08x}"


@cocotb.test()
async def test_alu_shifts(dut):
    """Test ALU shift operations"""
    dut._log.info("Testing ALU shift operations")
    
    test_value = 0x12345678
    shift_amounts = [0, 1, 4, 8, 16, 31]
    
    for shift in shift_amounts:
        dut.operand_a_i.value = test_value
        dut.operand_b_i.value = shift
        
        # Test SLL (Shift Left Logical)
        dut.alu_op_i.value = ALUOp.SLL
        await Timer(1, units="ns")
        expected_sll = (test_value << shift) & 0xFFFFFFFF
        assert dut.result_o.value.integer == expected_sll, f"SLL failed: {test_value:08x} << {shift}"
        
        # Test SRL (Shift Right Logical)
        dut.alu_op_i.value = ALUOp.SRL
        await Timer(1, units="ns")
        expected_srl = test_value >> shift
        assert dut.result_o.value.integer == expected_srl, f"SRL failed: {test_value:08x} >> {shift}"


@cocotb.test()
async def test_alu_sra(dut):
    """Test ALU arithmetic right shift"""
    dut._log.info("Testing ALU SRA operation")
    
    # Test with positive number
    dut.operand_a_i.value = 0x12345678
    dut.operand_b_i.value = 4
    dut.alu_op_i.value = ALUOp.SRA
    await Timer(1, units="ns")
    expected_pos = 0x01234567
    assert dut.result_o.value.integer == expected_pos, f"SRA positive failed"
    
    # Test with negative number (sign extension)
    dut.operand_a_i.value = 0x87654321
    dut.operand_b_i.value = 4
    await Timer(1, units="ns")
    expected_neg = 0xF8765432
    assert dut.result_o.value.integer == expected_neg, f"SRA negative failed"


@cocotb.test()
async def test_alu_comparison(dut):
    """Test ALU comparison operations"""
    dut._log.info("Testing ALU comparison operations")
    
    test_cases = [
        # (a, b, slt_expected, sltu_expected)
        (5, 10, 1, 1),           # 5 < 10 (both signed and unsigned)
        (10, 5, 0, 0),           # 10 > 5 (both signed and unsigned)
        (5, 5, 0, 0),            # 5 == 5
        (-1, 1, 1, 0),           # -1 < 1 (signed), 0xFFFFFFFF > 1 (unsigned)
        (0x80000000, 1, 1, 0),   # Most negative < 1 (signed), large > 1 (unsigned)
    ]
    
    for a, b, slt_exp, sltu_exp in test_cases:
        # Convert to 32-bit representation
        a_val = a & 0xFFFFFFFF
        b_val = b & 0xFFFFFFFF
        
        dut.operand_a_i.value = a_val
        dut.operand_b_i.value = b_val
        
        # Test SLT (Set Less Than)
        dut.alu_op_i.value = ALUOp.SLT
        await Timer(1, units="ns")
        assert dut.result_o.value.integer == slt_exp, f"SLT failed: {a} < {b} (signed)"
        
        # Test SLTU (Set Less Than Unsigned)
        dut.alu_op_i.value = ALUOp.SLTU
        await Timer(1, units="ns")
        assert dut.result_o.value.integer == sltu_exp, f"SLTU failed: {a_val:08x} < {b_val:08x} (unsigned)"


@cocotb.test()
async def test_alu_special_ops(dut):
    """Test special ALU operations (LUI, COPY)"""
    dut._log.info("Testing ALU special operations")
    
    # Test LUI (Load Upper Immediate) - should pass operand_b
    test_value = 0x12345678
    dut.operand_a_i.value = 0xDEADBEEF  # Should be ignored
    dut.operand_b_i.value = test_value
    dut.alu_op_i.value = ALUOp.LUI
    await Timer(1, units="ns")
    assert dut.result_o.value.integer == test_value, f"LUI failed"
    
    # Test COPY (Copy operand_a) - should pass operand_a
    test_value = 0x87654321
    dut.operand_a_i.value = test_value
    dut.operand_b_i.value = 0xDEADBEEF  # Should be ignored
    dut.alu_op_i.value = ALUOp.COPY
    await Timer(1, units="ns")
    assert dut.result_o.value.integer == test_value, f"COPY failed"


@cocotb.test()
async def test_alu_flags(dut):
    """Test ALU flag generation"""
    dut._log.info("Testing ALU flags")
    
    # Test zero flag
    dut.operand_a_i.value = 0x12345678
    dut.operand_b_i.value = 0x12345678
    dut.alu_op_i.value = ALUOp.SUB
    await Timer(1, units="ns")
    assert dut.zero_o.value == 1, "Zero flag not set when result is zero"
    assert dut.result_o.value.integer == 0, "Result should be zero"
    
    # Test negative flag
    dut.operand_a_i.value = 0x00000001
    dut.operand_b_i.value = 0x00000002
    dut.alu_op_i.value = ALUOp.SUB
    await Timer(1, units="ns")
    assert dut.negative_o.value == 1, "Negative flag not set when result is negative"
    assert dut.result_o.value.integer == 0xFFFFFFFF, "Result should be negative"


@cocotb.test()
async def test_alu_random(dut):
    """Random testing of ALU operations"""
    dut._log.info("Running random ALU tests")
    
    for _ in range(100):
        a = random.randint(0, 0xFFFFFFFF)
        b = random.randint(0, 0xFFFFFFFF)
        op = random.choice([ALUOp.ADD, ALUOp.SUB, ALUOp.AND, ALUOp.OR, ALUOp.XOR])
        
        dut.operand_a_i.value = a
        dut.operand_b_i.value = b
        dut.alu_op_i.value = op
        
        await Timer(1, units="ns")
        
        # Calculate expected result
        if op == ALUOp.ADD:
            expected = (a + b) & 0xFFFFFFFF
        elif op == ALUOp.SUB:
            expected = (a - b) & 0xFFFFFFFF
        elif op == ALUOp.AND:
            expected = a & b
        elif op == ALUOp.OR:
            expected = a | b
        elif op == ALUOp.XOR:
            expected = a ^ b
        
        result = dut.result_o.value.integer
        assert result == expected, f"Random test failed: op={op}, a={a:08x}, b={b:08x}, got={result:08x}, expected={expected:08x}"


# Test configuration for cocotb-test
if __name__ == "__main__":
    import os
    from cocotb_test.simulator import run
    
    # Set up the test
    sim = os.getenv("SIM", "verilator")
    
    run(
        verilog_sources=["../../rtl/core/alu.sv"],
        toplevel="alu",
        module="test_alu",
        simulator=sim,
        extra_args=["--trace", "--trace-structs"] if sim == "verilator" else []
    ) 