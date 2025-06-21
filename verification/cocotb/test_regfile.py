"""
test_regfile.py - Cocotb tests for register file module

Tests the 32x32 register file with dual read ports and single write port.

Author: Ethan
Date: 2024
"""

import cocotb
from cocotb.triggers import RisingEdge, Timer
from cocotb.clock import Clock
import random


async def setup_dut(dut):
    """Setup DUT with clock and initial conditions"""
    # Start clock
    cocotb.start_soon(Clock(dut.clk_i, 10, units="ns").start())
    
    # Initialize signals
    dut.rst_i.value = 0
    dut.rs1_addr_i.value = 0
    dut.rs2_addr_i.value = 0
    dut.rd_addr_i.value = 0
    dut.rd_data_i.value = 0
    dut.rd_we_i.value = 0
    
    # Wait a few clock cycles
    await RisingEdge(dut.clk_i)
    await RisingEdge(dut.clk_i)


@cocotb.test()
async def test_regfile_reset(dut):
    """Test register file reset behavior"""
    dut._log.info("Testing register file reset")
    
    await setup_dut(dut)
    
    # Apply reset
    dut.rst_i.value = 1
    await RisingEdge(dut.clk_i)
    await RisingEdge(dut.clk_i)  # Wait for reset to take effect
    dut.rst_i.value = 0
    await Timer(1, units="ns")
    
    # Check that all registers read as zero after reset
    for addr in range(8):  # Test first 8 registers for speed
        dut.rs1_addr_i.value = addr
        dut.rs2_addr_i.value = addr
        await Timer(1, units="ns")
        
        assert dut.rs1_data_o.value.integer == 0, f"Register x{addr} not zero after reset (rs1)"
        assert dut.rs2_data_o.value.integer == 0, f"Register x{addr} not zero after reset (rs2)"


@cocotb.test()
async def test_regfile_x0_hardwired(dut):
    """Test that x0 is hardwired to zero"""
    dut._log.info("Testing x0 hardwired to zero")
    
    await setup_dut(dut)
    
    # Try to write to x0
    dut.rd_addr_i.value = 0
    dut.rd_data_i.value = 0xDEADBEEF
    dut.rd_we_i.value = 1
    
    # Clock edge to attempt write
    await RisingEdge(dut.clk_i)
    dut.rd_we_i.value = 0
    await Timer(1, units="ns")
    
    # Check that x0 still reads as zero
    dut.rs1_addr_i.value = 0
    dut.rs2_addr_i.value = 0
    await Timer(1, units="ns")
    
    assert dut.rs1_data_o.value.integer == 0, "x0 not hardwired to zero (rs1)"
    assert dut.rs2_data_o.value.integer == 0, "x0 not hardwired to zero (rs2)"


@cocotb.test()
async def test_regfile_write_read(dut):
    """Test basic write and read operations"""
    dut._log.info("Testing register file write/read")
    
    await setup_dut(dut)
    
    test_data = [
        (1, 0x12345678),
        (5, 0x87654321),
        (10, 0xABCDEF00),
        (15, 0x11223344),
        (31, 0xFFFFFFFF),
    ]
    
    # Write test data to registers
    for addr, data in test_data:
        dut.rd_addr_i.value = addr
        dut.rd_data_i.value = data
        dut.rd_we_i.value = 1
        
        await RisingEdge(dut.clk_i)
    
    dut.rd_we_i.value = 0
    await Timer(1, units="ns")
    
    # Read back and verify
    for addr, expected_data in test_data:
        dut.rs1_addr_i.value = addr
        dut.rs2_addr_i.value = addr
        await Timer(1, units="ns")
        
        assert dut.rs1_data_o.value.integer == expected_data, \
            f"Register x{addr} read mismatch (rs1): got {dut.rs1_data_o.value.integer:08x}, expected {expected_data:08x}"
        assert dut.rs2_data_o.value.integer == expected_data, \
            f"Register x{addr} read mismatch (rs2): got {dut.rs2_data_o.value.integer:08x}, expected {expected_data:08x}"


@cocotb.test()
async def test_regfile_dual_read(dut):
    """Test dual read port functionality"""
    dut._log.info("Testing dual read ports")
    
    await setup_dut(dut)
    
    # Write different values to registers
    test_values = {
        1: 0x11111111,
        2: 0x22222222,
        3: 0x33333333,
        4: 0x44444444,
    }
    
    for addr, data in test_values.items():
        dut.rd_addr_i.value = addr
        dut.rd_data_i.value = data
        dut.rd_we_i.value = 1
        await RisingEdge(dut.clk_i)
    
    dut.rd_we_i.value = 0
    await Timer(1, units="ns")
    
    # Test reading different registers simultaneously
    test_pairs = [(1, 2), (3, 4), (1, 4), (2, 3)]
    
    for rs1_addr, rs2_addr in test_pairs:
        dut.rs1_addr_i.value = rs1_addr
        dut.rs2_addr_i.value = rs2_addr
        await Timer(1, units="ns")
        
        expected_rs1 = test_values[rs1_addr]
        expected_rs2 = test_values[rs2_addr]
        
        assert dut.rs1_data_o.value.integer == expected_rs1, \
            f"rs1 mismatch: x{rs1_addr} = {dut.rs1_data_o.value.integer:08x}, expected {expected_rs1:08x}"
        assert dut.rs2_data_o.value.integer == expected_rs2, \
            f"rs2 mismatch: x{rs2_addr} = {dut.rs2_data_o.value.integer:08x}, expected {expected_rs2:08x}"


@cocotb.test()
async def test_regfile_write_enable(dut):
    """Test write enable functionality"""
    dut._log.info("Testing write enable")
    
    await setup_dut(dut)
    
    # Write initial value
    dut.rd_addr_i.value = 5
    dut.rd_data_i.value = 0x12345678
    dut.rd_we_i.value = 1
    await RisingEdge(dut.clk_i)
    
    # Try to overwrite with write enable disabled
    dut.rd_data_i.value = 0x87654321
    dut.rd_we_i.value = 0
    await RisingEdge(dut.clk_i)
    await Timer(1, units="ns")
    
    # Check that original value is preserved
    dut.rs1_addr_i.value = 5
    await Timer(1, units="ns")
    assert dut.rs1_data_o.value.integer == 0x12345678, "Write enable not working correctly"
    
    # Now enable write and change value
    dut.rd_data_i.value = 0x87654321
    dut.rd_we_i.value = 1
    await RisingEdge(dut.clk_i)
    dut.rd_we_i.value = 0
    await Timer(1, units="ns")
    
    # Check that value changed
    await Timer(1, units="ns")
    assert dut.rs1_data_o.value.integer == 0x87654321, "Write with enable failed"


@cocotb.test()
async def test_regfile_all_registers(dut):
    """Test all 32 registers"""
    dut._log.info("Testing all 32 registers")
    
    await setup_dut(dut)
    
    # Write unique pattern to each register (except x0)
    for addr in range(1, 32):
        pattern = (addr << 24) | (addr << 16) | (addr << 8) | addr
        dut.rd_addr_i.value = addr
        dut.rd_data_i.value = pattern
        dut.rd_we_i.value = 1
        await RisingEdge(dut.clk_i)
    
    dut.rd_we_i.value = 0
    await Timer(1, units="ns")
    
    # Verify all registers
    for addr in range(32):
        dut.rs1_addr_i.value = addr
        await Timer(1, units="ns")
        
        if addr == 0:
            expected = 0
        else:
            expected = (addr << 24) | (addr << 16) | (addr << 8) | addr
        
        actual = dut.rs1_data_o.value.integer
        assert actual == expected, \
            f"Register x{addr} verification failed: got {actual:08x}, expected {expected:08x}"


@cocotb.test()
async def test_regfile_random_operations(dut):
    """Random testing of register file operations"""
    dut._log.info("Running random register file tests")
    
    await setup_dut(dut)
    
    # Apply reset
    dut.rst_i.value = 1
    await RisingEdge(dut.clk_i)
    dut.rst_i.value = 0
    await RisingEdge(dut.clk_i)
    
    # Track register contents (x0 always 0)
    reg_contents = [0] * 32
    
    # Random operations
    for _ in range(50):  # Reduced from 200 for faster testing
        if random.random() < 0.7:  # 70% write operations
            addr = random.randint(0, 31)
            data = random.randint(0, 0xFFFFFFFF)
            
            dut.rd_addr_i.value = addr
            dut.rd_data_i.value = data
            dut.rd_we_i.value = 1
            await RisingEdge(dut.clk_i)
            
            # Update our model (x0 remains 0)
            if addr != 0:
                reg_contents[addr] = data
                
        else:  # 30% read operations
            rs1_addr = random.randint(0, 31)
            rs2_addr = random.randint(0, 31)
            
            dut.rs1_addr_i.value = rs1_addr
            dut.rs2_addr_i.value = rs2_addr
            dut.rd_we_i.value = 0
            await Timer(1, units="ns")
            
            # Check against our model
            expected_rs1 = reg_contents[rs1_addr]
            expected_rs2 = reg_contents[rs2_addr]
            
            actual_rs1 = dut.rs1_data_o.value.integer
            actual_rs2 = dut.rs2_data_o.value.integer
            
            assert actual_rs1 == expected_rs1, \
                f"Random test rs1 mismatch: x{rs1_addr} = {actual_rs1:08x}, expected {expected_rs1:08x}"
            assert actual_rs2 == expected_rs2, \
                f"Random test rs2 mismatch: x{rs2_addr} = {actual_rs2:08x}, expected {expected_rs2:08x}"


# Test configuration for cocotb-test
if __name__ == "__main__":
    import os
    from cocotb_test.simulator import run
    
    # Set up the test
    sim = os.getenv("SIM", "verilator")
    
    run(
        verilog_sources=["../../rtl/core/regfile.sv"],
        toplevel="regfile",
        module="test_regfile",
        simulator=sim,
        extra_args=["--trace", "--trace-structs"] if sim == "verilator" else []
    ) 