"""
test_instruction_memory.py - Cocotb test for instruction memory module

Tests the instruction memory module functionality including:
- Basic Wishbone B4 read operations
- Word-aligned access enforcement
- Error handling for misaligned/invalid access
- Memory initialization and data integrity

Author: Ethan
Date: 2024
"""

import random
import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, FallingEdge, Timer
from cocotb.result import TestFailure

# Test parameters
CLK_PERIOD = 10  # 100MHz clock


async def setup_dut(dut):
    """Setup DUT with clock and initial reset"""
    # Create clock
    cocotb.start_soon(Clock(dut.clk_i, CLK_PERIOD, units="ns").start())
    
    # Initialize inputs
    dut.cyc_i.value = 0
    dut.stb_i.value = 0
    dut.we_i.value = 0
    dut.adr_i.value = 0
    dut.dat_i.value = 0
    dut.sel_i.value = 0
    
    # Apply reset
    dut.rst_i.value = 1
    await RisingEdge(dut.clk_i)
    await RisingEdge(dut.clk_i)
    dut.rst_i.value = 0
    await RisingEdge(dut.clk_i)


async def wishbone_read(dut, address):
    """Perform a Wishbone read operation"""
    # Start transaction
    dut.cyc_i.value = 1
    dut.stb_i.value = 1
    dut.we_i.value = 0
    dut.adr_i.value = address
    dut.sel_i.value = 0xF  # Full word access
    
    # Wait for acknowledge or error
    while True:
        await RisingEdge(dut.clk_i)
        if dut.ack_o.value == 1:
            data = dut.dat_o.value.integer
            # End transaction
            dut.cyc_i.value = 0
            dut.stb_i.value = 0
            return data, False  # data, error
        elif dut.err_o.value == 1:
            # End transaction
            dut.cyc_i.value = 0
            dut.stb_i.value = 0
            return 0, True  # data, error


@cocotb.test()
async def test_imem_basic_read(dut):
    """Test basic instruction memory read operations"""
    dut._log.info("Testing basic instruction memory reads")
    
    await setup_dut(dut)
    
    # Test reading from address 0 (should contain NOP instruction)
    data, error = await wishbone_read(dut, 0x00000000)
    assert not error, "Unexpected error on valid read"
    assert data == 0x00000013, f"Expected NOP (0x00000013), got 0x{data:08x}"
    
    # Test reading from word-aligned addresses
    test_addresses = [0x00000004, 0x00000008, 0x0000000C, 0x00000010]
    for addr in test_addresses:
        data, error = await wishbone_read(dut, addr)
        assert not error, f"Unexpected error reading from 0x{addr:08x}"
        assert data == 0x00000013, f"Expected NOP at 0x{addr:08x}, got 0x{data:08x}"


@cocotb.test()
async def test_imem_misaligned_access(dut):
    """Test that misaligned accesses generate errors"""
    dut._log.info("Testing misaligned access error handling")
    
    await setup_dut(dut)
    
    # Test misaligned addresses (should generate errors)
    misaligned_addresses = [0x00000001, 0x00000002, 0x00000003, 0x00000005]
    
    for addr in misaligned_addresses:
        data, error = await wishbone_read(dut, addr)
        assert error, f"Expected error for misaligned access to 0x{addr:08x}"


@cocotb.test()
async def test_imem_write_protection(dut):
    """Test that write attempts are rejected"""
    dut._log.info("Testing write protection")
    
    await setup_dut(dut)
    
    # Attempt write operation (should generate error)
    dut.cyc_i.value = 1
    dut.stb_i.value = 1
    dut.we_i.value = 1  # Write enable
    dut.adr_i.value = 0x00000000
    dut.dat_i.value = 0xDEADBEEF
    dut.sel_i.value = 0xF
    
    await RisingEdge(dut.clk_i)
    
    # Should get error, not acknowledge
    assert dut.err_o.value == 1, "Expected error for write attempt"
    assert dut.ack_o.value == 0, "Should not acknowledge write operations"
    
    # End transaction
    dut.cyc_i.value = 0
    dut.stb_i.value = 0
    dut.we_i.value = 0


@cocotb.test()
async def test_imem_out_of_bounds(dut):
    """Test out of bounds access handling"""
    dut._log.info("Testing out of bounds access")
    
    await setup_dut(dut)
    
    # Test access beyond memory size (assuming 64KB = 16384 words)
    # Address 0x10000 (65536) should be out of bounds
    large_address = 0x10000
    
    data, error = await wishbone_read(dut, large_address)
    assert error, f"Expected error for out of bounds access to 0x{large_address:08x}"


@cocotb.test()
async def test_imem_address_boundary(dut):
    """Test access at memory boundaries"""
    dut._log.info("Testing memory boundary access")
    
    await setup_dut(dut)
    
    # Test last valid address (16383 * 4 = 65532 = 0xFFFC)
    last_valid_addr = 0xFFFC
    
    data, error = await wishbone_read(dut, last_valid_addr)
    assert not error, f"Unexpected error at last valid address 0x{last_valid_addr:08x}"
    
    # Test first invalid address (0x10000)
    first_invalid_addr = 0x10000
    
    data, error = await wishbone_read(dut, first_invalid_addr)
    assert error, f"Expected error for first invalid address 0x{first_invalid_addr:08x}"


@cocotb.test()
async def test_imem_wishbone_protocol(dut):
    """Test Wishbone protocol compliance"""
    dut._log.info("Testing Wishbone protocol compliance")
    
    await setup_dut(dut)
    
    # Test that strobe implies cycle
    # Start with cyc=0, stb=1 (invalid)
    dut.cyc_i.value = 0
    dut.stb_i.value = 1
    dut.adr_i.value = 0x00000000
    
    await RisingEdge(dut.clk_i)
    
    # Should not acknowledge invalid protocol
    assert dut.ack_o.value == 0, "Should not acknowledge when cyc=0, stb=1"
    
    # Test proper protocol: cyc=1, stb=1
    dut.cyc_i.value = 1
    dut.stb_i.value = 1
    
    await RisingEdge(dut.clk_i)
    
    # Should acknowledge valid protocol for valid address
    assert dut.ack_o.value == 1, "Should acknowledge when cyc=1, stb=1"
    
    # Clean up
    dut.cyc_i.value = 0
    dut.stb_i.value = 0


@cocotb.test()
async def test_imem_multiple_reads(dut):
    """Test multiple consecutive read operations"""
    dut._log.info("Testing multiple consecutive reads")
    
    await setup_dut(dut)
    
    # Perform multiple reads to different addresses
    addresses = [0x0000, 0x0004, 0x0008, 0x000C, 0x0010, 0x0100, 0x1000]
    
    for addr in addresses:
        data, error = await wishbone_read(dut, addr)
        assert not error, f"Unexpected error reading from 0x{addr:08x}"
        # All should contain NOP instructions initially
        assert data == 0x00000013, f"Expected NOP at 0x{addr:08x}, got 0x{data:08x}"
        
        dut._log.info(f"Read 0x{data:08x} from address 0x{addr:08x}")


@cocotb.test()
async def test_imem_random_access_pattern(dut):
    """Test random access patterns"""
    dut._log.info("Testing random access patterns")
    
    await setup_dut(dut)
    
    # Generate random word-aligned addresses within valid range
    random.seed(42)  # For reproducible results
    num_tests = 20
    
    for i in range(num_tests):
        # Generate word-aligned address (divisible by 4)
        word_index = random.randint(0, 1023)  # First 4KB for faster testing
        address = word_index * 4
        
        data, error = await wishbone_read(dut, address)
        assert not error, f"Unexpected error reading from 0x{address:08x}"
        assert data == 0x00000013, f"Expected NOP at 0x{address:08x}, got 0x{data:08x}"


# Test could be extended to include:
# - Memory initialization from file (if INIT_FILE parameter is used)
# - Back-to-back transactions
# - Cycle/strobe deassertion timing
# - Reset behavior during transactions 