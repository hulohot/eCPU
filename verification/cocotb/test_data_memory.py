"""
test_data_memory.py - Cocotb testbench for data memory module

Tests the data memory module functionality:
- Basic read/write operations
- Byte, halfword, and word access
- Wishbone B4 protocol compliance
- Error handling for out-of-bounds access
- Byte select functionality
- Memory initialization

Author: Ethan
Date: 2024
"""

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, FallingEdge, Timer
from cocotb.binary import BinaryValue
import random


class DataMemoryTB:
    """Testbench for data memory module"""
    
    def __init__(self, dut):
        self.dut = dut
        self.ADDR_WIDTH = 32
        self.DATA_WIDTH = 32
        self.MEM_SIZE = 16384  # 64KB / 4 words
        
    async def reset(self):
        """Reset the DUT"""
        self.dut.rst_i.value = 1
        self.dut.cyc_i.value = 0
        self.dut.stb_i.value = 0
        self.dut.we_i.value = 0
        self.dut.adr_i.value = 0
        self.dut.dat_i.value = 0
        self.dut.sel_i.value = 0
        
        await RisingEdge(self.dut.clk_i)
        await RisingEdge(self.dut.clk_i)
        self.dut.rst_i.value = 0
        await RisingEdge(self.dut.clk_i)
        
    async def write_word(self, address, data, sel_mask=0xF):
        """Write a word to memory"""
        self.dut.cyc_i.value = 1
        self.dut.stb_i.value = 1
        self.dut.we_i.value = 1
        self.dut.adr_i.value = address
        self.dut.dat_i.value = data
        self.dut.sel_i.value = sel_mask
        
        # Wait for acknowledge or error
        while True:
            await RisingEdge(self.dut.clk_i)
            if self.dut.ack_o.value == 1 or self.dut.err_o.value == 1:
                break
                
        # Clear signals
        self.dut.cyc_i.value = 0
        self.dut.stb_i.value = 0
        self.dut.we_i.value = 0
        
        return self.dut.err_o.value == 0
        
    async def read_word(self, address):
        """Read a word from memory"""
        self.dut.cyc_i.value = 1
        self.dut.stb_i.value = 1
        self.dut.we_i.value = 0
        self.dut.adr_i.value = address
        self.dut.sel_i.value = 0xF
        
        # Wait for acknowledge or error
        while True:
            await RisingEdge(self.dut.clk_i)
            if self.dut.ack_o.value == 1 or self.dut.err_o.value == 1:
                break
                
        data = int(self.dut.dat_o.value) if self.dut.ack_o.value == 1 else None
        error = self.dut.err_o.value == 1
        
        # Clear signals
        self.dut.cyc_i.value = 0
        self.dut.stb_i.value = 0
        
        return data, error


@cocotb.test()
async def test_dmem_basic_write_read(dut):
    """Test basic data memory write and read operations"""
    
    tb = DataMemoryTB(dut)
    
    # Start clock
    cocotb.start_soon(Clock(dut.clk_i, 10, units="ns").start())
    
    dut._log.info("Testing basic data memory write/read operations")
    
    # Reset
    await tb.reset()
    
    # Test basic write/read cycle
    test_data = [
        (0x00000000, 0x12345678),
        (0x00000004, 0xDEADBEEF),
        (0x00000008, 0xCAFEBABE),
        (0x0000000C, 0xAAAABBBB),
        (0x00001000, 0x11223344),
    ]
    
    # Write test data
    for addr, data in test_data:
        success = await tb.write_word(addr, data)
        assert success, f"Write failed for address 0x{addr:08x}"
        
    # Read back and verify
    for addr, expected_data in test_data:
        read_data, error = await tb.read_word(addr)
        assert not error, f"Read error for address 0x{addr:08x}"
        assert read_data == expected_data, f"Data mismatch at 0x{addr:08x}: expected 0x{expected_data:08x}, got 0x{read_data:08x}"


@cocotb.test()
async def test_dmem_byte_access(dut):
    """Test byte-level access with select signals"""
    
    tb = DataMemoryTB(dut)
    
    # Start clock
    cocotb.start_soon(Clock(dut.clk_i, 10, units="ns").start())
    
    dut._log.info("Testing data memory byte access")
    
    # Reset
    await tb.reset()
    
    # Write individual bytes
    address = 0x00000010
    await tb.write_word(address, 0x11, 0x1)  # Write byte 0
    await tb.write_word(address, 0x2200, 0x2)  # Write byte 1
    await tb.write_word(address, 0x330000, 0x4)  # Write byte 2
    await tb.write_word(address, 0x44000000, 0x8)  # Write byte 3
    
    # Read back full word
    read_data, error = await tb.read_word(address)
    assert not error, "Read error for byte access test"
    assert read_data == 0x44332211, f"Byte access failed: got 0x{read_data:08x}, expected 0x44332211"


@cocotb.test()
async def test_dmem_halfword_access(dut):
    """Test halfword access with select signals"""
    
    tb = DataMemoryTB(dut)
    
    # Start clock
    cocotb.start_soon(Clock(dut.clk_i, 10, units="ns").start())
    
    dut._log.info("Testing data memory halfword access")
    
    # Reset
    await tb.reset()
    
    # Write halfwords
    address = 0x00000020
    await tb.write_word(address, 0x1234, 0x3)  # Write lower halfword
    await tb.write_word(address, 0x56780000, 0xC)  # Write upper halfword
    
    # Read back full word
    read_data, error = await tb.read_word(address)
    assert not error, "Read error for halfword access test"
    assert read_data == 0x56781234, f"Halfword access failed: got 0x{read_data:08x}, expected 0x56781234"


@cocotb.test()
async def test_dmem_out_of_bounds(dut):
    """Test out of bounds access error handling"""
    
    tb = DataMemoryTB(dut)
    
    # Start clock
    cocotb.start_soon(Clock(dut.clk_i, 10, units="ns").start())
    
    dut._log.info("Testing data memory out of bounds access")
    
    # Reset
    await tb.reset()
    
    # Test addresses beyond memory size
    out_of_bounds_addresses = [
        tb.MEM_SIZE * 4,        # Exactly at boundary
        tb.MEM_SIZE * 4 + 4,    # Just beyond
        0xFFFFFFFC,             # Maximum address
    ]
    
    for addr in out_of_bounds_addresses:
        # Test write
        success = await tb.write_word(addr, 0x12345678)
        assert not success, f"Write should fail for out-of-bounds address 0x{addr:08x}"
        
        # Test read
        read_data, error = await tb.read_word(addr)
        assert error, f"Read should error for out-of-bounds address 0x{addr:08x}"


@cocotb.test()
async def test_dmem_wishbone_protocol(dut):
    """Test Wishbone protocol compliance"""
    
    tb = DataMemoryTB(dut)
    
    # Start clock
    cocotb.start_soon(Clock(dut.clk_i, 10, units="ns").start())
    
    dut._log.info("Testing Wishbone protocol compliance")
    
    # Reset
    await tb.reset()
    
    # Test that ack_o is only asserted when cyc_i and stb_i are high
    dut.cyc_i.value = 0
    dut.stb_i.value = 0
    dut.we_i.value = 0
    dut.adr_i.value = 0
    await RisingEdge(dut.clk_i)
    assert dut.ack_o.value == 0, "ack_o should not be asserted without cyc_i/stb_i"
    
    # Test cyc_i without stb_i
    dut.cyc_i.value = 1
    dut.stb_i.value = 0
    await RisingEdge(dut.clk_i)
    assert dut.ack_o.value == 0, "ack_o should not be asserted without stb_i"
    
    # Test stb_i without cyc_i
    dut.cyc_i.value = 0
    dut.stb_i.value = 1
    await RisingEdge(dut.clk_i)
    assert dut.ack_o.value == 0, "ack_o should not be asserted without cyc_i"
    
    # Test proper handshake
    dut.cyc_i.value = 1
    dut.stb_i.value = 1
    dut.adr_i.value = 0
    await RisingEdge(dut.clk_i)
    assert dut.ack_o.value == 1, "ack_o should be asserted with valid cyc_i/stb_i"


@cocotb.test()
async def test_dmem_simultaneous_ack_err(dut):
    """Test that ack and err are never asserted simultaneously"""
    
    tb = DataMemoryTB(dut)
    
    # Start clock
    cocotb.start_soon(Clock(dut.clk_i, 10, units="ns").start())
    
    dut._log.info("Testing that ack and err are mutually exclusive")
    
    # Reset
    await tb.reset()
    
    # Test various scenarios
    test_addresses = [
        0x00000000,           # Valid address
        tb.MEM_SIZE * 4,      # Invalid address
        0x00001000,           # Valid address
        0xFFFFFFFC,           # Invalid address
    ]
    
    for addr in test_addresses:
        # Test read
        dut.cyc_i.value = 1
        dut.stb_i.value = 1
        dut.we_i.value = 0
        dut.adr_i.value = addr
        dut.sel_i.value = 0xF
        
        await RisingEdge(dut.clk_i)
        
        # Check mutual exclusion
        ack = dut.ack_o.value
        err = dut.err_o.value
        assert not (ack and err), f"ack_o and err_o both asserted for address 0x{addr:08x}"
        
        dut.cyc_i.value = 0
        dut.stb_i.value = 0


@cocotb.test()
async def test_dmem_reset_behavior(dut):
    """Test memory behavior during reset"""
    
    tb = DataMemoryTB(dut)
    
    # Start clock
    cocotb.start_soon(Clock(dut.clk_i, 10, units="ns").start())
    
    dut._log.info("Testing data memory reset behavior")
    
    # Reset
    await tb.reset()
    
    # Write some data
    await tb.write_word(0x00000000, 0x12345678)
    
    # Verify data is written
    read_data_1, error = await tb.read_word(0x00000000)
    assert not error and read_data_1 == 0x12345678, "Initial write failed"
    
    # Assert reset
    dut.rst_i.value = 1
    await RisingEdge(dut.clk_i)
    await RisingEdge(dut.clk_i)
    
    # Check outputs during reset
    assert dut.ack_o.value == 0, "ack_o should be 0 during reset"
    assert dut.err_o.value == 0, "err_o should be 0 during reset" 
    assert dut.dat_o.value == 0, "dat_o should be 0 during reset"
    
    # Release reset
    dut.rst_i.value = 0
    await RisingEdge(dut.clk_i)
    
    # Verify data is preserved (memory contents should survive reset)
    read_data_2, error = await tb.read_word(0x00000000)
    assert not error and read_data_2 == 0x12345678, "Data not preserved through reset"


@cocotb.test()
async def test_dmem_random_access_pattern(dut):
    """Test random access patterns to stress test the memory"""
    
    tb = DataMemoryTB(dut)
    
    # Start clock
    cocotb.start_soon(Clock(dut.clk_i, 10, units="ns").start())
    
    dut._log.info("Testing random access patterns")
    
    # Reset
    await tb.reset()
    
    # Generate random test data
    random.seed(0x12345678)  # Fixed seed for reproducibility
    test_data = {}
    
    # Perform random writes
    for _ in range(50):
        addr = random.randrange(0, (tb.MEM_SIZE * 4) - 4, 4)  # Word-aligned addresses
        data = random.randint(0, 0xFFFFFFFF)
        
        success = await tb.write_word(addr, data)
        assert success, f"Random write failed for address 0x{addr:08x}"
        test_data[addr] = data
    
    # Verify all written data
    for addr, expected_data in test_data.items():
        read_data, error = await tb.read_word(addr)
        assert not error, f"Random read error for address 0x{addr:08x}"
        assert read_data == expected_data, f"Random access data mismatch at 0x{addr:08x}: expected 0x{expected_data:08x}, got 0x{read_data:08x}" 