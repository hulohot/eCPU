#!/usr/bin/env python3
"""
Simple test runner for cocotb tests.
Alternative to Makefile-based execution.
"""

import os
import sys
from pathlib import Path

def run_test(test_module, rtl_files, toplevel, simulator="verilator"):
    """Run a single cocotb test"""
    try:
        from cocotb_test.simulator import run
        
        print(f"Running {test_module} test with {simulator}")
        print(f"RTL files: {rtl_files}")
        print(f"Toplevel: {toplevel}")
        
        # Convert relative paths to absolute
        base_dir = Path(__file__).parent
        abs_rtl_files = []
        for rtl_file in rtl_files:
            abs_path = (base_dir / rtl_file).resolve()
            if abs_path.exists():
                abs_rtl_files.append(str(abs_path))
            else:
                print(f"ERROR: RTL file not found: {abs_path}")
                return False
        
        extra_args = ["--trace", "--trace-structs"] if simulator == "verilator" else []
        
        run(
            verilog_sources=abs_rtl_files,
            toplevel=toplevel,
            module=test_module,
            simulator=simulator,
            extra_args=extra_args
        )
        
        print(f"✅ {test_module} test passed")
        return True
        
    except ImportError as e:
        print(f"❌ Import error: {e}")
        print("Make sure cocotb and cocotb-test are installed:")
        print("  pip install cocotb cocotb-test")
        return False
    except Exception as e:
        print(f"❌ {test_module} test failed: {e}")
        return False


def main():
    """Main test runner"""
    if len(sys.argv) < 2:
        print("Usage: python run_test.py <test_name>")
        print("Available tests: alu, regfile, instruction_memory, data_memory, fetch, decode")
        return 1
    
    test_name = sys.argv[1].lower()
    
    # Test configurations
    tests = {
        "alu": {
            "module": "test_alu",
            "rtl_files": ["../../rtl/core/alu.sv"],
            "toplevel": "alu"
        },
        "regfile": {
            "module": "test_regfile", 
            "rtl_files": ["../../rtl/core/regfile.sv"],
            "toplevel": "regfile"
        },
        "instruction_memory": {
            "module": "test_instruction_memory",
            "rtl_files": ["../../rtl/memory/instruction_memory.sv"],
            "toplevel": "instruction_memory"
        },
        "data_memory": {
            "module": "test_data_memory",
            "rtl_files": ["../../rtl/memory/data_memory.sv"],
            "toplevel": "data_memory"
        },
        "fetch": {
            "module": "test_fetch",
            "rtl_files": ["../../rtl/core/fetch.sv"],
            "toplevel": "fetch"
        },
        "decode": {
            "module": "test_decode",
            "rtl_files": ["../../rtl/core/decode.sv"],
            "toplevel": "decode"
        }
    }
    
    if test_name not in tests:
        print(f"❌ Unknown test: {test_name}")
        print(f"Available tests: {', '.join(tests.keys())}")
        return 1
    
    test_config = tests[test_name]
    
    # Check if test module exists
    test_file = Path(f"{test_config['module']}.py")
    if not test_file.exists():
        print(f"❌ Test file not found: {test_file}")
        return 1
    
    success = run_test(
        test_config["module"],
        test_config["rtl_files"], 
        test_config["toplevel"]
    )
    
    return 0 if success else 1


if __name__ == "__main__":
    sys.exit(main())