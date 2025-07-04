#!/bin/bash

# eCPU CI Test Script
# This script helps test the CI pipeline by creating intentionally failing scenarios

set -e

echo "🧪 eCPU CI Test Script"
echo "======================"

# Function to create test files that should fail CI
create_failing_test() {
    local test_type=$1
    
    case $test_type in
        "lint-python")
            echo "Creating Python linting failure..."
            mkdir -p scripts/
            cat > scripts/test_fail.py << 'EOF'
# This file intentionally has linting issues
import os,sys
def bad_function( ):
    x=1+2
    if x==3:
        print("bad formatting")
    return x
EOF
            echo "✅ Created scripts/test_fail.py with linting issues"
            ;;
            
        "lint-sv")
            echo "Creating SystemVerilog linting failure..."
            mkdir -p rtl/test/
            cat > rtl/test/bad_module.sv << 'EOF'
// This module has intentional syntax errors
module bad_module
    input wire clk,
    input wire rst,
    output reg [31:0] data
);

// Missing parentheses and semicolon
always @(posedge clk
    if (rst
        data <= 32'h0;
    else
        data <= data + 1;

endmodule
EOF
            echo "✅ Created rtl/test/bad_module.sv with syntax errors"
            ;;
            
        "test-failure")
            echo "Creating failing cocotb test..."
            mkdir -p verification/cocotb/
            cat > verification/cocotb/test_fail.py << 'EOF'
import cocotb
from cocotb.triggers import Timer

@cocotb.test()
async def test_intentional_failure(dut):
    """This cocotb test is designed to fail"""
    await Timer(1, units="ns")
    assert False, "This cocotb test intentionally fails to test CI"

@cocotb.test()
async def test_another_failure(dut):
    """Another failing cocotb test"""
    await Timer(1, units="ns") 
    assert 1 == 2, "Math is still broken in cocotb!"
EOF
            
            # Also create a simple failing RTL module for the test
            mkdir -p rtl/test/
            cat > rtl/test/fail_module.sv << 'EOF'
module fail_module (
    input wire clk_i,
    input wire rst_i,
    output wire [31:0] data_o
);
    assign data_o = 32'hDEADBEEF;
endmodule
EOF
            echo "✅ Created verification/cocotb/test_fail.py with failing cocotb tests"
            echo "✅ Created rtl/test/fail_module.sv for testing"
            ;;
            
        "clean")
            echo "Cleaning up test files..."
            rm -f scripts/test_fail.py
            rm -f rtl/test/bad_module.sv
            rm -f rtl/test/fail_module.sv
            rm -f verification/cocotb/test_fail.py
            rmdir scripts/ 2>/dev/null || true
            rmdir rtl/test/ 2>/dev/null || true
            echo "✅ Cleaned up test files"
            ;;
            
        *)
            echo "❌ Unknown test type: $test_type"
            echo "Available types: lint-python, lint-sv, test-failure, clean"
            exit 1
            ;;
    esac
}

# Function to run local CI checks
run_local_checks() {
    echo "🔍 Running local CI checks..."
    
    # Check if we have the necessary tools
    echo "Checking required tools..."
    
    if ! command -v python3 &> /dev/null; then
        echo "❌ Python3 not found"
        return 1
    fi
    
    if ! command -v verilator &> /dev/null; then
        echo "⚠️  Verilator not found - skipping SystemVerilog checks"
    else
        echo "✅ Verilator found"
    fi
    
    # Install Python tools if needed
    echo "Installing Python tools..."
    pip3 install --user black flake8 isort 2>/dev/null || echo "⚠️  Could not install Python tools"
    
    # Run Python linting
    if [ -d "verification/" ] || [ -d "scripts/" ]; then
        echo "Running Python formatting check..."
        if command -v black &> /dev/null; then
            black --check verification/ scripts/ 2>/dev/null || echo "❌ Black formatting check failed"
        fi
        
        echo "Running Python linting..."
        if command -v flake8 &> /dev/null; then
            flake8 verification/ scripts/ 2>/dev/null || echo "❌ Flake8 linting failed"
        fi
    fi
    
    # Run SystemVerilog linting  
    if command -v verilator &> /dev/null; then
        echo "Running SystemVerilog linting..."
        find rtl/ -name "*.sv" -o -name "*.v" | head -5 | while read file; do
            echo "  Checking $file"
            verilator --lint-only -Wall "$file" || echo "❌ Lint failed for $file"
        done
    fi
    
    echo "✅ Local checks completed"
}

# Function to show CI status
show_ci_status() {
    echo "📊 CI Configuration Status"
    echo "=========================="
    
    if [ -f ".github/workflows/ci.yml" ]; then
        echo "✅ CI workflow file exists"
        
        # Check for problematic continue-on-error
        if grep -q "continue-on-error: true" .github/workflows/ci.yml; then
            echo "⚠️  Found continue-on-error in CI (check if this is intentional)"
            grep -n "continue-on-error: true" .github/workflows/ci.yml
        else
            echo "✅ No problematic continue-on-error found"
        fi
    else
        echo "❌ No CI workflow file found"
    fi
    
    if [ -f ".github/branch-protection.md" ]; then
        echo "✅ Branch protection documentation exists"
    else
        echo "❌ No branch protection documentation found"
    fi
    
    echo ""
    echo "📋 Required status checks:"
    echo "  - Code Quality & Linting"
    echo "  - Unit Tests" 
    echo "  - Synthesis Check"
    echo "  - Documentation Build"
}

# Main script logic
case "${1:-help}" in
    "fail-lint-python")
        create_failing_test "lint-python"
        ;;
    "fail-lint-sv") 
        create_failing_test "lint-sv"
        ;;
    "fail-tests")
        create_failing_test "test-failure"
        ;;
    "clean")
        create_failing_test "clean"
        ;;
    "check")
        run_local_checks
        ;;
    "status")
        show_ci_status
        ;;
    "help"|*)
        echo "Usage: $0 <command>"
        echo ""
        echo "Commands:"
        echo "  fail-lint-python  Create Python linting failures for testing"
        echo "  fail-lint-sv      Create SystemVerilog linting failures"  
        echo "  fail-tests        Create failing unit tests"
        echo "  clean             Remove all test failure files"
        echo "  check             Run local CI checks"
        echo "  status            Show CI configuration status"
        echo "  help              Show this help message"
        echo ""
        echo "Example workflow to test CI:"
        echo "  1. $0 status                 # Check current CI setup"
        echo "  2. $0 fail-lint-python      # Create failing code"
        echo "  3. git add -A && git commit  # Commit the failing code"
        echo "  4. git push                  # Push to trigger CI (should fail)"
        echo "  5. $0 clean                 # Clean up the failing code"
        echo "  6. git add -A && git commit  # Commit the cleanup"
        echo "  7. git push                  # Push again (should pass)"
        ;;
esac