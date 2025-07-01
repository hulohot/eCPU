# Cocotb Dependency Fix

## Issue Identified

The CI was failing with:
```
ModuleNotFoundError: No module named 'cocotb_test'
```

## Root Cause

1. **Missing `cocotb-test` in requirements.txt** - Only `cocotb` was specified
2. **CI installing packages individually** instead of using requirements.txt
3. **No verification** that cocotb_test was properly installed

## Fixes Applied

### 1. Updated Requirements File
**File**: `verification/cocotb/requirements.txt`

**Before**:
```
cocotb>=1.8.0
```

**After**:
```
cocotb>=1.8.0
cocotb-test>=0.2.4
```

### 2. Fixed CI Installation Process
**File**: `.github/workflows/ci.yml`

**Before**:
```yaml
- name: Install Python dependencies
  run: |
    python -m pip install --upgrade pip
    pip install cocotb cocotb-test pytest pytest-cov pytest-xdist
```

**After**:
```yaml
- name: Install Python dependencies
  run: |
    python -m pip install --upgrade pip
    pip install wheel setuptools
    pip install -r verification/cocotb/requirements.txt
    pip install pytest-cov pytest-xdist
    echo "Installed packages:"
    pip list | grep -E "(cocotb|pytest)"
```

### 3. Added Installation Verification
```yaml
- name: Verify cocotb installation
  run: |
    python -c "import cocotb; print(f'cocotb version: {cocotb.__version__}')"
    python -c "import cocotb_test; print('cocotb_test imported successfully')"
```

### 4. Created Alternative Test Runner
**File**: `verification/cocotb/run_test.py`

- Standalone Python script that can run cocotb tests
- Better error handling and diagnostics
- Fallback when Makefile approach fails
- Absolute path resolution for RTL files

### 5. Added Fallback Logic
CI now tries both methods:
```yaml
if make test-alu; then
  echo "✅ ALU tests passed via Makefile"
else
  echo "⚠️ Makefile approach failed, trying alternative runner..."
  python run_test.py alu
fi
```

## Testing the Fix

To verify locally:
```bash
cd verification/cocotb

# Check installation
python -c "import cocotb_test; print('OK')"

# Test with Makefile
make test-alu

# Test with alternative runner
python run_test.py alu
```

## Expected CI Output

With the fix, you should see:
```
✅ cocotb version: 1.8.x
✅ cocotb_test imported successfully
✅ Attempting to run ALU tests...
✅ ALU tests passed via Makefile
```

## Benefits

- ✅ **Proper dependency management** using requirements.txt
- ✅ **Installation verification** before running tests
- ✅ **Better debugging** with package listing
- ✅ **Fallback mechanism** for robustness  
- ✅ **Clearer error messages** when things fail

The `ModuleNotFoundError: No module named 'cocotb_test'` should now be resolved! 🎯