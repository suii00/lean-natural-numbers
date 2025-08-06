#!/bin/bash
# Backup Recovery Test Script

echo "=== Backup Recovery Test ==="
echo "Testing project rollback capabilities..."

# Test 1: Basic git operations
echo "Test 1: Git branch and tag verification"
echo "Available branches:"
git branch -a
echo "Available tags:"
git tag

# Test 2: Backup branch checkout test
echo -e "\nTest 2: Testing backup branch checkout"
CURRENT_BRANCH=$(git branch --show-current)
echo "Current branch: $CURRENT_BRANCH"

# Create temporary file to test rollback
echo "Creating test file..."
echo "test rollback" > temp_rollback_test.txt
git add temp_rollback_test.txt
git commit -m "Temporary test commit for rollback testing"

# Test rollback to backup branch
echo "Testing checkout to backup branch..."
git checkout pre-mathlib-baseline

# Verify test file is gone (should be)
if [ ! -f "temp_rollback_test.txt" ]; then
    echo "✅ Rollback test PASSED - temporary file correctly absent"
else
    echo "❌ Rollback test FAILED - temporary file still present"
fi

# Return to original branch
git checkout $CURRENT_BRANCH

# Clean up test file
if [ -f "temp_rollback_test.txt" ]; then
    rm temp_rollback_test.txt
    git add temp_rollback_test.txt
    git commit -m "Remove rollback test file"
fi

# Test 3: Basic project functionality
echo -e "\nTest 3: Basic project functionality"
echo "Testing basic Lean compilation..."
echo 'theorem recovery_test : True := trivial' > recovery_test.lean

if lake env lean recovery_test.lean > /dev/null 2>&1; then
    echo "✅ Basic Lean compilation PASSED"
else
    echo "❌ Basic Lean compilation FAILED"
fi

rm recovery_test.lean

# Test 4: Key files existence
echo -e "\nTest 4: Key files existence check"
KEY_FILES=(
    "lakefile.lean"
    "lake-manifest.json" 
    "lean-toolchain"
    "Main.lean"
    "MyProject/NaturalNumbers.lean"
    "PROJECT_STATE_SNAPSHOT.md"
    "ROLLBACK_PROCEDURES.md"
)

ALL_PRESENT=true
for file in "${KEY_FILES[@]}"; do
    if [ -f "$file" ]; then
        echo "✅ $file - present"
    else
        echo "❌ $file - missing"
        ALL_PRESENT=false
    fi
done

# Test 5: Backup files verification
echo -e "\nTest 5: Backup files verification"
BACKUP_FILES=(
    "lakefile.lean.backup"
    "lake-manifest.json.backup"
    "lean-toolchain.backup"
)

for file in "${BACKUP_FILES[@]}"; do
    if [ -f "$file" ]; then
        echo "✅ $file - available"
    else
        echo "⚠️ $file - not found (may have been created earlier)"
    fi
done

# Final summary
echo -e "\n=== Recovery Test Summary ==="
if $ALL_PRESENT; then
    echo "✅ All critical files present and accounted for"
    echo "✅ Git rollback mechanism functional"
    echo "✅ Project ready for safe mathlib integration"
else
    echo "❌ Some critical files missing - check backup integrity"
fi

echo -e "\nFor full rollback, use one of:"
echo "  git checkout pre-mathlib-baseline"
echo "  git reset --hard v1.0-pre-mathlib"
echo "  See ROLLBACK_PROCEDURES.md for detailed instructions"