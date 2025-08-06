# Debug file creation

Write-Host "Debug File Creation" -ForegroundColor Green

# Create test file with different methods
$content = "theorem test : True := trivial"

# Method 1: Out-File with UTF8
$content | Out-File -FilePath "test1.lean" -Encoding UTF8

# Method 2: Set-Content  
Set-Content -Path "test2.lean" -Value $content -Encoding UTF8

# Method 3: [System.IO.File]::WriteAllText
[System.IO.File]::WriteAllText("$(pwd)\test3.lean", $content)

Write-Host "Files created. Testing each..." -ForegroundColor Yellow

$testFiles = @("simple_test.lean", "test1.lean", "test2.lean", "test3.lean")

foreach ($file in $testFiles) {
    if (Test-Path $file) {
        Write-Host "`nTesting: $file" -ForegroundColor Yellow
        
        # Show file size and first few bytes
        $fileInfo = Get-Item $file
        Write-Host "  Size: $($fileInfo.Length) bytes" -ForegroundColor Gray
        
        # Show hex dump of first few bytes
        $bytes = [System.IO.File]::ReadAllBytes($file)
        $hexString = ($bytes[0..10] | ForEach-Object { $_.ToString("X2") }) -join " "
        Write-Host "  First bytes (hex): $hexString" -ForegroundColor Gray
        
        # Show raw content
        $rawContent = [System.IO.File]::ReadAllText($file)
        Write-Host "  Content length: $($rawContent.Length)" -ForegroundColor Gray
        Write-Host "  Content: '$rawContent'" -ForegroundColor Gray
        
        # Test with lean
        $output = & lean $file 2>&1
        $success = $LASTEXITCODE -eq 0
        
        if ($success) {
            Write-Host "  LEAN: SUCCESS" -ForegroundColor Green
        } else {
            Write-Host "  LEAN: FAILED" -ForegroundColor Red
            $output | ForEach-Object {
                Write-Host "    $_" -ForegroundColor Red
            }
        }
    }
}

# Cleanup
Remove-Item "test*.lean" -ErrorAction SilentlyContinue

Write-Host "`nDebug complete!" -ForegroundColor Green