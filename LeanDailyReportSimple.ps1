# Lean証明進捗日報システム (シンプル版)

param(
    [Parameter(Mandatory=$false)]
    [string]$ProjectDir = ".",
    
    [Parameter(Mandatory=$false)]
    [string]$OutputDir = "daily-reports",
    
    [Parameter(Mandatory=$false)]
    [switch]$ShowHistory = $false
)

Write-Host "Lean Daily Report System" -ForegroundColor Cyan

if ($ShowHistory) {
    if (Test-Path $OutputDir) {
        $reports = Get-ChildItem -Path $OutputDir -Filter "*.md" | Sort-Object Name -Descending
        Write-Host "`n=== Report History ===" -ForegroundColor Green
        foreach ($report in $reports) {
            Write-Host "  $($report.Name)" -ForegroundColor Yellow
        }
    } else {
        Write-Host "No reports found" -ForegroundColor Yellow
    }
    exit
}

Write-Host "Analyzing Lean proofs..." -ForegroundColor Yellow

# Find all Lean files modified today
$today = Get-Date -Format "yyyy-MM-dd"
$leanFiles = Get-ChildItem -Path $ProjectDir -Recurse -Filter "*.lean"
$modifiedFiles = @()
$allProofs = @()
$allTactics = @()

foreach ($file in $leanFiles) {
    if ($file.LastWriteTime.ToString("yyyy-MM-dd") -eq $today) {
        $modifiedFiles += $file
        Write-Host "  Found modified file: $($file.Name)" -ForegroundColor Gray
        
        # Parse the file content
        $content = Get-Content $file.FullName
        $lineNum = 0
        
        foreach ($line in $content) {
            $lineNum++
            
            # Find theorems, lemmas, and examples
            if ($line -match '^\s*(theorem|lemma|example)\s+([^:]+):') {
                $proof = @{
                    Type = $matches[1]
                    Name = $matches[2].Trim()
                    File = $file.Name
                    Line = $lineNum
                }
                $allProofs += $proof
            }
            
            # Find tactics
            $tactics = @('exact', 'rw', 'simp', 'apply', 'intro', 'cases', 'induction', 
                        'constructor', 'use', 'have', 'calc', 'ring', 'norm_num', 
                        'rfl', 'sorry', 'obtain', 'left', 'right')
            
            foreach ($tactic in $tactics) {
                if ($line -match "\b$tactic\b") {
                    $allTactics += $tactic
                }
            }
        }
    }
}

# Count tactic usage
$tacticCounts = @{}
foreach ($tactic in $allTactics) {
    if ($tacticCounts.ContainsKey($tactic)) {
        $tacticCounts[$tactic]++
    } else {
        $tacticCounts[$tactic] = 1
    }
}

# Sort tactics by usage
$sortedTactics = $tacticCounts.GetEnumerator() | Sort-Object Value -Descending

# Create output directory if needed
if (!(Test-Path $OutputDir)) {
    New-Item -ItemType Directory -Path $OutputDir | Out-Null
}

# Generate the report
$reportFile = Join-Path $OutputDir "report-$today.md"
$report = "# Lean Daily Report - $today`n`n"
$report += "## Summary`n`n"
$report += "- Modified files: $($modifiedFiles.Count)`n"
$report += "- Proofs completed: $($allProofs.Count)`n"
$report += "- Unique tactics used: $($tacticCounts.Count)`n"
$report += "- Total tactic usages: $($allTactics.Count)`n`n"

$report += "## Completed Proofs`n`n"
if ($allProofs.Count -gt 0) {
    foreach ($proof in $allProofs) {
        $report += "### $($proof.Name)`n"
        $report += "- Type: $($proof.Type)`n"
        $report += "- File: $($proof.File):$($proof.Line)`n`n"
    }
} else {
    $report += "No proofs completed today.`n`n"
}

$report += "## Tactic Usage Statistics`n`n"
if ($sortedTactics.Count -gt 0) {
    $report += "| Tactic | Count |`n"
    $report += "|--------|-------|`n"
    foreach ($tactic in $sortedTactics) {
        $report += "| ``$($tactic.Key)`` | $($tactic.Value) |`n"
    }
} else {
    $report += "No tactics used today.`n"
}

$report += "`n## Learning Concepts`n`n"

# Identify concepts based on proofs and tactics
$concepts = @()
if ($allTactics -contains 'induction') { $concepts += "Mathematical Induction" }
if ($allTactics -contains 'cases') { $concepts += "Case Analysis" }
if ($allTactics -contains 'ring') { $concepts += "Ring Theory" }
if ($allTactics -contains 'calc') { $concepts += "Calculational Proofs" }
if ($allTactics -contains 'obtain') { $concepts += "Existential Elimination" }
if ($allTactics -contains 'use') { $concepts += "Existential Introduction" }
if ($allTactics -contains 'constructor') { $concepts += "Constructive Proofs" }

if ($concepts.Count -gt 0) {
    foreach ($concept in $concepts) {
        $report += "- $concept`n"
    }
} else {
    $report += "Continue practicing basic proof techniques.`n"
}

$report += "`n---`n"
$report += "*Generated at $(Get-Date -Format 'yyyy-MM-dd HH:mm:ss')*`n"

# Save the report
$report | Out-File -FilePath $reportFile -Encoding UTF8

Write-Host "`nReport generated successfully!" -ForegroundColor Green
Write-Host "Location: $reportFile" -ForegroundColor White

# Display summary
Write-Host "`nToday's Progress:" -ForegroundColor Magenta
Write-Host "  Proofs: $($allProofs.Count)" -ForegroundColor Yellow
Write-Host "  Tactics: $($tacticCounts.Count) types, $($allTactics.Count) uses" -ForegroundColor Yellow

if ($sortedTactics.Count -gt 0) {
    $topTactic = $sortedTactics | Select-Object -First 1
    Write-Host "  Most used: $($topTactic.Key) ($($topTactic.Value) times)" -ForegroundColor Cyan
}