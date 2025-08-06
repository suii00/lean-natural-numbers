# Mathlib自動変換システム
# 既存のLean証明コードをMathlib形式に自動変換

param(
    [string]$InputFile,
    [string]$OutputFile = "",
    [switch]$InPlace,
    [switch]$DryRun,
    [switch]$Verbose
)

# 変換ルール定義
$conversionRules = @{
    # Import変換ルール
    ImportMappings = @{
        "^-- import なし$" = "import Mathlib.Tactic.Basic"
        "^import Std" = "import Mathlib.Init.Logic"
        "^import Init" = "import Mathlib.Init"
    }
    
    # 定理名変換ルール
    TheoremMappings = @{
        "Nat\.add_zero" = "add_zero"
        "Nat\.zero_add" = "zero_add"
        "Nat\.add_comm" = "add_comm"
        "Nat\.add_assoc" = "add_assoc"
        "Nat\.mul_comm" = "mul_comm"
        "Int\.add_zero" = "add_zero"
        "Int\.zero_add" = "zero_add"
    }
    
    # 戦術変換ルール
    TacticMappings = @{
        "exact \⟨([^⟩]*)\⟩" = "use $1"
        "rfl" = "rfl"
        "simp \[([^\]]*)\]" = "simp [$1]"
        "omega" = "omega"  # 既に正しい場合はそのまま
    }
    
    # 構文変換ルール
    SyntaxMappings = @{
        # 型注釈の修正
        ": Nat" = ": ℕ"
        ": Int" = ": ℤ"
        ": Real" = ": ℝ"
        
        # Unicode記号の統一
        "\\bNat\\b" = "ℕ"
        "\\bInt\\b" = "ℤ"
        "\\bReal\\b" = "ℝ"
    }
    
    # エラーパターン解決ルール
    ErrorFixRules = @{
        "unknown tactic 'use'" = @{
            RequiredImport = "import Mathlib.Tactic.Use"
            Alternative = "exact ⟨⟩"
        }
        "unknown tactic 'ring'" = @{
            RequiredImport = "import Mathlib.Tactic.Ring"
            Alternative = "simp [add_mul, mul_add]"
        }
        "unknown tactic 'omega'" = @{
            RequiredImport = "import Mathlib.Tactic.Omega"
            Alternative = "simp [Nat.add_zero, Nat.zero_add]"
        }
        "unknown identifier 'Even'" = @{
            RequiredImport = "import Mathlib.Data.Nat.Parity"
            Alternative = "∃ k, n = 2 * k"
        }
    }
}

function Convert-ImportStatements {
    param([string[]]$Lines)
    
    $convertedLines = @()
    $hasImports = $false
    
    foreach ($line in $Lines) {
        $converted = $line
        
        foreach ($pattern in $conversionRules.ImportMappings.Keys) {
            if ($line -match $pattern) {
                $converted = $conversionRules.ImportMappings[$pattern]
                $hasImports = $true
                if ($Verbose) { 
                    Write-Host "Import変換: '$line' -> '$converted'" -ForegroundColor Yellow 
                }
                break
            }
        }
        
        $convertedLines += $converted
    }
    
    # 基本importが不足している場合は追加
    if (-not $hasImports -and $convertedLines -notcontains "import Mathlib.Tactic.Basic") {
        $convertedLines = @("import Mathlib.Tactic.Basic", "") + $convertedLines
        if ($Verbose) { 
            Write-Host "基本import追加: import Mathlib.Tactic.Basic" -ForegroundColor Green 
        }
    }
    
    return $convertedLines
}

function Convert-TheoremNames {
    param([string[]]$Lines)
    
    $convertedLines = @()
    
    foreach ($line in $Lines) {
        $converted = $line
        
        foreach ($pattern in $conversionRules.TheoremMappings.Keys) {
            if ($line -match $pattern) {
                $replacement = $conversionRules.TheoremMappings[$pattern]
                $converted = $line -replace $pattern, $replacement
                if ($Verbose) { 
                    Write-Host "定理名変換: '$line' -> '$converted'" -ForegroundColor Cyan 
                }
            }
        }
        
        $convertedLines += $converted
    }
    
    return $convertedLines
}

function Convert-Tactics {
    param([string[]]$Lines)
    
    $convertedLines = @()
    
    foreach ($line in $Lines) {
        $converted = $line
        
        foreach ($pattern in $conversionRules.TacticMappings.Keys) {
            if ($line -match $pattern) {
                $replacement = $conversionRules.TacticMappings[$pattern]
                $converted = $line -replace $pattern, $replacement
                if ($Verbose) { 
                    Write-Host "戦術変換: '$line' -> '$converted'" -ForegroundColor Magenta 
                }
            }
        }
        
        $convertedLines += $converted
    }
    
    return $convertedLines
}

function Convert-Syntax {
    param([string[]]$Lines)
    
    $convertedLines = @()
    
    foreach ($line in $Lines) {
        $converted = $line
        
        foreach ($pattern in $conversionRules.SyntaxMappings.Keys) {
            if ($line -match $pattern) {
                $replacement = $conversionRules.SyntaxMappings[$pattern]
                $converted = $line -replace $pattern, $replacement
                if ($Verbose) { 
                    Write-Host "構文変換: '$line' -> '$converted'" -ForegroundColor Blue 
                }
            }
        }
        
        $convertedLines += $converted
    }
    
    return $convertedLines
}

function Test-ConvertedFile {
    param([string]$FilePath)
    
    Write-Host "変換結果テスト: $FilePath" -ForegroundColor Yellow
    
    try {
        $output = & lake env lean $FilePath 2>&1
        $success = $LASTEXITCODE -eq 0
        
        if ($success) {
            Write-Host "✅ コンパイル成功" -ForegroundColor Green
            return @{Success = $true; Errors = @()}
        } else {
            Write-Host "❌ コンパイルエラー" -ForegroundColor Red
            $errors = $output | Where-Object { $_ -match "error:" }
            return @{Success = $false; Errors = $errors}
        }
    } catch {
        Write-Host "❌ テスト実行エラー: $_" -ForegroundColor Red
        return @{Success = $false; Errors = @($_.Exception.Message)}
    }
}

function Fix-ConversionErrors {
    param([string[]]$Lines, [string[]]$Errors)
    
    $fixedLines = $Lines
    $appliedFixes = @()
    
    foreach ($error in $Errors) {
        foreach ($pattern in $conversionRules.ErrorFixRules.Keys) {
            if ($error -match $pattern) {
                $fix = $conversionRules.ErrorFixRules[$pattern]
                
                # Import追加が必要な場合
                if ($fix.RequiredImport) {
                    if ($fixedLines[0] -notmatch "import.*") {
                        $fixedLines = @($fix.RequiredImport, "") + $fixedLines
                    } else {
                        $fixedLines = @($fixedLines[0], $fix.RequiredImport) + $fixedLines[1..($fixedLines.Length-1)]
                    }
                    $appliedFixes += "Import追加: $($fix.RequiredImport)"
                }
                
                # 代替構文置換
                if ($fix.Alternative) {
                    # エラー箇所を特定して置換（簡易版）
                    for ($i = 0; $i -lt $fixedLines.Length; $i++) {
                        if ($fixedLines[$i] -match $pattern) {
                            $fixedLines[$i] = $fixedLines[$i] -replace $pattern, $fix.Alternative
                            $appliedFixes += "代替構文: $($fix.Alternative)"
                        }
                    }
                }
            }
        }
    }
    
    if ($appliedFixes.Count -gt 0) {
        Write-Host "適用された修正:" -ForegroundColor Green
        $appliedFixes | ForEach-Object { Write-Host "  - $_" -ForegroundColor Gray }
    }
    
    return $fixedLines
}

# メイン変換処理
function Convert-LeanFile {
    param([string]$FilePath)
    
    if (-not (Test-Path $FilePath)) {
        Write-Error "ファイルが見つかりません: $FilePath"
        return
    }
    
    Write-Host "🔄 Lean証明ファイル変換開始: $FilePath" -ForegroundColor Green
    
    # ファイル読み込み
    $originalLines = Get-Content $FilePath -Encoding UTF8
    Write-Host "原本: $($originalLines.Count)行" -ForegroundColor Gray
    
    # 段階的変換
    Write-Host "📝 段階1: Import文変換" -ForegroundColor Yellow
    $lines = Convert-ImportStatements $originalLines
    
    Write-Host "📝 段階2: 定理名変換" -ForegroundColor Yellow  
    $lines = Convert-TheoremNames $lines
    
    Write-Host "📝 段階3: 戦術変換" -ForegroundColor Yellow
    $lines = Convert-Tactics $lines
    
    Write-Host "📝 段階4: 構文変換" -ForegroundColor Yellow
    $lines = Convert-Syntax $lines
    
    # 出力ファイル決定
    $outputPath = if ($OutputFile) { 
        $OutputFile 
    } elseif ($InPlace) { 
        $FilePath 
    } else { 
        $FilePath -replace "\.lean$", "_mathlib.lean" 
    }
    
    if ($DryRun) {
        Write-Host "🔍 DryRun: 変換結果プレビュー" -ForegroundColor Cyan
        $lines | Select-Object -First 10 | ForEach-Object { Write-Host "  $_" -ForegroundColor Gray }
        Write-Host "  ... (省略) ..." -ForegroundColor Gray
        Write-Host "出力先: $outputPath" -ForegroundColor Gray
        return
    }
    
    # 一時ファイルに保存してテスト
    $tempFile = [System.IO.Path]::GetTempFileName() + ".lean"
    $lines | Out-File -FilePath $tempFile -Encoding UTF8
    
    Write-Host "🧪 段階5: 変換結果テスト" -ForegroundColor Yellow
    $testResult = Test-ConvertedFile $tempFile
    
    # エラーがある場合は修正を試行
    if (-not $testResult.Success -and $testResult.Errors.Count -gt 0) {
        Write-Host "🔧 段階6: エラー修正" -ForegroundColor Yellow
        $lines = Fix-ConversionErrors $lines $testResult.Errors
        
        # 修正版を再テスト
        $lines | Out-File -FilePath $tempFile -Encoding UTF8
        $retestResult = Test-ConvertedFile $tempFile
        
        if ($retestResult.Success) {
            Write-Host "✅ エラー修正成功" -ForegroundColor Green
        } else {
            Write-Host "⚠️ 一部エラーが残存:" -ForegroundColor Yellow
            $retestResult.Errors | ForEach-Object { Write-Host "  $_" -ForegroundColor Red }
        }
    }
    
    # 最終出力
    $lines | Out-File -FilePath $outputPath -Encoding UTF8
    Remove-Item $tempFile -ErrorAction SilentlyContinue
    
    Write-Host "✅ 変換完了: $outputPath" -ForegroundColor Green
    Write-Host "変換後: $($lines.Count)行" -ForegroundColor Gray
}

# スクリプト実行
if ($InputFile) {
    Convert-LeanFile $InputFile
} else {
    Write-Host "使用方法:"
    Write-Host "  .\MathLibConverter.ps1 -InputFile 'path\to\file.lean' [-OutputFile 'output.lean'] [-Verbose] [-DryRun]"
    Write-Host ""
    Write-Host "オプション:"
    Write-Host "  -InputFile    : 変換対象ファイル"
    Write-Host "  -OutputFile   : 出力ファイル（省略時は元ファイル名_mathlib.lean）"
    Write-Host "  -InPlace      : 元ファイルを直接更新"  
    Write-Host "  -DryRun       : 実際の変換は行わず、プレビューのみ"
    Write-Host "  -Verbose      : 詳細ログ出力"
}