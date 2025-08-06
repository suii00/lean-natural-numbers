# Mathlib対話的エラー修正システム
# 変換エラーを段階的に解決

param(
    [string]$InputFile,
    [switch]$AutoFix,
    [int]$MaxIterations = 5
)

# 高度なエラー解決パターン
$advancedErrorPatterns = @{
    # Import関連エラー
    "object file.*\.olean.*does not exist" = @{
        Type = "MissingImport"
        Solutions = @(
            @{Action = "AddImport"; Import = "Mathlib.Data.Nat.Basic"},
            @{Action = "AddImport"; Import = "Mathlib.Tactic.Basic"},
            @{Action = "BuildDependency"; Target = "Std"}
        )
    }
    
    # 戦術エラー
    "unknown tactic '(\w+)'" = @{
        Type = "UnknownTactic"
        Solutions = @(
            @{Action = "ReplaceStrategy"; Mappings = @{
                "use" = "exact ⟨⟩"
                "ring" = "simp [add_mul, mul_add, mul_comm]"
                "omega" = "simp [add_zero, zero_add]"
                "norm_num" = "rfl"
            }}
        )
    }
    
    # 型エラー
    "type mismatch.*expected.*ℕ.*got.*Nat" = @{
        Type = "TypeMismatch"
        Solutions = @(
            @{Action = "ReplaceAll"; From = "Nat"; To = "ℕ"},
            @{Action = "AddImport"; Import = "Mathlib.Data.Nat.Notation"}
        )
    }
    
    # 識別子エラー
    "unknown identifier '([^']+)'" = @{
        Type = "UnknownIdentifier"
        Solutions = @(
            @{Action = "LookupTheorem"; Name = "$1"},
            @{Action = "AddImport"; Import = "Mathlib.Data.Nat.Basic"}
        )
    }
}

function Analyze-CompilationError {
    param([string]$ErrorOutput)
    
    $errors = @()
    $lines = $ErrorOutput -split "`n"
    
    foreach ($line in $lines) {
        if ($line -match "error:") {
            $errorInfo = @{
                Line = $line
                Type = "Unknown"
                Solutions = @()
                Confidence = 0
            }
            
            foreach ($pattern in $advancedErrorPatterns.Keys) {
                if ($line -match $pattern) {
                    $solution = $advancedErrorPatterns[$pattern]
                    $errorInfo.Type = $solution.Type
                    $errorInfo.Solutions = $solution.Solutions
                    $errorInfo.Confidence = 0.8
                    break
                }
            }
            
            $errors += $errorInfo
        }
    }
    
    return $errors
}

function Apply-ErrorSolution {
    param([string[]]$FileLines, [hashtable]$Solution, [string]$ErrorLine)
    
    $modifiedLines = $FileLines
    $applied = $false
    
    switch ($Solution.Action) {
        "AddImport" {
            # Import文を適切な位置に追加
            $importLine = "import $($Solution.Import)"
            
            # 既存のimport文を探して追加
            $importIndex = -1
            for ($i = 0; $i -lt $modifiedLines.Length; $i++) {
                if ($modifiedLines[$i] -match "^import") {
                    $importIndex = $i
                }
            }
            
            if ($importIndex -ge 0) {
                # 最後のimport文の後に追加
                $modifiedLines = $modifiedLines[0..$importIndex] + $importLine + $modifiedLines[($importIndex+1)..($modifiedLines.Length-1)]
            } else {
                # ファイル先頭に追加
                $modifiedLines = @($importLine, "") + $modifiedLines
            }
            
            $applied = $true
            Write-Host "  ✅ Import追加: $importLine" -ForegroundColor Green
        }
        
        "ReplaceStrategy" {
            # 戦術置換
            foreach ($from in $Solution.Mappings.Keys) {
                $to = $Solution.Mappings[$from]
                
                for ($i = 0; $i -lt $modifiedLines.Length; $i++) {
                    if ($modifiedLines[$i] -match "\b$from\b") {
                        $modifiedLines[$i] = $modifiedLines[$i] -replace "\b$from\b", $to
                        $applied = $true
                        Write-Host "  ✅ 戦術置換: $from -> $to" -ForegroundColor Green
                    }
                }
            }
        }
        
        "ReplaceAll" {
            # 全体置換
            $from = $Solution.From
            $to = $Solution.To
            
            for ($i = 0; $i -lt $modifiedLines.Length; $i++) {
                if ($modifiedLines[$i] -match $from) {
                    $modifiedLines[$i] = $modifiedLines[$i] -replace $from, $to
                    $applied = $true
                }
            }
            
            if ($applied) {
                Write-Host "  ✅ 全体置換: $from -> $to" -ForegroundColor Green
            }
        }
        
        "LookupTheorem" {
            # 定理名検索（簡易版）
            $theoremName = $Solution.Name
            $commonMappings = @{
                "Nat.add_zero" = "add_zero"
                "Nat.zero_add" = "zero_add" 
                "Nat.add_comm" = "add_comm"
                "Even" = "Even"  # Mathlib.Data.Nat.Parityが必要
            }
            
            if ($commonMappings.ContainsKey($theoremName)) {
                $replacement = $commonMappings[$theoremName]
                
                for ($i = 0; $i -lt $modifiedLines.Length; $i++) {
                    if ($modifiedLines[$i] -match [regex]::Escape($theoremName)) {
                        $modifiedLines[$i] = $modifiedLines[$i] -replace [regex]::Escape($theoremName), $replacement
                        $applied = $true
                        Write-Host "  ✅ 定理名置換: $theoremName -> $replacement" -ForegroundColor Green
                    }
                }
            }
        }
    }
    
    return @{Lines = $modifiedLines; Applied = $applied}
}

function Fix-LeanFileIteratively {
    param([string]$FilePath)
    
    if (-not (Test-Path $FilePath)) {
        Write-Error "ファイルが見つかりません: $FilePath"
        return
    }
    
    Write-Host "🔧 対話的エラー修正開始: $FilePath" -ForegroundColor Green
    
    $originalLines = Get-Content $FilePath -Encoding UTF8
    $currentLines = $originalLines
    $iteration = 0
    $fixHistory = @()
    
    while ($iteration -lt $MaxIterations) {
        $iteration++
        Write-Host "`n--- 修正サイクル $iteration ---" -ForegroundColor Cyan
        
        # 一時ファイルに現在の内容を保存
        $tempFile = [System.IO.Path]::GetTempFileName() + ".lean"
        $currentLines | Out-File -FilePath $tempFile -Encoding UTF8
        
        # コンパイルテスト
        Write-Host "コンパイルテスト実行中..." -ForegroundColor Yellow
        $output = & lake env lean $tempFile 2>&1
        $success = $LASTEXITCODE -eq 0
        
        if ($success) {
            Write-Host "✅ コンパイル成功！修正完了" -ForegroundColor Green
            Remove-Item $tempFile -ErrorAction SilentlyContinue
            break
        }
        
        # エラー解析
        Write-Host "❌ エラー検出、解析中..." -ForegroundColor Red
        $errors = Analyze-CompilationError ($output -join "`n")
        
        if ($errors.Count -eq 0) {
            Write-Host "⚠️ 解析可能なエラーが見つかりません" -ForegroundColor Yellow
            break
        }
        
        Write-Host "検出されたエラー: $($errors.Count)個" -ForegroundColor Yellow
        
        # 修正適用
        $appliedFixes = 0
        
        foreach ($error in $errors) {
            Write-Host "`nエラー: $($error.Type)" -ForegroundColor Yellow
            Write-Host "詳細: $($error.Line)" -ForegroundColor Gray
            
            if ($error.Solutions.Count -gt 0) {
                if ($AutoFix) {
                    # 自動修正
                    foreach ($solution in $error.Solutions) {
                        $result = Apply-ErrorSolution $currentLines $solution $error.Line
                        if ($result.Applied) {
                            $currentLines = $result.Lines
                            $appliedFixes++
                            $fixHistory += @{
                                Iteration = $iteration
                                Error = $error.Line
                                Solution = $solution.Action
                            }
                        }
                    }
                } else {
                    # 対話的修正
                    Write-Host "利用可能な修正策:" -ForegroundColor Cyan
                    for ($i = 0; $i -lt $error.Solutions.Count; $i++) {
                        $solution = $error.Solutions[$i]
                        Write-Host "  $($i+1). $($solution.Action)" -ForegroundColor White
                    }
                    
                    $choice = Read-Host "修正策を選択してください (1-$($error.Solutions.Count), s=スキップ, q=終了)"
                    
                    if ($choice -eq 'q') {
                        Write-Host "修正を中断します" -ForegroundColor Yellow
                        Remove-Item $tempFile -ErrorAction SilentlyContinue
                        return
                    } elseif ($choice -ne 's' -and $choice -match '^\d+$') {
                        $choiceIndex = [int]$choice - 1
                        if ($choiceIndex -ge 0 -and $choiceIndex -lt $error.Solutions.Count) {
                            $solution = $error.Solutions[$choiceIndex]
                            $result = Apply-ErrorSolution $currentLines $solution $error.Line
                            if ($result.Applied) {
                                $currentLines = $result.Lines
                                $appliedFixes++
                                $fixHistory += @{
                                    Iteration = $iteration
                                    Error = $error.Line
                                    Solution = $solution.Action
                                }
                            }
                        }
                    }
                }
            }
        }
        
        Remove-Item $tempFile -ErrorAction SilentlyContinue
        
        if ($appliedFixes -eq 0) {
            Write-Host "⚠️ 適用可能な修正が見つかりませんでした" -ForegroundColor Yellow
            break
        }
        
        Write-Host "適用された修正: $appliedFixes 個" -ForegroundColor Green
    }
    
    # 修正結果を保存
    if ($fixHistory.Count -gt 0) {
        $outputFile = $FilePath -replace "\.lean$", "_fixed.lean"
        $currentLines | Out-File -FilePath $outputFile -Encoding UTF8
        
        Write-Host "`n📊 修正サマリー:" -ForegroundColor Cyan
        Write-Host "修正サイクル数: $iteration" -ForegroundColor Gray
        Write-Host "適用された修正: $($fixHistory.Count)個" -ForegroundColor Gray
        Write-Host "出力ファイル: $outputFile" -ForegroundColor Gray
        
        # 修正履歴表示
        Write-Host "`n修正履歴:" -ForegroundColor Cyan
        $fixHistory | ForEach-Object {
            Write-Host "  サイクル$($_.Iteration): $($_.Solution)" -ForegroundColor Gray
        }
        
        return $outputFile
    } else {
        Write-Host "修正は適用されませんでした" -ForegroundColor Yellow
        return $null
    }
}

# スクリプト実行
if ($InputFile) {
    $result = Fix-LeanFileIteratively $InputFile
    
    if ($result) {
        Write-Host "`n🎯 修正完了: $result" -ForegroundColor Green
    }
} else {
    Write-Host "使用方法:"
    Write-Host "  .\InteractiveErrorFixer.ps1 -InputFile 'path\to\file.lean' [-AutoFix] [-MaxIterations 5]"
}