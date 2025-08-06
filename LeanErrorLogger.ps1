# Leanプロジェクトエラー自動記録システム

param(
    [Parameter(Mandatory=$false)]
    [string]$Command = "build",
    
    [Parameter(Mandatory=$false)]
    [string]$LogDir = "error-logs",
    
    [Parameter(Mandatory=$false)]
    [switch]$AutoCommit = $false,
    
    [Parameter(Mandatory=$false)]
    [switch]$ShowHistory = $false
)

# エラー記録のデータ構造
class LeanErrorRecord {
    [string]$Timestamp
    [string]$Command
    [string]$ErrorType
    [string]$ErrorMessage
    [string]$FileName
    [int]$LineNumber
    [string]$OriginalCode
    [string]$FixDescription
    [string]$LearningPoint
    [string]$GitHash
    
    LeanErrorRecord() {
        $this.Timestamp = Get-Date -Format "yyyy-MM-dd HH:mm:ss"
    }
}

# エラーパーサー
function Parse-LeanError {
    param([string]$ErrorOutput)
    
    $errors = @()
    $lines = $ErrorOutput -split "`n"
    
    for ($i = 0; $i -lt $lines.Length; $i++) {
        $line = $lines[$i].Trim()
        
        if ($line -match "(.+):(\d+):(\d+): error: (.+)") {
            $error = [LeanErrorRecord]::new()
            $error.FileName = $matches[1] -replace "\\\\", "\" -replace "^\.\\\.\\\.", ""
            $error.LineNumber = [int]$matches[2]
            $error.ErrorMessage = $matches[4]
            
            $error.ErrorType = Get-ErrorType -ErrorMessage $error.ErrorMessage
            
            if (Test-Path $error.FileName) {
                $error.OriginalCode = Get-ErrorContext -FileName $error.FileName -LineNumber $error.LineNumber
            }
            
            $errors += $error
        }
    }
    
    return $errors
}

# エラータイプの分類
function Get-ErrorType {
    param([string]$ErrorMessage)
    
    if ($ErrorMessage -like "*unknown tactic*") { return "戦術エラー" }
    if ($ErrorMessage -like "*type mismatch*") { return "型不一致" }
    if ($ErrorMessage -like "*unsolved goals*") { return "未解決ゴール" }
    if ($ErrorMessage -like "*unknown constant*") { return "未定義定数" }
    if ($ErrorMessage -like "*failed to prove termination*") { return "停止性証明失敗" }
    if ($ErrorMessage -like "*application type mismatch*") { return "適用型不一致" }
    if ($ErrorMessage -like "*unexpected token*") { return "構文エラー" }
    if ($ErrorMessage -like "*unknown identifier*") { return "未定義識別子" }
    
    return "その他のエラー"
}

# エラー発生箇所のコンテキストを取得
function Get-ErrorContext {
    param([string]$FileName, [int]$LineNumber)
    
    if (-not (Test-Path $FileName)) {
        return ""
    }
    
    $lines = Get-Content $FileName
    $startLine = [Math]::Max(0, $LineNumber - 3)
    $endLine = [Math]::Min($lines.Length - 1, $LineNumber + 2)
    
    $context = @()
    for ($i = $startLine; $i -le $endLine; $i++) {
        $marker = if ($i -eq ($LineNumber - 1)) { ">>> " } else { "    " }
        $context += "$marker$($i + 1): $($lines[$i])"
    }
    
    return $context -join "`n"
}

# 修正提案の生成
function Get-FixSuggestion {
    param([LeanErrorRecord]$ErrorRecord)
    
    switch ($ErrorRecord.ErrorType) {
        "戦術エラー" {
            $ErrorRecord.FixDescription = "正しい戦術名を使用するか、利用可能な戦術を確認してください"
            $ErrorRecord.LearningPoint = "Leanの基本戦術: exact, rw, simp, apply, intro, cases, induction"
        }
        "型不一致" {
            $ErrorRecord.FixDescription = "期待される型と実際の型を確認し、適切な変換や証明を追加してください"
            $ErrorRecord.LearningPoint = "型チェックはLeanの基本概念。#check コマンドで型を確認できます"
        }
        "未解決ゴール" {
            $ErrorRecord.FixDescription = "残されたゴールを証明するか、sorry で一時的にスキップしてください"
            $ErrorRecord.LearningPoint = "証明は全てのゴールを解決する必要があります。未完成の場合はsorryを使用"
        }
        "未定義定数" {
            $ErrorRecord.FixDescription = "定数名のスペルを確認し、必要に応じてimportを追加してください"
            $ErrorRecord.LearningPoint = "名前空間とimportの管理が重要。#check で定義の存在を確認"
        }
        "停止性証明失敗" {
            $ErrorRecord.FixDescription = "termination_by句を追加するか、再帰構造を見直してください"
            $ErrorRecord.LearningPoint = "再帰関数は停止することを証明する必要があります"
        }
        "適用型不一致" {
            $ErrorRecord.FixDescription = "関数の引数の型と順序を確認してください"
            $ErrorRecord.LearningPoint = "関数適用時は引数の型が正確に一致する必要があります"
        }
        "構文エラー" {
            $ErrorRecord.FixDescription = "構文規則を確認し、括弧や記号の使用を見直してください"
            $ErrorRecord.LearningPoint = "Lean4の構文は厳密です。公式ドキュメントで構文を確認"
        }
        "未定義識別子" {
            $ErrorRecord.FixDescription = "識別子名のスペルを確認し、スコープ内で定義されているか確認してください"
            $ErrorRecord.LearningPoint = "変数や関数のスコープとライフタイムを理解することが重要"
        }
        default {
            $ErrorRecord.FixDescription = "エラーメッセージを詳しく読み、公式ドキュメントを参照してください"
            $ErrorRecord.LearningPoint = "未知のエラーは学習の機会。コミュニティやドキュメントで情報を探しましょう"
        }
    }
}

# エラー記録をJSONファイルに保存
function Save-ErrorRecord {
    param([LeanErrorRecord[]]$ErrorRecords, [string]$LogDir)
    
    if (-not (Test-Path $LogDir)) {
        New-Item -ItemType Directory -Path $LogDir | Out-Null
    }
    
    $timestamp = Get-Date -Format "yyyy-MM-dd_HH-mm-ss"
    $logFile = Join-Path $LogDir "error-log-$timestamp.json"
    
    $ErrorRecords | ConvertTo-Json -Depth 10 | Out-File -FilePath $logFile -Encoding UTF8
    return $logFile
}

# エラー記録をMarkdownレポートとして出力
function Generate-ErrorReport {
    param([LeanErrorRecord[]]$ErrorRecords, [string]$LogDir)
    
    $timestamp = Get-Date -Format "yyyy-MM-dd_HH-mm-ss"
    $reportFile = Join-Path $LogDir "error-report-$timestamp.md"
    
    $markdown = "# Lean エラーレポート - $(Get-Date -Format 'yyyy年MM月dd日 HH:mm:ss')`n`n"
    $markdown += "## 概要`n"
    $markdown += "- 総エラー数: $($ErrorRecords.Length)`n"
    $markdown += "- 生成日時: $(Get-Date -Format 'yyyy年MM月dd日 HH:mm:ss')`n`n"
    $markdown += "## エラー詳細`n`n"

    for ($i = 0; $i -lt $ErrorRecords.Length; $i++) {
        $error = $ErrorRecords[$i]
        
        $markdown += "### エラー $($i + 1): $($error.ErrorType)`n`n"
        $markdown += "ファイル: $($error.FileName):$($error.LineNumber)`n"
        $markdown += "エラーメッセージ: $($error.ErrorMessage)`n`n"
        $markdown += "発生箇所のコード:`n"
        $markdown += "``````lean`n"
        $markdown += "$($error.OriginalCode)`n"
        $markdown += "```````n`n"
        $markdown += "修正方法: $($error.FixDescription)`n`n"
        $markdown += "学習ポイント: $($error.LearningPoint)`n`n"
        $markdown += "---`n`n"
    }
    
    $markdown | Out-File -FilePath $reportFile -Encoding UTF8
    return $reportFile
}

# Git コミット機能
function Commit-ErrorLog {
    param([string]$LogFile, [string]$ReportFile, [int]$ErrorCount)
    
    try {
        $gitStatus = git status 2>&1
        if ($LASTEXITCODE -ne 0) {
            Write-Warning "Gitリポジトリが初期化されていません。git init を実行してください。"
            return
        }
        
        git add $LogFile 2>&1 | Out-Null
        git add $ReportFile 2>&1 | Out-Null
        
        $commitMessage = "Lean エラーログ: $ErrorCount 件のエラーを記録"
        
        git commit -m $commitMessage 2>&1 | Out-Null
        
        if ($LASTEXITCODE -eq 0) {
            $hash = git rev-parse HEAD
            Write-Host "✅ エラーログがコミットされました (Hash: $($hash.Substring(0, 8)))" -ForegroundColor Green
            return $hash
        } else {
            Write-Warning "Gitコミットに失敗しました"
        }
    }
    catch {
        Write-Warning "Git操作エラー: $($_.Exception.Message)"
    }
}

# エラー履歴表示
function Show-ErrorHistory {
    param([string]$LogDir)
    
    if (-not (Test-Path $LogDir)) {
        Write-Host "エラーログが見つかりません" -ForegroundColor Yellow
        return
    }
    
    $logFiles = Get-ChildItem -Path $LogDir -Filter "*.json" | Sort-Object CreationTime -Descending
    
    if ($logFiles.Count -eq 0) {
        Write-Host "エラーログが見つかりません" -ForegroundColor Yellow
        return
    }
    
    Write-Host "`n=== Lean エラー履歴 ===" -ForegroundColor Cyan
    
    foreach ($file in $logFiles) {
        try {
            $errors = Get-Content $file.FullName | ConvertFrom-Json
            $errorCount = if ($errors -is [array]) { $errors.Length } else { 1 }
            
            Write-Host "`n📅 $($file.CreationTime.ToString('yyyy-MM-dd HH:mm:ss'))" -ForegroundColor Green
            Write-Host "   📁 $($file.Name)" -ForegroundColor Gray
            Write-Host "   🔢 エラー数: $errorCount" -ForegroundColor Yellow
            
            if ($errors -is [array] -and $errors.Length -gt 0) {
                $errorTypes = $errors | Group-Object ErrorType | Sort-Object Count -Descending
                Write-Host "   📊 エラータイプ:" -ForegroundColor Magenta
                foreach ($type in $errorTypes) {
                    Write-Host "      - $($type.Name): $($type.Count)件" -ForegroundColor White
                }
            }
        }
        catch {
            Write-Host "   ⚠️ ファイル読み込みエラー: $($file.Name)" -ForegroundColor Red
        }
    }
}

# メイン処理
Write-Host "🔍 Lean エラー自動記録システム" -ForegroundColor Cyan
Write-Host "================================" -ForegroundColor Cyan

if ($ShowHistory) {
    Show-ErrorHistory -LogDir $LogDir
    exit
}

Write-Host "📦 Leanプロジェクトをビルド中..." -ForegroundColor Yellow

$buildOutput = ""
if ($Command -eq "build") {
    $buildOutput = lake build 2>&1 | Out-String
} else {
    $buildOutput = Invoke-Expression "$Command 2>&1" | Out-String
}

if ($buildOutput -match "error:" -or $LASTEXITCODE -ne 0) {
    Write-Host "❌ エラーが検出されました。解析中..." -ForegroundColor Red
    
    $errors = Parse-LeanError -ErrorOutput $buildOutput
    
    if ($errors.Length -eq 0) {
        Write-Host "⚠️ エラーを解析できませんでした" -ForegroundColor Yellow
        Write-Host "ビルド出力:`n$buildOutput" -ForegroundColor Gray
        exit
    }
    
    foreach ($error in $errors) {
        Get-FixSuggestion -ErrorRecord $error
    }
    
    $logFile = Save-ErrorRecord -ErrorRecords $errors -LogDir $LogDir
    $reportFile = Generate-ErrorReport -ErrorRecords $errors -LogDir $LogDir
    
    Write-Host "📝 エラーログが保存されました:" -ForegroundColor Green
    Write-Host "   JSON: $logFile" -ForegroundColor White
    Write-Host "   レポート: $reportFile" -ForegroundColor White
    
    if ($AutoCommit) {
        $gitHash = Commit-ErrorLog -LogFile $logFile -ReportFile $reportFile -ErrorCount $errors.Length
    }
    
    Write-Host "`n📊 エラーサマリー:" -ForegroundColor Magenta
    Write-Host "   総エラー数: $($errors.Length)" -ForegroundColor White
    
    $errorTypeCounts = $errors | Group-Object ErrorType
    foreach ($typeCount in $errorTypeCounts) {
        Write-Host "   - $($typeCount.Name): $($typeCount.Count)件" -ForegroundColor Yellow
    }
    
    Write-Host "`n💡 主な学習ポイント:" -ForegroundColor Magenta
    $learningPoints = $errors | Select-Object -ExpandProperty LearningPoint -Unique
    foreach ($point in $learningPoints) {
        Write-Host "   • $point" -ForegroundColor Cyan
    }
    
} else {
    Write-Host "✅ ビルドが成功しました！エラーはありませんでした。" -ForegroundColor Green
}