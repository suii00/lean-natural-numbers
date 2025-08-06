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

Write-Host "🔍 Lean エラー自動記録システム" -ForegroundColor Cyan

if ($ShowHistory) {
    if (Test-Path $LogDir) {
        $logFiles = Get-ChildItem -Path $LogDir -Filter "*.json" | Sort-Object CreationTime -Descending
        Write-Host "=== エラー履歴 ===" -ForegroundColor Green
        foreach ($file in $logFiles) {
            Write-Host "📁 $($file.Name) - $($file.CreationTime)" -ForegroundColor Yellow
        }
    } else {
        Write-Host "エラーログが見つかりません" -ForegroundColor Yellow
    }
    exit
}

Write-Host "📦 Leanプロジェクトをビルド中..." -ForegroundColor Yellow

$buildOutput = lake build 2>&1 | Out-String

if ($buildOutput -match "error:" -or $LASTEXITCODE -ne 0) {
    Write-Host "❌ エラーが検出されました。解析中..." -ForegroundColor Red
    
    # エラー記録を作成
    $errors = @()
    $lines = $buildOutput -split "`n"
    
    foreach ($line in $lines) {
        if ($line -match "(.+):(\d+):(\d+): error: (.+)") {
            $error = @{
                Timestamp = Get-Date -Format "yyyy-MM-dd HH:mm:ss"
                FileName = $matches[1] -replace "\\\\", "\"
                LineNumber = [int]$matches[2]
                ErrorMessage = $matches[4]
                ErrorType = ""
                FixDescription = ""
                LearningPoint = ""
            }
            
            # エラータイプを分類
            if ($error.ErrorMessage -like "*unknown tactic*") {
                $error.ErrorType = "戦術エラー"
                $error.FixDescription = "正しい戦術名を使用してください"
                $error.LearningPoint = "基本戦術: exact, rw, simp, apply, intro, cases"
            }
            elseif ($error.ErrorMessage -like "*type mismatch*") {
                $error.ErrorType = "型不一致"
                $error.FixDescription = "期待される型と実際の型を確認してください"
                $error.LearningPoint = "型チェックは重要。#checkで型を確認"
            }
            elseif ($error.ErrorMessage -like "*unsolved goals*") {
                $error.ErrorType = "未解決ゴール"
                $error.FixDescription = "残されたゴールを証明するかsorryを使用"
                $error.LearningPoint = "全てのゴールを解決する必要があります"
            }
            elseif ($error.ErrorMessage -like "*unknown constant*") {
                $error.ErrorType = "未定義定数"
                $error.FixDescription = "定数名を確認し、必要に応じてimport追加"
                $error.LearningPoint = "名前空間とimportの管理が重要"
            }
            else {
                $error.ErrorType = "その他のエラー"
                $error.FixDescription = "エラーメッセージを詳しく確認してください"
                $error.LearningPoint = "公式ドキュメントを参照しましょう"
            }
            
            # ソースコードの取得
            if (Test-Path $error.FileName) {
                try {
                    $lines = Get-Content $error.FileName
                    $startLine = [Math]::Max(0, $error.LineNumber - 3)
                    $endLine = [Math]::Min($lines.Length - 1, $error.LineNumber + 2)
                    
                    $context = @()
                    for ($i = $startLine; $i -le $endLine; $i++) {
                        $marker = if ($i -eq ($error.LineNumber - 1)) { ">>> " } else { "    " }
                        $context += "$marker$($i + 1): $($lines[$i])"
                    }
                    $error.OriginalCode = $context -join "`n"
                }
                catch {
                    $error.OriginalCode = "ファイル読み込みエラー"
                }
            }
            
            $errors += $error
        }
    }
    
    if ($errors.Length -gt 0) {
        # エラーログディレクトリを作成
        if (-not (Test-Path $LogDir)) {
            New-Item -ItemType Directory -Path $LogDir | Out-Null
        }
        
        # JSONファイルとして保存
        $timestamp = Get-Date -Format "yyyy-MM-dd_HH-mm-ss"
        $logFile = Join-Path $LogDir "error-log-$timestamp.json"
        $errors | ConvertTo-Json -Depth 10 | Out-File -FilePath $logFile -Encoding UTF8
        
        # Markdownレポート生成
        $reportFile = Join-Path $LogDir "error-report-$timestamp.md"
        $markdown = "# Lean エラーレポート - $(Get-Date -Format 'yyyy年MM月dd日 HH:mm:ss')`n`n"
        $markdown += "## 概要`n"
        $markdown += "- 総エラー数: $($errors.Length)`n"
        $markdown += "- 生成日時: $(Get-Date -Format 'yyyy年MM月dd日 HH:mm:ss')`n`n"
        
        for ($i = 0; $i -lt $errors.Length; $i++) {
            $error = $errors[$i]
            $markdown += "## エラー $($i + 1): $($error.ErrorType)`n`n"
            $markdown += "**ファイル**: $($error.FileName):$($error.LineNumber)`n"
            $markdown += "**メッセージ**: $($error.ErrorMessage)`n`n"
            $markdown += "**修正方法**: $($error.FixDescription)`n`n"
            $markdown += "**学習ポイント**: $($error.LearningPoint)`n`n"
            if ($error.OriginalCode) {
                $markdown += "**コード**:`n``````lean`n$($error.OriginalCode)`n```````n`n"
            }
            $markdown += "---`n`n"
        }
        
        $markdown | Out-File -FilePath $reportFile -Encoding UTF8
        
        Write-Host "📝 エラーログが保存されました:" -ForegroundColor Green
        Write-Host "   JSON: $logFile" -ForegroundColor White
        Write-Host "   レポート: $reportFile" -ForegroundColor White
        
        # Git コミット
        if ($AutoCommit) {
            try {
                git add $logFile 2>&1 | Out-Null
                git add $reportFile 2>&1 | Out-Null
                git commit -m "Lean エラーログ: $($errors.Length) 件のエラーを記録" 2>&1 | Out-Null
                
                if ($LASTEXITCODE -eq 0) {
                    $hash = git rev-parse HEAD
                    Write-Host "✅ エラーログがコミットされました (Hash: $($hash.Substring(0, 8)))" -ForegroundColor Green
                }
            }
            catch {
                Write-Warning "Git操作に失敗しました"
            }
        }
        
        # エラーサマリー表示
        Write-Host "`n📊 エラーサマリー:" -ForegroundColor Magenta
        Write-Host "   総エラー数: $($errors.Length)" -ForegroundColor White
        
        $errorTypes = $errors | Group-Object ErrorType
        foreach ($type in $errorTypes) {
            Write-Host "   - $($type.Name): $($type.Count)件" -ForegroundColor Yellow
        }
        
        Write-Host "`n💡 学習ポイント:" -ForegroundColor Magenta
        $points = $errors | Select-Object -ExpandProperty LearningPoint -Unique
        foreach ($point in $points) {
            Write-Host "   • $point" -ForegroundColor Cyan
        }
    } else {
        Write-Host "⚠️ エラーを解析できませんでした" -ForegroundColor Yellow
        Write-Host "ビルド出力:`n$buildOutput" -ForegroundColor Gray
    }
} else {
    Write-Host "✅ ビルドが成功しました！" -ForegroundColor Green
}