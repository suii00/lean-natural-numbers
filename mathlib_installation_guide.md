# Mathlib インストールガイドとトラブルシューティング

## 📋 実行済みステップ

### ✅ 完了済み
1. **プロジェクトバックアップ**: lakefile.lean.backup, lake-manifest.json.backup作成済み
2. **Git状態の保存**: Pre-mathlib状態をコミット済み
3. **lakefile.lean更新**: mathlib依存関係を追加済み

### ⚠️ 現在のエラー
```
error: RPC failed; curl 56 Recv failure: Connection was reset  
error: 7 bytes of body are still expected
fetch-pack: unexpected disconnect while reading sideband packet
fatal: early EOF
```

**原因**: ネットワーク接続の問題でmathlibリポジトリのクローンが失敗

---

## 🔧 エラー対処法

### 方法1: 手動でのmathlib取得
```bash
# .lakeディレクトリを作成
mkdir -p .lake/packages

# mathlibを浅いクローンで取得
git clone --depth 1 https://github.com/leanprover-community/mathlib4.git .lake/packages/mathlib

# lake buildを実行
lake build
```

### 方法2: 特定バージョンの指定
lakefile.leanで安定版を指定:
```lean
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"v4.3.0"
```

### 方法3: キャッシュの利用
```bash
# mathlibキャッシュを使用（高速）
lake exe cache get
lake build
```

### 方法4: プロキシ/ネットワーク設定
```bash
# Git設定の調整
git config --global http.postBuffer 524288000
git config --global http.lowSpeedLimit 0
git config --global http.lowSpeedTime 999999
```

---

## 🎯 推奨順序

1. **方法1**: 手動での浅いクローン（最も確実）
2. **方法3**: キャッシュ利用（最も高速）
3. **方法2**: 特定バージョン指定
4. **方法4**: ネットワーク設定調整

---

## 📊 現在のプロジェクト状態

### lakefile.lean (更新済み)
```lean
import Lake
open Lake DSL

package «myproject» where
  -- add package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"v4.3.0"

lean_lib «MyProject» where
  -- add library configuration options here

lean_lib «TestError» where

@[default_target]
lean_exe «myproject» where
  root := `Main
```

### バックアップファイル
- ✅ `lakefile.lean.backup`
- ✅ `lake-manifest.json.backup`  
- ✅ `lean-toolchain.backup`

---

## 🧪 インストール確認方法

### テスト1: 基本的なmathlib機能
```lean
-- test_mathlib_basic.lean
import Mathlib.Data.Nat.Basic

example : 2 + 2 = 4 := by norm_num
```

### テスト2: 既存証明の改善
```lean
-- square_even.leanでmathlib戦術使用
import Mathlib.Tactic

theorem even_square_main (n : Int) : MyEven (n * n) → MyEven n := by
  contrapose!
  intro h
  -- mathlib戦術が使用可能
  use_mathlib_tactics
```

---

## 🔄 ロールバック手順

問題が発生した場合:
```bash
# 元の状態に戻す
cp lakefile.lean.backup lakefile.lean
cp lake-manifest.json.backup lake-manifest.json
rm -rf .lake

# Gitで前の状態に戻す
git checkout HEAD~1 -- lakefile.lean
```

---

## 📝 次のステップ

1. 手動インストール試行
2. mathlibインストール確認
3. 既存証明ファイルのテスト
4. 成功時のコミット作成