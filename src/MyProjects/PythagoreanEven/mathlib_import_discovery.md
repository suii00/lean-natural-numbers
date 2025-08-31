# Mathlib4 Import Discovery Log

## 日付: 2025-08-15

## 課題
ピタゴラス数の偶奇性の証明において、`Mathlib.Data.Nat.Parity`が見つからない問題

## 解決策の探索

### 1. 試行したインポート組み合わせ

#### ❌ 組み合わせ1: 基本的な場所
```lean
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Dvd.Basic
```
**結果**: `Mathlib.Data.Nat.Dvd.Basic`モジュールが存在しない

#### ❌ 組み合わせ2: Algebra.Group.Even
```lean
import Mathlib.Algebra.Group.Even
import Mathlib.Data.Nat.Basic
```
**結果**: 
- `Even`の定義は提供される
- `Nat.even_iff_two_dvd`や`Nat.odd_iff_not_even`などの補題が不足

#### ⚠️ 組み合わせ3: モジュラー算術
```lean
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.ZMod.Basic
```
**結果**:
- `Even`と`Odd`の定義は提供される
- `Nat.even_iff_two_dvd`が存在しない

#### ✅ 組み合わせ4: 環論的アプローチ（成功）
```lean
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.ZMod.Basic
```
**結果**: 完全に動作

## 発見された重要な事実

### Mathlib4での偶奇性関連モジュールの再編成

1. **`Mathlib.Data.Nat.Parity`は廃止/移動**
   - Mathlib4では自然数特有の偶奇性モジュールは独立して存在しない

2. **`Mathlib.Algebra.Ring.Parity`が新しい中心地**
   - より一般的な環での偶奇性を扱う
   - `even_iff_two_dvd`などの基本補題を提供
   - 自然数にも適用可能

3. **必要な補題と定義の所在地**
   - `Even`, `Odd`: `Mathlib.Algebra.Ring.Parity`
   - `even_iff_two_dvd`: `Mathlib.Algebra.Ring.Parity`
   - `Nat.mod_two_eq_zero_or_one`: `Mathlib.Data.Nat.ModEq`
   - `Nat.dvd_iff_mod_eq_zero`: `Mathlib.Data.Nat.Basic`
   - `Nat.div_add_mod`: `Mathlib.Data.Nat.Basic`

## 証明で使用した主要な補題

1. **偶奇性の特徴付け**
   ```lean
   even_iff_two_dvd : Even a ↔ 2 ∣ a
   ```

2. **mod 2の性質**
   ```lean
   Nat.mod_two_eq_zero_or_one : a % 2 = 0 ∨ a % 2 = 1
   ```

3. **除法の基本定理**
   ```lean
   Nat.div_add_mod : 2 * (a / 2) + a % 2 = a
   ```

## 実装上の注意点

1. **`.symm`の必要性**
   - `Nat.div_add_mod`は`2 * (a / 2) + a % 2 = a`の形
   - `a = 2 * (a / 2) + a % 2`が必要な場合は`.symm`を使用

2. **calc環境での証明**
   - mod算術の計算には`calc`が有効
   - 特に`Nat.add_mod`との組み合わせ

3. **背理法での矛盾導出**
   - `absurd`を使った矛盾の明示
   - または直接的な数値計算での矛盾証明

## 推奨インポート構成

ピタゴラス数や偶奇性を扱う証明には：

```lean
-- 環論的な偶奇性の定義（Even, Odd, even_iff_two_dvd）
import Mathlib.Algebra.Ring.Parity

-- mod算術のサポート
import Mathlib.Data.Nat.ModEq

-- 必要に応じてZMod
import Mathlib.Data.ZMod.Basic

-- 一般的なタクティクス
import Mathlib.Tactic
```

## 今後の参考

Mathlib4では多くのモジュールが再編成されており、Mathlib3からの移行時には：
1. より一般的なモジュール（Ring > Nat）を先に確認
2. 複数のインポートの組み合わせが必要な場合が多い
3. 補題名も変更されている可能性があるため、類似名を探索