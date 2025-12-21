import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Order.WellFounded
import MyProjects.ST.RankCore.Basic

/-!
# ユークリッドの互除法の停止性証明（RankCoreアプローチ）

Goal-Driven Design に基づく実装:
1. 最終目標の定理を先に特定
2. 必要条件を逆算
3. 最小限の実装
4. 計算例での確認
5. 目標定理の証明

実装時間目安: 約20分
-/

namespace GCD_Example

/-! ## Step 1: 目標定理の特定 (Time: ~2 min) -/

/-
最終的に証明したい定理:
  `theorem gcd_terminates : WellFounded gcd_step`

または、実用的には:
  `def gcd (a b : ℕ) : ℕ := ...` (termination hint付き)

これを証明するために、何が必要かを次のステップで逆算する。
-/

/-! ## Step 2: 必要条件の抽出 (Time: ~3 min) -/

/-
目標定理 `WellFounded gcd_step` の仮定から必要なもの:

1. **状態空間**: `GCDState := ℕ × ℕ` (a, b のペア)

2. **rank関数**: `GCDState → ℕ`
   - 数学的直観: 除数 b が減少する → rank := b (第2成分)
   - 型: `rank (a, b) = b`

3. **step関数**: `GCDState → GCDState`
   - 数学的意味: ユークリッド互除法の一歩
   - 定義: `step (a, b) = (b, a % b)`

4. **rank減少の証明**: `rank (step x) < rank x`
   - キー補題: `Nat.mod_lt` (a % b < b when b ≠ 0)
   - 条件: b ≠ 0 のとき

これらを実装すれば、WellFoundednessが自動的に従う。
-/

/-! ## Step 3: 最小実装 (Time: ~10 min) -/

/-- GCD計算の状態: (被除数, 除数) のペア -/
def GCDState := ℕ × ℕ

/-- Rank関数: 除数（第2成分）を返す
数学的直観: ユークリッド互除法では除数が単調減少する -/
def gcd_rank : GCDState → ℕ := fun (_, b) => b

/-- Step関数: ユークリッド互除法の一歩
(a, b) ↦ (b, a mod b) -/
def gcd_step : GCDState → GCDState := fun (a, b) => (b, a % b)

/-- RankCore インスタンス（チェックリスト的実装）
このインスタンスは「WellFoundednessに必要な要件」を列挙しているだけ -/
instance : ST.Ranked ℕ GCDState where
  rank := gcd_rank

/-
以下、rank減少を証明するための準備。
WellFoundednessは「rank < によって誘導される関係」で成り立つ。
-/

/-- Rank減少補題: b ≠ 0 のとき、step後のrankは厳密に減少
証明戦略: Nat.mod_lt を使用 -/
lemma gcd_rank_decreases : ∀ (s : GCDState), s.2 ≠ 0 →
    gcd_rank (gcd_step s) < gcd_rank s := by
  intro ⟨a, b⟩ hb
  -- gcd_rank (b, a % b) = a % b
  -- gcd_rank (a, b) = b
  -- a % b < b (by Nat.mod_lt)
  simp [gcd_rank, gcd_step]
  exact Nat.mod_lt a (Nat.pos_of_ne_zero hb)

/-- GCD step relation (next, current). -/
def gcd_rel : GCDState → GCDState → Prop :=
  fun s2 s1 => s2 = gcd_step s1 ∧ s1.2 ≠ 0

/-- Rank strictly decreases along `gcd_rel`. -/
lemma gcd_rel_rank_lt {s1 s2 : GCDState} (h : gcd_rel s2 s1) :
    gcd_rank s2 < gcd_rank s1 := by
  rcases h with ⟨rfl, hne⟩
  exact gcd_rank_decreases s1 hne

/-! ## Step 4: 計算例での確認 (Time: ~2 min) -/

/-
#evalで実際の計算を確認して、rankが減少することを見る
-/

#eval gcd_step (48, 18)  -- = (18, 12)
#eval gcd_rank (48, 18)  -- = 18
#eval gcd_rank (18, 12)  -- = 12 < 18 ✓

#eval gcd_step (18, 12)  -- = (12, 6)
#eval gcd_rank (18, 12)  -- = 12
#eval gcd_rank (12, 6)   -- = 6 < 12 ✓

#eval gcd_step (12, 6)   -- = (6, 0)
#eval gcd_rank (12, 6)   -- = 6
#eval gcd_rank (6, 0)    -- = 0 < 6 ✓
-- b = 0 で停止

-- Example test: the step relation holds on a concrete state.
example : gcd_rel (gcd_step (48, 18)) (48, 18) := by
  exact ⟨rfl, by decide⟩

/-
別の例: gcd(100, 35)
-/
#eval gcd_step (100, 35)  -- = (35, 30)
#eval gcd_rank (100, 35)  -- = 35
#eval gcd_rank (35, 30)   -- = 30 < 35 ✓

/-! ## Step 5: 目標定理の証明 (Time: ~3 min) -/

/-- 主定理: GCD step関係はWellFoundedである
証明戦略:
  1. gcd_relを自然数の<関係へinvImageで持ち上げ
  2. ℕの<はWellFounded (Nat.lt_wfRel)
  3. gcd_rank_decreasesにより、gcd_relは rank < を引き起こす
  4. よってgcd_relもWellFounded
-/
theorem gcd_terminates : WellFounded gcd_rel := by
  -- Proof strategy: use well-foundedness of InvImage (<) and monotonicity.
  refine (WellFounded.mono (r := InvImage (· < ·) gcd_rank) (r' := gcd_rel) ?wf ?h)
  · exact InvImage.wf gcd_rank (wellFounded_lt)
  · intro s2 s1 hrel
    exact gcd_rel_rank_lt hrel

/-- 実用的な定義: GCD関数（terminationヒント付き）
Leanのterminationチェッカーに、rankが減少することを伝える -/
def gcd (a b : ℕ) : ℕ :=
  if h : b = 0 then a
  else
    have : a % b < b := Nat.mod_lt a (Nat.pos_of_ne_zero h)
    gcd b (a % b)
termination_by b
decreasing_by assumption

/-
計算例での確認
-/
#eval gcd 48 18   -- = 6
#eval gcd 100 35  -- = 5
#eval gcd 1071 462 -- = 21 (有名な例)

/-! ## 数学的コメント -/

/-
**なぜこのrankなのか**:
  ユークリッド互除法では、(a, b) → (b, a mod b) の遷移で
  必ず b > a mod b が成り立つ（b ≠ 0 のとき）。
  したがって、除数 b が測度として自然。

**RankCoreの役割**:
  RankCoreインスタンスは「WellFoundednessに必要な条件リスト」として機能。
  抽象理論から入るのではなく、
  「gcd_terminatesを証明したい → rankが必要 → RankCoreで整理」
  という逆算のアプローチが学習に効果的。

**停止性の直観**:
  各ステップで b が減少し、自然数は無限降下列を持たない。
  したがって、有限ステップで b = 0 に到達する。
-/

end GCD_Example
