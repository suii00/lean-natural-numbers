import MyProjects.ST.Formalization.P4.Martingale_StructureTower
import MyProjects.ST.Formalization.P3.StoppingTime_MinLayer
import MyProjects.ST.Rank.Prob.P1.StoppingTime_C
import MyProjects.ST.Rank.P3.RankTower
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic


/-!
# Martingale Theory via Rank Structure

**実装戦略**: 薄いラッパーから始める

既存の Martingale_StructureTower / StoppingTime_MinLayer の補題を
Rank Structure の言葉で再定式化する「橋渡し層」。

この段階では：
- Statement の翻訳に集中
- 証明は既存補題を呼ぶだけ
- 完全な一般化は OptionalStopping_RankTheory.lean に譲る

## 理論的意義

**なぜこのアプローチを取るか**:

1. **心理的負担の最小化**: 既存の証明済み補題を活用し、新規証明を避ける
2. **段階的構築**: まず骨格を作り、後で拡張する布石とする
3. **概念の橋渡し**: マルチンゲール理論とRank理論の接続を明示

**数学的動機**:

マルチンゲール理論における停止時間は、構造塔理論におけるminLayer関数と本質的に同一である：
- 停止時間 τ(ω) = 「標本点ωが初めて決定される時刻」
- minLayer(x) = 「要素xが属する最小の層」

この対応により、Optional Stopping Theorem等の古典的結果が
構造塔の普遍性から自然に導出されることが期待される。

## 参考文献
- Williams, D. "Probability with Martingales" (1991)
- RankTower.lean: 双方向対応理論
- Martingale_StructureTower.md: bounded OST の実装
- StoppingTime_MinLayer.md: 停止過程のAPI
-/

open scoped Classical
open MeasureTheory StructureTowerProbability

namespace StructureTowerProbability.Rank

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]

/-!
## セクション1: 基本的な概念の翻訳

薄いラッパー戦略の第一歩として、既存の概念をrank版として再定義する。
-/

/-- 停止時間をrank関数として解釈する（薄いラッパー）。

**数学的意味**:
停止時間 τ : Ω → ℕ は、そのままrank関数 ρ : Ω → ℕ と見なせる。

**既存理論との対応**:
StoppingTime_C.lean の `stoppingTimeToRank` と同一。
-/
abbrev stoppingTimeAsRank (ℱ : Filtration Ω) (τ : StoppingTime ℱ) : Ω → ℕ :=
  stoppingTimeToRank ℱ τ

/-- マルチンゲールの停止過程をrank理論で解釈する（薄いラッパー）。

**数学的意味**:
マルチンゲールMを停止時間τで止めた過程 M^τ は、
構造塔の視点では「rank ≤ n の層に属する標本点での値」として理解できる。

**既存理論との対応**:
Martingale_StructureTower.md の `stoppedProcess` の別名。
-/
abbrev rankStoppedProcess (M : Martingale μ) (τ : Ω → ℕ) : ℕ → Ω → ℝ :=
  Martingale.stoppedProcess M τ

/-!
## セクション2: 薄いラッパー定理群

以下の定理は、既存のMartingale_StructureTower.mdとStoppingTime_MinLayer.mdの
補題を「rank版のstatement」に翻訳するだけ。証明は既存補題を呼ぶ一行。
-/

/-!
### 定理1: Bounded Optional Stopping (Rank版)

**Statement の翻訳**:
有界な停止時間（＝有界なrank関数）でマルチンゲールを止めると、
期待値が保存される。

**既存補題との対応**:
Martingale_StructureTower.md の bounded OST を
rank理論の言葉で再定式化したもの。

**証明戦略**:
`exact` で既存の定理を一行で呼ぶだけ。
 -/
-- NOTE: `MyStoppingTime` や `ℱ.base.𝓕` まわりの依存が未整理のため、
-- 下記の定理本体は一時的にコメントアウトしています。
-- 依存が揃い次第、既存補題を呼ぶ一行証明に差し戻してください。
theorem rankOptionalStopping_bounded
    (M : Martingale μ)
    (τ : Ω → ℕ)
    (hτ : ∀ n, @MeasurableSet Ω (M.filtration n) {ω : Ω | τ ω ≤ n})
    (hτ_bdd : ∃ K, ∀ ω, τ ω ≤ K) :
    ∀ n, ∫ ω, rankStoppedProcess M τ n ω ∂μ
        = ∫ ω, rankStoppedProcess M τ 0 ω ∂μ := by
  classical
  -- 停止過程は有界停止時間のもとで再びマルチンゲールになる
  set H : Martingale μ :=
    M.stoppedProcess_martingale_of_bdd (τ := τ) hτ hτ_bdd
  -- マルチンゲールの期待値は時刻に依らず一定であることを示す
  have hconst : ∀ k, ∫ ω, H.process k ω ∂μ = ∫ ω, H.process 0 ω ∂μ :=
  by
    refine Nat.rec ?base ?step
    · -- k = 0
      rfl
    · intro k ih
      -- martingale 性：E[X_{k+1} | 𝓕_k] = X_k
      have hmart : condExp μ H.filtration k (H.process (k + 1))
                    =ᵐ[μ] H.process k := H.martingale k
      -- condExp の積分は元の積分に一致
      have hcond :
          ∫ ω, condExp μ H.filtration k (H.process (k + 1)) ω ∂μ
            = ∫ ω, H.process (k + 1) ω ∂μ := by
        -- 条件付き期待値の積分は元の積分に一致
        -- （mathlib: `MeasureTheory.integral_condExp`）
        simpa [StructureTowerProbability.condExp] using
          (MeasureTheory.integral_condExp
            (μ := μ)
            (m := H.filtration k)
            (m₀ := ‹MeasurableSpace Ω›)
            (f := H.process (k + 1))
            (hm := H.filtration.le k))
      calc
        ∫ ω, H.process (k + 1) ω ∂μ
            = ∫ ω, condExp μ H.filtration k (H.process (k + 1)) ω ∂μ := by
                symm; exact hcond
        _ = ∫ ω, H.process k ω ∂μ := by
                have hcongr := MeasureTheory.integral_congr_ae hmart
                simpa using hcongr
        _ = ∫ ω, H.process 0 ω ∂μ := ih
  -- rankStoppedProcess は H.process に一致
  intro n
  have hrepr : ∫ ω, rankStoppedProcess M τ n ω ∂μ
              = ∫ ω, H.process n ω ∂μ := by rfl
  have hrepr0 : ∫ ω, rankStoppedProcess M τ 0 ω ∂μ
               = ∫ ω, H.process 0 ω ∂μ := by rfl
  calc
    ∫ ω, rankStoppedProcess M τ n ω ∂μ
        = ∫ ω, H.process n ω ∂μ := hrepr
    _   = ∫ ω, H.process 0 ω ∂μ := hconst n
    _   = ∫ ω, rankStoppedProcess M τ 0 ω ∂μ := hrepr0.symm

/-
### 定理2: 停止過程の適合性 (Rank版)

**Statement の翻訳**:
rank関数τが「停止集合 = rank ≤ n の層」を定義するとき、
停止過程は元のフィルトレーションに適合する。

**既存補題との対応**:
StoppingTime_MinLayer.md の `stopped_stronglyMeasurable_of_stoppingSets`
をrank理論として再解釈。

**証明戦略**:
既存補題を `exact` で呼ぶだけ。

NOTE: `rankStoppedProcess ⟨ℱ, X, hX, …⟩` まわりで未整理の依存があるため、
定理本体は一時的にコメントアウトしています。依存が揃い次第復活させてください。
-/
theorem rankStopped_adapted
    (M : Martingale μ)
    (τ : Ω → ℕ)
    (hτ : ∀ n, @MeasurableSet Ω (M.filtration n) {ω : Ω | τ ω ≤ n}) :
    ∀ n, StronglyMeasurable[M.filtration n] (rankStoppedProcess M τ n) := by
  intro n
  simpa [rankStoppedProcess] using
    (M.stoppedProcess_stronglyMeasurable_of_stoppingSets (τ := τ) hτ n)

/-
### 定理3: 停止過程の可積分性 (Rank版)

**Statement の翻訳**:
有界なrank関数で止めた過程は、各時刻で可積分性を保つ。

**既存補題との対応**:
StoppingTime_MinLayer.md の `stopped_integrable_of_bdd` のrank版。

**証明戦略**:
既存補題を `exact` で呼ぶだけ。

NOTE: 依存補題の束縛が未整理のため、定理本体は一時コメントアウト。
依存が整い次第、`exact stopped_integrable_of_bdd …` の一行に戻す。
-/
theorem rankStopped_integrable
    (M : Martingale μ)
    (τ : Ω → ℕ)
    (hτ : ∀ n, @MeasurableSet Ω (M.filtration n) {ω : Ω | τ ω ≤ n})
    (hτ_bdd : ∃ K, ∀ ω, τ ω ≤ K) :
    ∀ n, Integrable (rankStoppedProcess M τ n) μ := by
  intro n
  simpa [rankStoppedProcess] using
    (M.stoppedProcess_integrable_of_bdd (τ := τ) hτ hτ_bdd n)

/-
### 定理4: 停止過程のマルチンゲール性 (Rank版)

**Statement の翻訳**:
有界なrank関数で止めたマルチンゲールは、
依然としてマルチンゲール性を保つ。

**既存補題との対応**:
Martingale_StructureTower.md の
`stoppedProcess_martingale_property_of_bdd` のrank版。

**証明戦略**:
既存補題を `exact` で呼ぶだけ。

NOTE: こちらも依存整理待ちのため一時コメントアウト。
復旧後は `exact Martingale.stoppedProcess_martingale_property_of_bdd …` に戻す。
-/
theorem rankStopped_martingale_property
    (M : Martingale μ)
    (τ : Ω → ℕ)
    (hτ : ∀ n, @MeasurableSet Ω (M.filtration n) {ω : Ω | τ ω ≤ n})
    (hτ_bdd : ∃ K, ∀ ω, τ ω ≤ K) :
    ∀ n, condExp μ M.filtration n (rankStoppedProcess M τ (n + 1))
          =ᵐ[μ] rankStoppedProcess M τ n := by
  intro n
  simpa [rankStoppedProcess, condExp] using
    (M.stoppedProcess_martingale_property_of_bdd
      (τ := τ) hτ hτ_bdd n)

/-!
## 今後の展開

この薄い層の上に、OptionalStopping_RankTheory.lean で
完全な rank 版 OST の理論を構築する予定。

**次のステップ**:
1. 無界停止時間への拡張
2. Doob's Optional Stopping Theorem の完全証明
3. Rank理論の普遍性からOSTを導出する圏論的証明
4. マルチンゲール収束定理のrank版

**この薄いラッパーの意義**:
- 心理的負担を最小化しつつ、rank理論とマルチンゲール理論の接続を確立
- 既存の証明済み補題を活用することで、正確性を保証
- 段階的拡張の布石として機能

**Bourbakiの精神**:
「必要十分な一般性」の原則に従い、まず最小限の抽象化から始め、
徐々に一般化していく手法を採用。
-/

end StructureTowerProbability.Rank

/-!
## 学習のまとめ

**この薄いラッパーから学べること**:

1. **翻訳の技法**: 既存の定理を新しい言葉で再定式化する方法
2. **証明の再利用**: `exact` による既存補題の活用パターン
3. **段階的構築**: 完全な理論の前に骨格を作る重要性
4. **概念の橋渡し**: 異なる数学分野（確率論・構造塔理論）の統合手法

**このアプローチの利点**:

- ✅ 実装コストが低い（3-5個の薄い定理で十分）
- ✅ 既存証明の正確性を継承
- ✅ 後続の拡張への明確な道筋
- ✅ 教育的価値が高い（翻訳のプロセスが明示的）

**このアプローチの限界**:

- ⚠️ 完全な一般化ではない（有界停止時間のみ）
- ⚠️ 新しい洞察は限定的（既存理論の言い換えに過ぎない）
- ⚠️ 圏論的構造は未整備

しかし、これらの限界は意図的なものであり、
OptionalStopping_RankTheory.lean での完全な理論構築への
「心理的に優しい入口」として機能する。

## 参考文献

- Williams, D. (1991). "Probability with Martingales". Cambridge University Press.
- Rogers, L. C. G., & Williams, D. (2000). "Diffusions, Markov Processes, and Martingales". Cambridge University Press.
- Kallenberg, O. (2002). "Foundations of Modern Probability". Springer.
- RankTower.lean: 本プロジェクトの双方向対応理論
- Martingale_StructureTower.md: マルチンゲール理論の基礎
- StoppingTime_MinLayer.md: 停止時間のminLayer解釈
-/
