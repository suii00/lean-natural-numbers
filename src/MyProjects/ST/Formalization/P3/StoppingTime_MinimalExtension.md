/-!
# 停止過程の最小限の追加実装

既存の `stopped` 関数に以下を追加:
1. 停止時刻での値 `atStoppingTime`
2. 型付き構造 `StoppedProcess`  
3. 基本的な性質 (2-3個)
4. 簡単な example

これを StoppingTime_MinLayer.lean の末尾(line 350付近)に追加してください。
-/

namespace StructureTowerProbability

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### 停止時刻での値 -/

/-- 停止時刻 τ における過程の値: X_τ(ω) = X(τ(ω), ω) -/
def atStoppingTime {β : Type*} (X : ℕ → Ω → β) (τ : Ω → ℕ) : Ω → β :=
  fun ω => X (τ ω) ω

/-- `stopped` と `atStoppingTime` の関係 -/
lemma stopped_at_infinity_eq_atStoppingTime 
    {β : Type*} (X : ℕ → Ω → β) (τ : Ω → ℕ) (ω : Ω) 
    (N : ℕ) (hN : τ ω ≤ N) :
    stopped X τ N ω = atStoppingTime X τ ω := by
  simp [stopped, atStoppingTime, Nat.min_eq_right hN]

/-! ### 型付き停止過程構造 -/

/-- 停止過程の構造（最小限版） -/
structure StoppedProcess (ℱ : Filtration Ω) where
  /-- 元の過程 -/
  X : ℕ → Ω → ℝ
  /-- 停止時間 -/
  τ : StoppingTime ℱ
  
/-- 停止過程の値 -/
def StoppedProcess.value (SP : StoppedProcess ℱ) : ℕ → Ω → ℝ :=
  stopped SP.X SP.τ.τ

/-- 停止時刻での値 -/
def StoppedProcess.valueAt (SP : StoppedProcess ℱ) : Ω → ℝ :=
  atStoppingTime SP.X SP.τ.τ

/-! ### 基本的な性質 -/

/-- 停止過程は停止前では元の過程と一致 -/
theorem StoppedProcess.eq_before_stopping 
    (SP : StoppedProcess ℱ) {n : ℕ} {ω : Ω} 
    (hn : n ≤ SP.τ.τ ω) :
    SP.value n ω = SP.X n ω := by
  unfold value
  exact stopped_eq_of_le SP.X SP.τ.τ hn

/-- 停止過程は停止後は値が固定 -/
theorem StoppedProcess.const_after_stopping 
    (SP : StoppedProcess ℱ) {n m : ℕ} {ω : Ω}
    (hτ : SP.τ.τ ω ≤ n) (hnm : n ≤ m) :
    SP.value m ω = SP.value n ω := by
  unfold value
  exact stopped_const_of_ge SP.X SP.τ.τ hτ hnm

/-- 停止過程の値は停止時刻での値に収束 -/
theorem StoppedProcess.converges_to_valueAt 
    (SP : StoppedProcess ℱ) (ω : Ω) (N : ℕ) 
    (hN : SP.τ.τ ω ≤ N) :
    SP.value N ω = SP.valueAt ω := by
  unfold value valueAt
  exact stopped_at_infinity_eq_atStoppingTime SP.X SP.τ.τ ω N hN

end StructureTowerProbability

/-! ## 使用例の追加 -/

-- 既存の example の後に以下を追加:

/-- 停止過程の基本的な使用例 -/
example {Ω : Type*} [MeasurableSpace Ω]
    (ℱ : StructureTowerProbability.Filtration Ω)
    (X : ℕ → Ω → ℝ) (τ : StructureTowerProbability.StoppingTime ℱ)
    (ω : Ω) (n : ℕ) (hn : n ≤ τ.τ ω) :
    let SP := StructureTowerProbability.StoppedProcess.mk X τ
    SP.value n ω = X n ω := by
  intro SP
  exact StructureTowerProbability.StoppedProcess.eq_before_stopping SP hn

/-- 停止後の値の固定 -/
example {Ω : Type*} [MeasurableSpace Ω]
    (ℱ : StructureTowerProbability.Filtration Ω)
    (X : ℕ → Ω → ℝ) (τ : StructureTowerProbability.StoppingTime ℱ)
    (ω : Ω) (hτ : τ.τ ω ≤ 5) :
    let SP := StructureTowerProbability.StoppedProcess.mk X τ
    SP.value 10 ω = SP.value 5 ω := by
  intro SP
  exact StructureTowerProbability.StoppedProcess.const_after_stopping 
    SP hτ (by norm_num : 5 ≤ 10)

/-- 具体的な計算例: 定数過程の停止 -/
example {Ω : Type*} [MeasurableSpace Ω]
    (ℱ : StructureTowerProbability.Filtration Ω)
    (c : ℝ) (τ : StructureTowerProbability.StoppingTime ℱ)
    (ω : Ω) (n : ℕ) :
    let X : ℕ → Ω → ℝ := fun _ _ => c  -- 定数過程
    let SP := StructureTowerProbability.StoppedProcess.mk X τ
    SP.value n ω = c := by
  intro X SP
  unfold StructureTowerProbability.StoppedProcess.value
  simp [StructureTowerProbability.stopped, X]

/-!
## まとめ

追加された最小限の実装:

1. **`atStoppingTime`**: 停止時刻での値 X_τ(ω)
2. **`StoppedProcess`**: 型付き構造
3. **基本的な性質**:
   - `eq_before_stopping`: 停止前は元の過程
   - `const_after_stopping`: 停止後は固定
   - `converges_to_valueAt`: 停止時刻での値への収束
4. **3つの example**: 使用例の実演

これで停止過程の**最小限だが完結した実装**が完成。

### 将来の拡張候補

- 適合性 (adaptedness) の形式化
- 可測性の証明
- マルチンゲールとの接続
- オプショナル停止定理の準備

しかし、今は**この最小限で十分**です！
-/
