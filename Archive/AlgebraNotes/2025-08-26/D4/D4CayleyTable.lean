-- Mode: explore
-- Goal: "D4群のCayley表を完全に実装し、視覚的理解を促進する"

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fin.Basic

/-!
# D4二面体群のCayley表

## D4群の元（8個）
- e  (0): 単位元
- r  (1): 90度回転
- r² (2): 180度回転
- r³ (3): 270度回転
- s  (4): 垂直反射
- sr (5): sr合成
- sr²(6): sr²合成
- sr³(7): sr³合成

## Cayley表（積表）
```
    | e  | r  | r² | r³ | s  | sr | sr²| sr³|
----|----|----|----|----|----|----|----|----|
e   | e  | r  | r² | r³ | s  | sr | sr²| sr³|
r   | r  | r² | r³ | e  | sr | sr²| sr³| s  |
r²  | r² | r³ | e  | r  | sr²| sr³| s  | sr |
r³  | r³ | e  | r  | r² | sr³| s  | sr | sr²|
s   | s  | sr³| sr²| sr | e  | r³ | r² | r  |
sr  | sr | s  | sr³| sr²| r  | e  | r³ | r² |
sr² | sr²| sr | s  | sr³| r² | r  | e  | r³ |
sr³ | sr³| sr²| sr | s  | r³ | r² | r  | e  |
```
-/

namespace D4CayleyTable

/-- D4の元を表す型（Fin 8） -/
abbrev D4 := Fin 8

/-- 元の名前 -/
def element_name : D4 → String
  | ⟨0, _⟩ => "e"
  | ⟨1, _⟩ => "r"
  | ⟨2, _⟩ => "r²"
  | ⟨3, _⟩ => "r³"
  | ⟨4, _⟩ => "s"
  | ⟨5, _⟩ => "sr"
  | ⟨6, _⟩ => "sr²"
  | ⟨7, _⟩ => "sr³"
  | _ => "?"

/-- D4群の乗法表を行列として定義 -/
def cayley_matrix : Matrix D4 D4 D4 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7],  -- e行
    ![1, 2, 3, 0, 5, 6, 7, 4],  -- r行
    ![2, 3, 0, 1, 6, 7, 4, 5],  -- r²行
    ![3, 0, 1, 2, 7, 4, 5, 6],  -- r³行
    ![4, 7, 6, 5, 0, 3, 2, 1],  -- s行
    ![5, 4, 7, 6, 1, 0, 3, 2],  -- sr行
    ![6, 5, 4, 7, 2, 1, 0, 3],  -- sr²行
    ![7, 6, 5, 4, 3, 2, 1, 0]]  -- sr³行

/-- cayley_matrixを使った群演算 -/
def mul_by_table (a b : D4) : D4 := cayley_matrix a b

/-- 演算記法 -/
instance : Mul D4 := ⟨mul_by_table⟩

/-- 単位元 -/
instance : One D4 := ⟨⟨0, by norm_num⟩⟩

/-- 逆元表 -/
def inv_table : D4 → D4
  | ⟨0, _⟩ => ⟨0, by norm_num⟩  -- e⁻¹ = e
  | ⟨1, _⟩ => ⟨3, by norm_num⟩  -- r⁻¹ = r³
  | ⟨2, _⟩ => ⟨2, by norm_num⟩  -- (r²)⁻¹ = r²
  | ⟨3, _⟩ => ⟨1, by norm_num⟩  -- (r³)⁻¹ = r
  | ⟨4, _⟩ => ⟨4, by norm_num⟩  -- s⁻¹ = s
  | ⟨5, _⟩ => ⟨5, by norm_num⟩  -- (sr)⁻¹ = sr
  | ⟨6, _⟩ => ⟨6, by norm_num⟩  -- (sr²)⁻¹ = sr²
  | ⟨7, _⟩ => ⟨7, by norm_num⟩  -- (sr³)⁻¹ = sr³
  | _ => ⟨0, by norm_num⟩

instance : Inv D4 := ⟨inv_table⟩

/-- Cayley表の性質：単位元の行と列 -/
theorem cayley_unit_row (b : D4) : cayley_matrix 0 b = b := by
  fin_cases b <;> rfl

theorem cayley_unit_col (a : D4) : cayley_matrix a 0 = a := by
  fin_cases a <;> rfl

/-- 基本関係式の検証 -/

/-- r⁴ = e -/
theorem r_pow_4 : (1 : D4) * 1 * 1 * 1 = 1 := by
  simp [Mul.mul, mul_by_table, cayley_matrix]
  rfl

/-- s² = e -/
theorem s_squared : (4 : D4) * 4 = 1 := by
  simp [Mul.mul, mul_by_table, cayley_matrix]
  rfl

/-- srs = r⁻¹ (= r³) -/
theorem braid_relation : (4 : D4) * 1 * 4 = 3 := by
  simp [Mul.mul, mul_by_table, cayley_matrix]
  rfl

/-- 各元の位数 -/
def order : D4 → ℕ
  | ⟨0, _⟩ => 1  -- e
  | ⟨1, _⟩ => 4  -- r
  | ⟨2, _⟩ => 2  -- r²
  | ⟨3, _⟩ => 4  -- r³
  | ⟨4, _⟩ => 2  -- s
  | ⟨5, _⟩ => 2  -- sr
  | ⟨6, _⟩ => 2  -- sr²
  | ⟨7, _⟩ => 2  -- sr³
  | _ => 1

/-- 位数2の元は自己逆元 -/
theorem order_2_self_inverse (a : D4) (h : order a = 2) : a * a = 1 := by
  fin_cases a <;> simp [order] at h
  · contradiction  -- eの位数は1
  · contradiction  -- rの位数は4
  · simp [Mul.mul, mul_by_table, cayley_matrix]; rfl  -- r²
  · contradiction  -- r³の位数は4
  · simp [Mul.mul, mul_by_table, cayley_matrix]; rfl  -- s
  · simp [Mul.mul, mul_by_table, cayley_matrix]; rfl  -- sr
  · simp [Mul.mul, mul_by_table, cayley_matrix]; rfl  -- sr²
  · simp [Mul.mul, mul_by_table, cayley_matrix]; rfl  -- sr³

/-- 共役類の代表元 -/
def conjugacy_class_rep (a : D4) : D4 :=
  match a with
  | ⟨0, _⟩ => ⟨0, by norm_num⟩  -- {e}
  | ⟨1, _⟩ => ⟨1, by norm_num⟩  -- {r, r³}
  | ⟨2, _⟩ => ⟨2, by norm_num⟩  -- {r²}
  | ⟨3, _⟩ => ⟨1, by norm_num⟩  -- {r, r³}
  | ⟨4, _⟩ => ⟨4, by norm_num⟩  -- {s, sr²}
  | ⟨5, _⟩ => ⟨5, by norm_num⟩  -- {sr, sr³}
  | ⟨6, _⟩ => ⟨4, by norm_num⟩  -- {s, sr²}
  | ⟨7, _⟩ => ⟨5, by norm_num⟩  -- {sr, sr³}
  | _ => ⟨0, by norm_num⟩

/-- 共役類の個数定理：D4には5つの共役類がある -/
theorem num_conjugacy_classes : 
  Finset.card (Finset.image conjugacy_class_rep Finset.univ) = 5 := by
  -- 共役類: {e}, {r²}, {r, r³}, {s, sr²}, {sr, sr³}
  -- TODO: reason="共役類の完全分類", missing_lemma="conjugacy_classification", priority=low
  sorry

/-- 中心Z(D4) = {e, r²} -/
def center : Set D4 := {⟨0, by norm_num⟩, ⟨2, by norm_num⟩}

theorem center_characterization (a : D4) : 
  a ∈ center ↔ ∀ b : D4, a * b = b * a := by
  constructor
  · intro ha b
    simp [center] at ha
    cases ha with
    | inl h => simp [h, Mul.mul, mul_by_table]; apply cayley_unit_row
    | inr h => 
      simp [h]
      fin_cases b <;> simp [Mul.mul, mul_by_table, cayley_matrix]
  · intro comm
    -- TODO: reason="可換性からの中心の特徴付け", missing_lemma="center_from_commutativity", priority=med
    sorry

end D4CayleyTable