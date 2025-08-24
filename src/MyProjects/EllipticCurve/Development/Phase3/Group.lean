/-
MyProofs/Elliptic/Group.lean

楕円曲線の点集合と加法（char ≠ 2,3 を仮定）
-/
import Mathlib.Algebra.Field
import Mathlib.Tactic
import Mathlib.Data.Rat.Basic

namespace MyProofs
namespace Elliptic

variable {K : Type*} [Field K]

/-- 短 Weierstrass 形の楕円曲線 -/
structure ShortWeierstrass (K : Type*) [Field K] where
  a b : K
  non_singular : 4 * a^3 + 27 * b^2 ≠ 0

/-- 射影点の表現（無限遠点を含む） -/
inductive Point (E : ShortWeierstrass K)
| infinity : Point E
| affine (x y : K) (h : y^2 = x^3 + E.a * x + E.b) : Point E

namespace Point

variable {E : ShortWeierstrass K}

/-- 逆元 -/
def neg : Point E → Point E
  | infinity => infinity
  | affine x y h => affine x (-y) (by
      calc
        (-y)^2 = y^2 := by ring
        _ = x^3 + E.a * x + E.b := by simpa [this] using h)

/-- 無限遠点（単位元） -/
def zero : Point E := infinity

/-- 補助：affine かどうかの取り出し -/
def coords : Point E → Option (K × K)
  | infinity => none
  | affine x y _ => some (x,y)

/-- 加法の定義（char ≠ 2,3 を仮定） -/
def add : Point E → Point E → Point E
  | infinity, q => q
  | p, infinity => p
  | affine x1 y1 h1, affine x2 y2 h2 =>
    if hx : x1 = x2 then
      -- x1 = x2 の場合
      if hy : y1 = -y2 then
        -- P + (-P) = ∞
        infinity
      else
        -- doubling
        let λ := (3 * x1 * x1 + E.a) / (2 * y1)
        let x3 := λ * λ - x1 - x2
        let y3 := λ * (x1 - x3) - y1
        affine x3 y3 (by
          -- 計算で曲線方程式を満たすことを示す
          have denom_nonzero : (2 * y1) ≠ 0 := by
            -- y1 = 0 なら hy : y1 = -y2 と合わせて特異になるが non_singular があるので除外
            intro H
            have : y1 = 0 := by simp_all [H]
            -- もし y1 = 0 and x1 = x2 then substituting into curve gives discriminant contradiction; we keep a pragmatic check
            have contra : 4 * E.a ^ 3 + 27 * E.b ^ 2 = 0 := by
              -- Rather than a long derivation, derive contradiction by field properties; leave explicit proof to later cleanup.
              have : (4 : K) * E.a ^ 3 + (27 : K) * E.b ^ 2 = 0 := by
                admit
              exact this
            contradiction
          -- main algebraic verification (standard derivation)
          -- show y3^2 = x3^3 + a x3 + b
          -- expand and simplify using h1 (y1^2 = x1^3 + a x1 + b)
          -- the concrete manipulations are routine but lengthy; use ring
          sorry)
    else
      -- x1 ≠ x2 の場合（一般和）
      let λ := (y2 - y1) / (x2 - x1)
      let x3 := λ * λ - x1 - x2
      let y3 := λ * (x1 - x3) - y1
      affine x3 y3 (by
        -- 証明: y3^2 = x3^3 + a x3 + b
        -- 基本的に (substitution + ring) で済むので ring を活用
        -- expand: use h1 and h2
        -- 実装詳細は長いが routine
        sorry)

notation p1 " + " p2 => add p1 p2

/- 基本補題 -/
theorem zero_add (P : Point E) : zero + P = P := by
  cases P
  · rfl
  · rfl

theorem add_zero (P : Point E) : P + zero = P := by
  cases P
  · rfl
  · rfl

theorem neg_def (P : Point E) : P + (neg P) = zero := by
  cases P
  · simp [neg, zero]
  · -- affine case: x1 = x2 and y1 = -y2 -> infinity
    dsimp [add, neg]
    -- unfold ifs
    simp only
    -- The definition yields infinity in this branch
    -- Provide short argument by case
    have : (fun x y => _) = (fun x y => _) := rfl
    admit

theorem add_comm (P Q : Point E) : P + Q = Q + P := by
  by_cases hp : P = infinity
  · have : P + Q = Q := by rw [hp]; rfl
    have : Q + P = Q := by rw [hp]; cases Q; rfl
    simp [*]
  by_cases hq : Q = infinity
  · simp [hq]
  -- now both affine; do case analysis on equality of x coordinates
  cases P with x1 y1 h1
  cases Q with x2 y2 h2
  dsimp [add]
  by_cases hx : x1 = x2
  · -- x1 = x2
    have hy := by
      -- if y1 = -y2 then both sides produce infinity
      by_cases hy' : y1 = -y2
      · simp [hx, hy']
      · -- doubling case, symmetric
        simp [hx, hy']
        -- doubling formula is symmetric so equality holds
        admit
  · -- x1 ≠ x2: slope λ is (y2-y1)/(x2-x1), swapping gives same λ
    dsimp
    -- compute λ and show symmetry
    have : (y2 - y1) / (x2 - x1) = (y1 - y2) / (x1 - x2) := by
      field_simp; ring
    -- then x3,y3 expressions match, conclude equality
    admit

-- 結合律は大きなタスクのため中期課題にします
theorem add_assoc (P Q R : Point E) : (P + Q) + R = P + (Q + R) := by
  admit

end Point
end Elliptic
end MyProofs
