import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Topology.Basic
import Mathlib.Topology.Instances.Real.Lemmas
/-!
# Phase 0: 微分の基礎と連続性

このモジュールは `src/MyProjects/Set/Integral/P0.md` に記された Bourbaki 風の課題を Lean 上で再現するものです。
高校的な直感と大学・形式数学の厳密性をつなぐために、mathlib の定理（`deriv_const`, `deriv_id`, `deriv_add`, `continuous_const`, `continuous_id`, `Continuous.comp`, `Continuous.add`）を順番に活用します。

## 例
- `deriv_const` を使って定数関数の導関数が 0 になることを示す
- `Continuous.comp` によって連続関数の合成が連続であることを確かめる
- `deriv_add` には `Differentiable` という仮定が必要なことも示す
-/

namespace MyProjects.Set.Integral.P0

example (c : ℝ) : deriv (fun _ : ℝ => c) = fun _ : ℝ => 0 := by
  ext x
  simp [deriv_const]

example : deriv (fun x : ℝ => x) = fun _ : ℝ => 1 := by
  ext x
  simp [deriv_id]

example (f g : ℝ → ℝ) (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
    deriv (fun x : ℝ => f x + g x) = fun x => deriv f x + deriv g x := by
  ext x
  simp [hf.differentiableAt, hg.differentiableAt, deriv_add]

example (c : ℝ) : Continuous (fun _ : ℝ => c) := continuous_const

example : Continuous (fun x : ℝ => x) := continuous_id

example (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) :
    Continuous fun x => f (g x) := hf.comp hg

example (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) :
    Continuous fun x => f x + g x := hf.add hg

end MyProjects.Set.Integral.P0
