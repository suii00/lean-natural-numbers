-- 重要度2 TQFT基盤importのテスト

-- 代数的位相幾何学（位相不変量の基盤）
import Mathlib.Topology.Homotopy.Basic             -- ホモトピー理論
import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic  -- 基本群（結び目理論）

-- 線形代数（量子状態空間）
import Mathlib.LinearAlgebra.TensorProduct.Basic   -- テンソル積
import Mathlib.Analysis.InnerProductSpace.Basic    -- ヒルベルト空間

import Mathlib.Tactic

-- テスト：重要度2構造が利用可能か確認
#check ContinuousMap.Homotopy
#check FundamentalGroupoid
#check TensorProduct  
#check InnerProductSpace

-- テスト用の実際の構造
variable (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y]
variable (R : Type*) [CommRing R]
variable (M N : Type*) [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
variable (f₀ f₁ : C(X, Y))

#check ContinuousMap.Homotopy f₀ f₁  -- ホモトピー
#check FundamentalGroupoid X         -- 基本群oid
#check TensorProduct R M N           -- テンソル積