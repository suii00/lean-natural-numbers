-- 重要度3 TQFT中重要度基盤importのテスト

-- 測度論（経路積分の基盤）
import Mathlib.MeasureTheory.MeasurableSpace.Basic  -- 可測空間

-- 束理論（ゲージ場理論）
import Mathlib.Topology.FiberBundle.Basic          -- ファイバー束
import Mathlib.Topology.VectorBundle.Basic         -- ベクトル束

import Mathlib.Tactic

-- テスト：重要度3構造が利用可能か確認
#check MeasurableSpace
#check FiberBundle
#check VectorBundle

-- テスト用の実際の構造
variable (α : Type*) [MeasurableSpace α]
variable (B : Type*) [TopologicalSpace B]
variable (F : Type*) [TopologicalSpace F]
variable (E : B → Type*) [(b : B) → TopologicalSpace (E b)]
variable [TopologicalSpace (Bundle.TotalSpace F E)]

#check α                              -- 可測空間
#check FiberBundle F E                -- ファイバー束（正しい構文）