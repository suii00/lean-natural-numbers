-- 完全な測度論importのテスト

-- 測度の基本定義（基本的な測度空間）
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

-- より詳細な測度の性質（これが従来の "Basic" に相当）
import Mathlib.MeasureTheory.Measure.MeasureSpace

-- Bochner積分（ベクトル値関数の積分）
import Mathlib.MeasureTheory.Integral.Bochner.Basic

-- Lebesgue積分（非負値関数の積分）  
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

-- 可測空間（既に確認済み）
import Mathlib.MeasureTheory.MeasurableSpace.Basic

import Mathlib.Tactic

-- テスト：完全な測度論構造
#check MeasureTheory.MeasureSpace
#check MeasureTheory.Measure
#check MeasurableSpace

-- 積分構造のテスト
variable (α : Type*) [MeasureTheory.MeasureSpace α]
variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (f : α → E)

#check ∫ x, f x                      -- Bochner積分が利用可能
-- Lebesgue積分は構文確認を省略