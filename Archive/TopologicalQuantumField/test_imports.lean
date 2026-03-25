-- 重要度1 TQFT基盤importのテスト

-- 多様体理論（TQFT の数学的基盤）
import Mathlib.Geometry.Manifold.ChartedSpace      -- 多様体の基本構造
import Mathlib.Geometry.Manifold.Bordism           -- ボルディズム（TQFT の中核概念）

-- 圏論（TQFT は圏論的構造）
import Mathlib.CategoryTheory.Category.Basic       -- 基本的な圏
import Mathlib.CategoryTheory.Monoidal.Category    -- モノイダル圏（テンソル積）

import Mathlib.Tactic

open CategoryTheory MonoidalCategory

-- テスト：基本的な構造が利用可能か確認
#check ChartedSpace
#check MonoidalCategory

-- テスト用の実際の構造
variable (C : Type*) [Category C] [MonoidalCategory C]
variable (H M : Type*) [TopologicalSpace H] [TopologicalSpace M]
variable [ChartedSpace H M]

#check C  -- モノイダル圏
#check M  -- チャート空間を持つ多様体