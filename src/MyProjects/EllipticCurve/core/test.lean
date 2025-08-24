-- test.leanを以下のように更新
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Formula
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

-- Mathlibの実装を確認
#check WeierstrassCurve.Affine.addChar
#check WeierstrassCurve.Affine.add
#print WeierstrassCurve.Affine.add

-- 加法公式の証明があるか確認
#check WeierstrassCurve.Affine.add_of_Y_ne