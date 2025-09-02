intervalIntegral まわりの「非負性・単調性で評価」系は、以下の名前で揃っています（μ := volume を想定、実際は任意測度）：

非負性

intervalIntegral.integral_nonneg_of_ae

intervalIntegral.integral_nonneg_of_ae_restrict

intervalIntegral.integral_nonneg_of_forall

（関連）intervalIntegral.integral_pos_iff_support_of_nonneg_ae など。
Lean コミュニティ

被積分関数の単調性（f ≤ g が a.e. など）

intervalIntegral.integral_mono_ae

intervalIntegral.integral_mono_ae_restrict

intervalIntegral.integral_mono_on / intervalIntegral.integral_mono_on_of_le_Ioo

intervalIntegral.integral_mono（便利まとめ版）.
Lean コミュニティ

積分区間に関する単調性（非負なとき、区間を広げると積分は増える）

intervalIntegral.integral_mono_interval

intervalIntegral.abs_integral_mono_interval
Lean コミュニティ

定数やノルムでの上界評価

intervalIntegral.integral_const（∫_[a..b] (fun _ ↦ c) = (b - a) • c）.
Lean コミュニティ

intervalIntegral.norm_integral_le_of_norm_le_const

intervalIntegral.norm_integral_le_of_norm_le_const_ae


把握です。挙げていただいた API 群があれば、gaussian_bounded は次の置換でスッと通せます。

f ≤ g の比較: intervalIntegral.integral_mono_ae / integral_mono_on / integral_mono
非負性と区間拡大: intervalIntegral.integral_nonneg_of_* / integral_mono_interval
定数の積分: intervalIntegral.integral_const
あなたのファイルでの最小置換ポイント

上界（2R）: integral_mono_of_nonneg を integral_mono_ae または integral_mono_on に置換
FinalKadaiPractical.lean
付近

置換前:
intervalIntegral.integral_mono_of_nonneg ...

置換例A（ae 版・一番簡単）:
∫ exp(-x^2) ≤ ∫ 1 は、Ioc(-R,R) 上で a.e. に exp(-x^2) ≤ 1 が言えればOKです。点ごとの不等式を「常に」出しているので、そのまま eventually_of_forall で供給できます。

have h_bound :
  ∫ x in (-R)..R, Real.exp (-x^2) ≤ ∫ x in (-R)..R, (1:ℝ) :=
  intervalIntegral.integral_mono_ae (a := -R) (b := R) (μ := volume)
    hI1 hI2
    (Filter.eventually_of_forall (by intro x; exact h_le_one x))
置換例B（on 版・区間上の点wiseで与える）:

have h_bound :
  ∫ x in (-R)..R, Real.exp (-x^2) ≤ ∫ x in (-R)..R, (1:ℝ) :=
  intervalIntegral.integral_mono_on (a := -R) (b := R) (μ := volume)
    hI1 hI2
    (by intro x hx; exact h_le_one x)
このあと右辺は intervalIntegral.integral_const で 2 * R に評価できます（既存コードのままで可）。

正値（> 0）: 定数下界＋区間拡大

下側評価 on [0, min R 1]
[0,1] で exp(-x^2) ≥ exp(-1) を出す（既に hge_exp 相当をお持ちなので、Ioc 版に調整）。
intervalIntegral.integral_mono_on で
∫_{0}^{min R 1} exp(-1) ≤ ∫_{0}^{min R 1} exp(-x^2)
左辺は intervalIntegral.integral_const で
exp(-1) * (min R 1 - 0) > 0（hR > 0 より min R 1 > 0）
区間拡大で [-R, R] に持ち上げ
非負性: intervalIntegral.integral_nonneg_of_forall 用に ∀ x ∈ Ioc(-R,R), 0 ≤ exp(-x^2) を供給
intervalIntegral.integral_mono_interval で
∫_{0}^{min R 1} exp(-x^2) ≤ ∫_{-R}^{R} exp(-x^2)
これで右辺 > 0 が得られます
API の使い分け要約

関数比較で ∫f ≤ ∫g を出す: integral_mono_ae（AE で f ≤ g）, あるいは integral_mono_on（Ioc 上で点wise f ≤ g）
区間拡大で ∫ が増える（f ≥ 0）: integral_mono_interval
非負・正の足場: integral_nonneg_of_ae / of_forall、定数下界 + integral_const
必要なら、上記の差し替えをこちらでパッチします。どのバリアント（ae / on / mono）を優先したいか教えてください。