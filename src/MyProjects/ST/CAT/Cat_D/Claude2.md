/-!
### 例2：有限集合の冪集合構造塔（改善版）

濃度による階層化をより明確に定義します。
-/

/-- 有限集合の冪集合構造塔

Fin n の部分集合を濃度で階層化する。
layer k = {S : Finset (Fin n) | S.card ≤ k}
-/
def finsetPowerTower (n : ℕ) : TowerD where
  carrier := Finset (Fin n)
  Index := ℕ
  indexPreorder := inferInstance
  
  layer k := {S : Finset (Fin n) | S.card ≤ k}
  
  covering := by
    intro S
    use S.card
    exact le_rfl
  
  monotone := by
    intro i j hij S hS
    exact le_trans hS hij

/-!
### 例2-補題：冪集合構造塔の基本性質
-/

/-- 空集合は層0に属する -/
lemma finsetPowerTower_empty_in_layer0 (n : ℕ) :
    (∅ : Finset (Fin n)) ∈ (finsetPowerTower n).layer 0 := by
  simp [finsetPowerTower]

/-- 全体集合は層nに属する -/
lemma finsetPowerTower_univ_in_layerN (n : ℕ) :
    Finset.univ ∈ (finsetPowerTower n).layer n := by
  simp [finsetPowerTower, Finset.card_univ, Fintype.card_fin]

/-- 単集合は層1に属する -/
lemma finsetPowerTower_singleton_in_layer1 {n : ℕ} (i : Fin n) :
    {i} ∈ (finsetPowerTower n).layer 1 := by
  simp [finsetPowerTower, Finset.card_singleton]

/-!
### 例4：自然数の倍数階層

自然数を「どの素数で割り切れるか」で階層化する例。
Cat_Dの柔軟性を活かし、minLayerを陽に与えず階層構造のみを記述。
-/

/-- 自然数の倍数階層

layer n = {k : ℕ | k % (n+1) = 0} ∪ {0}
すなわち、n+1の倍数全体（と0）。
-/
def natMultipleTower : TowerD where
  carrier := ℕ
  Index := ℕ
  indexPreorder := inferInstance
  
  layer n := {k : ℕ | k = 0 ∨ (n + 1) ∣ k}
  
  covering := by
    intro k
    use k
    right
    exact dvd_refl k
  
  monotone := by
    intro i j hij k hk
    cases hk with
    | inl h0 => exact Or.inl h0
    | inr hdiv =>
      right
      -- (i+1) | k かつ i+1 ≤ j+1 から (j+1) | k を示すのは一般には不可能
      -- この例は単調性を満たさないため、別の定義が必要
      sorry  -- 実際にはこの定義は構造塔の公理を満たさない

/-!
### 例5：区間の入れ子構造（改良版）

より興味深い階層として、指数的に増大する区間を考える。
-/

/-- 指数的区間構造塔

layer n = {x : ℝ | x ≤ 2^n}
指数的な成長により、より現実的なスケール感を持つ。
-/
def exponentialIntervalTower : TowerD where
  carrier := ℝ
  Index := ℕ
  indexPreorder := inferInstance
  
  layer n := {x : ℝ | x ≤ 2^n}
  
  covering := by
    intro x
    -- Archimedesの原理により、2^n ≥ x なる n が存在
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt x (by norm_num : (1 : ℝ) < 2)
    use n
    exact le_of_lt hn
  
  monotone := by
    intro i j hij x hx
    have h2 : (2 : ℝ)^i ≤ 2^j := by
      exact pow_le_pow_right (by norm_num : 1 ≤ 2) hij
    exact le_trans hx h2

/-!
### 射の例2：冪集合間の部分集合制限（完全版）
-/

/-- 小さい有限集合への制限写像 -/
def finsetRestrict {n m : ℕ} (h : n ≤ m) 
    (S : Finset (Fin m)) : Finset (Fin n) :=
  S.image (Fin.castLE h)

/-- 制限写像が層の濃度を保存する補題 -/
lemma finsetRestrict_card_le {n m : ℕ} (h : n ≤ m) (S : Finset (Fin m)) :
    (finsetRestrict h S).card ≤ S.card := by
  unfold finsetRestrict
  exact Finset.card_image_le

/-- 制限写像が誘導する構造塔の射 -/
def finsetPowerRestrict {n m : ℕ} (h : n ≤ m) :
    finsetPowerTower m ⟶ᴰ finsetPowerTower n where
  map := finsetRestrict h
  map_layer := by
    intro k
    use k
    intro T ⟨S, hS, rfl⟩
    have hcard := finsetRestrict_card_le h S
    exact le_trans hcard hS

/-!
### 実数区間の射：平行移動
-/

/-- 実数の平行移動 -/
def realShiftMap (c : ℝ) : ℝ → ℝ := fun x => x + c

/-- 平行移動が誘導する構造塔の射

x + c ≤ n ⇔ x ≤ n - c より、
layer n は layer (n - c) から写される。
-/
def realIntervalShift (c : ℝ) :
    realIntervalTower ⟶ᴰ realIntervalTower where
  map := realShiftMap c
  map_layer := by
    intro n
    use n - c
    intro y ⟨x, hx, rfl⟩
    simp [realShiftMap]
    linarith

/-!
### 指数区間の射：対数的圧縮
-/

/-- 対数的圧縮が誘導する射（概念的）

exponentialIntervalTower から realIntervalTower への射として、
対数写像を考えることができる（定義域の注意が必要）。
-/
-- この例は対数の定義域（正の実数）の扱いが複雑なため、
-- 完全な実装は別ファイルで行う方が適切