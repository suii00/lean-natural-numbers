-- Mathlib 4の中国剰余定理 完全使用ガイド
-- Mathlib.Data.Nat.ChineseRemainder.lean

import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.ModEq

/-!
# 基本的な使用方法

## 1. 主要な定義と定理

### chineseRemainderOfList
リストを使った中国剰余定理の実装。これが最も基本的で重要な関数です。

型署名:
```lean
Nat.chineseRemainderOfList (a : ι → ℕ) (s : ι → ℕ) (l : List ι) 
  (co : List.Pairwise (Nat.Coprime on s) l) : 
  { k : ℕ // ∀ i ∈ l, k ≡ a i [MOD s i] }
```

パラメータ:
- `a`: 剰余値を返す関数 (a i が i での剰余)
- `s`: 法を返す関数 (s i が i での法)
- `l`: インデックスのリスト
- `co`: s関数がlの要素で互いに素であることの証明
-/

-- 例1: 基本的な3つの数での中国剰余定理
example : ∃ x : ℕ, x % 3 = 2 ∧ x % 5 = 3 ∧ x % 7 = 2 := by
  -- 手動での計算例
  use 23
  norm_num

-- 例2: chineseRemainderOfListを使った解法
def solve_crt_basic : ℕ := by
  let a : Fin 3 → ℕ := ![2, 3, 2]  -- 剰余
  let s : Fin 3 → ℕ := ![3, 5, 7]  -- 法
  let l : List (Fin 3) := [0, 1, 2]
  
  -- 互いに素の証明が必要
  have co : List.Pairwise (Nat.Coprime on s) l := by
    simp [List.Pairwise]
    norm_num [Nat.Coprime]
    
  exact (Nat.chineseRemainderOfList a s l co).val

-- 例3: より実用的な使用例（型推論を活用）
def crt_example_1 : ℕ := by
  let mods := [3, 5, 7]
  let remainders := [2, 3, 2]
  
  -- 実際の実装では、Finsetやリストの処理が必要
  sorry -- 実装は複雑になるため省略

/-!
## 2. 重要な定理と補題

### 解の範囲
chineseRemainderOfList_lt_prod: 解は法の積より小さい
-/

theorem solution_bound_example (a : Fin 3 → ℕ) (s : Fin 3 → ℕ) 
  (l : List (Fin 3)) (co : List.Pairwise (Nat.Coprime on s) l) :
  (Nat.chineseRemainderOfList a s l co).val < List.prod (List.map s l) :=
  Nat.chineseRemainderOfList_lt_prod a s l co (by simp [List.map_map])

/-!
### 解の一意性
chineseRemainderOfList_modEq_unique: 条件を満たす数は解と合同
-/

theorem solution_uniqueness_example (a : Fin 3 → ℕ) (s : Fin 3 → ℕ) 
  (l : List (Fin 3)) (co : List.Pairwise (Nat.Coprime on s) l) 
  (z : ℕ) (hz : ∀ i ∈ l, z ≡ a i [MOD s i]) :
  z ≡ (Nat.chineseRemainderOfList a s l co).val [MOD List.prod (List.map s l)] :=
  Nat.chineseRemainderOfList_modEq_unique a s l co hz

/-!
## 3. Finsetバージョンの使用

### chineseRemainderOfFinset
有限集合を使った版。多くの場合、こちらの方が使いやすい。
-/

def crt_finset_example : ℕ := by
  let indices : Finset (Fin 3) := {0, 1, 2}
  let a : Fin 3 → ℕ := ![2, 3, 2]
  let s : Fin 3 → ℕ := ![3, 5, 7]
  
  -- 互いに素の証明
  have hs : ∀ i ∈ indices, s i ≠ 0 := by simp [indices]; norm_num
  have pp : Set.Pairwise (↑indices) (Nat.Coprime on s) := by
    simp [Set.Pairwise, indices]
    norm_num [Nat.Coprime]
  
  exact (Nat.chineseRemainderOfFinset a s indices hs pp).val

/-!
## 4. 実用的な関数の定義

実際のプログラムで使いやすい形に包んだ関数
-/

-- 自然数のリストから中国剰余定理を解く
def solve_chinese_remainder (mods remainders : List ℕ) 
  (h_len : mods.length = remainders.length)
  (h_pos : ∀ m ∈ mods, m ≠ 0)
  (h_coprime : List.Pairwise Nat.Coprime mods) : ℕ := by
  -- 実装は複雑になるため、概念的な構造のみ示す
  -- 実際にはList.zipWithIndex等を使って実装
  sorry

-- より簡単な2つの数での中国剰余定理
def solve_crt_two (m₁ m₂ : ℕ) (a₁ a₂ : ℕ) 
  (h_coprime : Nat.Coprime m₁ m₂) : ℕ := by
  let a : Fin 2 → ℕ := ![a₁, a₂]
  let s : Fin 2 → ℕ := ![m₁, m₂]
  let l : List (Fin 2) := [0, 1]
  
  have co : List.Pairwise (Nat.Coprime on s) l := by
    simp [List.Pairwise]
    exact h_coprime
    
  exact (Nat.chineseRemainderOfList a s l co).val

-- 使用例
#eval solve_crt_two 3 5 2 3 (by norm_num : Nat.Coprime 3 5)  -- 8が期待される

/-!
## 5. エラーハンドリングとデバッグ

### よくある問題と解決法
-/

-- 問題1: 互いに素でない場合のエラー
example : False := by
  -- これは失敗する例
  let m₁ : ℕ := 6
  let m₂ : ℕ := 9  -- gcd(6, 9) = 3 ≠ 1
  -- have h : Nat.Coprime m₁ m₂ := by norm_num  -- これは証明できない
  sorry

-- 問題2: 法が0の場合
example : False := by
  -- これも失敗する例
  let s : Fin 2 → ℕ := ![3, 0]  -- 0は法として使えない
  -- have hs : ∀ i ∈ ({0, 1} : Finset (Fin 2)), s i ≠ 0 := by simp [s]  -- 証明できない
  sorry

/-!
## 6. 高度な使用例

### 多数の法での中国剰余定理
-/

def large_crt_example : ℕ := by
  -- 10個の互いに素な法での例
  let mods : Fin 10 → ℕ := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29]
  let remainders : Fin 10 → ℕ := ![1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
  let indices : List (Fin 10) := List.range 10 |>.map Fin.ofNat'
  
  -- 互いに素の証明（素数なので自明）
  have co : List.Pairwise (Nat.Coprime on mods) indices := by
    -- 素数は互いに素なので証明可能
    sorry
    
  exact (Nat.chineseRemainderOfList remainders mods indices co).val

/-!
## 7. パフォーマンスと最適化

### 大きな数での計算時の注意点
-/

-- 計算効率を考慮した実装
def efficient_crt (mods remainders : Array ℕ) : Option ℕ := by
  -- 実際の実装では以下を考慮：
  -- 1. 事前条件のチェック（互いに素、非零）
  -- 2. 効率的なアルゴリズム（拡張ユークリッド算法）
  -- 3. 大きな数でのオーバーフロー対策
  sorry

/-!
## 8. テストとベリフィケーション

### 解の検証
-/

def verify_crt_solution (mods remainders : List ℕ) (solution : ℕ) : Bool :=
  List.zip mods remainders |>.all (fun (m, r) => solution % m = r)

-- テスト例
example : verify_crt_solution [3, 5, 7] [2, 3, 2] 23 = true := by
  simp [verify_crt_solution]
  norm_num

/-!
## 9. Mathlib内の関連定理

### ModEqとの連携
-/

-- ModEq記法との組み合わせ
example (x : ℕ) : x ≡ 2 [MOD 3] ∧ x ≡ 3 [MOD 5] → x ≡ 8 [MOD 15] := by
  intro h
  -- 中国剰余定理を使った証明
  sorry

/-!
## 10. 実際のプロジェクトでの使用パターン

### 暗号学での応用
-/

-- RSA暗号での中国剰余定理の使用例
def rsa_crt_optimization (p q : ℕ) (c : ℕ) (dp dq : ℕ) 
  (h_prime_p : Nat.Prime p) (h_prime_q : Nat.Prime q) 
  (h_coprime : Nat.Coprime p q) : ℕ := by
  -- c^dp mod p と c^dq mod q を計算してから
  -- 中国剰余定理で結合
  let mp := c % p
  let mq := c % q
  let vp := mp ^ dp % p
  let vq := mq ^ dq % q
  
  -- 中国剰余定理を適用
  exact solve_crt_two p q vp vq h_coprime

/-!
## 使用上の注意点とベストプラクティス

1. **事前条件の確認**: 必ず法が互いに素であることを確認
2. **型安全性**: Mathlib 4では型レベルで多くの制約が表現される
3. **計算効率**: 大きな数では専用の最適化アルゴリズムを検討
4. **エラーハンドリング**: Option型やExcept型での安全な実装
5. **テスト**: 必ず小さな例でテストしてから本格的な計算に使用

## 関連ファイル
- `Mathlib.Data.Nat.ModEq`: 合同式の基本的な性質
- `Mathlib.Data.Nat.GCD`: 最大公約数と互いに素の性質
- `Mathlib.RingTheory.ChineseRemainder`: より一般的な環での中国剰余定理
-/