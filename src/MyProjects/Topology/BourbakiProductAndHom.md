# BourbakiProductAndHom — Ordered Pairs, Projections, and Morphisms

本ノートは `src/MyProjects/Topology/BourbakiProductAndHom.lean` の数学的背景を、ニコラ・ブルバキ『数学原論』の精神（集合・順序対・射と射影による構造化）に沿って解説します。

## 哲学的背景（ブルバキ流）
- 構造の担い手は集合であり、順序対 `(x, y)` は射影 `π₁, π₂`（第一・第二射影）を通じて特徴づける。
- 直積位相は「射影が連続になる最弱の位相」として与えられる。ゆえに連続性は射影を通じて検査できる。
- 構造保存写像（群準同型など）は合成に関して閉じており、圏論的には対象（構造つき集合）と射（構造保存写像）からなる圏を成す。
- 位相群では群構造と位相が両立し、基本的な構造射（積・逆元・単位）が連続となる。

## ファイル内の主な定義・定理

- `π₁ : X × Y → X`, `π₂ : X × Y → Y`
  - 順序対の射影。Lean では既存の `Prod.fst`, `Prod.snd` に対応するが、ブルバキ的説明のため名前を与えている。
  - `continuous_π₁`, `continuous_π₂` により射影が連続であることを確認。

- `continuous_prod_map`
  - 内容: `f : X → Z`, `g : Y → W` が連続なら、`X × Y → Z × W, p ↦ (f p.1, g p.2)` は連続。
  - 意味: 射影を介した普遍性により、「成分が連続なら対の組も連続」という標準事実（直積の構造の普遍性）。
  - 証明要旨: `continuous_fst/snd` と合成の連続性、`Continuous.prodMk` を用いる。

- `groupHomComp (φ : G →* H) (ψ : H →* K) : G →* K`
  - 群準同型（Mathlib では `MonoidHom`）の合成。圏論的合成に一致。
  - `@[simp] groupHomComp_apply` で `groupHomComp φ ψ g = ψ (φ g)` が即約できる。

- `topological_group_hom_continuous_inv`
  - 内容: 位相群 `H` に対し、`f : G →* H` が連続なら、`g ↦ (f g)⁻¹` も連続。
  - 意味: `H` の逆元写像 `inv : H → H` の連続性と、`f` の連続性の合成。
  - 重要点: 連続性に必要なのは `H` 側の位相群構造（`IsTopologicalGroup H`）であり、`G` は位相空間であれば十分。

## 直積の普遍性と射影の役割
- 普遍性（ユニバーサル・プロパティ）: 射影 `π₁, π₂` が連続である最弱の位相を `X × Y` に入れる。任意の空間 `T` からの写像 `h : T → X × Y` が連続であることは、合成 `π₁ ∘ h`, `π₂ ∘ h` の両方が連続であることと同値。
- 本ファイルの `continuous_prod_map` は、特定の `h`（成分ごとに与えられた連続写像）についてこの原理を具体化したもの。

## Lean 実装上のポイント
- 直積と射影: `continuous_fst`, `continuous_snd` を利用。
- 合成と対の構成: `Continuous.comp`, `Continuous.prodMk` を利用。
- 群準同型の合成: `MonoidHom.comp` による定義をラップ（`groupHomComp`）。
- 位相群の逆写像の連続性: `continuous_inv : Continuous fun h : H => h⁻¹` を用い、`continuous_inv.comp hf` で結論。
- 依存関係: `TopologicalSpace` 構造、`Group` 構造、位相群性は `IsTopologicalGroup H` のみを要求（`G` 側は不要）。

## 簡単な使用例（スケッチ）

- 直積の連続写像
```lean
variable {X Y Z W : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y]
variable [TopologicalSpace Z] [TopologicalSpace W]
variable {f : X → Z} {g : Y → W}

example (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun p : X × Y => (f p.1, g p.2)) :=
  continuous_prod_map hf hg
```

- 群準同型の合成
```lean
variable {G H K : Type*} [Group G] [Group H] [Group K]
variable (φ : G →* H) (ψ : H →* K) (g : G)

#simp groupHomComp_apply φ ψ g -- ⊢ groupHomComp φ ψ g = ψ (φ g)
```

- 位相群での逆元合成の連続性
```lean
variable {G H : Type*}
variable [TopologicalSpace G] [Group G]
variable [TopologicalSpace H] [Group H] [IsTopologicalGroup H]
variable (f : G →* H)

example (hf : Continuous f) : Continuous (fun g : G => (f g)⁻¹) :=
  topological_group_hom_continuous_inv f hf
```

## 拡張の方向性
- 普遍性の同値を明示する補題（`h` の連続性 ↔ 射影合成の連続性）を追加。
- `Top`（位相空間の圏）や `Grp`（群の圏）での関手的な整理：`prod` の普遍性、`MonoidHom` の合成の結合性や単位律の明示。
- 位相群の基本射（積・逆・単位）の連続性をまとめた API との接合と、具体例（例：実数加法群）でのインスタンス化。

以上により、順序対と射影に基づくブルバキ的「構造＋射」の視点で、直積位相・群準同型・位相群の継続性を Lean 上で明確に表現しています。
