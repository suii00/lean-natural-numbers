# ADR-0003: homeq / Cat_eq の用語整理

## Status
Accepted (2025-12-17)

## Context
homeq と Cat_eq が「minLayer 等号保存」と「bijective HomLe」を混同していた。

## Decision
- homeq := StructureTowerWithMin.Hom (minLayer_preserving = 等号)
- TowerD 側の bijective HomLe は HomLeBij として別概念に分離
- Cat_eq は「真の同型（逆も layer_preserving）」にのみ使用する

## Consequences
- 用語衝突が消え、Cat2 と TowerD の役割が明確になる
- 既存の TowerD.HomEq は改名・移動が必要
