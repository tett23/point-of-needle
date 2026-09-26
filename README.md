# PointOfNeedle

針の上で天使は何人踊れるか — その答えが**計算可能**であることの Lean 4 + Mathlib による形式証明。

証明本体: [PointOfNeedle/Basic.lean](PointOfNeedle/Basic.lean)

| 定理 | 内容 |
|---|---|
| `capacity_eq_iff`, `canDance_iff` | 任意の有限な針・決定可能な「近すぎる」関係で、全探索 `capacity` が真の最大人数であり、「k 人踊れるか」は決定可能 |
| `danceCapacity_eq` | n×n プランク格子上で、各天使が周囲 8 マスを必要とするとき、最大人数 = ⌈n/2⌉² |
| `danceCapacity_primrec` / `danceCapacity_computable` | その関数は原始再帰的、したがって Mathlib の意味で `Computable` |
| `canDance_primrecPred` | 「(n, k) で k 人踊れるか」は原始再帰述語 |
| `thomisticCapacity_eq` | トマス説（同じ場所に二天使は居られない）では n²、これも計算可能 |
| `overlapping_unbounded` | 天使が自由に重なれるなら有限の上限は存在しない |

## あらゆる天使の分類（アクィナス説を仮定しない）

[PointOfNeedle/AllAngels.lean](PointOfNeedle/AllAngels.lean)

| 天使の存在様態 | 踊れる数 | 定理 |
|---|---|---|
| 非物質的（占める場所なし／大きさ0の点） | 上限なし。いくらでも踊れる | `immaterial_canDance`, `point_angels_unbounded` |
| 有限個の場所・任意の身体形状・大小の聖歌隊が混在・1か所に c 人まで重なれる | 有限。c·\|P\| 以下で、最大値は全探索で計算できる | `count_le`, `maxDancers_spec` |
| 離散モデルの有限性の必要十分条件 | 有限 ⇔ 非物質的な天使がいない | `bounded_iff` |
| 離散モデルの「k 人踊れるか」 | どの様態でも決定可能 | `canDance_iff` |
| 連続体・大きさ ≥ ε > 0 | 有限。μ(針) / ε 以下 | `card_mul_le_measure`, `bounded_of_size_ge` |
| 連続体・種類が有限（九つの聖歌隊など）で各種類の大きさが正 | 有限 | `bounded_of_finite_kinds` |
| 連続体・大きさは正だが下限なし | 高々可算だが、同時に無限人が踊れて有限の上限はない | `countable_of_material`, `infinitely_many_shrinking` |

直径約 1mm の針（約 6.2×10³¹ プランク長）では 9.61×10⁶² 人。

```bash
lake build
```

## License

MIT — see [LICENSE](LICENSE).
