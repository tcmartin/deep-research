import FormalConjecturesUtil

open SimpleGraph
open scoped BigOperators

#check SimpleGraph.exists_isNIndepSet_indepNum
#check SimpleGraph.IsIndepSet.card_le_indepNum
#check SimpleGraph.isIndepSet_induce
#check SimpleGraph.degree_compl
#check SimpleGraph.card_neighborFinset_eq_degree
#check SimpleGraph.Connected.degree_pos
#check Finset.sum_sq_le_card_mul_sum_sq
#check Finset.sum_mul
#check Real.sq_sqrt
#check Real.sqrt_le_iff
#check Real.le_sqrt
#check Int.le_ceil
#check Int.ceil_lt_add_one
#check Nat.cast_le

namespace Graffiti100

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

example (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    let maxL := (Finset.univ.image (indepNeighborsCard G)).max' (by simp)
    (G.indepNum : ℝ) ≤ ⌈((maxL : ℝ) + (1 / 2) * (degreeL2Norm Gᶜ : ℝ)) / 2⌉ := by
  dsimp
  sorry

end Graffiti100
