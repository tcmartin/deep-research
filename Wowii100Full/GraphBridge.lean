import Wowii100Full.Arithmetic

namespace Wowii100Full

open SimpleGraph
open scoped BigOperators

variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable def crossCount (G : SimpleGraph α) [DecidableRel G.Adj]
    (I : Finset α) (x : α) : ℕ :=
  (I.filter fun i => G.Adj x i).card

lemma crossCount_le_local (G : SimpleGraph α) [DecidableRel G.Adj]
    (I : Finset α) (hI : G.IsIndepSet I) (x : α) :
    crossCount G I x ≤ indepNeighborsCard G x := by
  classical
  let H := G.induce (G.neighborSet x)
  let S : Finset (G.neighborSet x) :=
    Finset.univ.filter (fun y => (y.1 : α) ∈ I)
  have hS : H.IsIndepSet S := by
    intro y hy z hz hyz
    have hyI : (y.1 : α) ∈ I := by
      simpa [S] using hy
    have hzI : (z.1 : α) ∈ I := by
      simpa [S] using hz
    have hne : (y.1 : α) ≠ z.1 := by
      intro hval
      apply hyz.ne
      exact Subtype.ext hval
    exact hI hyI hzI hne hyz
  have hle := hS.card_le_indepNum
  change S.card ≤ indepNeighborsCard G x at hle
  have hcard : S.card = crossCount G I x := by
    simp [S, crossCount, SimpleGraph.mem_neighborSet, G.adj_comm]
  simpa [hcard] using hle

lemma cross_double_count (G : SimpleGraph α) [DecidableRel G.Adj]
    (I J : Finset α) :
    (∑ i ∈ I, (J.filter fun x => G.Adj i x).card) =
      ∑ x ∈ J, crossCount G I x := by
  classical
  simp [crossCount, Finset.card_eq_sum_ones, Finset.sum_comm, G.adj_comm]

end Wowii100Full
