import Wowii100Full.GraphBridge
import Wowii100Full.InvariantLemmas

namespace Wowii100Full

open SimpleGraph
open scoped BigOperators

variable {α : Type*} [Fintype α] [DecidableEq α]

lemma outside_neighbor_count_eq_degree (G : SimpleGraph α) [DecidableRel G.Adj]
    (I : Finset α) (hI : G.IsIndepSet I) {i : α} (hi : i ∈ I) :
    ((Iᶜ).filter fun x => G.Adj i x).card = G.degree i := by
  classical
  rw [← G.card_neighborFinset_eq_degree]
  congr 1
  ext x
  constructor
  · intro hx
    have h := Finset.mem_filter.mp hx
    simpa using h.2
  · intro hx
    have hix : G.Adj i x := by simpa using hx
    apply Finset.mem_filter.mpr
    refine ⟨?_, hix⟩
    simp only [Finset.mem_compl]
    intro hxI
    exact hI hi hxI (G.ne_of_adj hix) hix

lemma degree_sum_eq_cross_sum (G : SimpleGraph α) [DecidableRel G.Adj]
    (I : Finset α) (hI : G.IsIndepSet I) :
    (∑ i ∈ I, G.degree i) = ∑ x ∈ Iᶜ, crossCount G I x := by
  classical
  rw [← cross_double_count G I Iᶜ]
  apply Finset.sum_congr rfl
  intro i hi
  exact (outside_neighbor_count_eq_degree G I hI hi).symm

lemma crossCount_zero_of_mem_indep (G : SimpleGraph α) [DecidableRel G.Adj]
    (I : Finset α) (hI : G.IsIndepSet I) {x : α} (hx : x ∈ I) :
    crossCount G I x = 0 := by
  classical
  unfold crossCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro i hiI
  intro hadj
  exact hI hx hiI (G.ne_of_adj hadj) hadj

end Wowii100Full
