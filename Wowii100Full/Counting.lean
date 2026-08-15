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
  simp only [Finset.mem_filter, Finset.mem_compl, Finset.mem_neighborFinset]
  constructor
  · exact fun h => h.2
  · intro hix
    refine ⟨?_, hix⟩
    intro hxI
    exact hI hi hxI (G.ne_of_adj hix) hix

lemma degree_sum_eq_cross_sum (G : SimpleGraph α) [DecidableRel G.Adj]
    (I : Finset α) (hI : G.IsIndepSet I) :
    (∑ i ∈ I, G.degree i) = ∑ x ∈ Iᶜ, crossCount G I x := by
  classical
  rw [← cross_double_count G I Iᶜ]
  apply Finset.sum_congr rfl
  intro i hi
  exact outside_neighbor_count_eq_degree G I hI hi

lemma crossCount_zero_of_mem_indep (G : SimpleGraph α) [DecidableRel G.Adj]
    (I : Finset α) (hI : G.IsIndepSet I) {x : α} (hx : x ∈ I) :
    crossCount G I x = 0 := by
  classical
  apply Finset.card_eq_zero.mpr
  intro i hi
  have hi' := Finset.mem_filter.mp hi
  exact hI hx hi'.1 (G.ne_of_adj hi'.2) hi'.2

end Wowii100Full
