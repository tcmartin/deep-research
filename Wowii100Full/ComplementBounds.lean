import Wowii100Full.Parameters

namespace Wowii100Full

open SimpleGraph
open scoped BigOperators

variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable def complCrossCount (G : SimpleGraph α) [DecidableRel G.Adj]
    (I : Finset α) (x : α) : ℕ :=
  (I.filter fun i => Gᶜ.Adj x i).card

lemma cross_add_complCross_eq_card (G : SimpleGraph α) [DecidableRel G.Adj]
    (I : Finset α) {x : α} (hx : x ∉ I) :
    crossCount G I x + complCrossCount G I x = I.card := by
  classical
  unfold crossCount complCrossCount
  simp_rw [card_filter_eq_sum_indicator]
  rw [← Finset.sum_add_distrib]
  calc
    (∑ i ∈ I, ((if G.Adj x i then 1 else 0) + if Gᶜ.Adj x i then 1 else 0)) =
        ∑ i ∈ I, 1 := by
      apply Finset.sum_congr rfl
      intro i hi
      have hne : x ≠ i := by
        intro hxi
        apply hx
        simpa [hxi] using hi
      by_cases h : G.Adj x i
      · have hc : ¬ Gᶜ.Adj x i := by simp [h]
        simp [h, hc]
      · have hc : Gᶜ.Adj x i := by simp [hne, h]
        simp [h, hc]
    _ = I.card := by simp

lemma complCrossCount_le_degree (G : SimpleGraph α) [DecidableRel G.Adj]
    (I : Finset α) (x : α) : complCrossCount G I x ≤ Gᶜ.degree x := by
  classical
  unfold complCrossCount
  rw [← Gᶜ.card_neighborFinset_eq_degree]
  apply Finset.card_le_card
  intro i hi
  have hadj : Gᶜ.Adj x i := (Finset.mem_filter.mp hi).2
  simpa using hadj

lemma card_le_cross_add_compl_degree (G : SimpleGraph α) [DecidableRel G.Adj]
    (I : Finset α) {x : α} (hx : x ∉ I) :
    I.card ≤ crossCount G I x + Gᶜ.degree x := by
  rw [← cross_add_complCross_eq_card G I hx]
  exact Nat.add_le_add_left (complCrossCount_le_degree G I x) _

/-- Pointwise complement-degree bound for vertices outside a maximum independent set. -/
lemma outside_compl_degree_bound (G : SimpleGraph α) [DecidableRel G.Adj]
    (I : Finset α) (hI : G.IsNIndepSet G.indepNum I) {x : α} (hx : x ∈ Iᶜ) :
    G.indepNum ≤ maxLocalIndep G + Gᶜ.degree x := by
  classical
  have hxnot : x ∉ I := by simpa using hx
  have hbase := card_le_cross_add_compl_degree G I hxnot
  have hlocal : crossCount G I x ≤ maxLocalIndep G :=
    (crossCount_le_local G I hI.isIndepSet x).trans (local_le_maxLocalIndep G x)
  rw [hI.card_eq] at hbase
  omega

end Wowii100Full
