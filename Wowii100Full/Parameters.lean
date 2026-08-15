import Wowii100Full.Counting

namespace Wowii100Full

open SimpleGraph
open scoped BigOperators

variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable def maxLocalIndep (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  (Finset.univ.image (indepNeighborsCard G)).max' (by simp)

lemma local_le_maxLocalIndep (G : SimpleGraph α) [DecidableRel G.Adj] (v : α) :
    indepNeighborsCard G v ≤ maxLocalIndep G := by
  classical
  unfold maxLocalIndep
  apply Finset.le_max'
  exact Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩

lemma maxLocalIndep_le_indepNum (G : SimpleGraph α) [DecidableRel G.Adj] :
    maxLocalIndep G ≤ G.indepNum := by
  classical
  unfold maxLocalIndep
  apply Finset.max'_le
  intro y hy
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
  exact indepNeighborsCard_le_indepNum G v

lemma indepNum_pos [Nonempty α] (G : SimpleGraph α) : 0 < G.indepNum := by
  classical
  let v : α := Classical.choice ‹Nonempty α›
  have hsingle : G.IsIndepSet ({v} : Finset α) := by simp
  have hle := hsingle.card_le_indepNum
  simpa using hle

lemma one_le_maxLocalIndep_of_connected [Nontrivial α]
    (G : SimpleGraph α) [DecidableRel G.Adj] (hconn : G.Connected) :
    1 ≤ maxLocalIndep G := by
  classical
  let v : α := Classical.choice (inferInstance : Nonempty α)
  have hd : 0 < G.degree v := hconn.preconnected.degree_pos_of_nontrivial v
  obtain ⟨w, hw⟩ := (G.degree_pos_iff_exists_adj v).mp hd
  let w' : G.neighborSet v := ⟨w, hw⟩
  have hs : (G.induce (G.neighborSet v)).IsIndepSet ({w'} : Finset (G.neighborSet v)) := by
    simp
  have hlocal : 1 ≤ indepNeighborsCard G v := by
    have hle := hs.card_le_indepNum
    simpa [indepNeighborsCard] using hle
  exact hlocal.trans (local_le_maxLocalIndep G v)

/-- For a maximum independent set `I`, if `m` is the number of vertices outside `I`
and `L` is the maximum neighborhood independence number, connectedness gives `α ≤ mL`. -/
lemma indepNum_le_outside_mul_maxLocal [Nontrivial α]
    (G : SimpleGraph α) [DecidableRel G.Adj] (hconn : G.Connected)
    (I : Finset α) (hI : G.IsNIndepSet G.indepNum I) :
    G.indepNum ≤ Iᶜ.card * maxLocalIndep G := by
  classical
  have hdeg : ∀ i ∈ I, 1 ≤ G.degree i := by
    intro i hi
    exact hconn.preconnected.degree_pos_of_nontrivial i
  have hlower : I.card ≤ ∑ i ∈ I, G.degree i := by
    calc
      I.card = ∑ i ∈ I, 1 := by simp
      _ ≤ ∑ i ∈ I, G.degree i := by
        apply Finset.sum_le_sum
        intro i hi
        exact hdeg i hi
  have hcross := degree_sum_eq_cross_sum G I hI.isIndepSet
  have hupper : (∑ x ∈ Iᶜ, crossCount G I x) ≤ Iᶜ.card * maxLocalIndep G := by
    calc
      (∑ x ∈ Iᶜ, crossCount G I x) ≤ ∑ x ∈ Iᶜ, maxLocalIndep G := by
        apply Finset.sum_le_sum
        intro x hx
        exact (crossCount_le_local G I hI.isIndepSet x).trans
          (local_le_maxLocalIndep G x)
      _ = Iᶜ.card * maxLocalIndep G := by simp
  rw [hI.card_eq]
  exact hlower.trans (hcross.le.trans hupper)

end Wowii100Full
