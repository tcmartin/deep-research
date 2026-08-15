import Wowii100Full.Arithmetic

namespace Wowii100Full

open SimpleGraph
open scoped BigOperators

variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable def crossCount (G : SimpleGraph α) [DecidableRel G.Adj]
    (I : Finset α) (x : α) : ℕ :=
  (I.filter fun i => G.Adj x i).card

lemma card_filter_eq_sum_indicator (s : Finset α) (p : α → Prop) [DecidablePred p] :
    (s.filter p).card = ∑ x ∈ s, if p x then 1 else 0 := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      by_cases hp : p a <;> simp [ha, hp, ih]

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
      apply hyz
      exact Subtype.ext hval
    intro hadj
    exact hI hyI hzI hne hadj
  have hle := hS.card_le_indepNum
  change S.card ≤ indepNeighborsCard G x at hle
  have hcard : S.card = crossCount G I x := by
    unfold crossCount
    apply Finset.card_bij (fun y _ => y.1)
    · intro y hy
      have hyI : (y.1 : α) ∈ I := by simpa [S] using hy
      exact Finset.mem_filter.mpr ⟨hyI, y.2⟩
    · intro y₁ hy₁ y₂ hy₂ hval
      exact Subtype.ext hval
    · intro i hi
      have hi' := Finset.mem_filter.mp hi
      refine ⟨⟨i, hi'.2⟩, ?_, rfl⟩
      simp [S, hi'.1]
  simpa [hcard] using hle

lemma cross_double_count (G : SimpleGraph α) [DecidableRel G.Adj]
    (I J : Finset α) :
    (∑ i ∈ I, (J.filter fun x => G.Adj i x).card) =
      ∑ x ∈ J, crossCount G I x := by
  classical
  simp_rw [card_filter_eq_sum_indicator]
  unfold crossCount
  simp_rw [card_filter_eq_sum_indicator]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro i hi
  rw [G.adj_comm]

end Wowii100Full
