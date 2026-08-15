import Wowii100Full.ComplementBounds

namespace Wowii100Full

open SimpleGraph
open scoped BigOperators

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

lemma degree_le_outside_card (G : SimpleGraph α) [DecidableRel G.Adj]
    (I : Finset α) (hI : G.IsIndepSet I) {i : α} (hi : i ∈ I) :
    G.degree i ≤ Iᶜ.card := by
  rw [← outside_neighbor_count_eq_degree G I hI hi]
  exact Finset.card_le_card (Finset.filter_subset _ _)

lemma inside_compl_degree_balance (G : SimpleGraph α) [DecidableRel G.Adj]
    (I : Finset α) (hI : G.IsIndepSet I) {i : α} (hi : i ∈ I) :
    (Gᶜ.degree i : ℝ) + (G.degree i : ℝ) + 1 = (I.card : ℝ) + (Iᶜ.card : ℝ) := by
  have hdeg : G.degree i ≤ Iᶜ.card := degree_le_outside_card G I hI hi
  have hcard : Iᶜ.card = Fintype.card α - I.card := Finset.card_compl I
  have hIcard : I.card ≤ Fintype.card α := Finset.card_le_univ I
  have hIpos : 0 < I.card := Finset.card_pos.mpr ⟨i, hi⟩
  have htotal : I.card + Iᶜ.card = Fintype.card α := by
    rw [hcard]
    omega
  have hdeg1 : G.degree i + 1 ≤ Fintype.card α := by
    omega
  have hdc : Gᶜ.degree i = Fintype.card α - 1 - G.degree i := by
    simpa using (G.degree_compl (v := i))
  have hnat : Gᶜ.degree i + G.degree i + 1 = I.card + Iᶜ.card := by
    omega
  exact_mod_cast hnat

lemma inside_compl_degree_sum_lower (G : SimpleGraph α) [DecidableRel G.Adj]
    (I : Finset α) (hI : G.IsIndepSet I) :
    (I.card : ℝ) * ((I.card : ℝ) - 1) +
        (Iᶜ.card : ℝ) * ((I.card : ℝ) - (maxLocalIndep G : ℝ)) ≤
      ∑ i ∈ I, (Gᶜ.degree i : ℝ) := by
  classical
  have hsumdegN : (∑ i ∈ I, G.degree i) ≤ Iᶜ.card * maxLocalIndep G :=
    degree_sum_le_outside_mul_maxLocal G I hI
  have hsumdegR : (∑ i ∈ I, (G.degree i : ℝ)) ≤
      (Iᶜ.card : ℝ) * (maxLocalIndep G : ℝ) := by
    exact_mod_cast hsumdegN
  have hbal :
      (∑ i ∈ I, (Gᶜ.degree i : ℝ)) + (∑ i ∈ I, (G.degree i : ℝ)) + (I.card : ℝ) =
        (I.card : ℝ) * ((I.card : ℝ) + (Iᶜ.card : ℝ)) := by
    calc
      (∑ i ∈ I, (Gᶜ.degree i : ℝ)) + (∑ i ∈ I, (G.degree i : ℝ)) + (I.card : ℝ) =
          ∑ i ∈ I, ((Gᶜ.degree i : ℝ) + (G.degree i : ℝ) + 1) := by
            simp_rw [Finset.sum_add_distrib]
            simp
      _ = ∑ i ∈ I, ((I.card : ℝ) + (Iᶜ.card : ℝ)) := by
            apply Finset.sum_congr rfl
            intro i hi
            exact inside_compl_degree_balance G I hI hi
      _ = (I.card : ℝ) * ((I.card : ℝ) + (Iᶜ.card : ℝ)) := by ring
  nlinarith

lemma outside_sq_sum_lower (G : SimpleGraph α) [DecidableRel G.Adj]
    (I : Finset α) (hI : G.IsNIndepSet G.indepNum I) :
    (Iᶜ.card : ℝ) * ((G.indepNum : ℝ) - (maxLocalIndep G : ℝ)) ^ 2 ≤
      ∑ x ∈ Iᶜ, (Gᶜ.degree x : ℝ) ^ 2 := by
  classical
  have hLa : maxLocalIndep G ≤ G.indepNum := maxLocalIndep_le_indepNum G
  have hLaR : (maxLocalIndep G : ℝ) ≤ (G.indepNum : ℝ) := by exact_mod_cast hLa
  calc
    (Iᶜ.card : ℝ) * ((G.indepNum : ℝ) - (maxLocalIndep G : ℝ)) ^ 2 =
        ∑ x ∈ Iᶜ, ((G.indepNum : ℝ) - (maxLocalIndep G : ℝ)) ^ 2 := by simp
    _ ≤ ∑ x ∈ Iᶜ, (Gᶜ.degree x : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro x hx
      have hb := outside_compl_degree_bound G I hI hx
      have hbR : (G.indepNum : ℝ) ≤ (maxLocalIndep G : ℝ) + (Gᶜ.degree x : ℝ) := by
        exact_mod_cast hb
      have hd : 0 ≤ (Gᶜ.degree x : ℝ) := by positivity
      have hdiff : 0 ≤ (G.indepNum : ℝ) - (maxLocalIndep G : ℝ) := by linarith
      nlinarith

lemma inside_cauchy (G : SimpleGraph α) [DecidableRel G.Adj] (I : Finset α) :
    (∑ i ∈ I, (Gᶜ.degree i : ℝ)) ^ 2 ≤
      (I.card : ℝ) * ∑ i ∈ I, (Gᶜ.degree i : ℝ) ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq I (fun _ => (1 : ℝ))
      (fun i => (Gᶜ.degree i : ℝ))
  simpa using h

theorem scaled_norm_lower_bound (G : SimpleGraph α) [DecidableRel G.Adj]
    (I : Finset α) (hI : G.IsNIndepSet G.indepNum I) :
    ((G.indepNum : ℝ) * ((G.indepNum : ℝ) - 1) +
          (Iᶜ.card : ℝ) * ((G.indepNum : ℝ) - (maxLocalIndep G : ℝ))) ^ 2 +
        (G.indepNum : ℝ) * (Iᶜ.card : ℝ) *
          ((G.indepNum : ℝ) - (maxLocalIndep G : ℝ)) ^ 2 ≤
      (G.indepNum : ℝ) * (degreeL2Norm Gᶜ) ^ 2 := by
  classical
  let B : ℝ :=
    (G.indepNum : ℝ) * ((G.indepNum : ℝ) - 1) +
      (Iᶜ.card : ℝ) * ((G.indepNum : ℝ) - (maxLocalIndep G : ℝ))
  have hB : B ≤ ∑ i ∈ I, (Gᶜ.degree i : ℝ) := by
    dsimp [B]
    simpa [hI.card_eq] using inside_compl_degree_sum_lower G I hI.isIndepSet
  have hB0 : 0 ≤ B := by
    dsimp [B]
    have ha1 : (1 : ℝ) ≤ G.indepNum := by
      exact_mod_cast (show 1 ≤ G.indepNum by
        have := indepNum_pos G
        omega)
    have hLaR : (maxLocalIndep G : ℝ) ≤ G.indepNum := by
      exact_mod_cast maxLocalIndep_le_indepNum G
    positivity
  have hsum0 : 0 ≤ ∑ i ∈ I, (Gᶜ.degree i : ℝ) := by positivity
  have hBsq : B ^ 2 ≤ (I.card : ℝ) * ∑ i ∈ I, (Gᶜ.degree i : ℝ) ^ 2 := by
    calc
      B ^ 2 ≤ (∑ i ∈ I, (Gᶜ.degree i : ℝ)) ^ 2 := by nlinarith
      _ ≤ (I.card : ℝ) * ∑ i ∈ I, (Gᶜ.degree i : ℝ) ^ 2 := inside_cauchy G I
  have hout := outside_sq_sum_lower G I hI
  have haR : 0 ≤ (G.indepNum : ℝ) := by positivity
  have hparts :
      (∑ i ∈ I, (Gᶜ.degree i : ℝ) ^ 2) +
        (∑ x ∈ Iᶜ, (Gᶜ.degree x : ℝ) ^ 2) =
        ∑ v, (Gᶜ.degree v : ℝ) ^ 2 := by
    rw [← Finset.sum_add_sum_compl]
  have hnorm : (degreeL2Norm Gᶜ) ^ 2 = ∑ v, (Gᶜ.degree v : ℝ) ^ 2 := by
    unfold degreeL2Norm
    rw [Real.sq_sqrt]
    positivity
  rw [hI.card_eq] at hBsq
  dsimp [B] at hBsq ⊢
  rw [hnorm, ← hparts]
  nlinarith

end Wowii100Full
