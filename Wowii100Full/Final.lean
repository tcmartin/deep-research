import Wowii100Full.NormBound

namespace Wowii100Full

open SimpleGraph
open scoped BigOperators

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- Fully assembled proof of WOWII / Graffiti.pc Conjecture 100, using the exact
invariants from the formal-conjectures statement. -/
theorem full_conjecture100_core (G : SimpleGraph α) [DecidableRel G.Adj]
    (hconn : G.Connected) :
    (G.indepNum : ℝ) ≤
      ⌈((maxLocalIndep G : ℝ) + (1 / 2 : ℝ) * degreeL2Norm Gᶜ) / 2⌉ := by
  classical
  obtain ⟨I, hI⟩ := G.exists_isNIndepSet_indepNum
  have ha1 : 1 ≤ G.indepNum := by
    have hp := indepNum_pos G
    omega
  have hL1 : 1 ≤ maxLocalIndep G := one_le_maxLocalIndep_of_connected G hconn
  have hLa : maxLocalIndep G ≤ G.indepNum := maxLocalIndep_le_indepNum G
  have ham : G.indepNum ≤ Iᶜ.card * maxLocalIndep G :=
    indepNum_le_outside_mul_maxLocal G hconn I hI
  have hN0 : 0 ≤ degreeL2Norm Gᶜ := by
    unfold degreeL2Norm
    exact Real.sqrt_nonneg _
  have hthreshold :
      (G.indepNum : ℝ) - 1 <
        ((maxLocalIndep G : ℝ) + (1 / 2 : ℝ) * degreeL2Norm Gᶜ) / 2 := by
    by_cases haeq : G.indepNum = 1
    · have hL1R : (1 : ℝ) ≤ maxLocalIndep G := by exact_mod_cast hL1
      rw [haeq]
      norm_num
      nlinarith
    · have ha2 : 2 ≤ G.indepNum := by omega
      have hcore := arithmetic_core G.indepNum (maxLocalIndep G) Iᶜ.card
        ha2 hL1 hLa ham
      have hscaled := scaled_norm_lower_bound G I hI
      have haR : (0 : ℝ) < G.indepNum := by exact_mod_cast (show 0 < G.indepNum by omega)
      have hsq :
          (4 * ((G.indepNum : ℝ) - 1) - 2 * (maxLocalIndep G : ℝ)) ^ 2 <
            (degreeL2Norm Gᶜ) ^ 2 := by
        nlinarith
      have hT0 :
          0 ≤ 4 * ((G.indepNum : ℝ) - 1) - 2 * (maxLocalIndep G : ℝ) := by
        have ha2R : (2 : ℝ) ≤ G.indepNum := by exact_mod_cast ha2
        have hLaR : (maxLocalIndep G : ℝ) ≤ G.indepNum := by exact_mod_cast hLa
        nlinarith
      have hTN :
          4 * ((G.indepNum : ℝ) - 1) - 2 * (maxLocalIndep G : ℝ) <
            degreeL2Norm Gᶜ := by
        nlinarith
      nlinarith
  have hceil : (G.indepNum : ℤ) ≤
      ⌈((maxLocalIndep G : ℝ) + (1 / 2 : ℝ) * degreeL2Norm Gᶜ) / 2⌉ := by
    rw [Int.le_ceil_iff]
    norm_num
    exact hthreshold
  exact_mod_cast hceil

/-- The exact let-bound shape used by the Formal Conjectures source. -/
theorem full_conjecture100 (G : SimpleGraph α) [DecidableRel G.Adj] (hconn : G.Connected) :
    let maxL := (Finset.univ.image (indepNeighborsCard G)).max' (by simp)
    (G.indepNum : ℝ) ≤
      ⌈((maxL : ℝ) + (1 / 2) * (degreeL2Norm Gᶜ : ℝ)) / 2⌉ := by
  dsimp
  simpa [maxLocalIndep] using full_conjecture100_core G hconn

end Wowii100Full
