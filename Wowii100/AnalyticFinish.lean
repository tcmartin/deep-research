import Wowii100.Conjecture100

namespace Wowii100

/-- From the graph-theoretic lower bound on the squared complement-degree norm,
the Graffiti/WOWII threshold lies strictly above `a - 1`.  Thus its ceiling is at least `a`.
This theorem, together with `arithmetic_core`, kernel-checks the entire real-algebraic finish. -/
theorem threshold_from_scaled_norm (a L m : ℕ) (N : ℝ)
    (ha : 2 ≤ a) (hL1 : 1 ≤ L) (hLa : L ≤ a) (ham : a ≤ m * L)
    (hN : 0 ≤ N)
    (hscaled :
      ((a : ℝ) * ((a : ℝ) - 1) + (m : ℝ) * ((a : ℝ) - (L : ℝ))) ^ 2 +
          (a : ℝ) * (m : ℝ) * ((a : ℝ) - (L : ℝ)) ^ 2
        ≤ (a : ℝ) * N ^ 2) :
    (a : ℝ) - 1 < ((L : ℝ) + N / 2) / 2 := by
  let T : ℝ := 4 * ((a : ℝ) - 1) - 2 * (L : ℝ)
  have hcore := arithmetic_core a L m ha hL1 hLa ham
  have haR : (0 : ℝ) < (a : ℝ) := by positivity
  have ha2R : (2 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hLaR : (L : ℝ) ≤ (a : ℝ) := by exact_mod_cast hLa
  have hT0 : (0 : ℝ) ≤ T := by
    dsimp [T]
    nlinarith
  have hsq : T ^ 2 < N ^ 2 := by
    dsimp [T] at hcore ⊢
    nlinarith
  have hTN : T < N := by
    by_contra hnot
    have hNT : N ≤ T := le_of_not_gt hnot
    have hprod : 0 ≤ (T - N) * (T + N) :=
      mul_nonneg (sub_nonneg.mpr hNT) (add_nonneg hT0 hN)
    nlinarith
  dsimp [T] at hTN
  linarith

end Wowii100
