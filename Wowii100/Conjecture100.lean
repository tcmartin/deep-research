import Mathlib

namespace Wowii100

open SimpleGraph
open scoped BigOperators

/-- The arithmetic core of the proof. It is stated without square roots or division:
`a * T^2 < P`, where `P/a` is the lower bound for the squared complement-degree norm. -/
theorem arithmetic_core (a L m : ℕ)
    (ha : 2 ≤ a) (hL1 : 1 ≤ L) (hLa : L ≤ a) (ham : a ≤ m * L) :
    (a : ℝ) * (4 * ((a : ℝ) - 1) - 2 * (L : ℝ)) ^ 2 <
      ((a : ℝ) * ((a : ℝ) - 1) + (m : ℝ) * ((a : ℝ) - (L : ℝ))) ^ 2 +
        (a : ℝ) * (m : ℝ) * ((a : ℝ) - (L : ℝ)) ^ 2 := by
  by_cases hEq : L = a
  · subst L
    let x := a - 2
    have hx : a = x + 2 := by omega
    rw [hx]
    norm_num
    have hp :
        0 < ((x : ℝ) + 2) * ((x : ℝ) ^ 3 + 5 * (x : ℝ) + 2) := by
      positivity
    nlinarith
  by_cases hOne : L = 1
  · subst L
    have hm : a ≤ m := by simpa using ham
    let x := a - 2
    let k := m - a
    have hx : a = x + 2 := by omega
    have hk : m = a + k := by omega
    rw [hk, hx]
    norm_num
    have hp :
        0 < 5 * (x : ℝ) ^ 4 + 5 * (x : ℝ) ^ 3 * (k : ℝ) + 14 * (x : ℝ) ^ 3 +
          (x : ℝ) ^ 2 * (k : ℝ) ^ 2 + 20 * (x : ℝ) ^ 2 * (k : ℝ) +
          17 * (x : ℝ) ^ 2 + 2 * (x : ℝ) * (k : ℝ) ^ 2 +
          25 * (x : ℝ) * (k : ℝ) + 24 * (x : ℝ) +
          (k : ℝ) ^ 2 + 10 * (k : ℝ) + 12 := by
      positivity
    nlinarith
  have hL2 : 2 ≤ L := by omega
  have hLt : L < a := by omega
  have hm2 : 2 ≤ m := by
    by_contra hn
    have hmle : m ≤ 1 := by omega
    interval_cases m <;> norm_num at ham <;> omega
  let s := L - 2
  let t := a - L - 1
  let k := m - 2
  have hs : L = s + 2 := by omega
  have ht : a = L + t + 1 := by omega
  have hk : m = k + 2 := by omega
  have hcore :
      0 < (t : ℝ) ^ 4 - 5 * (t : ℝ) ^ 2 + 14 * (t : ℝ) + 22 := by
    have hsquare : 0 ≤ ((t : ℝ) ^ 2 - 3) ^ 2 := sq_nonneg _
    nlinarith
  have hrest :
      0 ≤ (s : ℝ) ^ 4 + 4 * (s : ℝ) ^ 3 * (t : ℝ) + 6 * (s : ℝ) ^ 3 +
        6 * (s : ℝ) ^ 2 * (t : ℝ) ^ 2 + 14 * (s : ℝ) ^ 2 * (t : ℝ) +
        13 * (s : ℝ) ^ 2 + 4 * (s : ℝ) * (t : ℝ) ^ 3 +
        8 * (s : ℝ) * (t : ℝ) ^ 2 + 10 * (s : ℝ) * (t : ℝ) +
        18 * (s : ℝ) := by
    positivity
  have hbase :
      0 < (s : ℝ) ^ 4 + 4 * (s : ℝ) ^ 3 * (t : ℝ) + 6 * (s : ℝ) ^ 3 +
        6 * (s : ℝ) ^ 2 * (t : ℝ) ^ 2 + 14 * (s : ℝ) ^ 2 * (t : ℝ) +
        13 * (s : ℝ) ^ 2 + 4 * (s : ℝ) * (t : ℝ) ^ 3 +
        8 * (s : ℝ) * (t : ℝ) ^ 2 + 10 * (s : ℝ) * (t : ℝ) +
        18 * (s : ℝ) +
        ((t : ℝ) ^ 4 - 5 * (t : ℝ) ^ 2 + 14 * (t : ℝ) + 22) := by
    nlinarith
  have hd : 0 ≤ (a : ℝ) - (L : ℝ) := by exact_mod_cast hLa
  have hextra :
      0 ≤ (k : ℝ) * ((a : ℝ) - (L : ℝ)) *
          (2 * (a : ℝ) * ((a : ℝ) - 1) +
            ((m : ℝ) + 2) * ((a : ℝ) - (L : ℝ))) +
        (a : ℝ) * (k : ℝ) * ((a : ℝ) - (L : ℝ)) ^ 2 := by
    positivity
  rw [hk, ht, hs] at hextra ⊢
  norm_num at hextra ⊢
  nlinarith

end Wowii100
