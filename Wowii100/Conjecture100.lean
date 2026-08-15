import Mathlib

namespace Wowii100

open SimpleGraph
open scoped BigOperators

/-- The sharp arithmetic inequality needed for Graffiti.pc / WOWII Conjecture 100. -/
theorem arithmetic_core (a L m : ℕ)
    (ha : 2 ≤ a) (hL1 : 1 ≤ L) (hLa : L ≤ a) (ham : a ≤ m * L) :
    (a : ℝ) * (4 * ((a : ℝ) - 1) - 2 * (L : ℝ)) ^ 2 <
      ((a : ℝ) * ((a : ℝ) - 1) + (m : ℝ) * ((a : ℝ) - (L : ℝ))) ^ 2 +
        (a : ℝ) * (m : ℝ) * ((a : ℝ) - (L : ℝ)) ^ 2 := by
  by_cases hEq : L = a
  · subst L
    let x := a - 2
    have hx : a = x + 2 := by omega
    have hxR : (a : ℝ) = (x : ℝ) + 2 := by exact_mod_cast hx
    have hp :
        (0 : ℝ) < ((x : ℝ) + 2) * ((x : ℝ) ^ 3 + 5 * (x : ℝ) + 2) := by
      positivity
    have hid :
        (((a : ℝ) * ((a : ℝ) - 1) + (m : ℝ) * ((a : ℝ) - (a : ℝ))) ^ 2 +
            (a : ℝ) * (m : ℝ) * ((a : ℝ) - (a : ℝ)) ^ 2) -
          (a : ℝ) * (4 * ((a : ℝ) - 1) - 2 * (a : ℝ)) ^ 2 =
          ((x : ℝ) + 2) * ((x : ℝ) ^ 3 + 5 * (x : ℝ) + 2) := by
      rw [hxR]
      ring
    nlinarith
  by_cases hOne : L = 1
  · subst L
    have hm : a ≤ m := by simpa using ham
    let x := a - 2
    let k := m - a
    have hx : a = x + 2 := by omega
    have hk : m = a + k := by omega
    have hxR : (a : ℝ) = (x : ℝ) + 2 := by exact_mod_cast hx
    have hkR : (m : ℝ) = (a : ℝ) + (k : ℝ) := by exact_mod_cast hk
    have hx0 : (0 : ℝ) ≤ (x : ℝ) := Nat.cast_nonneg _
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
    have hsum :
        (0 : ℝ) ≤ 5 * (x : ℝ) ^ 4 + 5 * (x : ℝ) ^ 3 * (k : ℝ) +
          14 * (x : ℝ) ^ 3 + (x : ℝ) ^ 2 * (k : ℝ) ^ 2 +
          20 * (x : ℝ) ^ 2 * (k : ℝ) + 17 * (x : ℝ) ^ 2 +
          2 * (x : ℝ) * (k : ℝ) ^ 2 + 25 * (x : ℝ) * (k : ℝ) +
          24 * (x : ℝ) + (k : ℝ) ^ 2 + 10 * (k : ℝ) := by
      positivity
    have hp :
        (0 : ℝ) < 5 * (x : ℝ) ^ 4 + 5 * (x : ℝ) ^ 3 * (k : ℝ) +
          14 * (x : ℝ) ^ 3 + (x : ℝ) ^ 2 * (k : ℝ) ^ 2 +
          20 * (x : ℝ) ^ 2 * (k : ℝ) + 17 * (x : ℝ) ^ 2 +
          2 * (x : ℝ) * (k : ℝ) ^ 2 + 25 * (x : ℝ) * (k : ℝ) +
          24 * (x : ℝ) + (k : ℝ) ^ 2 + 10 * (k : ℝ) + 12 := by
      nlinarith
    have hid :
        (((a : ℝ) * ((a : ℝ) - 1) + (m : ℝ) * ((a : ℝ) - 1)) ^ 2 +
            (a : ℝ) * (m : ℝ) * ((a : ℝ) - 1) ^ 2) -
          (a : ℝ) * (4 * ((a : ℝ) - 1) - 2) ^ 2 =
          5 * (x : ℝ) ^ 4 + 5 * (x : ℝ) ^ 3 * (k : ℝ) +
            14 * (x : ℝ) ^ 3 + (x : ℝ) ^ 2 * (k : ℝ) ^ 2 +
            20 * (x : ℝ) ^ 2 * (k : ℝ) + 17 * (x : ℝ) ^ 2 +
            2 * (x : ℝ) * (k : ℝ) ^ 2 + 25 * (x : ℝ) * (k : ℝ) +
            24 * (x : ℝ) + (k : ℝ) ^ 2 + 10 * (k : ℝ) + 12 := by
      rw [hkR, hxR]
      ring
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
  have hsR : (L : ℝ) = (s : ℝ) + 2 := by exact_mod_cast hs
  have htR : (a : ℝ) = (L : ℝ) + (t : ℝ) + 1 := by exact_mod_cast ht
  have hkR : (m : ℝ) = (k : ℝ) + 2 := by exact_mod_cast hk
  let base : ℝ :=
      (s : ℝ) ^ 4 + 4 * (s : ℝ) ^ 3 * (t : ℝ) + 6 * (s : ℝ) ^ 3 +
        6 * (s : ℝ) ^ 2 * (t : ℝ) ^ 2 + 14 * (s : ℝ) ^ 2 * (t : ℝ) +
        13 * (s : ℝ) ^ 2 + 4 * (s : ℝ) * (t : ℝ) ^ 3 +
        8 * (s : ℝ) * (t : ℝ) ^ 2 + 10 * (s : ℝ) * (t : ℝ) +
        18 * (s : ℝ) + (t : ℝ) ^ 4 - (5 : ℝ) * (t : ℝ) ^ 2 +
        14 * (t : ℝ) + 22
  have hcore :
      (0 : ℝ) < (t : ℝ) ^ 4 - (5 : ℝ) * (t : ℝ) ^ 2 +
        14 * (t : ℝ) + 22 := by
    have hidcore :
        (t : ℝ) ^ 4 - (5 : ℝ) * (t : ℝ) ^ 2 + 14 * (t : ℝ) + 22 =
          ((t : ℝ) ^ 2 - 3) ^ 2 + (t : ℝ) ^ 2 + 14 * (t : ℝ) + 13 := by
      ring
    rw [hidcore]
    positivity
  have hrest :
      (0 : ℝ) ≤ (s : ℝ) ^ 4 + 4 * (s : ℝ) ^ 3 * (t : ℝ) +
        6 * (s : ℝ) ^ 3 + 6 * (s : ℝ) ^ 2 * (t : ℝ) ^ 2 +
        14 * (s : ℝ) ^ 2 * (t : ℝ) + 13 * (s : ℝ) ^ 2 +
        4 * (s : ℝ) * (t : ℝ) ^ 3 + 8 * (s : ℝ) * (t : ℝ) ^ 2 +
        10 * (s : ℝ) * (t : ℝ) + 18 * (s : ℝ) := by
    positivity
  have hbase : (0 : ℝ) < base := by
    dsimp [base]
    nlinarith
  let extra : ℝ :=
      (k : ℝ) * ((a : ℝ) - (L : ℝ)) *
          (2 * (a : ℝ) * ((a : ℝ) - 1) +
            ((m : ℝ) + 2) * ((a : ℝ) - (L : ℝ))) +
        (a : ℝ) * (k : ℝ) * ((a : ℝ) - (L : ℝ)) ^ 2
  have hd : (0 : ℝ) ≤ (a : ℝ) - (L : ℝ) := by exact_mod_cast hLa
  have hextra : (0 : ℝ) ≤ extra := by
    dsimp [extra]
    positivity
  have hid :
      (((a : ℝ) * ((a : ℝ) - 1) + (m : ℝ) * ((a : ℝ) - (L : ℝ))) ^ 2 +
          (a : ℝ) * (m : ℝ) * ((a : ℝ) - (L : ℝ)) ^ 2) -
        (a : ℝ) * (4 * ((a : ℝ) - 1) - 2 * (L : ℝ)) ^ 2 = base + extra := by
    dsimp [base, extra]
    rw [hkR, htR, hsR]
    ring
  nlinarith

end Wowii100
