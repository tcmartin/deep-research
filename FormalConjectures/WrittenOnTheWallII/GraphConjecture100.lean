import Wowii100Full.Final

open Classical SimpleGraph

namespace WrittenOnTheWallII.GraphConjecture100

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- WOWII / Graffiti.pc Conjecture 100, in the exact statement shape of the
Google DeepMind Formal Conjectures source. -/
theorem conjecture100 (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    let maxL := (Finset.univ.image (indepNeighborsCard G)).max' (by simp)
    (G.indepNum : ℝ) ≤
      ⌈((maxL : ℝ) + (1 / 2) * (degreeL2Norm Gᶜ : ℝ)) / 2⌉ := by
  exact Wowii100Full.full_conjecture100 G h

end WrittenOnTheWallII.GraphConjecture100
