import Mathlib

/-! Temporary exact-definition mirror for fast local iteration.
The final verification switches back to google-deepmind/formal-conjectures at commit
2411d22e1bd550d050d0eac6c1fb379a76a3e7c5. -/

open Classical SimpleGraph
open scoped BigOperators

namespace SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable def indepNeighborsCard (G : SimpleGraph α) [DecidableRel G.Adj] (v : α) : ℕ :=
  (G.induce (G.neighborSet v)).indepNum

noncomputable def degreeL2Norm (G : SimpleGraph α) [DecidableRel G.Adj] : ℝ :=
  Real.sqrt (∑ v, (G.degree v : ℝ) ^ 2)

end SimpleGraph
