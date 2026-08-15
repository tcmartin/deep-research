import Mathlib

open Classical SimpleGraph
open scoped BigOperators

namespace SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Independence number of the graph induced by the neighbors of `v`.
Exact definition used by WOWII / Graffiti.pc Conjecture 100. -/
noncomputable def indepNeighborsCard (G : SimpleGraph α) [DecidableRel G.Adj] (v : α) : ℕ :=
  (G.induce (G.neighborSet v)).indepNum

/-- Euclidean norm of the degree sequence.
Exact definition used by WOWII / Graffiti.pc Conjecture 100. -/
noncomputable def degreeL2Norm (G : SimpleGraph α) [DecidableRel G.Adj] : ℝ :=
  Real.sqrt (∑ v, (G.degree v : ℝ) ^ 2)

end SimpleGraph
