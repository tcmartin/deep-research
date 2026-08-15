import Wowii100Full.Arithmetic

namespace Wowii100Full

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Local independence is at most global independence. -/
lemma indepNeighborsCard_le_indepNum (G : SimpleGraph α) [DecidableRel G.Adj] (v : α) :
    indepNeighborsCard G v ≤ G.indepNum := by
  classical
  let H := G.induce (G.neighborSet v)
  obtain ⟨s, hs⟩ := H.exists_isNIndepSet_indepNum
  let e : (G.neighborSet v) ↪ α := ⟨Subtype.val, Subtype.val_injective⟩
  have hsG : G.IsNIndepSet H.indepNum (s.map e) := by
    rw [← SimpleGraph.isNIndepSet_induce]
    simpa [H, e] using hs
  have hle := hsG.isIndepSet.card_le_indepNum
  rw [hsG.card_eq] at hle
  simpa [H, indepNeighborsCard] using hle

end Wowii100Full
