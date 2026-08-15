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
  have hSI : G.IsIndepSet (s.map e) := by
    intro y hy z hz hyz
    simp only [Finset.mem_map] at hy hz
    obtain ⟨y', hy', rfl⟩ := hy
    obtain ⟨z', hz', rfl⟩ := hz
    have hne : y' ≠ z' := by
      intro h
      apply hyz
      exact congrArg Subtype.val h
    exact hs.isIndepSet hy' hz' hne
  have hle := hSI.card_le_indepNum
  have hcard : (s.map e).card = H.indepNum := by
    simpa using hs.card_eq
  rw [hcard] at hle
  simpa [H, indepNeighborsCard] using hle

end Wowii100Full
