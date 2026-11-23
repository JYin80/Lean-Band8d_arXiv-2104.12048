module

public import RBM8D.Graph.Isolated

@[expose] public section

/-!
# Nesting of isolated subsets

The minimal isolated subset of a molecular graph is well defined ([II, Def 5.4 (i)] under
[II, Def 5.9 (ii)]): `MGraph.MIS_spec`.
-/

noncomputable section

open scoped BigOperators

namespace RBM8D.Graphs

section Nesting

variable {V E : Type}

end Nesting

/-! ### Theorems -/

/-- The minimal isolated subset is well defined ([II, Def 5.4 (i)] under [II, Def 5.9 (ii)]):
it is the set of all internal vertices or isolated, it has no proper isolated subset, and it is
the only such set. -/
theorem MGraph.MIS_spec :
  ∀ (V E : Type) (G : MGraph V E), G.IsoChain →
    G.IsoOrTop G.MIS ∧ (∀ Q, ¬ G.IsProperIso G.MIS Q) ∧
      ∀ S, G.IsoOrTop S → (∀ Q, ¬ G.IsProperIso S Q) → S = G.MIS := by
  intro V E G hch
  classical
  by_cases hex : ∃ P, G.IsProperIso G.int P
  · let Ps : Finset (Finset V) := G.int.powerset.filter fun P => G.IsProperIso G.int P
    have hmem : ∀ P, G.IsProperIso G.int P → P ∈ Ps := fun P hP =>
      Finset.mem_filter.2 ⟨Finset.mem_powerset.2 hP.1.1, hP⟩
    obtain ⟨P, hP⟩ := hex
    obtain ⟨P₀, hP₀, hmin⟩ := Finset.exists_min_image Ps Finset.card ⟨P, hmem P hP⟩
    have hP₀' : G.IsProperIso G.int P₀ := (Finset.mem_filter.1 hP₀).2
    have hle : ∀ P, G.IsProperIso G.int P → P₀ ⊆ P := by
      intro P hP
      rcases hch P₀ P hP₀' hP with h | h
      · exact h
      · rw [Finset.eq_of_subset_of_card_le h (hmin P (hmem P hP))]
    have hMIS : G.MIS = P₀ := by
      ext v
      simp only [MGraph.MIS, Finset.mem_filter]
      exact ⟨fun hv => hv.2 P₀ hP₀', fun hv => ⟨hP₀'.1.1 hv, fun P hP => hle P hP hv⟩⟩
    rw [hMIS]
    refine ⟨Or.inr hP₀'.1, ?_, ?_⟩
    · intro Q hQ
      have hQ₂ := Finset.ssubset_iff_subset_ne.1 hQ.2
      exact hQ₂.2 (Finset.Subset.antisymm hQ₂.1 (hle Q ⟨hQ.1, hQ.2.trans hP₀'.2⟩))
    · intro S hS hno
      by_cases hSint : S = G.int
      · rw [hSint] at hno
        exact absurd hP₀' (hno P₀)
      · have hSi : G.IsIsolated S := hS.resolve_left hSint
        have hsub := hle S ⟨hSi, Finset.ssubset_iff_subset_ne.2 ⟨hSi.1, hSint⟩⟩
        by_contra hne
        exact hno P₀ ⟨hP₀'.1, Finset.ssubset_iff_subset_ne.2 ⟨hsub, fun h => hne h.symm⟩⟩
  · have hno : ∀ P, ¬ G.IsProperIso G.int P := fun P hP => hex ⟨P, hP⟩
    have hMIS : G.MIS = G.int := by
      ext v
      simp only [MGraph.MIS, Finset.mem_filter]
      exact ⟨fun hv => hv.1, fun hv => ⟨hv, fun P hP => absurd hP (hno P)⟩⟩
    rw [hMIS]
    refine ⟨Or.inl rfl, hno, ?_⟩
    intro S hS _
    rcases hS with h | h
    · exact h
    · by_contra hne
      exact hno S ⟨h, Finset.ssubset_iff_subset_ne.2 ⟨h.1, hne⟩⟩

section Instances

variable {V E : Type}

end Instances

end RBM8D.Graphs
