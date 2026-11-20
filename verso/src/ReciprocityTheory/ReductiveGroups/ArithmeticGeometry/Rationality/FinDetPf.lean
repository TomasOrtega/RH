import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.FiniteDetectStatement

namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

/- English proof (translation)
Introduce `L E _ _ _ _ W FF hkill hdet`. Set `S : Set (Submodule L E)` to `{P | ∃ s : Finset (Module.Dual L E), ↑s ⊆ FF ∧ (⨅ c ∈ s, LinearMap.ker c) = P}`. Establish `hS : S.Nonempty` using `⟨_, ∅, by simp, rfl⟩`. Take `⟨P, ⟨s, hsFF, rfl⟩, hmin⟩` from `IsArtinian.set_has_minimal S hS`. Use `⟨s, hsFF, le_antisymm ?_ ?_⟩` and prove the remaining obligations.

Introduce `x hx`. Assume the negation of the conclusion as `hxW`. Take `⟨c, hcFF, hcx⟩` from `hdet x hxW`. Establish `hmem : (⨅ d ∈ insert c s, LinearMap.ker d) ∈ S` using `⟨insert c s, by`. Introduce `d hd`.

Break down `Finset.mem_insert.mp hd with rfl | hd` into its components or cases. Conclude with `hcFF`. Conclude with `hsFF hd, rfl⟩`. Apply `hmin _ hmem` to reduce the goal to its premises. Use `lt_of_le_of_ne ?_ ?_` and prove the remaining obligations.

Conclude with `le_iInf₂ fun d hd => iInf₂_le d (Finset.mem_insert_of_mem hd)`. Introduce `heq`. Establish `hx' : x ∈ ⨅ d ∈ insert c s, LinearMap.ker d` using `heq ▸ hx`. Establish `: x ∈ LinearMap.ker c` using `(Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp hx' c) (Finset.mem_insert_self c s)`. Conclude with `hcx this`.

Conclude with `le_iInf₂ fun c hc => hkill c (hsFF hc)`.
-/
theorem finiteDetect_holds : FiniteDetectStatement := by
  intro L E _ _ _ _ W FF hkill hdet
  classical
  let S : Set (Submodule L E) :=
    {P | ∃ s : Finset (Module.Dual L E), ↑s ⊆ FF ∧ (⨅ c ∈ s, LinearMap.ker c) = P}
  have hS : S.Nonempty := ⟨_, ∅, by simp, rfl⟩
  obtain ⟨P, ⟨s, hsFF, rfl⟩, hmin⟩ := IsArtinian.set_has_minimal S hS
  refine ⟨s, hsFF, le_antisymm ?_ ?_⟩
  · intro x hx
    by_contra hxW
    obtain ⟨c, hcFF, hcx⟩ := hdet x hxW
    have hmem : (⨅ d ∈ insert c s, LinearMap.ker d) ∈ S :=
      ⟨insert c s, by
        intro d hd
        rcases Finset.mem_insert.mp hd with rfl | hd
        · exact hcFF
        · exact hsFF hd, rfl⟩
    apply hmin _ hmem
    refine lt_of_le_of_ne ?_ ?_
    · exact le_iInf₂ fun d hd => iInf₂_le d (Finset.mem_insert_of_mem hd)
    · intro heq
      have hx' : x ∈ ⨅ d ∈ insert c s, LinearMap.ker d := heq ▸ hx
      have : x ∈ LinearMap.ker c :=
        (Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp hx' c) (Finset.mem_insert_self c s)
      exact hcx this
  · exact le_iInf₂ fun c hc => hkill c (hsFF hc)

end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
