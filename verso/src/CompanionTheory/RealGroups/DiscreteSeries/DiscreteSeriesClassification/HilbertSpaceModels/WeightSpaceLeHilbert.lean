import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.HilbertSpaceModels.StepSqInt

noncomputable section

open Finset Matrix

namespace CompanionTheory.RgDs.Hilb

open ReciprocityTheory.ChartRestriction.DS

/- English proof (translation)
Introduce and unpack `_ ⟨v, hv, rfl⟩`. Conclude with `UnitaryGroupOfForm.mem_closGen (E := smE ε (rreg ε)) (datumV ε Ψ T.w) v hv`.
-/
theorem weight_space_le_hilbert {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
    (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)) : V1 ε Ψ ≤ Hlam ε Ψ T.w := by
  rintro _ ⟨v, hv, rfl⟩
  exact UnitaryGroupOfForm.mem_closGen (E := smE ε (rreg ε)) (datumV ε Ψ T.w) v hv

/- English proof (translation)
Introduce `n ε lam T Ψ hl hP hK`. Establish `hst` using `h1 n ε lam T Ψ hP`. Take `⟨hcoe, hU, hnt⟩` from `h0 n ε lam T Ψ hP hst`. Establish `hlow` using `h6 h1 h3 h4 h2 n ε lam T Ψ hl hP hK`. Establish `hinj : Function.Injective (Hlam ε Ψ T.w).subtype` using `Subtype.val_injective`.

Establish `hint : ∀ g ∈ Formalism.REAL.Kset ε, ∀ x, (Hlam ε Ψ T.w).subtype (sigLam ε Ψ T.w g x) = rreg ε g ((Hlam ε Ψ T.w).subtype x)`. Introduce `g hg x`. Rewrite `hg` using `[mir_Kset_eq]`. Conclude with `hcoe g (UnitaryGroupOfForm.K_mem_UJ hg) x`. Establish `hcone : ∀ (η : Fin n → ℝ) (S : Submodule ℂ (Hlam ε Ψ T.w)), Formalism.MainNotions.S.IsKTypeOf ε (sigLam ε Ψ T.w) η S → InCone (lowK ε lam) η`.

Introduce `η S hS`. Rewrite `hS` using `[isKTypeOf_map_iff _ hinj hint]`. Conclude with `h5 h1 h3 h4 n ε lam T Ψ hl hP hK η _ (Submodule.map_subtype_le _ _) hS`. Establish `hirr : Formalism.MainNotions.S.IsIrredOn (Formalism.MainNotions.S.UJset ε) (sigLam ε Ψ T.w)`. Introduce `S hSc hSG`.

Establish `hcl : IsClosed ((S.map (Hlam ε Ψ T.w).subtype : Submodule ℂ (L2 ε)) : Set (L2 ε))`. Establish `h` using `(Submodule.isClosed_topologicalClosure _).isClosedEmbedding_subtypeVal.isClosedMap (S : Set (Hlam ε Ψ T.w)) hSc`. Rewrite using `[Submodule.map_coe]`. Conclude with `h`. Establish `hst' : ∀ g ∈ UJset ε, ∀ x ∈ S.map (Hlam ε Ψ T.w).subtype, rreg ε g x ∈ S.map (Hlam ε Ψ T.w).subtype`.

Introduce and unpack `g hg _ ⟨x, hx, rfl⟩`. Conclude with `⟨sigLam ε Ψ T.w g x, hSG g (by rw [mir_UJset_eq]; exact hg) x hx, hcoe g hg x⟩`. Break down `h7 h2 n ε lam T Ψ hP hst hlow _ (Submodule.map_subtype_le _ _) hcl hst' with h | h` into its components or cases. Use `left`. Conclude with `Submodule.map_injective_of_injective hinj (h.trans (Submodule.map_bot _).symm)`.

Use `right`. Apply `Submodule.map_injective_of_injective hinj` to reduce the goal to its premises. Rewrite using `[h, Submodule.map_top, Submodule.range_subtype]`. Use `⟨⟨inferInstance, hnt, ?_, hirr, h10 h0 n ε lam T Ψ hP hst (h8 h2 n ε lam T Ψ hP hst hlow) hirr, ?_, ?_⟩, hcone⟩` and prove the remaining obligations. Rewrite using `[mir_isURepOn_iff, mir_UJset_eq]`.

Conclude with `hU`. Use `⟨(V1 ε Ψ).comap (Hlam ε Ψ T.w).subtype, ?_⟩` and prove the remaining obligations. Rewrite using `[isKTypeOf_map_iff _ hinj hint, Submodule.map_comap_subtype, inf_eq_right.2 (weight_space_le_hilbert Ψ), mir_lowK_eq]`. Conclude with `h2 n ε lam T Ψ hP`. Introduce `μ S hS`.

Conclude with `h9 n ε lam μ hl (hcone μ S hS)`.
-/
theorem hilb_of (h1 : StepStable) (h2 : StepDatum) (h0 : StepSig) (h3 : StepMoll) (h4 : StepWtSpan)
    (h5 : StepStable → StepMoll → StepWtSpan → StepCone)
    (h6 : StepStable → StepMoll → StepWtSpan → StepDatum → StepLowEq)
    (h7 : StepDatum → StepIrred) (h8 : StepDatum → StepFormulaF) (h10 : StepSig → StepSqInt)
    (h9 : StepVogan) : Hilb := by
  intro n ε lam T Ψ hl hP hK
  have hst := h1 n ε lam T Ψ hP
  obtain ⟨hcoe, hU, hnt⟩ := h0 n ε lam T Ψ hP hst
  have hlow := h6 h1 h3 h4 h2 n ε lam T Ψ hl hP hK
  have hinj : Function.Injective (Hlam ε Ψ T.w).subtype := Subtype.val_injective
  have hint : ∀ g ∈ Formalism.REAL.Kset ε, ∀ x, (Hlam ε Ψ T.w).subtype (sigLam ε Ψ T.w g x) =
      rreg ε g ((Hlam ε Ψ T.w).subtype x) := by
    intro g hg x
    rw [mir_Kset_eq] at hg
    exact hcoe g (UnitaryGroupOfForm.K_mem_UJ hg) x
  have hcone : ∀ (η : Fin n → ℝ) (S : Submodule ℂ (Hlam ε Ψ T.w)),
      Formalism.MainNotions.S.IsKTypeOf ε (sigLam ε Ψ T.w) η S → InCone (lowK ε lam) η := by
    intro η S hS
    rw [isKTypeOf_map_iff _ hinj hint] at hS
    exact h5 h1 h3 h4 n ε lam T Ψ hl hP hK η _ (Submodule.map_subtype_le _ _) hS
  have hirr : Formalism.MainNotions.S.IsIrredOn (Formalism.MainNotions.S.UJset ε) (sigLam ε Ψ T.w) := by
    intro S hSc hSG
    have hcl : IsClosed ((S.map (Hlam ε Ψ T.w).subtype : Submodule ℂ (L2 ε)) : Set (L2 ε)) := by
      have h := (Submodule.isClosed_topologicalClosure _).isClosedEmbedding_subtypeVal.isClosedMap
        (S : Set (Hlam ε Ψ T.w)) hSc
      rw [Submodule.map_coe]
      exact h
    have hst' : ∀ g ∈ UJset ε, ∀ x ∈ S.map (Hlam ε Ψ T.w).subtype,
        rreg ε g x ∈ S.map (Hlam ε Ψ T.w).subtype := by
      rintro g hg _ ⟨x, hx, rfl⟩
      exact ⟨sigLam ε Ψ T.w g x, hSG g (by rw [mir_UJset_eq]; exact hg) x hx, hcoe g hg x⟩
    rcases h7 h2 n ε lam T Ψ hP hst hlow _ (Submodule.map_subtype_le _ _) hcl hst' with h | h
    · left
      exact Submodule.map_injective_of_injective hinj (h.trans (Submodule.map_bot _).symm)
    · right
      apply Submodule.map_injective_of_injective hinj
      rw [h, Submodule.map_top, Submodule.range_subtype]
  refine ⟨⟨inferInstance, hnt, ?_, hirr, h10 h0 n ε lam T Ψ hP hst (h8 h2 n ε lam T Ψ hP hst hlow) hirr, ?_, ?_⟩, hcone⟩
  · rw [mir_isURepOn_iff, mir_UJset_eq]
    exact hU
  · refine ⟨(V1 ε Ψ).comap (Hlam ε Ψ T.w).subtype, ?_⟩
    rw [isKTypeOf_map_iff _ hinj hint, Submodule.map_comap_subtype, inf_eq_right.2 (weight_space_le_hilbert Ψ), mir_lowK_eq]
    exact h2 n ε lam T Ψ hP
  · intro μ S hS
    exact h9 n ε lam μ hl (hcone μ S hS)

end CompanionTheory.RgDs.Hilb
