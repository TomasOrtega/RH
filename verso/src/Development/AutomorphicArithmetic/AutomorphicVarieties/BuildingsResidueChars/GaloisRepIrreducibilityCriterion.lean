import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcDefs
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published

/- English proof (translation)
Use `⟨fun Γ Γ' k _ _ _ n r => ⟨fun φ h => ?_, fun h => ?_, fun δ h => ?_⟩, fun Γ k _ _ _ _ _ n r δ hr hδ => ?_⟩` and prove the remaining obligations. Conclude with `⟨h.1, fun _ _ _ => Submodule.mem_top, fun W hW hinv => h.2.2 W hW fun g v hv => hinv (φ g) v hv⟩`. Introduce `W hW`. Break down `h.2.2 W le_top hW with rfl | rfl` into its components or cases. Conclude with `⟨⊤, fun _ _ _ => Submodule.mem_top, isCompl_bot_top⟩`.

Use `⟨⊥, fun g v hv => ?_, isCompl_top_bot⟩` and prove the remaining obligations. Rewrite using `[(Submodule.mem_bot k).1 hv, Matrix.mulVec_zero]`. Conclude with `Submodule.zero_mem _`. Establish `key : ∀ W, IsInv (tw r δ) W ↔ IsInv r W` using `fun W => by`. Prove the components needed by the constructor for the conclusion.

Introduce `h g v hv`. Use `W.smul_mem ((δ g : k)⁻¹) (h g v hv)` as an intermediate fact. Rewrite `this` using `[tw_val, Matrix.smul_mulVec, smul_smul, inv_mul_cancel₀ (Units.ne_zero _), one_smul]`. Then use the resulting hypothesis. Introduce `h g v hv`. Rewrite using `[tw_val, Matrix.smul_mulVec]`.

Conclude with `W.smul_mem _ (h g v hv)`. Introduce `W hW`. Take `⟨W', hW', hc⟩` from `h W ((key W).1 hW)`. Conclude with `⟨W', (key W').2 hW', hc⟩`. Take `⟨hr1, hr2⟩` from `Units.continuous_iff.1 hr`.

Take `⟨hd1, hd2⟩` from `Units.continuous_iff.1 hδ`. Use `Units.continuous_iff.2 ⟨?_, ?_⟩` and prove the remaining obligations. Use `(hd1.smul hr1).congr fun g => ?_` and prove the remaining obligations. Conclude with `(tw_val r δ g).symm`. Use `(hd2.smul hr2).congr fun g => ?_` and prove the remaining obligations.

Use `tw_val r δ g⁻¹` as an intermediate fact. Simplify using `only [map_inv] at this`. Conclude with `this.symm`.
-/
theorem UpperTheory.galoisRep_irreducibility_criterion :
    UpperTheory.V.Af.Bc.IrrBasic := by
  refine ⟨fun Γ Γ' k _ _ _ n r => ⟨fun φ h => ?_, fun h => ?_, fun δ h => ?_⟩, fun Γ k _ _ _ _ _ n r δ hr hδ => ?_⟩
  · exact ⟨h.1, fun _ _ _ => Submodule.mem_top, fun W hW hinv => h.2.2 W hW fun g v hv => hinv (φ g) v hv⟩
  · intro W hW
    rcases h.2.2 W le_top hW with rfl | rfl
    · exact ⟨⊤, fun _ _ _ => Submodule.mem_top, isCompl_bot_top⟩
    · refine ⟨⊥, fun g v hv => ?_, isCompl_top_bot⟩
      rw [(Submodule.mem_bot k).1 hv, Matrix.mulVec_zero]
      exact Submodule.zero_mem _
  · have key : ∀ W, IsInv (tw r δ) W ↔ IsInv r W := fun W => by
      constructor
      · intro h g v hv
        have := W.smul_mem ((δ g : k)⁻¹) (h g v hv)
        rwa [tw_val, Matrix.smul_mulVec, smul_smul, inv_mul_cancel₀ (Units.ne_zero _), one_smul] at this
      · intro h g v hv
        rw [tw_val, Matrix.smul_mulVec]
        exact W.smul_mem _ (h g v hv)
    intro W hW
    obtain ⟨W', hW', hc⟩ := h W ((key W).1 hW)
    exact ⟨W', (key W').2 hW', hc⟩
  · obtain ⟨hr1, hr2⟩ := Units.continuous_iff.1 hr
    obtain ⟨hd1, hd2⟩ := Units.continuous_iff.1 hδ
    refine Units.continuous_iff.2 ⟨?_, ?_⟩
    · refine (hd1.smul hr1).congr fun g => ?_
      exact (tw_val r δ g).symm
    · refine (hd2.smul hr2).congr fun g => ?_
      have := tw_val r δ g⁻¹
      simp only [map_inv] at this
      exact this.symm
