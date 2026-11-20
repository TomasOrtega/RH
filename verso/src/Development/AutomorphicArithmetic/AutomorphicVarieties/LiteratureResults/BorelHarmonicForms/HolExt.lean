import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DerivativeRightTranslateL2
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Separate the alternatives or extract the components of the hypothesis. Supply the required witnesses or components.

Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Treat this case separately. Treat this case separately. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Supply the required witnesses or components. Treat this case separately. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem UpperTheory.V.Lit.Bor.holExt :
    UpperTheory.V.Lit.Bor.HolExt := by
  intro E _ _ _ a f hf
  induction hf using Algebra.adjoin_induction with
  | mem f hf =>
    rcases hf with ⟨τ, i, j, rfl⟩ | ⟨τ, rfl⟩
    · exact ⟨fun x => x i j τ, by fun_prop, fun _ => rfl⟩
    · refine ⟨fun x => ((Matrix.of x).det τ)⁻¹, DifferentiableOn.inv ?_ fun x hx => ?_, fun y => ?_⟩
      · simp only [Matrix.det_apply', Finset.sum_apply, Pi.mul_apply, Finset.prod_apply, Matrix.of_apply]
        exact Differentiable.differentiableOn (Differentiable.fun_sum fun σ _ =>
          (differentiable_const _).mul (by fun_prop))
      · exact (((Matrix.isUnit_iff_isUnit_det _).1 hx).map (Pi.evalRingHom (fun _ : E →+* ℂ => ℂ) τ)).ne_zero
      · exact congrArg (fun z : (E →+* ℂ) → ℂ => (z τ)⁻¹) ((emb E).map_det y.val).symm
  | algebraMap c => exact ⟨fun _ => c, differentiableOn_const c, fun _ => rfl⟩
  | add f g _ _ h1 h2 =>
    obtain ⟨Φ, hΦ, e1⟩ := h1
    obtain ⟨Ψ, hΨ, e2⟩ := h2
    exact ⟨Φ + Ψ, hΦ.add hΨ, fun y => by rw [Pi.add_apply, Pi.add_apply, e1, e2]⟩
  | mul f g _ _ h1 h2 =>
    obtain ⟨Φ, hΦ, e1⟩ := h1
    obtain ⟨Ψ, hΨ, e2⟩ := h2
    exact ⟨Φ * Ψ, hΦ.mul hΨ, fun y => by rw [Pi.mul_apply, Pi.mul_apply, e1, e2]⟩
