import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.SecondFromFirstStatement

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af
open scoped TensorProduct

namespace UpperTheory.V.Lit.Dr

/- English proof (translation)
Proceed by induction. Treat this case separately. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Treat this case separately.

Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Treat this case separately. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
private theorem ev_comp {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a d : ℕ}
    (m : Sm E a ⊗[ℂ] (Fin d → ℂ)) (j : Fin d) :
    (fun g => ev m g j) = (TensorProduct.piScalarRight ℂ ℂ (Sm E a) (Fin d) m j).1 := by
  induction m using TensorProduct.induction_on with
  | zero =>
    rw [map_zero, map_zero]
    rfl
  | tmul φ v =>
    funext g
    simp [mul_comm]
  | add x y hx hy =>
    rw [map_add, map_add, Pi.add_apply, Submodule.coe_add, ← hx, ← hy]
    rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Reduce the claim to the hypotheses of an applicable result. Apply function extensionality and compare values at an arbitrary argument. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem evFacts : EvFacts := by
  intro E _ _ _ a d
  refine ⟨fun m m' h => ?_, fun m j => ?_, fun f hf => ?_⟩
  · apply (TensorProduct.piScalarRight ℂ ℂ (Sm E a) (Fin d)).injective
    funext j
    apply Subtype.ext
    rw [← ev_comp, ← ev_comp, h]
  · rw [ev_comp]
    exact Subtype.property _
  · refine ⟨(TensorProduct.piScalarRight ℂ ℂ (Sm E a) (Fin d)).symm fun j => ⟨_, hf j⟩, ?_⟩
    funext g j
    have := congrFun (ev_comp ((TensorProduct.piScalarRight ℂ ℂ (Sm E a) (Fin d)).symm fun j => ⟨_, hf j⟩) j) g
    rw [LinearEquiv.apply_symm_apply] at this
    exact this

end UpperTheory.V.Lit.Dr
