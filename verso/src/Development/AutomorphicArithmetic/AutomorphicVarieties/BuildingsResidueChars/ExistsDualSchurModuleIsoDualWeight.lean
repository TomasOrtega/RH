import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsoUnitaryIrrepConjDual
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.BasicNotions
open scoped TensorProduct

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the equality to equality of the corresponding arguments. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private theorem detPow_invTr (n : ℕ) (g : GL (Fin n) ℂ) (c : ℤ) :
    detPow ℂ n (inside₂ ℂ n g) c = detPow ℂ n g⁻¹ c := by
  unfold detPow
  congr 2
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply]
  exact Matrix.det_transpose _

/- English proof (translation)
By extensionality, compare the relevant components. Express the relevant assertion in an equivalent form by its definition. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
private theorem toDual_invTr (n : ℕ) (lam : DomWeight n) (g : GL (Fin n) ℂ) (x : nablaSq ℂ n lam) :
    GlobalTheory.ConjDual.toDual n lam (GlobalTheory.Branching.sqRep ℂ n lam (inside₂ ℂ n g) x) =
      GlobalTheory.ConjDual.toDual n lam x ∘ₗ GlobalTheory.Branching.sqRep ℂ n lam g⁻¹ := by
  ext y
  change GlobalTheory.ConjDual.bil _ (sqAct ℂ n lam (inside₂ ℂ n g) x.1) y.1 =
    GlobalTheory.ConjDual.bil _ x.1 (sqAct ℂ n lam g⁻¹ y.1)
  unfold sqAct
  rw [map_smul, map_smul, LinearMap.smul_apply, detPow_invTr, GlobalTheory.ConjDual.bil_rowAct,
    Matrix.transpose_transpose]
  rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Introduce a local definition for the expression. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities.
-/
theorem UpperTheory.exists_dual_schur_module_iso_dual_weight :
    ∀ (n : ℕ), 1 ≤ n → ∀ lam : DomWeight n, ∃ κ : Module.Dual ℂ (nablaSq ℂ n lam) ≃ₗ[ℂ] nablaSq ℂ n lam.dual, ∀ (g : GL (Fin n) ℂ) (ℓ : Module.Dual ℂ (nablaSq ℂ n lam)), κ (ℓ ∘ₗ GlobalTheory.Branching.sqRep ℂ n lam g⁻¹) = GlobalTheory.Branching.sqRep ℂ n lam.dual g (κ ℓ) := by
  intro n hn lam
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨κ, hκ⟩ := GlobalTheory.DefiniteBC.exists_equiv_dual lam
  let T : nablaSq ℂ (m + 1) lam ≃ₗ[ℂ] Module.Dual ℂ (nablaSq ℂ (m + 1) lam) :=
    (GlobalTheory.ConjDual.toDual (m + 1) lam).linearEquivOfInjective (GlobalTheory.ConjDual.toDual_injective _ lam)
      Subspace.dual_finrank_eq.symm
  have hT : ∀ x, T x = GlobalTheory.ConjDual.toDual (m + 1) lam x := fun _ => rfl
  refine ⟨T.symm.trans κ, fun g ℓ => ?_⟩
  obtain ⟨x, rfl⟩ := T.surjective ℓ
  rw [hT x, ← toDual_invTr, ← hT, ← hT, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    T.symm_apply_apply, T.symm_apply_apply, hκ, GlobalTheory.DefiniteBC.invTr_invTr]
