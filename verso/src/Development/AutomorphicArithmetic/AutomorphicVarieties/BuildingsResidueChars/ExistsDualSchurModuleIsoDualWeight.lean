import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsoUnitaryIrrepConjDual
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.BasicNotions
open scoped TensorProduct

/- English proof (translation)
Unfold `detPow`. Use `congr 2`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply]`. Conclude with `Matrix.det_transpose _`.
-/
private theorem detPow_invTr (n : ℕ) (g : GL (Fin n) ℂ) (c : ℤ) :
    detPow ℂ n (inside₂ ℂ n g) c = detPow ℂ n g⁻¹ c := by
  unfold detPow
  congr 2
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply]
  exact Matrix.det_transpose _

/- English proof (translation)
Use extensionality with `y`. Express the relevant statement in the definitionally equal form `GlobalTheory.ConjDual.bil _ (sqAct ℂ n lam (inside₂ ℂ n g) x.1) y.1 = GlobalTheory.ConjDual.bil _ x.1 (sqAct ℂ n lam g⁻¹ y.1)`. Unfold `sqAct`. Rewrite using `[map_smul, map_smul, LinearMap.smul_apply, detPow_invTr, GlobalTheory.ConjDual.bil_rowAct, Matrix.transpose_transpose]`. Both sides reduce to the same expression.
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
Introduce `n hn lam`. Take `⟨m, rfl⟩ : ∃ m, n = m + 1` from `⟨n - 1, by omega⟩`. Take `⟨κ, hκ⟩` from `GlobalTheory.DefiniteBC.exists_equiv_dual lam`. Set `T : nablaSq ℂ (m + 1) lam ≃ₗ[ℂ] Module.Dual ℂ (nablaSq ℂ (m + 1) lam)` to `(GlobalTheory.ConjDual.toDual (m + 1) lam).linearEquivOfInjective (GlobalTheory.ConjDual.toDual_injective _ lam) Subspace.dual_finrank_eq.symm`. Establish `hT : ∀ x, T x = GlobalTheory.ConjDual.toDual (m + 1) lam x` using `fun _ => rfl`.

Use `⟨T.symm.trans κ, fun g ℓ => ?_⟩` and prove the remaining obligations. Take `⟨x, rfl⟩` from `T.surjective ℓ`. Rewrite using `[hT x, ← toDual_invTr, ← hT, ← hT, LinearEquiv.trans_apply, LinearEquiv.trans_apply, T.symm_apply_apply, T.symm_apply_apply, hκ, GlobalTheory.DefiniteBC.invTr_invTr]`.
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
