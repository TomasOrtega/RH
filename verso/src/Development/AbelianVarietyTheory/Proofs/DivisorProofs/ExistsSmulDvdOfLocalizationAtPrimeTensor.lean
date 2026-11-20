import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFreeOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GalMapGalElt
open scoped TensorProduct
open TensorProduct

namespace GlobalTheory

/- English proof (translation)
Introduce `R C O _ _ _ _ _ Q _ b m ⟨m', hm'⟩`. Set `f` to `AlgebraTensorModule.rTensor R C (Algebra.linearMap O (Localization.AtPrime Q))`. Use `haveI : IsLocalizedModule Q.primeCompl f := inferInstance`. Establish `hf : ∀ x, (IsScalarTower.toAlgHom R O (Localization.AtPrime Q)).toLinearMap.rTensor C x = f x`. Introduce `x`.

Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a c => simp [f]`. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy]`. Rewrite `hm'` using `[hf, algebraMap_smul]`.

Take `⟨⟨m'', t⟩, rfl⟩` from `IsLocalizedModule.mk'_surjective Q.primeCompl f m'`. Simplify using `only [Function.uncurry_apply_pair] at hm'`. Establish `h2 : f ((t : O) • m) = f (b • m'')`. Rewrite using `[LinearMap.map_smul, hm', smul_comm (t : O) b, ← Submonoid.smul_def, IsLocalizedModule.mk'_cancel', LinearMap.map_smul_of_tower]`. Take `⟨u, hu⟩` from `IsLocalizedModule.exists_of_eq (S := Q.primeCompl) h2`.

Use `⟨(u : O) * t, (Q.primeCompl.mul_mem u.2 t.2 : _), (u : O) • m'', ?_⟩` and prove the remaining obligations. Rewrite using `[algebraMap_smul, mul_smul]`. Simplify `hu` using `[Submonoid.smul_def, smul_comm (u : O) b]`.
-/
theorem exists_smul_dvd_of_localization_atPrime_tensor :
    ∀ (R C O : Type) [CommRing R] [CommRing C] [Algebra R C] [CommRing O] [Algebra R O]
    (Q : Ideal O) [Q.IsPrime] (b : R) (m : O ⊗[R] C),
    (∃ m' : Localization.AtPrime Q ⊗[R] C,
      (IsScalarTower.toAlgHom R O (Localization.AtPrime Q)).toLinearMap.rTensor C m = algebraMap R (Localization.AtPrime Q) b • m') →
    ∃ s ∉ Q, ∃ m' : O ⊗[R] C, s • m = algebraMap R O b • m' := by
  intro R C O _ _ _ _ _ Q _ b m ⟨m', hm'⟩
  let f := AlgebraTensorModule.rTensor R C (Algebra.linearMap O (Localization.AtPrime Q))
  haveI : IsLocalizedModule Q.primeCompl f := inferInstance
  have hf : ∀ x, (IsScalarTower.toAlgHom R O (Localization.AtPrime Q)).toLinearMap.rTensor C x = f x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a c => simp [f]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  rw [hf, algebraMap_smul] at hm'
  obtain ⟨⟨m'', t⟩, rfl⟩ := IsLocalizedModule.mk'_surjective Q.primeCompl f m'
  simp only [Function.uncurry_apply_pair] at hm'
  have h2 : f ((t : O) • m) = f (b • m'') := by
    rw [LinearMap.map_smul, hm', smul_comm (t : O) b, ← Submonoid.smul_def, IsLocalizedModule.mk'_cancel',
      LinearMap.map_smul_of_tower]
  obtain ⟨u, hu⟩ := IsLocalizedModule.exists_of_eq (S := Q.primeCompl) h2
  refine ⟨(u : O) * t, (Q.primeCompl.mul_mem u.2 t.2 : _), (u : O) • m'', ?_⟩
  rw [algebraMap_smul, mul_smul]
  simpa [Submonoid.smul_def, smul_comm (u : O) b] using hu

end GlobalTheory
