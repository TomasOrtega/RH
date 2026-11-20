import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.CodiffUnit

open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

/- English proof (translation)
Introduce `E _ _ n`. Set `b` to `NumberField.RingOfIntegers.basis E`. Set `bZ` to `Pi.basis (fun _ : Fin n => b)`. Set `bQ` to `Pi.basis (fun _ : Fin n => NumberField.integralBasis E)`. Set `b1` to `Algebra.TensorProduct.basis ℚ bZ`.

Use `⟨b1.equiv bQ (Equiv.refl _), ?_⟩` and prove the remaining obligations. Set `f1 : (Fin n → 𝓞 E) →ₗ[ℤ] (Fin n → E)` to `((b1.equiv bQ (Equiv.refl _)).toLinearMap.restrictScalars ℤ) ∘ₗ TensorProduct.mk ℤ ℚ (Fin n → 𝓞 E) 1`. Set `f2 : (Fin n → 𝓞 E) →ₗ[ℤ] (Fin n → E)` to `LinearMap.pi (fun i => (algebraMap (𝓞 E) E).toIntAlgHom.toLinearMap ∘ₗ LinearMap.proj i)`. Establish `hf : f1 = f2`. Use `bZ.ext fun k => ?_` and prove the remaining obligations.

Establish `hk : f1 (bZ k) = b1.equiv bQ (Equiv.refl _) (b1 k)`. Rewrite using `[Algebra.TensorProduct.basis_apply]`. Both sides reduce to the same expression. Rewrite using `[hk, Module.Basis.equiv_apply]`. Take `⟨i, j⟩` from `k`.

Use function extensionality and compare the values at `l`. Simplify using `[bQ, bZ, f2, Pi.basis_apply, Pi.single_apply, NumberField.integralBasis_apply]`. Apply the tactic sequence `split_ifs <;> simp`. Both sides reduce to the same expression. Introduce `v i`.

Conclude with `congr_fun (LinearMap.congr_fun hf v) i`.
-/
theorem UpperTheory.Gal.W2.Seed.pRepEx :
    RepEx := by
  intro E _ _ n
  classical
  let b := NumberField.RingOfIntegers.basis E
  let bZ := Pi.basis (fun _ : Fin n => b)
  let bQ := Pi.basis (fun _ : Fin n => NumberField.integralBasis E)
  let b1 := Algebra.TensorProduct.basis ℚ bZ
  refine ⟨b1.equiv bQ (Equiv.refl _), ?_⟩
  let f1 : (Fin n → 𝓞 E) →ₗ[ℤ] (Fin n → E) :=
    ((b1.equiv bQ (Equiv.refl _)).toLinearMap.restrictScalars ℤ) ∘ₗ
      TensorProduct.mk ℤ ℚ (Fin n → 𝓞 E) 1
  let f2 : (Fin n → 𝓞 E) →ₗ[ℤ] (Fin n → E) :=
    LinearMap.pi (fun i => (algebraMap (𝓞 E) E).toIntAlgHom.toLinearMap ∘ₗ LinearMap.proj i)
  have hf : f1 = f2 := by
    refine bZ.ext fun k => ?_
    have hk : f1 (bZ k) = b1.equiv bQ (Equiv.refl _) (b1 k) := by
      rw [Algebra.TensorProduct.basis_apply]
      rfl
    rw [hk, Module.Basis.equiv_apply]
    obtain ⟨i, j⟩ := k
    funext l
    simp [bQ, bZ, f2, Pi.basis_apply, Pi.single_apply, NumberField.integralBasis_apply]
    split_ifs <;> simp
    rfl
  intro v i
  exact congr_fun (LinearMap.congr_fun hf v) i
