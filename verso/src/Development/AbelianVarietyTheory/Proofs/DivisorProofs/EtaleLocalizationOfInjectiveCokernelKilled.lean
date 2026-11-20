import Mathlib
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.ModDepthGE
open IsLocalRing TensorProduct Pointwise

namespace GlobalTheory

/- English proof (translation)
Set `Φ : TensorProduct S (Localization.AtPrime p) A →ₐ[Localization.AtPrime p] TensorProduct S (Localization.AtPrime p) B` to `Algebra.TensorProduct.map (AlgHom.id (Localization.AtPrime p) (Localization.AtPrime p)) ι`. Establish `inj : Function.Injective Φ` using `Module.Flat.lTensor_preserves_injective_linearMap (M := Localization.AtPrime p) (ι.toLinearMap.restrictScalars S) hι`. Establish `hu : IsUnit (algebraMap S (Localization.AtPrime p) s)` using `IsLocalization.map_units (Localization.AtPrime p) (⟨s, hs⟩ : p.primeCompl)`. Take `⟨u, hu'⟩` from `hu`. Establish `surj : Function.Surjective Φ`.

Introduce `z`. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => exact ⟨0, map_zero _⟩`. Consider the case `tmul r y`. Take `⟨a, ha⟩` from `hB y`.

Use `⟨(r * ↑u⁻¹) ⊗ₜ a, ?_⟩` and prove the remaining obligations. Simplify using `only [Φ, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]`. Rewrite using `[show ι a = s • y from ha, TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, ← hu', mul_left_comm, Units.mul_inv, mul_one]`. Consider the case `add x y hx hy`. Take `⟨a, rfl⟩` from `hx`.

Take `⟨b, rfl⟩` from `hy`. Conclude with `⟨a + b, map_add _ _ _⟩`. Conclude with `Algebra.Etale.of_equiv (AlgEquiv.ofBijective Φ ⟨inj, surj⟩)`.
-/
theorem etale_localization_of_cokernel_killed (S : Type) [CommRing S] (A B : Type) [CommRing A]
    [CommRing B] [Algebra S A] [Algebra S B] (ι : A →ₐ[S] B) (hι : Function.Injective ι)
    (p : Ideal S) [p.IsPrime] (s : S) (hs : s ∉ p) (hB : ∀ y : B, s • y ∈ ι.range)
    (hA : Algebra.Etale (Localization.AtPrime p) (TensorProduct S (Localization.AtPrime p) A)) :
    Algebra.Etale (Localization.AtPrime p) (TensorProduct S (Localization.AtPrime p) B) := by
  let Φ : TensorProduct S (Localization.AtPrime p) A →ₐ[Localization.AtPrime p]
      TensorProduct S (Localization.AtPrime p) B :=
    Algebra.TensorProduct.map (AlgHom.id (Localization.AtPrime p) (Localization.AtPrime p)) ι
  have inj : Function.Injective Φ :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := Localization.AtPrime p)
      (ι.toLinearMap.restrictScalars S) hι
  have hu : IsUnit (algebraMap S (Localization.AtPrime p) s) :=
    IsLocalization.map_units (Localization.AtPrime p) (⟨s, hs⟩ : p.primeCompl)
  obtain ⟨u, hu'⟩ := hu
  have surj : Function.Surjective Φ := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero _⟩
    | tmul r y =>
      obtain ⟨a, ha⟩ := hB y
      refine ⟨(r * ↑u⁻¹) ⊗ₜ a, ?_⟩
      simp only [Φ, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
      rw [show ι a = s • y from ha, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
        Algebra.smul_def, ← hu', mul_left_comm, Units.mul_inv, mul_one]
    | add x y hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      exact ⟨a + b, map_add _ _ _⟩
  exact Algebra.Etale.of_equiv (AlgEquiv.ofBijective Φ ⟨inj, surj⟩)

end GlobalTheory
