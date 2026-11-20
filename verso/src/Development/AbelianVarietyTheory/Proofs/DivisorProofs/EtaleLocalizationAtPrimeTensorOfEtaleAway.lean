import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorsTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OriginIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureFiniteEtale
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointAtZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodIffEtaleAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZmodTorsorExistsPointFiniteSeparable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalizationAtPrimeIsDomainIsIntegrallyClos
open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory

/- English proof (translation)
Introduce `R C _ _ _ b hE P _ hb`. Set `Rp` to `Localization.AtPrime P`. Set `Cb` to `Localization.Away (algebraMap R C b)`. Use `haveI : Algebra.Etale Rp (Rp ⊗[R] Cb) := Algebra.Etale.baseChange R Cb Rp`. Establish `hu : IsUnit ((Algebra.TensorProduct.includeRight : C →ₐ[R] Rp ⊗[R] C).toRingHom (algebraMap R C b))`.

Express the relevant statement in the definitionally equal form `IsUnit ((Algebra.TensorProduct.includeRight : C →ₐ[R] Rp ⊗[R] C) (algebraMap R C b))`. Rewrite using `[AlgHom.commutes, IsScalarTower.algebraMap_apply R Rp (Rp ⊗[R] C)]`. Conclude with `(IsLocalization.map_units Rp (⟨b, hb⟩ : P.primeCompl)).map _`. Set `g0 : Cb →+* Rp ⊗[R] C` to `IsLocalization.Away.lift (algebraMap R C b) hu`. Establish `hg0 : ∀ c : C, g0 (algebraMap C Cb c) = (1 : Rp) ⊗ₜ[R] c` using `fun c => IsLocalization.Away.lift_eq (algebraMap R C b) hu c`.

Set `g : Cb →ₐ[R] Rp ⊗[R] C` to `{ g0 with commutes' := fun r => by`. Express the relevant statement in the definitionally equal form `g0 (algebraMap R Cb r) = _`. Rewrite using `[IsScalarTower.algebraMap_apply R C Cb, hg0]`. Conclude with `(Algebra.TensorProduct.includeRight : C →ₐ[R] Rp ⊗[R] C).commutes r }`. Set `Φ : Rp ⊗[R] Cb →ₐ[Rp] Rp ⊗[R] C` to `Algebra.TensorProduct.lift (Algebra.ofId Rp _) g (fun _ _ => Commute.all _ _)`.

Set `Ψ : Rp ⊗[R] C →ₐ[Rp] Rp ⊗[R] Cb` to `Algebra.TensorProduct.map (AlgHom.id Rp Rp) (IsScalarTower.toAlgHom R C Cb)`. Establish `h1 : Φ.comp Ψ = AlgHom.id Rp _`. Use extensionality with `c`. Simplify using `[Φ, Ψ, g, hg0]`. Establish `h2 : Ψ.comp Φ = AlgHom.id Rp _`.

Use extensionality with `x`. Simplify using `only [AlgHom.comp_apply, AlgHom.id_apply]`. Express the relevant statement in the definitionally equal form `Ψ (Φ ((1 : Rp) ⊗ₜ[R] algebraMap C Cb x)) = (1 : Rp) ⊗ₜ[R] algebraMap C Cb x`. Establish `: Φ ((1 : Rp) ⊗ₜ[R] algebraMap C Cb x) = (1 : Rp) ⊗ₜ[R] x`. Simplify using `[Φ, g, hg0]`.

Rewrite using `[this]`. Simplify using `[Ψ]`. Conclude with `Algebra.Etale.of_equiv (AlgEquiv.ofAlgHom Ψ Φ h2 h1).symm`.
-/
theorem etale_localization_atPrime_tensor_of_etale_away : ∀ (R C : Type) [CommRing R] [CommRing C] [Algebra R C] (b : R),
    Algebra.Etale R (Localization.Away (algebraMap R C b)) →
    ∀ (P : Ideal R) [P.IsPrime], b ∉ P →
      Algebra.Etale (Localization.AtPrime P) (TensorProduct R (Localization.AtPrime P) C) := by
  intro R C _ _ _ b hE P _ hb
  let Rp := Localization.AtPrime P
  let Cb := Localization.Away (algebraMap R C b)
  haveI : Algebra.Etale Rp (Rp ⊗[R] Cb) := Algebra.Etale.baseChange R Cb Rp
  have hu : IsUnit ((Algebra.TensorProduct.includeRight : C →ₐ[R] Rp ⊗[R] C).toRingHom
      (algebraMap R C b)) := by
    change IsUnit ((Algebra.TensorProduct.includeRight : C →ₐ[R] Rp ⊗[R] C) (algebraMap R C b))
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply R Rp (Rp ⊗[R] C)]
    exact (IsLocalization.map_units Rp (⟨b, hb⟩ : P.primeCompl)).map _
  let g0 : Cb →+* Rp ⊗[R] C := IsLocalization.Away.lift (algebraMap R C b) hu
  have hg0 : ∀ c : C, g0 (algebraMap C Cb c) = (1 : Rp) ⊗ₜ[R] c := fun c =>
    IsLocalization.Away.lift_eq (algebraMap R C b) hu c
  let g : Cb →ₐ[R] Rp ⊗[R] C :=
    { g0 with
      commutes' := fun r => by
        change g0 (algebraMap R Cb r) = _
        rw [IsScalarTower.algebraMap_apply R C Cb, hg0]
        exact (Algebra.TensorProduct.includeRight : C →ₐ[R] Rp ⊗[R] C).commutes r }
  let Φ : Rp ⊗[R] Cb →ₐ[Rp] Rp ⊗[R] C :=
    Algebra.TensorProduct.lift (Algebra.ofId Rp _) g (fun _ _ => Commute.all _ _)
  let Ψ : Rp ⊗[R] C →ₐ[Rp] Rp ⊗[R] Cb :=
    Algebra.TensorProduct.map (AlgHom.id Rp Rp) (IsScalarTower.toAlgHom R C Cb)
  have h1 : Φ.comp Ψ = AlgHom.id Rp _ := by
    ext c
    simp [Φ, Ψ, g, hg0]
  have h2 : Ψ.comp Φ = AlgHom.id Rp _ := by
    ext x
    simp only [AlgHom.comp_apply, AlgHom.id_apply]
    change Ψ (Φ ((1 : Rp) ⊗ₜ[R] algebraMap C Cb x)) = (1 : Rp) ⊗ₜ[R] algebraMap C Cb x
    have : Φ ((1 : Rp) ⊗ₜ[R] algebraMap C Cb x) = (1 : Rp) ⊗ₜ[R] x := by
      simp [Φ, g, hg0]
    rw [this]
    simp [Ψ]
  exact Algebra.Etale.of_equiv (AlgEquiv.ofAlgHom Ψ Φ h2 h1).symm

end GlobalTheory
