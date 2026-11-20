import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
import GroundTheory.GlobalFields.ComplexMultiplication.MainTheorem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodExistenceCm
import CompanionTheory.AutomorphicTheory.PlaceSeparation.IsOpenQuotientMapArt0
open NumberField
open scoped nonZeroDivisors
open scoped GlobalTheory.Idele

noncomputable section

namespace GlobalTheory.CompanionTheory.EllipticCM

/- English proof (translation)
Set `ι' : algebraicClosure K ℂ →ₐ[K] ℂ` to `ι.comp (e : algebraicClosure K ℂ →ₐ[K] AlgebraicClosure K)`. Establish `hmem : ∀ y, ι' y ∈ (algebraicClosure K ℂ).toSubalgebra` using `fun y => mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic y).algHom ι')`. Set `ρ₀ : algebraicClosure K ℂ →ₐ[K] algebraicClosure K ℂ` to `ι'.codRestrict (algebraicClosure K ℂ).toSubalgebra hmem`. Set `ρ : algebraicClosure K ℂ ≃ₐ[K] algebraicClosure K ℂ` to `AlgEquiv.ofBijective ρ₀ (Algebra.IsAlgebraic.algHom_bijective ρ₀)`. Establish `hρ : ∀ w, ((ρ w : algebraicClosure K ℂ) : ℂ) = ι (e w)` using `fun _ => rfl`.

Use `⟨ρ, fun y => ?_⟩` and prove the remaining obligations. Take `⟨z, rfl⟩` from `ρ.surjective y`. Establish `h1 : (ρ * ((e.trans g).trans e.symm) * ρ⁻¹) (ρ z) = ρ (e.symm (g (e z)))`. Simplify using `[AlgEquiv.mul_apply, AlgEquiv.aut_inv]`. Rewrite using `[h1, hρ, hρ, hσ, AlgEquiv.apply_symm_apply]`.
-/
theorem exists_conj_eq_on_algebraicClosure {K : Type} [Field K] [Algebra K ℂ]
    (σ : ℂ ≃ₐ[K] ℂ) (ι : AlgebraicClosure K →ₐ[K] ℂ)
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (hσ : ∀ x, σ (ι x) = ι (g x))
    (e : algebraicClosure K ℂ ≃ₐ[K] AlgebraicClosure K) :
    ∃ ρ : algebraicClosure K ℂ ≃ₐ[K] algebraicClosure K ℂ,
      ∀ y : algebraicClosure K ℂ,
        (((ρ * ((e.trans g).trans e.symm) * ρ⁻¹) y : algebraicClosure K ℂ) : ℂ) = σ (y : ℂ) := by
  let ι' : algebraicClosure K ℂ →ₐ[K] ℂ := ι.comp (e : algebraicClosure K ℂ →ₐ[K] AlgebraicClosure K)
  have hmem : ∀ y, ι' y ∈ (algebraicClosure K ℂ).toSubalgebra := fun y =>
    mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic y).algHom ι')
  let ρ₀ : algebraicClosure K ℂ →ₐ[K] algebraicClosure K ℂ :=
    ι'.codRestrict (algebraicClosure K ℂ).toSubalgebra hmem
  let ρ : algebraicClosure K ℂ ≃ₐ[K] algebraicClosure K ℂ :=
    AlgEquiv.ofBijective ρ₀ (Algebra.IsAlgebraic.algHom_bijective ρ₀)
  have hρ : ∀ w, ((ρ w : algebraicClosure K ℂ) : ℂ) = ι (e w) := fun _ => rfl
  refine ⟨ρ, fun y => ?_⟩
  obtain ⟨z, rfl⟩ := ρ.surjective y
  have h1 : (ρ * ((e.trans g).trans e.symm) * ρ⁻¹) (ρ z) = ρ (e.symm (g (e z))) := by
    simp [AlgEquiv.mul_apply, AlgEquiv.aut_inv]
  rw [h1, hρ, hρ, hσ, AlgEquiv.apply_symm_apply]

/- English proof (translation)
Introduce `K _ _ _ _ _`. Set `e : algebraicClosure K ℂ ≃ₐ[K] AlgebraicClosure K` to `IsAlgClosure.equiv K _ _`. Take `⟨Art, hArt, hArtσ⟩` from `GlobalTheory.LatVal.exists_globalArtinMap (CompanionTheory.FamInh.isGlobalArtin_inv (E := K) (Ω := algebraicClosure K ℂ)) e`. Take `⟨φ, -, hφb, hφ⟩` from `GlobalTheory.HeckeGal.exists_abMap_of_algEquiv e`. Use `⟨Art, hArt, ?_⟩` and prove the remaining obligations.

Introduce and unpack `σ s ⟨ι, g, hσ, hg⟩ x`. Take `⟨ρ, hρ⟩` from `exists_conj_eq_on_algebraicClosure σ ι g hσ e`. Take `⟨τ, hτ⟩` from `GlobalTheory.HeckeGal.toAb_surjective (E := K) (Ω := algebraicClosure K ℂ) (CompanionTheory.FamInh.art0 K (algebraicClosure K ℂ) s)`. Establish `h1 : Art (QuotientGroup.mk s) = Neutral.B1.toAb K ((e.symm.trans τ).trans e)` using `hArtσ s τ (by rw [hτ, MonoidHom.inv_apply, inv_inv])`. Establish `h2 : (e.symm.trans ((e.trans g).trans e.symm)).trans e = g`.

Use extensionality with `y`. Simplify using the standard rewrite rules. Establish `h3 : GlobalTheory.HeckeGal.toAb K (algebraicClosure K ℂ) ((e.trans g).trans e.symm) = GlobalTheory.HeckeGal.toAb K (algebraicClosure K ℂ) τ` using `hφb.1 (by rw [hφ, hφ, h2, hg, h1])`. Establish `h4 : GlobalTheory.HeckeGal.toAb K (algebraicClosure K ℂ) (ρ * ((e.trans g).trans e.symm) * ρ⁻¹) = CompanionTheory.FamInh.art0 K (algebraicClosure K ℂ) s`. Rewrite using `[map_mul, map_mul, map_inv, h3, hτ, mul_comm (GlobalTheory.HeckeGal.toAb K _ ρ), mul_inv_cancel_right]`.

Establish `h5` using `GroundTheory.LocalField.topologicalAbelianizationEquiv_mk_apply K (algebraicClosure K ℂ) (ρ * ((e.trans g).trans e.symm) * ρ⁻¹) x`. Establish `h6 : GroundTheory.LocalField.topologicalAbelianizationEquiv K (algebraicClosure K ℂ) (((ρ * ((e.trans g).trans e.symm) * ρ⁻¹ : algebraicClosure K ℂ ≃ₐ[K] algebraicClosure K ℂ)) : TopologicalAbelianization (algebraicClosure K ℂ ≃ₐ[K] algebraicClosure K ℂ)) = GroundTheory.Global.ar …`. Use `Eq.trans (congrArg (GroundTheory.LocalField.topologicalAbelianizationEquiv K (algebraicClosure K ℂ)) h4) ?_` and prove the remaining obligations. Conclude with `(GroundTheory.LocalField.topologicalAbelianizationEquiv K (algebraicClosure K ℂ)).apply_symm_apply _`. Rewrite `h5` using `[h6]`.

Rewrite using `[h5, hρ]`.
-/
theorem exists_globalArtinMap_tied : ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Algebra K ℂ], Module.finrank ℚ K = 2 → ∃ Art₀ : Neutral.B1.IdeleClassGroup K →* Field.absoluteGaloisGroupAbelianization K, Neutral.B1.IsGlobalArtinMap K Art₀ ∧ ∀ (σ : ℂ ≃ₐ[K] ℂ) (s : Neutral.B1.Ideles K), GlobalTheory.EllipticCM.RestrictsTo σ (Art₀ (QuotientGroup.mk s)) → ∀ x : GroundTheory.LocalField.maximalAbelianExtension K (algebraicClosure K ℂ), ((GroundTheory.Global.artinMap K (algebraicClosure K ℂ) (GroundTheory.Global.IdeleClassGroup.mk K s) x : algebraicClosure K ℂ) : ℂ) = σ ((x : algebraicClosure K ℂ) : ℂ) := by
  intro K _ _ _ _ _
  let e : algebraicClosure K ℂ ≃ₐ[K] AlgebraicClosure K := IsAlgClosure.equiv K _ _
  obtain ⟨Art, hArt, hArtσ⟩ := GlobalTheory.LatVal.exists_globalArtinMap
    (CompanionTheory.FamInh.isGlobalArtin_inv (E := K) (Ω := algebraicClosure K ℂ)) e
  obtain ⟨φ, -, hφb, hφ⟩ := GlobalTheory.HeckeGal.exists_abMap_of_algEquiv e
  refine ⟨Art, hArt, ?_⟩
  rintro σ s ⟨ι, g, hσ, hg⟩ x
  obtain ⟨ρ, hρ⟩ := exists_conj_eq_on_algebraicClosure σ ι g hσ e
  obtain ⟨τ, hτ⟩ := GlobalTheory.HeckeGal.toAb_surjective (E := K) (Ω := algebraicClosure K ℂ)
    (CompanionTheory.FamInh.art0 K (algebraicClosure K ℂ) s)
  have h1 : Art (QuotientGroup.mk s) = Neutral.B1.toAb K ((e.symm.trans τ).trans e) :=
    hArtσ s τ (by rw [hτ, MonoidHom.inv_apply, inv_inv])
  have h2 : (e.symm.trans ((e.trans g).trans e.symm)).trans e = g := by
    ext y
    simp
  have h3 : GlobalTheory.HeckeGal.toAb K (algebraicClosure K ℂ) ((e.trans g).trans e.symm) =
      GlobalTheory.HeckeGal.toAb K (algebraicClosure K ℂ) τ :=
    hφb.1 (by rw [hφ, hφ, h2, hg, h1])
  have h4 : GlobalTheory.HeckeGal.toAb K (algebraicClosure K ℂ) (ρ * ((e.trans g).trans e.symm) * ρ⁻¹) =
      CompanionTheory.FamInh.art0 K (algebraicClosure K ℂ) s := by
    rw [map_mul, map_mul, map_inv, h3, hτ, mul_comm (GlobalTheory.HeckeGal.toAb K _ ρ), mul_inv_cancel_right]
  have h5 := GroundTheory.LocalField.topologicalAbelianizationEquiv_mk_apply K (algebraicClosure K ℂ)
    (ρ * ((e.trans g).trans e.symm) * ρ⁻¹) x
  have h6 : GroundTheory.LocalField.topologicalAbelianizationEquiv K (algebraicClosure K ℂ)
      (((ρ * ((e.trans g).trans e.symm) * ρ⁻¹ : algebraicClosure K ℂ ≃ₐ[K] algebraicClosure K ℂ)) :
        TopologicalAbelianization (algebraicClosure K ℂ ≃ₐ[K] algebraicClosure K ℂ)) =
      GroundTheory.Global.artinMap K (algebraicClosure K ℂ) (GroundTheory.Global.IdeleClassGroup.mk K s) := by
    refine Eq.trans (congrArg (GroundTheory.LocalField.topologicalAbelianizationEquiv K (algebraicClosure K ℂ)) h4) ?_
    exact (GroundTheory.LocalField.topologicalAbelianizationEquiv K (algebraicClosure K ℂ)).apply_symm_apply _
  rw [h6] at h5
  rw [h5, hρ]

end GlobalTheory.CompanionTheory.EllipticCM

end
