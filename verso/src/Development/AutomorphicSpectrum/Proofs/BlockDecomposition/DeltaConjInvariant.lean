import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaPartD
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundUnitary
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermInf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermOf
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteAdeleTopologyStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RatTuple
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SchwartzBruhatEqSumPure
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AdelicCharacterArchimedeanFormStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.StandardAdelicCharacterStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdeleHaarMapEqScaledVolumeStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField
open GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl GlobalTheory.CompanionTheory.SW.Core

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.DeltaMap

/- English proof (translation)
Establish `hinj : Function.Injective σ` using `(σ : E →+* E).injective`. Use `⟨hinj, ?_⟩` and prove the remaining obligations. Set `τ : E →ₐ[ℚ] E` to `(σ : E →+* E).toRatAlgHom`. Establish `h2 : Function.Injective τ.toLinearMap` using `hinj`. Conclude with `LinearMap.injective_iff_surjective.mp h2`.
-/
theorem bijective_algHom (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) : Function.Bijective σ := by
  have hinj : Function.Injective σ := (σ : E →+* E).injective
  refine ⟨hinj, ?_⟩
  let τ : E →ₐ[ℚ] E := (σ : E →+* E).toRatAlgHom
  have h2 : Function.Injective τ.toLinearMap := hinj
  exact LinearMap.injective_iff_surjective.mp h2

/- English proof (translation)
Set `e : E ≃+* E` to `(AlgEquiv.ofBijective σ (bijective_algHom F E σ)).toRingEquiv`. Set `ψ : 𝓞 E ≃+* 𝓞 E` to `NumberField.RingOfIntegers.mapRingEquiv e`. Establish `hψ : ∀ o : 𝓞 E, algebraMap (𝓞 E) E (ψ o) = σ (algebraMap (𝓞 E) E o)` using `fun o => rfl`. Set `φ : (Fin n → 𝓞 E) →+ (Fin n → 𝓞 E)` to `{ toFun := fun y i => ψ (y i) map_zero' := by`. Use function extensionality and compare the values at `i`.

Simplify using the standard rewrite rules. Use the proof step `map_add' := by`. Introduce `y z`. Use function extensionality and compare the values at `i`. Simplify using `}`.

Establish `hφ : ∀ y j, φ y j = ψ (y j)` using `fun y j => rfl`. Establish `hvec : ∀ y : Fin n → 𝓞 E, (c.map σ) *ᵥ (fun j => algebraMap (𝓞 E) E (φ y j)) = fun i => σ ((c *ᵥ fun j => algebraMap (𝓞 E) E (y j)) i)`. Introduce `y`. Use function extensionality and compare the values at `i`. Simplify using `only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul, hφ, hψ]`.

Establish `key : Kc c = (Kc (c.map σ)).comap φ`. Use extensionality with `y`. Rewrite using `[AddSubgroup.mem_comap]`. Use `show (∀ i, ∃ o : 𝓞 E, algebraMap (𝓞 E) E o = (c *ᵥ fun j => algebraMap (𝓞 E) E (y j)) i) ↔ (∀ i, ∃ o : 𝓞 E, algebraMap (𝓞 E) E o = ((c.map σ) *ᵥ fun j => algebraMap (𝓞 E) E (φ y j)) i)`. Rewrite using `[hvec]`.

Use `forall_congr' fun i => ⟨fun h => h.elim fun o ho => ⟨ψ o, by rw [hψ, ho]⟩, fun h => h.elim fun o ho => ⟨ψ.symm o, ?_⟩⟩` and prove the remaining obligations. Apply `e.injective` to reduce the goal to its premises. Use `show σ (algebraMap (𝓞 E) E (ψ.symm o)) = σ _`. Rewrite using `[← hψ, RingEquiv.apply_symm_apply, ho]`. Establish `hsurj : Function.Surjective φ` using `fun y => ⟨fun i => ψ.symm (y i), funext fun i => ψ.apply_symm_apply (y i)⟩`.

Use `show (Kc (c.map σ)).index = (Kc c).index`. Rewrite using `[key]`. Use `first`. Consider the case `exact (AddSubgroup.index_comap_of_surjective hsurj).symm`. Consider the case `exact (AddSubgroup.index_comap_of_surjective _ hsurj).symm`.

Consider the case `exact (AddSubgroup.index_comap_of_surjective (H := Kc (c.map σ)) hsurj).symm`.
-/
theorem delta_map (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n : ℕ) (c : Matrix (Fin n) (Fin n) E) : delta (c.map σ) = delta c := by
  classical
  let e : E ≃+* E := (AlgEquiv.ofBijective σ (bijective_algHom F E σ)).toRingEquiv
  let ψ : 𝓞 E ≃+* 𝓞 E := NumberField.RingOfIntegers.mapRingEquiv e
  have hψ : ∀ o : 𝓞 E, algebraMap (𝓞 E) E (ψ o) = σ (algebraMap (𝓞 E) E o) := fun o => rfl
  let φ : (Fin n → 𝓞 E) →+ (Fin n → 𝓞 E) :=
    { toFun := fun y i => ψ (y i)
      map_zero' := by
        funext i
        simp
      map_add' := by
        intro y z
        funext i
        simp }
  have hφ : ∀ y j, φ y j = ψ (y j) := fun y j => rfl
  have hvec : ∀ y : Fin n → 𝓞 E, (c.map σ) *ᵥ (fun j => algebraMap (𝓞 E) E (φ y j)) =
      fun i => σ ((c *ᵥ fun j => algebraMap (𝓞 E) E (y j)) i) := by
    intro y
    funext i
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul, hφ, hψ]
  have key : Kc c = (Kc (c.map σ)).comap φ := by
    ext y
    rw [AddSubgroup.mem_comap]
    show (∀ i, ∃ o : 𝓞 E, algebraMap (𝓞 E) E o = (c *ᵥ fun j => algebraMap (𝓞 E) E (y j)) i) ↔
      (∀ i, ∃ o : 𝓞 E, algebraMap (𝓞 E) E o = ((c.map σ) *ᵥ fun j => algebraMap (𝓞 E) E (φ y j)) i)
    rw [hvec]
    refine forall_congr' fun i => ⟨fun h => h.elim fun o ho => ⟨ψ o, by rw [hψ, ho]⟩,
      fun h => h.elim fun o ho => ⟨ψ.symm o, ?_⟩⟩
    apply e.injective
    show σ (algebraMap (𝓞 E) E (ψ.symm o)) = σ _
    rw [← hψ, RingEquiv.apply_symm_apply, ho]
  have hsurj : Function.Surjective φ := fun y =>
    ⟨fun i => ψ.symm (y i), funext fun i => ψ.apply_symm_apply (y i)⟩
  show (Kc (c.map σ)).index = (Kc c).index
  rw [key]
  first
    | exact (AddSubgroup.index_comap_of_surjective hsurj).symm
    | exact (AddSubgroup.index_comap_of_surjective _ hsurj).symm
    | exact (AddSubgroup.index_comap_of_surjective (H := Kc (c.map σ)) hsurj).symm

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.DeltaMap
