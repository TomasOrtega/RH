import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHTFormOver
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.MemEigSpOfMemHtDual
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsIntegralAdeleLimitCompatibleIntSystem
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DifferentIdealAutomorphismInvariantStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

/- English proof (translation)
Introduce `E _ _ s X Ω _ ξ G G' _ _ L L' V _ _ M M' n n' ρ τ q h`. Establish `hE : eigSp (ρ.comp s.toRingHom) (τ.comp s.toRingHom) = eigSp ρ τ` using `eigSp_comp_ringEquiv Ω V (𝓞 E) ρ s τ`. Establish `h1 : M'.htDual L' n' (ρ.comp s.toRingHom) (τ.comp s.toRingHom) q = M.htDual L n ρ τ q`. Unfold `LieModel.htDual`. Rewrite using `[hE, h]`.

Use `⟨h1, ?_⟩` and prove the remaining obligations. Unfold `LieModel.htW`. Rewrite using `[hE, h1]`. Use `congr 1`. Use extensionality with `e`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨he, H⟩`. Use `⟨he, fun d hd => ?_⟩` and prove the remaining obligations. Establish `hd' : s.symm d ∈ differentIdeal ℤ (𝓞 E)` using `(GlobalTheory.T.different_ideal_automorphism_invariant E s (s.symm d)).1 (by simpa using hd)`. Simplify using `using H _ hd'`.

Introduce and unpack `⟨he, H⟩`. Conclude with `⟨he, fun d hd => H _ ((GlobalTheory.T.different_ideal_automorphism_invariant E s d).2 hd)⟩`.
-/
theorem htDual_htW_relabel : ∀ (E : Type) [Field E] [NumberField E] (s : 𝓞 E ≃+* 𝓞 E) (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (G G' : Over X) [GrpObj G] [GrpObj G'] (L : LB G.left) (L' : LB G'.left) (V : Type) [AddCommGroup V] [Module Ω V] (M : LieModel G ξ V) (M' : LieModel G' ξ V) (n n' : ℕ) (ρ : 𝓞 E →+* Module.End Ω V) (τ : 𝓞 E →+* Ω) (q : Cpt ξ), M'.htOm L' n' q = M.htOm L n q → M'.htDual L' n' (ρ.comp s.toRingHom) (τ.comp s.toRingHom) q = M.htDual L n ρ τ q ∧ M'.htW L' n' (ρ.comp s.toRingHom) (τ.comp s.toRingHom) (differentIdeal ℤ (𝓞 E)) q = M.htW L n ρ τ (differentIdeal ℤ (𝓞 E)) q := by
  intro E _ _ s X Ω _ ξ G G' _ _ L L' V _ _ M M' n n' ρ τ q h
  have hE : eigSp (ρ.comp s.toRingHom) (τ.comp s.toRingHom) = eigSp ρ τ :=
    eigSp_comp_ringEquiv Ω V (𝓞 E) ρ s τ
  have h1 : M'.htDual L' n' (ρ.comp s.toRingHom) (τ.comp s.toRingHom) q = M.htDual L n ρ τ q := by
    unfold LieModel.htDual
    rw [hE, h]
  refine ⟨h1, ?_⟩
  unfold LieModel.htW
  rw [hE, h1]
  congr 1
  ext e
  constructor
  · rintro ⟨he, H⟩
    refine ⟨he, fun d hd => ?_⟩
    have hd' : s.symm d ∈ differentIdeal ℤ (𝓞 E) :=
      (GlobalTheory.T.different_ideal_automorphism_invariant E s (s.symm d)).1 (by simpa using hd)
    simpa using H _ hd'
  · rintro ⟨he, H⟩
    exact ⟨he, fun d hd => H _ ((GlobalTheory.T.different_ideal_automorphism_invariant E s d).2 hd)⟩

end GlobalTheory.CompanionTheory.Ar
