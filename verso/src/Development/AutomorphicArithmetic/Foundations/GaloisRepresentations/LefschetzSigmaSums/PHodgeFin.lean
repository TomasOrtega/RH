import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.HodgeTraceFromLefschetzAndGroupSide

open UpperTheory.Gal.LocalSmoothExtension

open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh

/- English proof (translation)
Introduce `hW Z s d hsm hproj a b`. Use `haveI := hsm`. Establish `hF : ∀ y : CxPts (Scheme.emptyTo Z ≫ s) (RingHom.id ℂ), y ∈ (∅ : Finset (CxPts (Scheme.emptyTo Z ≫ s) (RingHom.id ℂ))) ↔ y.1 ≫ Scheme.emptyTo Z = y.1 ≫ Scheme.emptyTo Z` using `fun y => (isEmptyElim (y.1.base (Classical.arbitrary _)) : False).elim`. Establish `key` using `hW Z s d hproj ∅ (Scheme.emptyTo Z ≫ s) (Scheme.emptyTo Z) (Scheme.emptyTo Z) rfl rfl inferInstance inferInstance ∅ hF (fun _ => 0) (fun y hy => by simp at hy) a`. Conclude with `key.1 b`.
-/
theorem UpperTheory.Gal.LocalSmoothExtension.hodgeFin_of :
    HolomorphicLefschetzFormula → HodgeFin := by
  intro hW Z s d hsm hproj a b
  haveI := hsm
  have hF : ∀ y : CxPts (Scheme.emptyTo Z ≫ s) (RingHom.id ℂ),
      y ∈ (∅ : Finset (CxPts (Scheme.emptyTo Z ≫ s) (RingHom.id ℂ))) ↔
        y.1 ≫ Scheme.emptyTo Z = y.1 ≫ Scheme.emptyTo Z :=
    fun y => (isEmptyElim (y.1.base (Classical.arbitrary _)) : False).elim
  have key := hW Z s d hproj ∅ (Scheme.emptyTo Z ≫ s) (Scheme.emptyTo Z) (Scheme.emptyTo Z) rfl rfl
    inferInstance inferInstance ∅ hF (fun _ => 0) (fun y hy => by simp at hy) a
  exact key.1 b
