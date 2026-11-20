import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ConjugateFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheafIffAlt
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowEqOfKaehlerDifferentialEqZeroOfSmoothDoStatement

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.AbDual
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ConjSeq

/- English proof (translation)
Introduce `p _ k _ _ hk X _ s _ U u hu`. Use `haveI hsm : Algebra.Smooth k (GlobalTheory.CechDR.Sec s U.1) := by haveI : IsOpenImmersion (GlobalTheory.CechDR.affPt s U) := IsAffineOpen.isOpenImmersion_fromSpec U.2`. Establish `h : Smooth (GlobalTheory.CechDR.affPt s U ≫ s)` using `inferInstance`. Rewrite `h` using `[GlobalTheory.CechDR.affPt_w]`. Conclude with `RingHom.smooth_algebraMap.1 ((HasRingHomProperty.Spec_iff (P := @Smooth)).1 h)`.

Distinguish the cases in `hU : Nonempty U.1`. Use `haveI : IsDomain (GlobalTheory.CechDR.Sec s U.1) := IsIntegral.component_integral (X := X) U.1`. Conclude with `GlobalTheory.T.exists_pow_eq_of_kaehler_D_eq_zero_of_smooth_domain p k hk _ u hu`. Establish `e : U.1 = ⊥`. Use extensionality with `x`.

Conclude with `⟨fun hx ↦ hU ⟨⟨x, hx⟩⟩, fun hx ↦ hx.elim⟩`. Establish `hs : Subsingleton Γ(X, U.1)` using `by rw [e]; infer_instance`. Use `haveI : Subsingleton (GlobalTheory.CechDR.Sec s U.1) := hs`. Conclude with `⟨u, Subsingleton.elim _ _⟩`.
-/
theorem sec_exists_pow_of_D_eq_zero : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [IsAlgClosed k] (hk : (p : k) = 0) (X : Scheme.{0}) [IsIntegral X] (s : X ⟶ Sp k) [Smooth s] (U : X.affineOpens) (u : GlobalTheory.CechDR.Sec s U.1), KaehlerDifferential.D k (GlobalTheory.CechDR.Sec s U.1) u = 0 → ∃ h : GlobalTheory.CechDR.Sec s U.1, h ^ p = u := by
  intro p _ k _ _ hk X _ s _ U u hu
  haveI hsm : Algebra.Smooth k (GlobalTheory.CechDR.Sec s U.1) := by
    haveI : IsOpenImmersion (GlobalTheory.CechDR.affPt s U) := IsAffineOpen.isOpenImmersion_fromSpec U.2
    have h : Smooth (GlobalTheory.CechDR.affPt s U ≫ s) := inferInstance
    rw [GlobalTheory.CechDR.affPt_w] at h
    exact RingHom.smooth_algebraMap.1 ((HasRingHomProperty.Spec_iff (P := @Smooth)).1 h)
  by_cases hU : Nonempty U.1
  · haveI : IsDomain (GlobalTheory.CechDR.Sec s U.1) := IsIntegral.component_integral (X := X) U.1
    exact GlobalTheory.T.exists_pow_eq_of_kaehler_D_eq_zero_of_smooth_domain p k hk _ u hu
  · have e : U.1 = ⊥ := by
      ext x
      exact ⟨fun hx ↦ hU ⟨⟨x, hx⟩⟩, fun hx ↦ hx.elim⟩
    have hs : Subsingleton Γ(X, U.1) := by rw [e]; infer_instance
    haveI : Subsingleton (GlobalTheory.CechDR.Sec s U.1) := hs
    exact ⟨u, Subsingleton.elim _ _⟩

end GlobalTheory.ConjSeq
