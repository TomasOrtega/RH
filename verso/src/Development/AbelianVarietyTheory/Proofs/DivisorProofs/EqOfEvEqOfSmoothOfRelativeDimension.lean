import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SerreHolomorphicSections
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.EqZeroOfForallAlgHomComplex

open CategoryTheory AlgebraicGeometry TopologicalSpace Set
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CxPts

namespace GlobalTheory

/- English proof (translation)
Introduce `Y p D hp W a b hab`. Establish `hsm : Smooth p` using `SmoothOfRelativeDimension.smooth D p`. Establish `hred : IsReduced Y` using `(isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field ℂ Y p hsm).1`. Use `TopCat.Presheaf.IsSheaf.section_ext Y.IsSheaf fun x hx => ?_` and prove the remaining obligations. Take `⟨U, hU, hxU, hUW⟩` from `Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens (show x ∈ W from hx)`.

Use `replace hU : IsAffineOpen U := hU`. Use `⟨U, hUW, hxU, ?_⟩` and prove the remaining obligations. Establish `hc : (algX p U).FiniteType`. Establish `h1 : (p.appLE ⊤ U (fun _ _ => trivial)).hom.FiniteType` using `HasRingHomProperty.appLE @LocallyOfFiniteType p inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ _`. Conclude with `h1.comp (RingHom.FiniteType.of_surjective _ (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv).2)`.

Set `: Algebra ℂ Γ(Y, U)` to `(algX p U).toAlgebra`. Establish `: Algebra.FiniteType ℂ Γ(Y, U)` using `hc`. Express the relevant statement in the definitionally equal form `resG Y hUW a = resG Y hUW b`. Rewrite using `[← sub_eq_zero]`. Use `eq_zero_of_forall_algHom_complex _ fun e => ?_` and prove the remaining obligations.

Establish `hm` using `ofHom_mem (p := p) (σ := RingHom.id ℂ) hU e.toRingHom (fun c => e.commutes c)`. Establish `h` using `hab _ (ptsIn_mono hUW hm)`. Rewrite `h` using `[← ev_res hUW hm, ← ev_res hUW hm, ev_ofHom, ev_ofHom]`. Rewrite using `[map_sub, sub_eq_zero]`. Conclude with `h`.
-/
theorem eq_of_ev_eq_of_smoothOfRelativeDimension :
    ∀ (Y : Scheme.{0}) (p : Y ⟶ Sp ℂ) (D : ℕ), SmoothOfRelativeDimension D p → ∀ (W : Y.Opens) (a b : Γ(Y, W)), (∀ y ∈ ptsIn p (RingHom.id ℂ) W, ev p (RingHom.id ℂ) W a y = ev p (RingHom.id ℂ) W b y) → a = b := by
  intro Y p D hp W a b hab
  have hsm : Smooth p := SmoothOfRelativeDimension.smooth D p
  have hred : IsReduced Y :=
    (isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field ℂ Y p hsm).1
  refine TopCat.Presheaf.IsSheaf.section_ext Y.IsSheaf fun x hx => ?_
  obtain ⟨U, hU, hxU, hUW⟩ := Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens (show x ∈ W from hx)
  replace hU : IsAffineOpen U := hU
  refine ⟨U, hUW, hxU, ?_⟩
  have hc : (algX p U).FiniteType := by
    have h1 : (p.appLE ⊤ U (fun _ _ => trivial)).hom.FiniteType :=
      HasRingHomProperty.appLE @LocallyOfFiniteType p inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ _
    exact h1.comp (RingHom.FiniteType.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv).2)
  let : Algebra ℂ Γ(Y, U) := (algX p U).toAlgebra
  have : Algebra.FiniteType ℂ Γ(Y, U) := hc
  change resG Y hUW a = resG Y hUW b
  rw [← sub_eq_zero]
  refine eq_zero_of_forall_algHom_complex _ fun e => ?_
  have hm := ofHom_mem (p := p) (σ := RingHom.id ℂ) hU e.toRingHom (fun c => e.commutes c)
  have h := hab _ (ptsIn_mono hUW hm)
  rw [← ev_res hUW hm, ← ev_res hUW hm, ev_ofHom, ev_ofHom] at h
  rw [map_sub, sub_eq_zero]
  exact h

end GlobalTheory
