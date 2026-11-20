import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

/- English proof (translation)
Introduce `a b h`. Establish `e` using `Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R)))`. Establish `h2` using `congrArg (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom h`. Establish `h3 : ∀ x, (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom ((jK R).appTop.hom x) = algebraMap R (FractionRing R) ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom x)` using `fun x => congrArg (fun f => f.hom x) e`. Rewrite `h2` using `[h3, h3]`.

Establish `h4` using `IsFractionRing.injective R (FractionRing R) h2`. Use `congrArg (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom h4` as an intermediate fact. Simplify using `using this`.
-/
theorem jK_appTop_injective (R : Type) [CommRing R] [IsDomain R] :
    Function.Injective (jK R).appTop.hom := by
  intro a b h
  have e := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R)))
  have h2 := congrArg (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom h
  have h3 : ∀ x, (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom ((jK R).appTop.hom x) =
      algebraMap R (FractionRing R) ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom x) := fun x =>
    congrArg (fun f => f.hom x) e
  rw [h3, h3] at h2
  have h4 := IsFractionRing.injective R (FractionRing R) h2
  have := congrArg (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom h4
  simpa using this

/- English proof (translation)
Use `haveI := M.integral`. Use `haveI := M.dominant`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `s hs`. Rewrite using `[← AlgebraicGeometry.basicOpen_eq_bot_iff, eq_bot_iff]`.

Introduce `x hx`. Take `⟨y, hy⟩` from `M.gp.denseRange.exists_mem_open (M.S.basicOpen s).isOpen ⟨x, hx⟩`. Establish `: y ∈ M.gp ⁻¹ᵁ M.S.basicOpen s` using `hy`. Rewrite `this` using `[Scheme.preimage_basicOpen_top, hs, Scheme.basicOpen_zero]`. Conclude with `absurd this (by simp)`.
-/
theorem Modif.gp_appTop_injective {R : Type} [CommRing R] [IsDomain R] (M : Modif R) :
    Function.Injective M.gp.appTop.hom := by
  haveI := M.integral
  haveI := M.dominant
  rw [injective_iff_map_eq_zero]
  intro s hs
  rw [← AlgebraicGeometry.basicOpen_eq_bot_iff, eq_bot_iff]
  intro x hx
  obtain ⟨y, hy⟩ := M.gp.denseRange.exists_mem_open (M.S.basicOpen s).isOpen ⟨x, hx⟩
  have : y ∈ M.gp ⁻¹ᵁ M.S.basicOpen s := hy
  rw [Scheme.preimage_basicOpen_top, hs, Scheme.basicOpen_zero] at this
  exact absurd this (by simp)

/- English proof (translation)
Rewrite using `[← M.gp_π, Scheme.Hom.comp_appTop]`. Both sides reduce to the same expression.
-/
theorem Modif.appTop_comp {R : Type} [CommRing R] [IsDomain R] (M : Modif R) (a : Γ(Sp R, ⊤)) :
    M.gp.appTop.hom (M.π.appTop.hom a) = (jK R).appTop.hom a := by
  rw [← M.gp_π, Scheme.Hom.comp_appTop]
  rfl

/- English proof (translation)
Introduce `R _ _ _ _ M`. Use `haveI := M.proper`. Use `haveI := M.integral`. Establish `hinj : Function.Injective M.π.appTop.hom` using `fun a b h => jK_appTop_injective R (by`. Rewrite using `[← M.appTop_comp, ← M.appTop_comp, h])`.

Use `⟨⟨hinj, fun b => ?_⟩, ⟨?_⟩⟩` and prove the remaining obligations. Take `⟨p, hpm, hp⟩` from `isIntegral_appTop_of_universallyClosed M.π b`. Set `eR` to `(Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv`. Set `eK` to `(Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).commRingCatIsoToRingEquiv`. Establish `e` using `Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R)))`.

Establish `h3 : ∀ x, eK ((jK R).appTop.hom x) = algebraMap R (FractionRing R) (eR x)` using `fun x => congrArg (fun f => f.hom x) e`. Establish `hc : IsIntegral R (eK (M.gp.appTop.hom b))`. Use `⟨p.map eR.toRingHom, hpm.map _, ?_⟩` and prove the remaining obligations. Rewrite using `[Polynomial.eval₂_map]`. Establish `: (algebraMap R (FractionRing R)).comp eR.toRingHom = (eK.toRingHom.comp M.gp.appTop.hom).comp M.π.appTop.hom`.

Use extensionality with `x`. Simplify using `only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]`. Rewrite using `[M.appTop_comp, h3]`. Rewrite using `[this]`. Combine the equalities or inequalities in the displayed calculation.

Take `⟨r, hr⟩` from `IsIntegrallyClosed.isIntegral_iff.1 hc`. Use `⟨eR.symm r, M.gp_appTop_injective (eK.injective ?_)⟩` and prove the remaining obligations. Rewrite using `[M.appTop_comp, h3, RingEquiv.apply_symm_apply, hr]`. Establish `hcl : IsClosed (Set.range M.π)` using `(M.π.isClosedMap).isClosed_range`. Establish `hd : Dense (Set.range (jK R))` using `(Modif.self R).dominant.denseRange`.

Establish `hsub : Set.range (jK R) ⊆ Set.range M.π`. Introduce and unpack `_ ⟨y, rfl⟩`. Conclude with `⟨M.gp y, by rw [← Scheme.Hom.comp_apply, M.gp_π]⟩`. Use `(hd.mono hsub).closure_eq` as an intermediate fact. Rewrite `this` using `[hcl.closure_eq]`.

Conclude with `Set.range_eq_univ.1 this`.
-/
theorem Modif.appTop_bijective_surjective : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] (M : Modif R), Function.Bijective M.π.appTop.hom ∧ Surjective M.π := by
  intro R _ _ _ _ M
  haveI := M.proper
  haveI := M.integral
  have hinj : Function.Injective M.π.appTop.hom := fun a b h => jK_appTop_injective R (by
    rw [← M.appTop_comp, ← M.appTop_comp, h])
  refine ⟨⟨hinj, fun b => ?_⟩, ⟨?_⟩⟩
  ·
    obtain ⟨p, hpm, hp⟩ := isIntegral_appTop_of_universallyClosed M.π b
    let eR := (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv
    let eK := (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).commRingCatIsoToRingEquiv
    have e := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R)))
    have h3 : ∀ x, eK ((jK R).appTop.hom x) = algebraMap R (FractionRing R) (eR x) := fun x =>
      congrArg (fun f => f.hom x) e
    have hc : IsIntegral R (eK (M.gp.appTop.hom b)) := by
      refine ⟨p.map eR.toRingHom, hpm.map _, ?_⟩
      rw [Polynomial.eval₂_map]
      have : (algebraMap R (FractionRing R)).comp eR.toRingHom =
          (eK.toRingHom.comp M.gp.appTop.hom).comp M.π.appTop.hom := by
        ext x
        simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
        rw [M.appTop_comp, h3]
      rw [this]
      calc _ = (eK.toRingHom.comp M.gp.appTop.hom) (p.eval₂ M.π.appTop.hom b) :=
            (Polynomial.hom_eval₂ _ _ _ _).symm
        _ = 0 := by rw [hp, map_zero]
    obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.1 hc
    refine ⟨eR.symm r, M.gp_appTop_injective (eK.injective ?_)⟩
    rw [M.appTop_comp, h3, RingEquiv.apply_symm_apply, hr]
  ·
    have hcl : IsClosed (Set.range M.π) := (M.π.isClosedMap).isClosed_range
    have hd : Dense (Set.range (jK R)) := (Modif.self R).dominant.denseRange
    have hsub : Set.range (jK R) ⊆ Set.range M.π := by
      rintro _ ⟨y, rfl⟩
      exact ⟨M.gp y, by rw [← Scheme.Hom.comp_apply, M.gp_π]⟩
    have := (hd.mono hsub).closure_eq
    rw [hcl.closure_eq] at this
    exact Set.range_eq_univ.1 this

end GlobalTheory.Mum
