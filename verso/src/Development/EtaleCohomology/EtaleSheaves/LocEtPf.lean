import Development.EtaleCohomology.EtaleSheaves.GlobalPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut LateralTheory.E.GlobalPf

namespace LateralTheory.E.LocEtPf

/- English proof (translation)
Use `(𝟙 X : X ⟶ X).etale_appLE hU hV h` as an intermediate fact. Use `show (X.presheaf.map (homOfLE h).op).hom.Etale`. Use `this using 2` and compare the differences between its conclusion and the goal. Both sides reduce to the same expression.
-/
lemma et_res {X : Scheme.{0}} {U V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) (h : V ≤ U) :
    Et (X.presheaf.map (homOfLE h).op) := by
  have := (𝟙 X : X ⟶ X).etale_appLE hU hV h
  show (X.presheaf.map (homOfLE h).op).hom.Etale
  convert this using 2
  rfl

/- English proof (translation)
Introduce `T X p _ x`. Take `⟨_, _, V0, hV0, hx0, -, -⟩` from `Smooth.exists_isStandardSmooth p x`. Establish `hf : (p.appLE ⊤ V0 (by simp)).hom.Smooth` using `p.smooth_appLE (isAffineOpen_top _) hV0 _`. Establish `hloc` using `(RingHom.Smooth.locally_isStandardSmooth hf).span_eq_top`. Establish `hcov` using `AlgebraicGeometry.iSup_basicOpen_of_span_eq_top V0 _ hloc`.

Establish `hx1 : x ∈ (⨆ i ∈ {g : Γ(X, V0) | ((algebraMap Γ(X, V0) (Localization.Away g)).comp (p.appLE ⊤ V0 (by simp)).hom).IsStandardSmooth}, X.basicOpen i)` using `by rw [hcov]; exact hx0`. Simplify using `only [TopologicalSpace.Opens.mem_iSup] at hx1`. Take `⟨t, ht, hxt⟩` from `hx1`. Establish `hB` using `hV0.basicOpen t`. Set `` to `hV0.isLocalization_basicOpen t`.

Set `e : Localization.Away t ≃ₐ[Γ(X, V0)] Γ(X, X.basicOpen t)` to `IsLocalization.algEquiv (Submonoid.powers t) _ _`. Establish `hs : (gam p (X.basicOpen t)).hom.IsStandardSmooth`. Establish `h1` using `(RingHom.isStandardSmooth_respectsIso.1 _ e.toRingEquiv ht)`. Establish `h2` using `RingHom.isStandardSmooth_respectsIso.2 _ (Scheme.ΓSpecIso T).commRingCatIsoToRingEquiv.symm h1`. Establish `hgam : gam p (X.basicOpen t) = (Scheme.ΓSpecIso T).inv ≫ p.appLE ⊤ V0 (by simp) ≫ X.presheaf.map (homOfLE (X.basicOpen_le t)).op`.

Simplify using `only [gam]`. Use `congr 1`. Conclude with `(Scheme.Hom.appLE_map ..).symm`. Establish `halg : algebraMap Γ(X, V0) Γ(X, X.basicOpen t) = (X.presheaf.map (homOfLE (X.basicOpen_le t)).op).hom` using `rfl`. Rewrite using `[hgam]`.

Use `h2 using 1` and compare the differences between its conclusion and the goal. Use extensionality with `a`. Simplify using `only [RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_comp, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, AlgEquiv.coe_ringEquiv, AlgEquiv.commutes, halg]`. Both sides reduce to the same expression. Take `⟨n, g, hgC, hg⟩` from `hs.exists_etale_mvPolynomial`.

Use `⟨X.basicOpen t, n, hxt, fun V hV hVU => ?_⟩` and prove the remaining obligations. Use `⟨CommRingCat.ofHom g ≫ X.presheaf.map (homOfLE hVU).op, ?_, ?_⟩` and prove the remaining obligations. Conclude with `RingHom.Etale.stableUnderComposition _ _ hg (et_res hB hV hVU)`. Use `ext1`. Rewrite using `[← Category.assoc]`.

Simplify using `only [CommRingCat.hom_comp, CommRingCat.hom_ofHom]`. Rewrite using `[hgC]`. Simplify using `only [gam, Scheme.Hom.appLE, ← CommRingCat.hom_comp, Category.assoc, ← Functor.map_comp]`. Both sides reduce to the same expression.
-/
theorem LocEt_of : LocEt := by
  intro T X p _ x
  obtain ⟨_, _, V0, hV0, hx0, -, -⟩ := Smooth.exists_isStandardSmooth p x
  have hf : (p.appLE ⊤ V0 (by simp)).hom.Smooth := p.smooth_appLE (isAffineOpen_top _) hV0 _
  have hloc := (RingHom.Smooth.locally_isStandardSmooth hf).span_eq_top
  have hcov := AlgebraicGeometry.iSup_basicOpen_of_span_eq_top V0 _ hloc
  have hx1 : x ∈ (⨆ i ∈ {g : Γ(X, V0) | ((algebraMap Γ(X, V0) (Localization.Away g)).comp
      (p.appLE ⊤ V0 (by simp)).hom).IsStandardSmooth}, X.basicOpen i) := by rw [hcov]; exact hx0
  simp only [TopologicalSpace.Opens.mem_iSup] at hx1
  obtain ⟨t, ht, hxt⟩ := hx1
  have hB := hV0.basicOpen t
  let := hV0.isLocalization_basicOpen t
  let e : Localization.Away t ≃ₐ[Γ(X, V0)] Γ(X, X.basicOpen t) :=
    IsLocalization.algEquiv (Submonoid.powers t) _ _
  have hs : (gam p (X.basicOpen t)).hom.IsStandardSmooth := by
    have h1 := (RingHom.isStandardSmooth_respectsIso.1 _ e.toRingEquiv ht)
    have h2 := RingHom.isStandardSmooth_respectsIso.2 _ (Scheme.ΓSpecIso T).commRingCatIsoToRingEquiv.symm h1
    have hgam : gam p (X.basicOpen t) = (Scheme.ΓSpecIso T).inv ≫ p.appLE ⊤ V0 (by simp) ≫
        X.presheaf.map (homOfLE (X.basicOpen_le t)).op := by
      simp only [gam]
      congr 1
      exact (Scheme.Hom.appLE_map ..).symm
    have halg : algebraMap Γ(X, V0) Γ(X, X.basicOpen t) = (X.presheaf.map (homOfLE (X.basicOpen_le t)).op).hom := rfl
    rw [hgam]
    convert h2 using 1
    ext a
    simp only [RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_comp, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, AlgEquiv.coe_ringEquiv, AlgEquiv.commutes, halg]
    rfl
  obtain ⟨n, g, hgC, hg⟩ := hs.exists_etale_mvPolynomial
  refine ⟨X.basicOpen t, n, hxt, fun V hV hVU => ?_⟩
  refine ⟨CommRingCat.ofHom g ≫ X.presheaf.map (homOfLE hVU).op, ?_, ?_⟩
  · exact RingHom.Etale.stableUnderComposition _ _ hg (et_res hB hV hVU)
  · ext1
    rw [← Category.assoc]
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom]
    rw [hgC]
    simp only [gam, Scheme.Hom.appLE, ← CommRingCat.hom_comp, Category.assoc, ← Functor.map_comp]
    rfl

end LateralTheory.E.LocEtPf
