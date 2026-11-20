import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic

open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

/- English proof (translation)
Use `letI : Algebra R R' := f.toAlgebra`. Use `letI : Algebra S S' := g.toAlgebra`. Use `letI : Algebra S (Localization.Away a ⊗[R] S) := Algebra.TensorProduct.rightAlgebra`. Establish `hM : Algebra.algebraMapSubmonoid S (Submonoid.powers a) = Submonoid.powers (algebraMap R S a)`. Simplify using `[Algebra.algebraMapSubmonoid, Submonoid.map_powers]`.

Use `haveI : IsLocalization (Algebra.algebraMapSubmonoid S (Submonoid.powers a)) S' := by`. Rewrite using `[hM]`. Conclude with `hg`. Use `haveI : IsLocalization (Algebra.algebraMapSubmonoid S (Submonoid.powers a)) (Localization.Away a ⊗[R] S) := IsLocalization.tensorRight _ (Submonoid.powers a)`. Set `e1` to `IsLocalization.algEquiv (Submonoid.powers a) (Localization.Away a) R'`.

Set `e2` to `IsLocalization.algEquiv (Algebra.algebraMapSubmonoid S (Submonoid.powers a)) (Localization.Away a ⊗[R] S) S'`. Establish `key : algebraMap (Localization.Away a) (Localization.Away a ⊗[R] S) = e2.symm.toRingEquiv.toRingHom.comp (h.comp e1.toRingEquiv.toRingHom)`. Apply `IsLocalization.ringHom_ext (Submonoid.powers a)` to reduce the goal to its premises. Use extensionality with `r`. Establish `h1 : e1 (algebraMap R (Localization.Away a) r) = f r`.

Rewrite using `[AlgEquiv.commutes]`. Both sides reduce to the same expression. Establish `h2 : h (f r) = g (algebraMap R S r)`. Rewrite using `[← RingHom.comp_apply, hc, RingHom.comp_apply]`. Establish `h3 : e2.symm (g (algebraMap R S r)) = algebraMap S (Localization.Away a ⊗[R] S) (algebraMap R S r)`.

Rewrite using `[← AlgEquiv.commutes e2.symm]`. Both sides reduce to the same expression. Simplify using `only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, AlgEquiv.coe_ringEquiv]`. Rewrite using `[h1, h2, h3]`. Simplify using `[Algebra.TensorProduct.algebraMap_apply, RingHom.algebraMap_toAlgebra, Algebra.TensorProduct.tmul_one_eq_one_tmul]`.

Rewrite using `[← RingHom.etale_algebraMap, key]`. Conclude with `RingHom.Etale.respectsIso.1 _ _ (RingHom.Etale.respectsIso.2 _ _ het)`.
-/
private theorem ring_step {R S R' S' : Type} [CommRing R] [CommRing S] [CommRing R'] [CommRing S'] [Algebra R S]
    (a : R) (f : R →+* R') (g : S →+* S') (h : R' →+* S') (hc : h.comp f = g.comp (algebraMap R S))
    (hf : letI := f.toAlgebra; IsLocalization.Away a R')
    (hg : letI := g.toAlgebra; IsLocalization.Away (algebraMap R S a) S') (het : h.Etale) :
    Algebra.Etale (Localization.Away a) (Localization.Away a ⊗[R] S) := by
  classical
  letI : Algebra R R' := f.toAlgebra
  letI : Algebra S S' := g.toAlgebra
  letI : Algebra S (Localization.Away a ⊗[R] S) := Algebra.TensorProduct.rightAlgebra
  have hM : Algebra.algebraMapSubmonoid S (Submonoid.powers a) =
      Submonoid.powers (algebraMap R S a) := by
    simp [Algebra.algebraMapSubmonoid, Submonoid.map_powers]
  haveI : IsLocalization (Algebra.algebraMapSubmonoid S (Submonoid.powers a)) S' := by
    rw [hM]; exact hg
  haveI : IsLocalization (Algebra.algebraMapSubmonoid S (Submonoid.powers a))
      (Localization.Away a ⊗[R] S) := IsLocalization.tensorRight _ (Submonoid.powers a)
  let e1 := IsLocalization.algEquiv (Submonoid.powers a) (Localization.Away a) R'
  let e2 := IsLocalization.algEquiv (Algebra.algebraMapSubmonoid S (Submonoid.powers a))
    (Localization.Away a ⊗[R] S) S'
  have key : algebraMap (Localization.Away a) (Localization.Away a ⊗[R] S) =
      e2.symm.toRingEquiv.toRingHom.comp (h.comp e1.toRingEquiv.toRingHom) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers a)
    ext r
    have h1 : e1 (algebraMap R (Localization.Away a) r) = f r := by
      rw [AlgEquiv.commutes]; rfl
    have h2 : h (f r) = g (algebraMap R S r) := by
      rw [← RingHom.comp_apply, hc, RingHom.comp_apply]
    have h3 : e2.symm (g (algebraMap R S r)) =
        algebraMap S (Localization.Away a ⊗[R] S) (algebraMap R S r) := by
      rw [← AlgEquiv.commutes e2.symm]; rfl
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      AlgEquiv.coe_ringEquiv]
    rw [h1, h2, h3]
    simp [Algebra.TensorProduct.algebraMap_apply, RingHom.algebraMap_toAlgebra,
      Algebra.TensorProduct.tmul_one_eq_one_tmul]
  rw [← RingHom.etale_algebraMap, key]
  exact RingHom.Etale.respectsIso.1 _ _ (RingHom.Etale.respectsIso.2 _ _ het)

/- English proof (translation)
Establish `hV : IsAffineOpen (D.ι ⁻¹ᵁ U')` using `hU'.preimage_of_isOpenImmersion D.ι (by rw [Scheme.Opens.opensRange_ι]; exact hUD)`. Establish `hW : IsAffineOpen ((p ⁻¹ᵁ D).ι ⁻¹ᵁ W')` using `hW'.preimage_of_isOpenImmersion _ (by rw [Scheme.Opens.opensRange_ι]; exact e.trans (fun x hx => hUD hx))`. Establish `e' : (p ⁻¹ᵁ D).ι ⁻¹ᵁ W' ≤ (p ∣_ D) ⁻¹ᵁ (D.ι ⁻¹ᵁ U')`. Introduce `x hx`. Establish `h1` using `e hx`.

Establish `h2 : D.ι ((p ∣_ D) x) = p ((p ⁻¹ᵁ D).ι x)`. Rewrite using `[← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]`. Express the relevant statement in the definitionally equal form `D.ι ((p ∣_ D) x) ∈ U'`. Rewrite using `[h2]`. Conclude with `h1`.

Establish `H` using `HasRingHomProperty.appLE @Etale (p ∣_ D) ‹_› ⟨D.ι ⁻¹ᵁ U', hV⟩ ⟨(p ⁻¹ᵁ D).ι ⁻¹ᵁ W', hW⟩ e'`. Rewrite `H` using `[morphismRestrict_appLE]`. Use `(Scheme.Hom.appLE_congr _ _ ?_ ?_ (fun f => f.hom.Etale)).mp H` and prove the remaining obligations. Rewrite using `[Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_eq_right.mpr hUD]`. Rewrite using `[Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_eq_right.mpr (e.trans (fun x hx => hUD hx))]`.
-/
private theorem appLE_step {Y Z : Scheme.{0}} (p : Z ⟶ Y) (D U' : Y.Opens) [Etale (p ∣_ D)] (hUD : U' ≤ D)
    (hU' : IsAffineOpen U') (W' : Z.Opens) (hW' : IsAffineOpen W') (e : W' ≤ p ⁻¹ᵁ U') :
    (p.appLE U' W' e).hom.Etale := by
  have hV : IsAffineOpen (D.ι ⁻¹ᵁ U') :=
    hU'.preimage_of_isOpenImmersion D.ι (by rw [Scheme.Opens.opensRange_ι]; exact hUD)
  have hW : IsAffineOpen ((p ⁻¹ᵁ D).ι ⁻¹ᵁ W') :=
    hW'.preimage_of_isOpenImmersion _
      (by rw [Scheme.Opens.opensRange_ι]; exact e.trans (fun x hx => hUD hx))
  have e' : (p ⁻¹ᵁ D).ι ⁻¹ᵁ W' ≤ (p ∣_ D) ⁻¹ᵁ (D.ι ⁻¹ᵁ U') := by
    intro x hx
    have h1 := e hx
    have h2 : D.ι ((p ∣_ D) x) = p ((p ⁻¹ᵁ D).ι x) := by
      rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]
    change D.ι ((p ∣_ D) x) ∈ U'
    rw [h2]
    exact h1
  have H := HasRingHomProperty.appLE @Etale (p ∣_ D) ‹_›
    ⟨D.ι ⁻¹ᵁ U', hV⟩ ⟨(p ⁻¹ᵁ D).ι ⁻¹ᵁ W', hW⟩ e'
  rw [morphismRestrict_appLE] at H
  refine (Scheme.Hom.appLE_congr _ _ ?_ ?_ (fun f => f.hom.Etale)).mp H
  · rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr hUD]
  · rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr (e.trans (fun x hx => hUD hx))]

/- English proof (translation)
Unfold `EtChart`. Introduce `l Y T U hU`. Use `letI := T.alg U`. Use `haveI := T.fin`. Use `haveI := T.et`.

Establish `hZU : IsAffineOpen (T.p ⁻¹ᵁ U)` using `hU.preimage T.p`. Establish `e0 : T.Z.basicOpen ((T.p.app U).hom (l : Γ(Y, U))) ≤ T.p ⁻¹ᵁ Y.basicOpen (l : Γ(Y, U))` using `(Scheme.preimage_basicOpen T.p _).ge`. Establish `hUD : Y.basicOpen (l : Γ(Y, U)) ≤ Y.basicOpen (l : Γ(Y, ⊤))`. Establish `hres : (Y.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom (l : Γ(Y, ⊤)) = (l : Γ(Y, U))` using `map_natCast _ l`. Rewrite using `[← hres, Scheme.basicOpen_res]`.

Conclude with `inf_le_right`. Establish `het` using `appLE_step T.p (Y.basicOpen (l : Γ(Y, ⊤))) (Y.basicOpen (l : Γ(Y, U))) hUD (hU.basicOpen _) _ (hZU.basicOpen _) e0`. Use `ring_step (l : Γ(Y, U)) (Y.presheaf.map (homOfLE (Y.basicOpen_le (l : Γ(Y, U)))).op).hom (T.Z.presheaf.map (homOfLE (T.Z.basicOpen_le ((T.p.app U).hom (l : Γ(Y, U))))).op).hom (T.p.appLE _ _ e0).hom ?_ (hU.isLocalization_basicOpen _) (hZU.isLocalization_basicOpen _) het` and prove the remaining obligations. Rewrite using `[← CommRingCat.hom_comp]`. Express the relevant statement in the definitionally equal form `_ = CommRingCat.Hom.hom (T.p.app U ≫ _)`.

Use `congr 1`. Simplify using `only [Scheme.Hom.map_appLE, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map]`.
-/
theorem UpperTheory.Gal.crystallineComparison.etChart_of :
    EtChart := by
  unfold EtChart
  intro l Y T U hU
  letI := T.alg U
  haveI := T.fin
  haveI := T.et
  have hZU : IsAffineOpen (T.p ⁻¹ᵁ U) := hU.preimage T.p
  have e0 : T.Z.basicOpen ((T.p.app U).hom (l : Γ(Y, U))) ≤
      T.p ⁻¹ᵁ Y.basicOpen (l : Γ(Y, U)) := (Scheme.preimage_basicOpen T.p _).ge
  have hUD : Y.basicOpen (l : Γ(Y, U)) ≤ Y.basicOpen (l : Γ(Y, ⊤)) := by
    have hres : (Y.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom (l : Γ(Y, ⊤)) =
        (l : Γ(Y, U)) := map_natCast _ l
    rw [← hres, Scheme.basicOpen_res]
    exact inf_le_right
  have het := appLE_step T.p (Y.basicOpen (l : Γ(Y, ⊤))) (Y.basicOpen (l : Γ(Y, U))) hUD
    (hU.basicOpen _) _ (hZU.basicOpen _) e0
  refine ring_step (l : Γ(Y, U))
    (Y.presheaf.map (homOfLE (Y.basicOpen_le (l : Γ(Y, U)))).op).hom
    (T.Z.presheaf.map (homOfLE (T.Z.basicOpen_le ((T.p.app U).hom (l : Γ(Y, U))))).op).hom
    (T.p.appLE _ _ e0).hom ?_ (hU.isLocalization_basicOpen _) (hZU.isLocalization_basicOpen _) het
  rw [← CommRingCat.hom_comp]
  change _ = CommRingCat.Hom.hom (T.p.app U ≫ _)
  congr 1
  simp only [Scheme.Hom.map_appLE, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map]
