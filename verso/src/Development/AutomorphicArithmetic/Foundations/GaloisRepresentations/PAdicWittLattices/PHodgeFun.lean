import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HodgePullHodgeTraceHodgePull
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.SplitsBasic

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

/- English proof (translation)
Rewrite using `[Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec f hU hV i, ← Category.assoc, ← Spec.map_comp]`. Both sides reduce to the same expression.
-/
private theorem affine_point_comp {X Y : Scheme.{0}} (f : X ⟶ Y) {V : X.Opens} {U : Y.Opens} (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) (i : V ≤ f ⁻¹ᵁ U) {Ω : Type} [Field Ω] (x : Γ(X, V) →+* Ω) :
    (Spec.map (CommRingCat.ofHom x) ≫ hV.fromSpec) ≫ f =
      Spec.map (CommRingCat.ofHom (x.comp (f.appLE U V i).hom)) ≫ hU.fromSpec := by
  rw [Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec f hU hV i, ← Category.assoc, ← Spec.map_comp]
  rfl

/- English proof (translation)
Establish `h'` using `Spec.map_injective ((cancel_mono _).1 h)`. Conclude with `congrArg CommRingCat.Hom.hom h'`.
-/
private theorem affine_point_injective {X : Scheme.{0}} {V : X.Opens} (hV : IsAffineOpen V) {Ω : Type} [Field Ω]
    {a b : Γ(X, V) →+* Ω}
    (h : Spec.map (CommRingCat.ofHom a) ≫ hV.fromSpec = Spec.map (CommRingCat.ofHom b) ≫ hV.fromSpec) : a = b := by
  have h' := Spec.map_injective ((cancel_mono _).1 h)
  exact congrArg CommRingCat.Hom.hom h'

/- English proof (translation)
Use `letI : Algebra (GlobalTheory.CechDR.Sec p U) (GlobalTheory.CechDR.Sec q (s ⁻¹ᵁ U)) := secAlg p q s U`. Use `haveI : Module.Finite (GlobalTheory.CechDR.Sec p U) (GlobalTheory.CechDR.Sec q (s ⁻¹ᵁ U)) := sec_finite hU`. Use `haveI : Algebra.Etale (GlobalTheory.CechDR.Sec p U) (GlobalTheory.CechDR.Sec q (s ⁻¹ᵁ U)) := sec_etale hU`. Use `letI : Algebra (GlobalTheory.CechDR.Sec p U) Γ(W, V) := (c.appLE U V hVU).hom.toAlgebra`. Establish `hcomp : ∀ j, s.app U ≫ (σ j).appLE (s ⁻¹ᵁ U) V (hVU.trans (GlobalTheory.GalTrace.preimage_le (hσ j) U)) = c.appLE U V hVU`.

Introduce `j`. Rewrite using `[Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]`. Simplify using `only [hσ j]`. Set `τ : J → GlobalTheory.CechDR.Sec q (s ⁻¹ᵁ U) →ₐ[GlobalTheory.CechDR.Sec p U] Γ(W, V)` to `fun j => { toRingHom := ((σ j).appLE (s ⁻¹ᵁ U) V (hVU.trans (GlobalTheory.GalTrace.preimage_le (hσ j) U))).hom commutes' := fun a => congrArg (fun f => CommRingCat.Hom.hom f a) (hcomp j) }`. Establish `hA' : IsAffineOpen (s ⁻¹ᵁ U)` using `hU.preimage s`.

Take `⟨e, he⟩` from `hS _ _ _ J τ (by`. Introduce `Ω _ _ x y hxy`. Establish `hring : y.comp (s.appLE U (s ⁻¹ᵁ U) le_rfl).hom = x.comp (c.appLE U V hVU).hom`. Rewrite using `[← Scheme.Hom.app_eq_appLE]`. Conclude with `hxy`.

Establish `hpt : (Spec.map (CommRingCat.ofHom y) ≫ hA'.fromSpec) ≫ s = (Spec.map (CommRingCat.ofHom x) ≫ hV.fromSpec) ≫ c` using `(affine_point_comp s hU hA' le_rfl y).trans ((congrArg (fun f => Spec.map (CommRingCat.ofHom f) ≫ hU.fromSpec) hring).trans (affine_point_comp c hU hV hVU x).symm)`. Take `⟨j, hj, huniq⟩` from `hP s c J σ hsp Ω _ _ hpt`. Use `⟨j, ?_, fun j' hj' => huniq j' ?_⟩` and prove the remaining obligations. Conclude with `affine_point_injective hA' ((affine_point_comp (σ j) hA' hV (hVU.trans (GlobalTheory.GalTrace.preimage_le (hσ j) U)) x).symm.trans hj)`. Conclude with `(affine_point_comp (σ j') hA' hV (hVU.trans (GlobalTheory.GalTrace.preimage_le (hσ j') U)) x).trans (congrArg (fun f => Spec.map (CommRingCat.ofHom f) ≫ hA'.fromSpec) hj'))`.

Conclude with `hT _ _ _ J τ e he b`.
-/
private theorem cech_section_local_split (hP : PtsOfSplits) (hS : AlgSplit) (hT : AlgTr) {k : Type} [Field k] {Z Y W : Scheme.{0}}
    (p : Z ⟶ sp k) (q : Y ⟶ sp k) (s : Y ⟶ Z) [IsFinite s] [Etale s] (c : W ⟶ Z) (J : Type) [Fintype J]
    (σ : J → (W ⟶ Y)) (hσ : ∀ j, σ j ≫ s = c) (hsp : Splits s c σ) (U : Z.Opens) (hU : IsAffineOpen U)
    (V : W.Opens) (hV : IsAffineOpen V) (hVU : V ≤ c ⁻¹ᵁ U) (b : GlobalTheory.CechDR.Sec q (s ⁻¹ᵁ U)) :
    (c.appLE U V hVU).hom (secTrace p q hU b) =
      ∑ j, ((σ j).appLE (s ⁻¹ᵁ U) V (hVU.trans (GlobalTheory.GalTrace.preimage_le (hσ j) U))).hom b := by
  letI : Algebra (GlobalTheory.CechDR.Sec p U) (GlobalTheory.CechDR.Sec q (s ⁻¹ᵁ U)) := secAlg p q s U
  haveI : Module.Finite (GlobalTheory.CechDR.Sec p U) (GlobalTheory.CechDR.Sec q (s ⁻¹ᵁ U)) := sec_finite hU
  haveI : Algebra.Etale (GlobalTheory.CechDR.Sec p U) (GlobalTheory.CechDR.Sec q (s ⁻¹ᵁ U)) := sec_etale hU
  letI : Algebra (GlobalTheory.CechDR.Sec p U) Γ(W, V) := (c.appLE U V hVU).hom.toAlgebra
  have hcomp : ∀ j, s.app U ≫ (σ j).appLE (s ⁻¹ᵁ U) V (hVU.trans (GlobalTheory.GalTrace.preimage_le (hσ j) U)) =
      c.appLE U V hVU := by
    intro j
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
    simp only [hσ j]
  let τ : J → GlobalTheory.CechDR.Sec q (s ⁻¹ᵁ U) →ₐ[GlobalTheory.CechDR.Sec p U] Γ(W, V) := fun j =>
    { toRingHom := ((σ j).appLE (s ⁻¹ᵁ U) V (hVU.trans (GlobalTheory.GalTrace.preimage_le (hσ j) U))).hom
      commutes' := fun a => congrArg (fun f => CommRingCat.Hom.hom f a) (hcomp j) }
  have hA' : IsAffineOpen (s ⁻¹ᵁ U) := hU.preimage s
  obtain ⟨e, he⟩ := hS _ _ _ J τ (by
    intro Ω _ _ x y hxy
    have hring : y.comp (s.appLE U (s ⁻¹ᵁ U) le_rfl).hom = x.comp (c.appLE U V hVU).hom := by
      rw [← Scheme.Hom.app_eq_appLE]
      exact hxy
    have hpt : (Spec.map (CommRingCat.ofHom y) ≫ hA'.fromSpec) ≫ s =
        (Spec.map (CommRingCat.ofHom x) ≫ hV.fromSpec) ≫ c :=
      (affine_point_comp s hU hA' le_rfl y).trans
        ((congrArg (fun f => Spec.map (CommRingCat.ofHom f) ≫ hU.fromSpec) hring).trans
          (affine_point_comp c hU hV hVU x).symm)
    obtain ⟨j, hj, huniq⟩ := hP s c J σ hsp Ω _ _ hpt
    refine ⟨j, ?_, fun j' hj' => huniq j' ?_⟩
    · exact affine_point_injective hA'
        ((affine_point_comp (σ j) hA' hV (hVU.trans (GlobalTheory.GalTrace.preimage_le (hσ j) U)) x).symm.trans hj)
    · exact (affine_point_comp (σ j') hA' hV (hVU.trans (GlobalTheory.GalTrace.preimage_le (hσ j') U)) x).trans
        (congrArg (fun f => Spec.map (CommRingCat.ofHom f) ≫ hA'.fromSpec) hj'))
  exact hT _ _ _ J τ e he b

/- English proof (translation)
Introduce `hP hS hT k _ Z Y W p q r s _ _ c J _ σ hσ hsp U hU b`. Use `TopCat.Sheaf.eq_of_locally_eq' W.sheaf (fun i : {V : W.Opens // IsAffineOpen V ∧ V ≤ c ⁻¹ᵁ U} => i.1) (c ⁻¹ᵁ U) (fun i => homOfLE i.2.2) ?_ _ _ ?_` and prove the remaining obligations. Introduce `x hx`. Take `⟨V, hV, hxV, hVU⟩` from `TopologicalSpace.Opens.isBasis_iff_nbhd.mp W.isBasis_affineOpens hx`. Conclude with `TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨V, hV, hVU⟩, hxV⟩`.

Introduce and unpack `⟨V, hV, hVU⟩`. Establish `key` using `cech_section_local_split hP hS hT p q s c J σ hσ hsp U hU V hV hVU b`. Use `key.trans ((Finset.sum_congr rfl fun j _ => ?_).trans (map_sum (W.presheaf.map (homOfLE hVU).op).hom _ _).symm)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `_ = ((σ j).app (s ⁻¹ᵁ U) ≫ W.presheaf.map (homOfLE (GlobalTheory.GalTrace.preimage_le (hσ j) U)).op ≫ W.presheaf.map (homOfLE hVU).op).hom b`. Rewrite using `[← Functor.map_comp, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map]`.
-/
theorem UpperTheory.Gal.G3.pHodgeFun :
    PtsOfSplits → AlgSplit → AlgTr → ∀ (k : Type) [Field k] {Z Y W : Scheme.{0}} (p : Z ⟶ sp k) (q : Y ⟶ sp k) (r : W ⟶ sp k) (s : Y ⟶ Z) [IsFinite s] [Etale s] (c : W ⟶ Z) (J : Type) [Fintype J] (σ : J → (W ⟶ Y)) (hσ : ∀ j, σ j ≫ s = c), Splits s c σ → ∀ (U : Z.Opens) (hU : IsAffineOpen U) (b : GlobalTheory.CechDR.Sec q (s ⁻¹ᵁ U)), GlobalTheory.HodgeCoh.appSec p r c U (secTrace p q hU b) = ∑ j, GlobalTheory.CechDR.Sec.res r (GlobalTheory.GalTrace.preimage_le (hσ j) U) (GlobalTheory.HodgeCoh.appSec q r (σ j) (s ⁻¹ᵁ U) b) := by
  intro hP hS hT k _ Z Y W p q r s _ _ c J _ σ hσ hsp U hU b
  refine TopCat.Sheaf.eq_of_locally_eq' W.sheaf (fun i : {V : W.Opens // IsAffineOpen V ∧ V ≤ c ⁻¹ᵁ U} => i.1) (c ⁻¹ᵁ U) (fun i => homOfLE i.2.2) ?_ _ _ ?_
  · intro x hx
    obtain ⟨V, hV, hxV, hVU⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp W.isBasis_affineOpens hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨V, hV, hVU⟩, hxV⟩
  · rintro ⟨V, hV, hVU⟩
    have key := cech_section_local_split hP hS hT p q s c J σ hσ hsp U hU V hV hVU b
    refine key.trans ((Finset.sum_congr rfl fun j _ => ?_).trans (map_sum (W.presheaf.map (homOfLE hVU).op).hom _ _).symm)
    change _ = ((σ j).app (s ⁻¹ᵁ U) ≫ W.presheaf.map (homOfLE (GlobalTheory.GalTrace.preimage_le (hσ j) U)).op ≫ W.presheaf.map (homOfLE hVU).op).hom b
    rw [← Functor.map_comp, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map]
