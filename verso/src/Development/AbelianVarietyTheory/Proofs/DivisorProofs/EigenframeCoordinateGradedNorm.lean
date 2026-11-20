import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DrAtNonneg
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GrNormPosOfBasis
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DualGramInterpGram
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenframeGenericAffineOpen
open NumberField IsDedekindDomain Filter Topology
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovHt.Link GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.Cartier GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal
open AlgebraicGeometry CategoryTheory
open GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CovHt.Link.DrAtFrame

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β} {F : Type} [Field F] {e : F ≃+* c.F} (Y : FlagCpt Z e)

/- English proof (translation)
Establish `hι` using `IsFractionRing.injective (Y.Y.X.presheaf.stalk b) Y.Y.X.functionField`. Take `rfl : φ₁ = φ` from `RingHom.ext fun x => hι ((RingHom.congr_fun a₁.2.1 x).symm.trans (RingHom.congr_fun a.2.1 x))`. Take `⟨k₁, hk₁⟩` from `f₁.exists_isMap _ a.2.1 a.1`. Take `⟨k, hk⟩` from `f.exists_isMap _ a.2.1 a.1`. Establish `e1 (τ i d) : k₁.co Y.f0 τ d i = ∑ j, k.co Y.f0 τ j i * algebraMap _ Y.Y.X.functionField (f₁.co f τ d j)`.

Rewrite using `[← k₁.co_mul k, hk₁.co τ hk a.1, Matrix.mul_apply]`. Conclude with `Finset.sum_congr rfl fun _ _ => mul_comm _ _`. Establish `hM (τ d i) (h : i < d) : f₁.co f τ d i = 0` using `hι ((CoordUniq.tri_of_mul (M := fun i a => algebraMap _ Y.Y.X.functionField (f₁.co f τ a i)) (fun i a => (a₁.co τ hk₁).1 a i) (fun i a' => (a.co τ hk).1 a' i) (fun i => (a.co τ hk).2 i ▸ (t τ i).ne_zero) (e1 τ) i d h).trans (map_zero _).symm)`. Establish `hu (τ i) : IsUnit (f₁.co f τ i i)`. Use `f₁.isUnit_det_co f τ` as an intermediate fact.

Rewrite `this` using `[Matrix.det_of_upperTriangular (M := f₁.co f τ) fun _ _ h => hM τ _ _ h]`. Conclude with `isUnit_of_dvd_unit (Finset.dvd_prod_of_mem (fun i => f₁.co f τ i i) (Finset.mem_univ i)) this`. Use `⟨fun τ i => (hu τ i).unit, fun τ i => Units.ext ?_, fun τ i => ⟨fun d => f₁.co f τ d i, (hu τ i).unit_spec.symm, fun d hd => hM τ d i hd, f₁.co_spec f τ i⟩⟩` and prove the remaining obligations. Rewrite using `[← (a₁.co τ hk₁).2, e1, Units.val_mul, ← (a.co τ hk).2]`. Conclude with `CoordUniq.diag_of_mul (M := fun i a => algebraMap _ Y.Y.X.functionField (f₁.co f τ a i)) (fun i a' => (a.co τ hk).1 a' i) (fun i a h => by simp only [hM τ a i h, map_zero]) i`.
-/
theorem compare {b : Y.Y.X} {φ₁ φ : c.F →+* Y.Y.X.presheaf.stalk b}
    {f₁ : EigFrame Z φ₁ (stalkPt Y.Y b ≫ Y.π ≫ genι Z)} {f : EigFrame Z φ (stalkPt Y.Y b ≫ Y.π ≫ genι Z)}
    {t₁ t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Y.Y.Fnˣ}
    (a₁ : f₁.Tri (algebraMap (Y.Y.X.presheaf.stalk b) Y.Y.X.functionField) Y.f0 t₁)
    (a : f.Tri (algebraMap (Y.Y.X.presheaf.stalk b) Y.Y.X.functionField) Y.f0 t) :
    ∃ u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Y.Y.X.presheaf.stalk b)ˣ,
      (∀ τ i, t₁ τ i = t τ i * Units.map (algebraMap _ Y.Y.X.functionField).toMonoidHom (u τ i)) ∧
      ∀ τ i, ∃ cf : Fin (Dw.mult τ) → Y.Y.X.presheaf.stalk b, cf i = u τ i ∧ (∀ k, i < k → cf k = 0) ∧
        IsCombAtG Z.t (stalkPt Y.Y b ≫ Y.π ≫ genι Z) (f₁.v τ) cf (f.v τ i) := by
  have hι := IsFractionRing.injective (Y.Y.X.presheaf.stalk b) Y.Y.X.functionField
  obtain rfl : φ₁ = φ := RingHom.ext fun x => hι ((RingHom.congr_fun a₁.2.1 x).symm.trans (RingHom.congr_fun a.2.1 x))
  obtain ⟨k₁, hk₁⟩ := f₁.exists_isMap _ a.2.1 a.1
  obtain ⟨k, hk⟩ := f.exists_isMap _ a.2.1 a.1
  have e1 (τ i d) : k₁.co Y.f0 τ d i = ∑ j, k.co Y.f0 τ j i * algebraMap _ Y.Y.X.functionField (f₁.co f τ d j) := by
    rw [← k₁.co_mul k, hk₁.co τ hk a.1, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  have hM (τ d i) (h : i < d) : f₁.co f τ d i = 0 := hι ((CoordUniq.tri_of_mul
    (M := fun i a => algebraMap _ Y.Y.X.functionField (f₁.co f τ a i)) (fun i a => (a₁.co τ hk₁).1 a i)
    (fun i a' => (a.co τ hk).1 a' i) (fun i => (a.co τ hk).2 i ▸ (t τ i).ne_zero) (e1 τ) i d h).trans (map_zero _).symm)
  have hu (τ i) : IsUnit (f₁.co f τ i i) := by
    have := f₁.isUnit_det_co f τ
    rw [Matrix.det_of_upperTriangular (M := f₁.co f τ) fun _ _ h => hM τ _ _ h] at this
    exact isUnit_of_dvd_unit (Finset.dvd_prod_of_mem (fun i => f₁.co f τ i i) (Finset.mem_univ i)) this
  refine ⟨fun τ i => (hu τ i).unit, fun τ i => Units.ext ?_, fun τ i =>
    ⟨fun d => f₁.co f τ d i, (hu τ i).unit_spec.symm, fun d hd => hM τ d i hd, f₁.co_spec f τ i⟩⟩
  rw [← (a₁.co τ hk₁).2, e1, Units.val_mul, ← (a.co τ hk).2]
  exact CoordUniq.diag_of_mul (M := fun i a => algebraMap _ Y.Y.X.functionField (f₁.co f τ a i))
    (fun i a' => (a.co τ hk).1 a' i) (fun i a h => by simp only [hM τ a i h, map_zero]) i

end Free

end GlobalTheory.CovHt.Link.DrAtFrame

namespace GlobalTheory.CovHt.Link.DrAtFrame

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `D A N j S κ s Φ k la K _ _ p x F φ xg gf a hg hc`. Take `⟨y, ψ, φ₁, f, t, t', r, hx, h2, h3, h4, rfl⟩` from `hc`. Establish `hs : below x ⤳ y`. Establish `: below x ∈ Set.range ((Φ.C k).Y.X.fromSpecStalk y)`. Rewrite using `[hx]`.

Conclude with `⟨_, rfl⟩`. Rewrite `this` using `[Scheme.range_fromSpecStalk]`. Then use the resulting hypothesis. Set `ρ` to `((Φ.C k).Y.X.presheaf.stalkSpecializes hs).hom`. Set `ev : (Φ.C k).Y.X.presheaf.stalk (below x) →+* K` to `(Scheme.stalkClosedPointTo x).hom`. Establish `h1 : spMap ρ ≫ stalkPt (Φ.C k).Y y = stalkPt (Φ.C k).Y (below x)` using `Scheme.SpecMap_stalkSpecializes_fromSpecStalk hs`.

Establish `hxe : spMap ev ≫ stalkPt (Φ.C k).Y (below x) = x` using `Scheme.Spec_stalkClosedPointTo_fromSpecStalk x`. Establish `h2' : ev.comp ρ = ψ` using `EigLoc.spMap_inj ((cancel_mono ((Φ.C k).Y.X.fromSpecStalk y)).1 (by`. Use `Eq.trans ?_ (hxe.trans hx)` and prove the remaining obligations. Rewrite using `[← h1, ← Category.assoc, ← Spec.map_comp]`. Use the proof step `rfl))`.

Establish `h3' : (algebraMap _ (Φ.C k).Y.X.functionField).comp ρ = algebraMap _ (Φ.C k).Y.X.functionField` using `congrArg CommRingCat.Hom.hom ((Φ.C k).Y.X.presheaf.stalkSpecializes_comp _ hs)`. Take `⟨f', hf⟩` from `f.exists_isMap ρ (x' := stalkPt (Φ.C k).Y (below x) ≫ (Φ.C k).π ≫ genι s.T.Z) rfl (by rw [← h1, Category.assoc])`. Establish `key : ∀ {k' : Type} [CommRing k'] (χ : (Φ.C k).Y.X.presheaf.stalk (below x) →+* k') {φ' : κ.c.F →+* k'} {x' : Sp k' ⟶ s.T.Z.X} {g : EigFrame s.T.Z φ' x'} {t'' : ∀ τ, Fin (S.Dw.mult τ) → k'ˣ}, f.Tri (χ.comp ρ) g t'' → f'.Tri χ g t''` using `fun χ _ _ g t'' h => ⟨by rw [h.1, ← h1, Category.assoc, ← Category.assoc (spMap χ), ← Spec.map_comp]; rfl, h.2.1, fun τ i => by simpa only [hf τ, GlobalTheory.GradedPieces.dual_comp] using h.2.2 τ i⟩`. Establish `a' : f'.Tri (algebraMap _ (Φ.C k).Y.X.functionField) (Φ.C k).f0 t` using `key _ (by rw [h3']; exact h2)`. Establish `b' : f'.Tri ev gf t'` using `key ev (by rw [h2']; exact h3)`.

Take `rfl` from `b'.1`. Take `⟨u, hut, hco⟩` from `compare (Φ.C k) ((Φ.C k).gr_spec (below x)).choose_spec.choose_spec.choose_spec.1 a'`. Establish `hgr : ∀ τ i, grNorm s.T.Z.t (spMap ev ≫ stalkPt (Φ.C k).Y (below x) ≫ (Φ.C k).π ≫ genι s.T.Z) (latDR s.T.Z.t (spMap ev ≫ stalkPt (Φ.C k).Y (below x) ≫ (Φ.C k).π ≫ genι s.T.Z)) (fun i => spMap (dualMap ev) ≫ ((Φ.C k).gr_spec (below x)).choose_spec.choose.v τ i) i = (‖(t' τ i : K)‖ …`. Introduce `τ i`. Establish `e1` using `Guard.grNorm_tri (u := fun i => spMap (dualMap ev) ≫ f'.v τ i) (u' := gf.v τ) (Λ := latDR s.T.Z.t (spMap ev ≫ stalkPt (Φ.C k).Y (below x) ≫ (Φ.C k).π ≫ genι s.T.Z)) (fun m => FactorDepth.isTanAtG_map _ ev (f'.tan τ m)) (d := fun i => (t' τ i : K)) (fun i => Units.ne_zero _) (b'.2 …`.

Establish `e2` using `Guard.grNorm_tri (u := fun i => spMap (dualMap ev) ≫ ((Φ.C k).gr_spec (below x)).choose_spec.choose.v τ i) (u' := fun i => spMap (dualMap ev) ≫ f'.v τ i) (Λ := latDR s.T.Z.t (spMap ev ≫ stalkPt (Φ.C k).Y (below x) ≫ (Φ.C k).π ≫ genι s.T.Z)) (fun m => FactorDepth.isTanAtG_map _ ev …`. Take `⟨cf, c1, c2, c3⟩` from `hco τ i`. Conclude with `⟨fun m => ev (cf m), by dsimp only; rw [c1], fun m hm => by dsimp only; rw [c2 m hm, map_zero], GradedPieces.comb_map ev rfl c3⟩) i`. Rewrite `e1` using `[hg τ i, e2, ← mul_assoc]`. Conclude with `eq_inv_of_mul_eq_one_right e1.symm`.

Establish `hsum : ∀ {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C] (xx : Sp C ⟶ s.T.Z.X) (U : ∀ τ : D.host.E →+* ℂ, Fin (S.Dw.mult τ) → (Sp (DualNumber C) ⟶ s.T.Z.t.G.left)), (drSym la).sum (fun a m => (m : ℝ) * lnStep s.T.Z.t xx U p (a.1 p) a.2.2) = ∑ z : Letter S.Dw, (expo S …`. Introduce `C _ _ xx U`. Simplify using `only [expo_drSym]`. Rewrite using `[drSym, ← Finsupp.sum_finset_sum_index (fun _ => by simp) (fun _ _ _ => by push_cast; ring)]`. Use `Finset.sum_congr rfl fun z _ => ?_` and prove the remaining obligations.

Rewrite using `[Finsupp.sum_single_index (by simp)]`. Simplify using `[lnStep, z.2.isLt, lat]`. Unfold `drAt`. Rewrite using `[hsum]`. Simplify using `only [hgr]`.

Establish `hpos : ∀ z : Letter S.Dw, 0 < ‖(t' z.1 z.2 : K)‖ * ‖ev (u z.1 z.2)‖` using `fun z => mul_pos (norm_pos_iff.2 (Units.ne_zero _)) (norm_pos_iff.2 ((u z.1 z.2).isUnit.map ev).ne_zero)`. Establish `hexp : Real.exp (∑ z : Letter S.Dw, (expo S.Dw (drSym la) z : ℝ) * Real.log (‖(t' z.1 z.2 : K)‖ * ‖ev (u z.1 z.2)‖)⁻¹) = ∏ z : Letter S.Dw, ((‖(t' z.1 z.2 : K)‖ * ‖ev (u z.1 z.2)‖)⁻¹) ^ expo S.Dw (drSym la) z`. Rewrite using `[Real.exp_sum]`. Use `Finset.prod_congr rfl fun z _ => ?_` and prove the remaining obligations. Rewrite using `[← Real.rpow_intCast, Real.rpow_def_of_pos (inv_pos.2 (hpos z)), mul_comm]`.

Establish `ht : (∏ z : Letter S.Dw, ((Φ.C k).gr_spec (below x)).choose_spec.choose_spec.choose z.1 z.2 ^ expo S.Dw (drSym la) z) = (∏ z : Letter S.Dw, t z.1 z.2 ^ expo S.Dw (drSym la) z) * Units.map (algebraMap _ (Φ.C k).Y.X.functionField).toMonoidHom (∏ z : Letter S.Dw, u z.1 z.2 ^ expo S. …`. Simplify using `only [hut, mul_zpow, Finset.prod_mul_distrib, map_prod, map_zpow]`. Establish `hv : F * ((∏ z : Letter S.Dw, ((Φ.C k).gr_spec (below x)).choose_spec.choose_spec.choose z.1 z.2 ^ expo S.Dw (drSym la) z : (Φ.C k).Y.Fnˣ) : (Φ.C k).Y.Fn) = algebraMap _ (Φ.C k).Y.X.functionField (ρ r * ((∏ z : Letter S.Dw, u z.1 z.2 ^ expo S.Dw (drSym la) z : ((Φ.C k).Y.X.preshe …`. Rewrite using `[ht, Units.val_mul, ← mul_assoc, ← h4, Units.coe_map, map_mul, ← RingHom.congr_fun h3' r]`. Both sides reduce to the same expression.

Establish `hev : ev ((∏ z : Letter S.Dw, u z.1 z.2 ^ expo S.Dw (drSym la) z : ((Φ.C k).Y.X.presheaf.stalk (below x))ˣ) : (Φ.C k).Y.X.presheaf.stalk (below x)) = ∏ z : Letter S.Dw, ev (u z.1 z.2) ^ expo S.Dw (drSym la) z`. Use `(congrArg Units.val (map_prod (Units.map ev.toMonoidHom) _ _)).trans ?_` and prove the remaining obligations. Simplify using `only [map_zpow, Units.coe_prod, Units.val_zpow_eq_zpow_val]`. Both sides reduce to the same expression. Establish `hval : GlobalTheory.TrueGeo.valAt x (algebraMap _ (Φ.C k).Y.X.functionField (ρ r * ((∏ z : Letter S.Dw, u z.1 z.2 ^ expo S.Dw (drSym la) z : ((Φ.C k).Y.X.presheaf.stalk (below x))ˣ) : (Φ.C k).Y.X.presheaf.stalk (below x)))) = ψ r * ∏ z : Letter S.Dw, ev (u z.1 z.2) ^ expo S.Dw (d …`.

Rewrite using `[Res.valAt_algebraMap]`. Conclude with `(map_mul ev _ _).trans (by rw [hev, ← RingHom.congr_fun h2' r]; rfl)`. Rewrite using `[hexp, hv, hval]`. Simplify using `only [norm_mul, norm_prod, norm_zpow, Units.coe_prod, Units.val_zpow_eq_zpow_val]`. Rewrite using `[mul_assoc, ← Finset.prod_mul_distrib]`.

Use `congr 1`. Use `Finset.prod_congr rfl fun z _ => ?_` and prove the remaining obligations. Establish `ha : ‖ev (u z.1 z.2)‖ ≠ 0` using `norm_ne_zero_iff.2 ((u z.1 z.2).isUnit.map ev).ne_zero`. Rewrite using `[mul_inv, mul_zpow, inv_zpow', inv_zpow', mul_left_comm, ← zpow_add₀ ha, add_neg_cancel, zpow_zero, mul_one]`.
-/
theorem drAt_eq_of_isCoord : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (Φ : s.Flag) (k : s.Comp) (la : AllWt.Weight S.Dw) (K : Type) [NontriviallyNormedField K] [IsUltrametricDist K] (p : ℕ) (x : Sp K ⟶ (Φ.C k).Y.X) (F : (Φ.C k).Y.Fn) (φ : κ.c.F →+* K) (xg : Sp K ⟶ s.T.Z.X) (gf : EigFrame s.T.Z φ xg) (a : K), (∀ τ i, grNorm s.T.Z.t xg (latDR s.T.Z.t xg) (gf.v τ) i = 1) → IsCoord (Φ.C k) x gf (expo S.Dw (drSym la)) F a → drAt Φ k la p x F = ‖a‖ := by
  intro D A N j S κ s Φ k la K _ _ p x F φ xg gf a hg hc
  obtain ⟨y, ψ, φ₁, f, t, t', r, hx, h2, h3, h4, rfl⟩ := hc
  have hs : below x ⤳ y := by
    have : below x ∈ Set.range ((Φ.C k).Y.X.fromSpecStalk y) := by
      rw [hx]; exact ⟨_, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  let ρ := ((Φ.C k).Y.X.presheaf.stalkSpecializes hs).hom
  let ev : (Φ.C k).Y.X.presheaf.stalk (below x) →+* K := (Scheme.stalkClosedPointTo x).hom
  have h1 : spMap ρ ≫ stalkPt (Φ.C k).Y y = stalkPt (Φ.C k).Y (below x) :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk hs
  have hxe : spMap ev ≫ stalkPt (Φ.C k).Y (below x) = x := Scheme.Spec_stalkClosedPointTo_fromSpecStalk x
  have h2' : ev.comp ρ = ψ := EigLoc.spMap_inj ((cancel_mono ((Φ.C k).Y.X.fromSpecStalk y)).1 (by
    refine Eq.trans ?_ (hxe.trans hx)
    rw [← h1, ← Category.assoc, ← Spec.map_comp]; rfl))
  have h3' : (algebraMap _ (Φ.C k).Y.X.functionField).comp ρ = algebraMap _ (Φ.C k).Y.X.functionField :=
    congrArg CommRingCat.Hom.hom ((Φ.C k).Y.X.presheaf.stalkSpecializes_comp _ hs)
  obtain ⟨f', hf⟩ := f.exists_isMap ρ (x' := stalkPt (Φ.C k).Y (below x) ≫ (Φ.C k).π ≫ genι s.T.Z) rfl
    (by rw [← h1, Category.assoc])
  have key : ∀ {k' : Type} [CommRing k'] (χ : (Φ.C k).Y.X.presheaf.stalk (below x) →+* k') {φ' : κ.c.F →+* k'}
      {x' : Sp k' ⟶ s.T.Z.X} {g : EigFrame s.T.Z φ' x'} {t'' : ∀ τ, Fin (S.Dw.mult τ) → k'ˣ},
      f.Tri (χ.comp ρ) g t'' → f'.Tri χ g t'' :=
    fun χ _ _ g t'' h => ⟨by rw [h.1, ← h1, Category.assoc, ← Category.assoc (spMap χ), ← Spec.map_comp]; rfl, h.2.1,
      fun τ i => by simpa only [hf τ, GlobalTheory.GradedPieces.dual_comp] using h.2.2 τ i⟩
  have a' : f'.Tri (algebraMap _ (Φ.C k).Y.X.functionField) (Φ.C k).f0 t := key _ (by rw [h3']; exact h2)
  have b' : f'.Tri ev gf t' := key ev (by rw [h2']; exact h3)
  obtain rfl := b'.1
  obtain ⟨u, hut, hco⟩ := compare (Φ.C k) ((Φ.C k).gr_spec (below x)).choose_spec.choose_spec.choose_spec.1 a'
  have hgr : ∀ τ i, grNorm s.T.Z.t (spMap ev ≫ stalkPt (Φ.C k).Y (below x) ≫ (Φ.C k).π ≫ genι s.T.Z)
      (latDR s.T.Z.t (spMap ev ≫ stalkPt (Φ.C k).Y (below x) ≫ (Φ.C k).π ≫ genι s.T.Z))
      (fun i => spMap (dualMap ev) ≫ ((Φ.C k).gr_spec (below x)).choose_spec.choose.v τ i) i =
        (‖(t' τ i : K)‖ * ‖ev (u τ i)‖)⁻¹ := by
    intro τ i
    have e1 := Guard.grNorm_tri (u := fun i => spMap (dualMap ev) ≫ f'.v τ i) (u' := gf.v τ)
      (Λ := latDR s.T.Z.t (spMap ev ≫ stalkPt (Φ.C k).Y (below x) ≫ (Φ.C k).π ≫ genι s.T.Z))
      (fun m => FactorDepth.isTanAtG_map _ ev (f'.tan τ m)) (d := fun i => (t' τ i : K)) (fun i => Units.ne_zero _)
      (b'.2.2 τ) i
    have e2 := Guard.grNorm_tri (u := fun i => spMap (dualMap ev) ≫ ((Φ.C k).gr_spec (below x)).choose_spec.choose.v τ i)
      (u' := fun i => spMap (dualMap ev) ≫ f'.v τ i)
      (Λ := latDR s.T.Z.t (spMap ev ≫ stalkPt (Φ.C k).Y (below x) ≫ (Φ.C k).π ≫ genι s.T.Z))
      (fun m => FactorDepth.isTanAtG_map _ ev (((Φ.C k).gr_spec (below x)).choose_spec.choose.tan τ m))
      (d := fun i => ev (u τ i)) (fun i => ((u τ i).isUnit.map ev).ne_zero)
      (fun i => by
        obtain ⟨cf, c1, c2, c3⟩ := hco τ i
        exact ⟨fun m => ev (cf m), by dsimp only; rw [c1], fun m hm => by dsimp only; rw [c2 m hm, map_zero], GradedPieces.comb_map ev rfl c3⟩) i
    rw [hg τ i, e2, ← mul_assoc] at e1
    exact eq_inv_of_mul_eq_one_right e1.symm
  have hsum : ∀ {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C] (xx : Sp C ⟶ s.T.Z.X)
      (U : ∀ τ : D.host.E →+* ℂ, Fin (S.Dw.mult τ) → (Sp (DualNumber C) ⟶ s.T.Z.t.G.left)),
      (drSym la).sum (fun a m => (m : ℝ) * lnStep s.T.Z.t xx U p (a.1 p) a.2.2) =
        ∑ z : Letter S.Dw, (expo S.Dw (drSym la) z : ℝ) * Real.log (grNorm s.T.Z.t xx (latDR s.T.Z.t xx) (U z.1) z.2) := by
    intro C _ _ xx U
    simp only [expo_drSym]
    rw [drSym, ← Finsupp.sum_finset_sum_index (fun _ => by simp) (fun _ _ _ => by push_cast; ring)]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [Finsupp.sum_single_index (by simp)]
    simp [lnStep, z.2.isLt, lat]
  unfold drAt
  rw [hsum]
  simp only [hgr]
  have hpos : ∀ z : Letter S.Dw, 0 < ‖(t' z.1 z.2 : K)‖ * ‖ev (u z.1 z.2)‖ := fun z =>
    mul_pos (norm_pos_iff.2 (Units.ne_zero _)) (norm_pos_iff.2 ((u z.1 z.2).isUnit.map ev).ne_zero)
  have hexp : Real.exp (∑ z : Letter S.Dw, (expo S.Dw (drSym la) z : ℝ) *
      Real.log (‖(t' z.1 z.2 : K)‖ * ‖ev (u z.1 z.2)‖)⁻¹) =
        ∏ z : Letter S.Dw, ((‖(t' z.1 z.2 : K)‖ * ‖ev (u z.1 z.2)‖)⁻¹) ^ expo S.Dw (drSym la) z := by
    rw [Real.exp_sum]
    refine Finset.prod_congr rfl fun z _ => ?_
    rw [← Real.rpow_intCast, Real.rpow_def_of_pos (inv_pos.2 (hpos z)), mul_comm]
  have ht : (∏ z : Letter S.Dw, ((Φ.C k).gr_spec (below x)).choose_spec.choose_spec.choose z.1 z.2 ^ expo S.Dw (drSym la) z) =
      (∏ z : Letter S.Dw, t z.1 z.2 ^ expo S.Dw (drSym la) z) *
        Units.map (algebraMap _ (Φ.C k).Y.X.functionField).toMonoidHom
          (∏ z : Letter S.Dw, u z.1 z.2 ^ expo S.Dw (drSym la) z) := by
    simp only [hut, mul_zpow, Finset.prod_mul_distrib, map_prod, map_zpow]
  have hv : F * ((∏ z : Letter S.Dw, ((Φ.C k).gr_spec (below x)).choose_spec.choose_spec.choose z.1 z.2 ^
      expo S.Dw (drSym la) z : (Φ.C k).Y.Fnˣ) : (Φ.C k).Y.Fn) =
        algebraMap _ (Φ.C k).Y.X.functionField (ρ r * ((∏ z : Letter S.Dw, u z.1 z.2 ^ expo S.Dw (drSym la) z :
          ((Φ.C k).Y.X.presheaf.stalk (below x))ˣ) : (Φ.C k).Y.X.presheaf.stalk (below x))) := by
    rw [ht, Units.val_mul, ← mul_assoc, ← h4, Units.coe_map, map_mul, ← RingHom.congr_fun h3' r]
    rfl
  have hev : ev ((∏ z : Letter S.Dw, u z.1 z.2 ^ expo S.Dw (drSym la) z :
      ((Φ.C k).Y.X.presheaf.stalk (below x))ˣ) : (Φ.C k).Y.X.presheaf.stalk (below x)) =
        ∏ z : Letter S.Dw, ev (u z.1 z.2) ^ expo S.Dw (drSym la) z := by
    refine (congrArg Units.val (map_prod (Units.map ev.toMonoidHom) _ _)).trans ?_
    simp only [map_zpow, Units.coe_prod, Units.val_zpow_eq_zpow_val]
    rfl
  have hval : GlobalTheory.TrueGeo.valAt x (algebraMap _ (Φ.C k).Y.X.functionField (ρ r * ((∏ z : Letter S.Dw,
      u z.1 z.2 ^ expo S.Dw (drSym la) z : ((Φ.C k).Y.X.presheaf.stalk (below x))ˣ) :
        (Φ.C k).Y.X.presheaf.stalk (below x)))) = ψ r * ∏ z : Letter S.Dw, ev (u z.1 z.2) ^ expo S.Dw (drSym la) z := by
    rw [Res.valAt_algebraMap]
    exact (map_mul ev _ _).trans (by rw [hev, ← RingHom.congr_fun h2' r]; rfl)
  rw [hexp, hv, hval]
  simp only [norm_mul, norm_prod, norm_zpow, Units.coe_prod, Units.val_zpow_eq_zpow_val]
  rw [mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun z _ => ?_
  have ha : ‖ev (u z.1 z.2)‖ ≠ 0 := norm_ne_zero_iff.2 ((u z.1 z.2).isUnit.map ev).ne_zero
  rw [mul_inv, mul_zpow, inv_zpow', inv_zpow', mul_left_comm, ← zpow_add₀ ha, add_neg_cancel, zpow_zero, mul_one]

end GlobalTheory.CovHt.Link.DrAtFrame
