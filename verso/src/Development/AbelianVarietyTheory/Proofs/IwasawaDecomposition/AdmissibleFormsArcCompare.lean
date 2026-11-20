import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoefSetNonemptyOfNonneg
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TangentVectorsThetaSectionArcWitnessBaseChange
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsPullCubicalId
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LocM.FJ
open GlobalTheory.Toroidal
open GlobalTheory.ArcQ (Wit LieImg)

noncomputable section

namespace GlobalTheory.ArcSubst

open GlobalTheory.ArcBaseChange GlobalTheory.ObjRebase

set_option maxHeartbeats 1600000 in

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c O _ β Y A _ _ _ b a₀ γ γ' h h' χ g W W' hD bc w₁ hgC hgX hU he hφ hw₁ T ν v v' hv hv'`. Introduce `n ρ' κ' vn' hρ₁ hρ₂ hκ₁ hκ₂ hb hf x`. Take `⟨wL, -, -, -, lev⟩` from `(isPullUnif_iff_stalks _ _ _ _ _ _ _ hD _ _ _ _ bc _ _).1 hU`. Take `⟨hm, hh, ⟨-, ht⟩, -⟩` from `lev n`. Take `⟨ho, Ht⟩` from `ht (W'.e x)`.

Rewrite `ho`, `Ht` using `[he]`. Establish `Hν` using `pmaps_pullIdIso _ _ _ (ν.isGen x)`. Establish `hs : W'.φ ≫ 𝟙 _ = (hD.e.hom.left ≫ pullback.fst W.P.D.toPre.P.A.hom (Out.specOf g)) ≫ W.φ` using `(Category.comp_id _).trans hφ`. Establish `S : Sq W.w hD.w (pullIdIso a₀.D₀.P.L) W'.w`. Introduce `Z r z j i i' k hj hi hi' hk`.

Establish `hj' : W'.φ (r z) ∈ a₀.D₀.P.L.U j` using `(congrArg (fun f => f (r z) ∈ a₀.D₀.P.L.U j) hφ).mpr hj`. Establish `pg` using `(isGen_iff W'.w).1 W'.spec.2.1 Z r z j i' k k hj' hi' hk hk`. Rewrite using `[← T Z r z j i k hj hi hk, ← gw_heq hφ hw₁ r z j k, pg, gm_self W'.P.D.toPre.P.isLB r z hk, inv_one, mul_one, gw_pullIdIso a₀.D₀.P.L (r ≫ W'.φ) z j i' hj' hi']`. Use `isLocalRing_trunc A n` as an intermediate fact. Use `ConstTan.isLocalRing_dual (PowerSeries A ⧸ Ideal.span {(PowerSeries.X : PowerSeries A)} ^ (n + 1))` as an intermediate fact.

Set `I : Ideal (PowerSeries A)` to `Ideal.span {PowerSeries.X}`. Establish `hI : I ^ (n + 1) ≤ (I ^ (n + 1)).comap g` using `Ideal.map_le_iff_le_comap.1 (by`. Rewrite using `[Ideal.map_pow, Ideal.map_span, Set.image_singleton]`. Conclude with `Ideal.pow_right_mono ((Ideal.span_singleton_le_iff_mem _).2 hgX) _)`. Set `gb : PowerSeries A ⧸ I ^ (n + 1) →+* PowerSeries A ⧸ I ^ (n + 1)` to `Ideal.quotientMap _ g hI`.

Set `ρ : DualNumber (PowerSeries A) →+* DualNumber (PowerSeries A ⧸ I ^ (n + 1))` to `dualMap (Ideal.Quotient.mk _)`. Set `κ : DualNumber A →+* DualNumber (PowerSeries A ⧸ I ^ (n + 1))` to `dualMap ((Ideal.Quotient.mk _).comp (PowerSeries.C (R := A)))`. Set `s : Sp (DualNumber (PowerSeries A ⧸ I ^ (n + 1))) ⟶ Sp (PowerSeries A ⧸ I ^ (n + 1))` to `spMap (algebraMap _ _)`. Establish `hs₀ : s ≫ Out.thick (PowerSeries A) I n = spMap ρ ≫ (epsR (PowerSeries A)).hom` using `((ArcBaseChange.spMap_comp' _ _).trans (congrArg spMap (RingHom.ext fun r => (dualMap_inl (Ideal.Quotient.mk (I ^ (n + 1))) r).symm : _ = ρ.comp (algebraMap _ _)))).trans (ArcBaseChange.spMap_comp' _ _).symm`. Set `vn : Sp (DualNumber (PowerSeries A ⧸ I ^ (n + 1))) ⟶ (Out.thickObj (PowerSeries A) I n W.t.G).left` to `pullback.lift (spMap ρ ≫ v.left) s (by rw [Category.assoc, Over.w v, hs₀])`.

Establish `hx : vn ≫ (Out.fstG I n W.t.G).left = spMap ρ ≫ v.left` using `pullback.lift_fst _ _ _`. Establish `G` using `hv n ρ κ vn (dualMap_inl _) (dualMap_eps' _) (dualMap_inl _) (dualMap_eps' _) (pullback.lift_snd _ _ _) hx x`. Set `q` to `spMap (dualMap gb)`. Establish `hρ : spMap ρ' ≫ spMap (dualMap g) = q ≫ spMap ρ`. Rewrite using `[ArcBaseChange.spMap_comp', ArcBaseChange.spMap_comp']`.

Use `congrArg spMap (dual_hom_ext (fun r => ?_) ?_)` and prove the remaining obligations. Simplify using `only [RingHom.comp_apply, ρ, dualMap_inl, hρ₁]`. Both sides reduce to the same expression. Simplify using `only [RingHom.comp_apply, ρ, dualMap_eps', hρ₂]`. Establish `hκ : spMap κ' ≫ 𝟙 _ = q ≫ spMap κ`.

Rewrite using `[Category.comp_id, ArcBaseChange.spMap_comp']`. Use `congrArg spMap (dual_hom_ext (fun r => ?_) ?_)` and prove the remaining obligations. Simplify using `only [RingHom.comp_apply, κ, dualMap_inl, hκ₁]`. Conclude with `congrArg (fun y => TrivSqZeroExt.inl (Ideal.Quotient.mk (I ^ (n + 1)) y)) (RingHom.congr_fun hgC r).symm`. Simplify using `only [RingHom.comp_apply, κ, dualMap_eps', hκ₂]`.

Establish `hvn : vn' ≫ hm = q ≫ vn`. Use `thick_mono (PowerSeries A) I n` as an intermediate fact. Establish `: Mono (Out.fstG I n W.t.G).left` using `inferInstanceAs (Mono (pullback.fst _ _))`. Rewrite using `[← cancel_mono (Out.fstG I n W.t.G).left, Category.assoc, hh, ← Category.assoc, hf, Category.assoc]`. Use `erw [hv']`.

Rewrite using `[← Category.assoc, hρ, Category.assoc, Category.assoc, hx]`. Use `genRelR_baseChange hs S W.spec.2.1 W.P.D.toPre.P.isLB a₀.D₀.P.isLB ((W.P.U.gt n).t_gen _) (ν.isGen _) ho Ht Hν hvn hκ (fun k => ?_) G` and prove the remaining obligations. Establish `e` using `comp_eq_of_squares hs (ho k) (g := Out.DegPre.gtφT a₀.D₀ (epsR A) ν.b x k) (g' := Out.DegPre.gtφT a₀.D₀ (epsR A) ν.b x k) (d := 𝟙 _) (by rw [Category.comp_id, Category.id_comp]) hvn hκ (G.1 k)`. Simplify `e` using `only [Category.comp_id]`.
-/
theorem lieImg_subst : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] (b : O →+* A) (a₀ : ArcIn Dw l β A b) (γ γ' : levelForms H l.M' a₀.D₀.X) (h : γ ∈ admitted H l.M' a₀.D₀.X) (h' : γ' ∈ admitted H l.M' a₀.D₀.X) (χ : Sp (PowerSeries A) ⟶ Y.X) (g : PowerSeries A →+* PowerSeries A) (W : Wit Y (withForm a₀ γ h) χ) (W' : Wit Y (withForm a₀ γ' h') (spMap g ≫ χ)) (hD : Out.IsPullDeg g W.P.D.toPre W'.P.D.toPre) (bc : W'.t.G ≅ (Over.pullback (Out.specOf g)).obj W.t.G) (w₁ : LB.Iso W'.P.D.toPre.P.L (a₀.D₀.P.L.pull ((hD.e.hom.left ≫ pullback.fst W.P.D.toPre.P.A.hom (Out.specOf g)) ≫ W.φ))), g.comp (PowerSeries.C (R := A)) = PowerSeries.C → g PowerSeries.X ∈ Ideal.span {PowerSeries.X} → Out.IsPullUnif g hD bc W.P.U W'.P.U → (∀ y, hD.xe (W'.e y) = W.e y) → W'.φ = (hD.e.hom.left ≫ pullback.fst W.P.D.toPre.P.A.hom (Out.specOf g)) ≫ W.φ → HEq W'.w w₁ → Tri W.w hD.w w₁ → ∀ (ν : Out.GtPt a₀.D₀ (epsR A)) (v : epsR (PowerSeries A) ⟶ W.t.G) (v' : epsR (PowerSeries A) ⟶ W'.t.G), LieImg W ν v → v'.left ≫ bc.hom.left ≫ pullback.fst W.t.G.hom (Out.specOf g) = spMap (dualMap g) ≫ v.left → LieImg W' ν v' := by
  intro E _ _ _ H Dw l Xo c O _ β Y A _ _ _ b a₀ γ γ' h h' χ g W W' hD bc w₁ hgC hgX hU he hφ hw₁ T ν v v' hv hv'
  intro n ρ' κ' vn' hρ₁ hρ₂ hκ₁ hκ₂ hb hf x
  obtain ⟨wL, -, -, -, lev⟩ := (isPullUnif_iff_stalks _ _ _ _ _ _ _ hD _ _ _ _ bc _ _).1 hU
  obtain ⟨hm, hh, ⟨-, ht⟩, -⟩ := lev n
  obtain ⟨ho, Ht⟩ := ht (W'.e x)
  rw [he] at ho Ht
  have Hν := pmaps_pullIdIso _ _ _ (ν.isGen x)
  have hs : W'.φ ≫ 𝟙 _ = (hD.e.hom.left ≫ pullback.fst W.P.D.toPre.P.A.hom (Out.specOf g)) ≫ W.φ :=
    (Category.comp_id _).trans hφ
  have S : Sq W.w hD.w (pullIdIso a₀.D₀.P.L) W'.w := by
    intro Z r z j i i' k hj hi hi' hk
    have hj' : W'.φ (r z) ∈ a₀.D₀.P.L.U j := (congrArg (fun f => f (r z) ∈ a₀.D₀.P.L.U j) hφ).mpr hj
    have pg := (isGen_iff W'.w).1 W'.spec.2.1 Z r z j i' k k hj' hi' hk hk
    rw [← T Z r z j i k hj hi hk, ← gw_heq hφ hw₁ r z j k, pg, gm_self W'.P.D.toPre.P.isLB r z hk, inv_one, mul_one,
      gw_pullIdIso a₀.D₀.P.L (r ≫ W'.φ) z j i' hj' hi']

  have := isLocalRing_trunc A n
  have := ConstTan.isLocalRing_dual (PowerSeries A ⧸ Ideal.span {(PowerSeries.X : PowerSeries A)} ^ (n + 1))
  let I : Ideal (PowerSeries A) := Ideal.span {PowerSeries.X}
  have hI : I ^ (n + 1) ≤ (I ^ (n + 1)).comap g := Ideal.map_le_iff_le_comap.1 (by
    rw [Ideal.map_pow, Ideal.map_span, Set.image_singleton]
    exact Ideal.pow_right_mono ((Ideal.span_singleton_le_iff_mem _).2 hgX) _)
  let gb : PowerSeries A ⧸ I ^ (n + 1) →+* PowerSeries A ⧸ I ^ (n + 1) := Ideal.quotientMap _ g hI
  let ρ : DualNumber (PowerSeries A) →+* DualNumber (PowerSeries A ⧸ I ^ (n + 1)) := dualMap (Ideal.Quotient.mk _)
  let κ : DualNumber A →+* DualNumber (PowerSeries A ⧸ I ^ (n + 1)) :=
    dualMap ((Ideal.Quotient.mk _).comp (PowerSeries.C (R := A)))
  let s : Sp (DualNumber (PowerSeries A ⧸ I ^ (n + 1))) ⟶ Sp (PowerSeries A ⧸ I ^ (n + 1)) := spMap (algebraMap _ _)
  have hs₀ : s ≫ Out.thick (PowerSeries A) I n = spMap ρ ≫ (epsR (PowerSeries A)).hom :=
    ((ArcBaseChange.spMap_comp' _ _).trans (congrArg spMap (RingHom.ext fun r =>
      (dualMap_inl (Ideal.Quotient.mk (I ^ (n + 1))) r).symm : _ = ρ.comp (algebraMap _ _)))).trans
      (ArcBaseChange.spMap_comp' _ _).symm
  let vn : Sp (DualNumber (PowerSeries A ⧸ I ^ (n + 1))) ⟶ (Out.thickObj (PowerSeries A) I n W.t.G).left :=
    pullback.lift (spMap ρ ≫ v.left) s (by rw [Category.assoc, Over.w v, hs₀])
  have hx : vn ≫ (Out.fstG I n W.t.G).left = spMap ρ ≫ v.left := pullback.lift_fst _ _ _
  have G := hv n ρ κ vn (dualMap_inl _) (dualMap_eps' _) (dualMap_inl _) (dualMap_eps' _)
    (pullback.lift_snd _ _ _) hx x
  let q := spMap (dualMap gb)
  have hρ : spMap ρ' ≫ spMap (dualMap g) = q ≫ spMap ρ := by
    rw [ArcBaseChange.spMap_comp', ArcBaseChange.spMap_comp']
    refine congrArg spMap (dual_hom_ext (fun r => ?_) ?_)
    · simp only [RingHom.comp_apply, ρ, dualMap_inl, hρ₁]
      rfl
    · simp only [RingHom.comp_apply, ρ, dualMap_eps', hρ₂]
  have hκ : spMap κ' ≫ 𝟙 _ = q ≫ spMap κ := by
    rw [Category.comp_id, ArcBaseChange.spMap_comp']
    refine congrArg spMap (dual_hom_ext (fun r => ?_) ?_)
    · simp only [RingHom.comp_apply, κ, dualMap_inl, hκ₁]
      exact congrArg (fun y => TrivSqZeroExt.inl (Ideal.Quotient.mk (I ^ (n + 1)) y)) (RingHom.congr_fun hgC r).symm
    · simp only [RingHom.comp_apply, κ, dualMap_eps', hκ₂]
  have hvn : vn' ≫ hm = q ≫ vn := by
    have := thick_mono (PowerSeries A) I n
    have : Mono (Out.fstG I n W.t.G).left := inferInstanceAs (Mono (pullback.fst _ _))
    rw [← cancel_mono (Out.fstG I n W.t.G).left, Category.assoc, hh, ← Category.assoc, hf, Category.assoc]
    erw [hv']
    rw [← Category.assoc, hρ, Category.assoc, Category.assoc, hx]
  refine genRelR_baseChange hs S W.spec.2.1 W.P.D.toPre.P.isLB a₀.D₀.P.isLB ((W.P.U.gt n).t_gen _) (ν.isGen _) ho Ht Hν
    hvn hκ (fun k => ?_) G
  have e := comp_eq_of_squares hs (ho k) (g := Out.DegPre.gtφT a₀.D₀ (epsR A) ν.b x k) (g' := Out.DegPre.gtφT a₀.D₀ (epsR A) ν.b x k) (d := 𝟙 _)
    (by rw [Category.comp_id, Category.id_comp]) hvn hκ (G.1 k)
  simpa only [Category.comp_id] using e

end GlobalTheory.ArcSubst
