import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EvenDefect
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefinesPolarisedDataRescaleCoboundary
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsScalarFormTraceForm
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GtActIffEqGtSmul
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyCubicalPull
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.RescaleForm

open GlobalTheory.TauTwist (unitAt unitAt_injective IsScalarForm)

/- English proof (translation)
Use `letI : Module O (GlobalTheory.PolDeg.rescale D g).X := inst`. Establish `hG` using `GlobalTheory.globalFns_holds`. Set `y : (TK R).left` to `IsLocalRing.closedPoint (FractionRing R)`. Take `⟨I, hJ⟩` from `GlobalTheory.DegPull.exists_good' D.P.isLB y`. Establish `vt : ∀ a b, val ((GlobalTheory.PolDeg.rescale D g).tau a b) (𝟙 _) y I = unitAt (𝟙 (TK R).left) y (g (a + b) * (g a)⁻¹ * (g b)⁻¹) * val (D.tau a b) (𝟙 _) y I` using `fun a b => by`.

Rewrite using `[map_mul, map_mul, map_inv, map_inv]`. Conclude with `GlobalTheory.PolDeg.rescale_tau_val D g a b hJ`. Establish `sy : ∀ a b, g (a + b) * (g a)⁻¹ * (g b)⁻¹ = g (b + a) * (g b)⁻¹ * (g a)⁻¹` using `fun a b => by`. Rewrite using `[add_comm, mul_right_comm]`. Establish `al : ∀ a a' b, g (a + a' + b) * (g (a + a'))⁻¹ * (g b)⁻¹ = (g (a + b) * (g a)⁻¹ * (g b)⁻¹) * (g (a' + b) * (g a')⁻¹ * (g b)⁻¹)` using `fun a a' b => by`.

Establish `e` using `(val_mul hJ _ _ _).symm.trans ((val_corr hJ (hB a a' b) (𝟙 _)).trans (val_mul hJ _ _ _))`. Establish `e'` using `(val_mul hJ _ _ _).symm.trans ((val_corr hJ (hB' a a' b) (𝟙 _)).trans (val_mul hJ _ _ _))`. Establish `e''` using `(congrArg₂ (· * ·) (vt (a + a') b).symm rfl).trans (e'.trans (congrArg₂ (· * ·) (vt a b) (vt a' b)))`. Rewrite `e''` using `[_root_.mul_mul_mul_comm, ← e, _root_.mul_assoc, ← map_mul]`. Conclude with `unitAt_injective y (mul_right_cancel e'')`.

Take `⟨onB', cl', tb'⟩` from `oa'`. Take `rfl : onB' = oa.onB` from `ho`. Use `⟨⟨fun a b b' => ?_, sy, fun x a b => ?_⟩, fun a => ?_⟩` and prove the remaining obligations. Rewrite using `[sy, sy a b, sy a b']`. Conclude with `al b b' a`.

Establish `hr` using `GlobalTheory.TorusExt.exists_isRos hG oa (star x)`. Rewrite `hr` using `[star_star]`. Take `⟨u, hu, u₀⟩` from `hr`. Establish `e` using `(val_mul hJ _ _ _).symm.trans (val_corr hJ (oa.tau_bal x u hu u₀ a b) (𝟙 _))`. Establish `e'` using `(val_mul hJ _ _ _).symm.trans (val_corr hJ (tb' x u hu u₀ a b) (𝟙 _))`.

Establish `e''` using `(congrArg₂ (· * ·) (vt (x • a) b).symm rfl).trans (e'.trans (vt a (star x • b)))`. Rewrite `e''` using `[← e, _root_.mul_assoc]`. Conclude with `unitAt_injective y (mul_right_cancel e'')`. Take `⟨u, hu, u₀, h⟩` from `hW`. Take `⟨u', hu', u₀', h'⟩` from `hW'`.

Establish `k` using `gen_unique' D.P.isLB (fun _ _ _ => rfl) D.P.A.hom (eSec D.P.A) (Over.w η[D.P.A]) (hG _ _ D.P.isAb).2 hu hu' (fun z J hz => by`. Establish `a` using `val_corr hz u₀ (𝟙 _)`. Establish `b` using `val_corr hz u₀' (𝟙 _)`. Rewrite `a` using `[val_pull hz, val_one, Category.id_comp]`. Establish `b'` using `((val_pull hz _ _ _).symm.trans b).trans (val_one _)`.

Rewrite `b'` using `[Category.id_comp]`. Conclude with `a.trans b'.symm) _ (𝟙 _ ≫ D.xK a) y I hJ`. Establish `e` using `(val_mul hJ _ _ _).symm.trans ((val_corr hJ (h a) (𝟙 _)).trans (val_mul hJ _ _ _))`. Establish `e'` using `(val_mul hJ _ _ _).symm.trans ((val_corr hJ (h' a) (𝟙 _)).trans (val_mul hJ _ _ _))`. Rewrite `e` using `[val_pull hJ]`.

Establish `e''` using `(congrArg₂ (· * ·) (vt a (w0 • a)).symm (k.trans (val_pull hJ _ _ _).symm)).trans (e'.trans (congrArg₂ (· * ·) (GlobalTheory.UU.val_scaleGen (unitOn (g a)) (D.psi a) (𝟙 _) hJ) rfl))`. Rewrite `e''` using `[_root_.mul_assoc, e]`. Conclude with `(unitAt_injective y (mul_right_cancel (e''.trans (_root_.mul_assoc _ _ _)))).symm`.
-/
theorem scalar_of_laws {R : Type} [CommRing R] [IsDomain R] {O : Type} [CommRing O] [StarRing O] (D : DegPre R)
    [inst : Module O D.X] (oa : D.OAct O) (w0 : O) (g : D.X → (FractionRing R)ˣ) (hB : D.TauBimult) (hW : TraceFormTwistIso D oa w0)
    (hB' : (GlobalTheory.PolDeg.rescale D g).TauBimult)
    (oa' : @DegPre.OAct R _ _ O _ _ (GlobalTheory.PolDeg.rescale D g) inst)
    (ho : @DegPre.OAct.onB R _ _ O _ _ (GlobalTheory.PolDeg.rescale D g) inst oa' = oa.onB)
    (hW' : @TraceFormTwistIso R _ _ O _ _ (GlobalTheory.PolDeg.rescale D g) inst oa' w0) :
    IsScalarForm O (fun a b => g (a + b) * (g a)⁻¹ * (g b)⁻¹) ∧
      ∀ y, g y = g (y + w0 • y) * (g y)⁻¹ * (g (w0 • y))⁻¹ := by
  letI : Module O (GlobalTheory.PolDeg.rescale D g).X := inst
  have hG := GlobalTheory.globalFns_holds
  let y : (TK R).left := IsLocalRing.closedPoint (FractionRing R)
  obtain ⟨I, hJ⟩ := GlobalTheory.DegPull.exists_good' D.P.isLB y
  have vt : ∀ a b, val ((GlobalTheory.PolDeg.rescale D g).tau a b) (𝟙 _) y I =
      unitAt (𝟙 (TK R).left) y (g (a + b) * (g a)⁻¹ * (g b)⁻¹) * val (D.tau a b) (𝟙 _) y I := fun a b => by
    rw [map_mul, map_mul, map_inv, map_inv]
    exact GlobalTheory.PolDeg.rescale_tau_val D g a b hJ
  have sy : ∀ a b, g (a + b) * (g a)⁻¹ * (g b)⁻¹ = g (b + a) * (g b)⁻¹ * (g a)⁻¹ := fun a b => by
    rw [add_comm, mul_right_comm]
  have al : ∀ a a' b, g (a + a' + b) * (g (a + a'))⁻¹ * (g b)⁻¹ =
      (g (a + b) * (g a)⁻¹ * (g b)⁻¹) * (g (a' + b) * (g a')⁻¹ * (g b)⁻¹) := fun a a' b => by
    have e := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (hB a a' b) (𝟙 _)).trans (val_mul hJ _ _ _))
    have e' := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (hB' a a' b) (𝟙 _)).trans (val_mul hJ _ _ _))
    have e'' := (congrArg₂ (· * ·) (vt (a + a') b).symm rfl).trans (e'.trans (congrArg₂ (· * ·) (vt a b) (vt a' b)))
    rw [_root_.mul_mul_mul_comm, ← e, _root_.mul_assoc, ← map_mul] at e''
    exact unitAt_injective y (mul_right_cancel e'')
  obtain ⟨onB', cl', tb'⟩ := oa'
  obtain rfl : onB' = oa.onB := ho
  refine ⟨⟨fun a b b' => ?_, sy, fun x a b => ?_⟩, fun a => ?_⟩
  · rw [sy, sy a b, sy a b']
    exact al b b' a
  · have hr := GlobalTheory.TorusExt.exists_isRos hG oa (star x)
    rw [star_star] at hr
    obtain ⟨u, hu, u₀⟩ := hr
    have e := (val_mul hJ _ _ _).symm.trans (val_corr hJ (oa.tau_bal x u hu u₀ a b) (𝟙 _))
    have e' := (val_mul hJ _ _ _).symm.trans (val_corr hJ (tb' x u hu u₀ a b) (𝟙 _))
    have e'' := (congrArg₂ (· * ·) (vt (x • a) b).symm rfl).trans (e'.trans (vt a (star x • b)))
    rw [← e, _root_.mul_assoc] at e''
    exact unitAt_injective y (mul_right_cancel e'')
  · obtain ⟨u, hu, u₀, h⟩ := hW
    obtain ⟨u', hu', u₀', h'⟩ := hW'
    have k := gen_unique' D.P.isLB (fun _ _ _ => rfl) D.P.A.hom (eSec D.P.A) (Over.w η[D.P.A]) (hG _ _ D.P.isAb).2 hu hu'
      (fun z J hz => by
        have a := val_corr hz u₀ (𝟙 _)
        have b := val_corr hz u₀' (𝟙 _)
        rw [val_pull hz, val_one, Category.id_comp] at a
        have b' := ((val_pull hz _ _ _).symm.trans b).trans (val_one _)
        rw [Category.id_comp] at b'
        exact a.trans b'.symm) _ (𝟙 _ ≫ D.xK a) y I hJ
    have e := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (h a) (𝟙 _)).trans (val_mul hJ _ _ _))
    have e' := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (h' a) (𝟙 _)).trans (val_mul hJ _ _ _))
    rw [val_pull hJ] at e
    have e'' := (congrArg₂ (· * ·) (vt a (w0 • a)).symm (k.trans (val_pull hJ _ _ _).symm)).trans (e'.trans
      (congrArg₂ (· * ·) (GlobalTheory.UU.val_scaleGen (unitOn (g a)) (D.psi a) (𝟙 _) hJ) rfl))
    rw [_root_.mul_assoc, e] at e''
    exact (unitAt_injective y (mul_right_cancel (e''.trans (_root_.mul_assoc _ _ _)))).symm

/- English proof (translation)
Introduce `D _ oa w0 g a b c oa' d e` and use `scalar_of_laws D oa w0 g a b c oa' d e`.
-/
theorem main : ∀ {R : Type} [CommRing R] [IsDomain R] {O : Type} [CommRing O] [StarRing O] (D : DegPre R) [inst : Module O D.X] (oa : D.OAct O) (w0 : O) (g : D.X → (FractionRing R)ˣ), D.TauBimult → TraceFormTwistIso D oa w0 → (GlobalTheory.PolDeg.rescale D g).TauBimult → ∀ (oa' : @DegPre.OAct R _ _ O _ _ (GlobalTheory.PolDeg.rescale D g) inst), @DegPre.OAct.onB R _ _ O _ _ (GlobalTheory.PolDeg.rescale D g) inst oa' = oa.onB → @TraceFormTwistIso R _ _ O _ _ (GlobalTheory.PolDeg.rescale D g) inst oa' w0 → GlobalTheory.TauTwist.IsScalarForm O (fun a b => g (a + b) * (g a)⁻¹ * (g b)⁻¹) ∧ ∀ y, g y = g (y + w0 • y) * (g y)⁻¹ * (g (w0 • y))⁻¹ :=
  fun D _ oa w0 g a b c oa' d e => scalar_of_laws D oa w0 g a b c oa' d e

end GlobalTheory.RescaleForm
