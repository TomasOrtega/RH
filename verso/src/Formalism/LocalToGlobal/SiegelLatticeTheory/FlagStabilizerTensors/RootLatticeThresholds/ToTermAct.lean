import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.KernelOfEmbedding
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.SubMemOfIndQ
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RightActionThreeFamilies
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGramActLIota
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ActMass

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.PackageTie2 Formalism.L2.SG.NormCut Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.Pf.unitaryCongruence

namespace Formalism.L2.SG.Pf.KernelOfEmbedding

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Act

variable {D : D7} {X : HidaSetting D} {Y : Full X} {u u' : D.what₂.Word}

/- English proof (translation)
Apply `LinearEquiv.ext` to reduce the goal to its premises. Introduce `y`. Apply `Formalism.L2.SG.Pf.Act.inclCrd_inj` to reduce the goal to its premises. Rewrite using `[Formalism.L2.SG.Pf.Act.isoG_spec, ← Formalism.L2.SG.Pf.LatDictK.ratLink_incl X hx y]`.
-/
theorem eq_isoG {g : Gam X u'} {β : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hx : RatLink X (g : X.B.I.GA) β) :
    β = Formalism.L2.SG.Pf.Act.isoG g := by
  apply LinearEquiv.ext
  intro y
  apply Formalism.L2.SG.Pf.Act.inclCrd_inj
  rw [Formalism.L2.SG.Pf.Act.isoG_spec, ← Formalism.L2.SG.Pf.LatDictK.ratLink_incl X hx y]

/- English proof (translation)
Unfold `Formalism.L2.SG.Pf.SatGramActL.kB`. Rewrite using `[Formalism.L2.SG.Pf.Act.aK_eq]`. Conclude with `γ.2`.
-/
theorem kB_mem (q : {Λ // Λ ∈ Y.what₂ u'}) (γ : Formalism.L2.SG.Pf.Act.GamL (Y.cs u') q) :
    Formalism.L2.SG.Pf.SatGramActL.kB (Y.cs u') q.1 γ.1 ∈ X.B.I.Kset := by
  unfold Formalism.L2.SG.Pf.SatGramActL.kB
  rw [Formalism.L2.SG.Pf.Act.aK_eq]
  exact γ.2

variable (Y) in

/- English proof (translation)
Take `⟨β, hx, hβ⟩` from `Formalism.L2.SG.Pf.SatGramActL.betaLift_holds D X u' (Y.what₂ u') (Y.cs u') q.1 q.2 γ.1 (kB_mem q γ)`. Establish `e` using `eq_isoG hx`. Substitute `e` using the available equality. Conclude with `⟨hx, hβ⟩`.
-/
theorem isoG_lift (q : {Λ // Λ ∈ Y.what₂ u'}) (γ : Formalism.L2.SG.Pf.Act.GamL (Y.cs u') q) :
    RatLink X (γ.1 : X.B.I.GA) (Formalism.L2.SG.Pf.Act.isoG γ.1) ∧
      Formalism.L2.SG.Pf.Act.isoG γ.1 ∈ Formalism.L2.SG.Saturated.AutF q.1 (lf D (X.Fu u')) := by
  obtain ⟨β, hx, hβ⟩ :=
    Formalism.L2.SG.Pf.SatGramActL.betaLift_holds D X u' (Y.what₂ u') (Y.cs u') q.1 q.2 γ.1 (kB_mem q γ)
  have e := eq_isoG hx
  subst e
  exact ⟨hx, hβ⟩

variable (Y) in

def act (q : {Λ // Λ ∈ Y.what₂ u'}) (γ : Formalism.L2.SG.Pf.Act.GamL (Y.cs u') q) (t : TT Y u u') : TT Y u u' :=
  Formalism.L2.SG.Pf.SatGramActR.tmap (γ.1 : X.B.I.GA) (Formalism.L2.SG.Pf.Act.isoG γ.1)
    Formalism.L2.SG.Pf.SatGramActR.autFConjN_holds (isoG_lift Y q γ).1 t

/- English proof (translation)
The claim follows from `Formalism.L2.SG.Pf.SatGramActR.toTerm_tmap _ _ _ _ t`.
-/
theorem toTerm_act (q : {Λ // Λ ∈ Y.what₂ u'}) (γ : Formalism.L2.SG.Pf.Act.GamL (Y.cs u') q) (t : TT Y u u') :
    (act Y q γ t).toTerm = t.toTerm :=
  Formalism.L2.SG.Pf.SatGramActR.toTerm_tmap _ _ _ _ t

/- English proof (translation)
Assemble the required witnesses or components as `⟨rfl, rfl⟩`.
-/
theorem lam_act (q : {Λ // Λ ∈ Y.what₂ u'}) (γ : Formalism.L2.SG.Pf.Act.GamL (Y.cs u') q) (t : TT Y u u') :
    (act Y q γ t).lam = t.lam ∧ (act Y q γ t).lam' = t.lam' := ⟨rfl, rfl⟩

/- English proof (translation)
Establish `hβt : Formalism.L2.SG.Pf.Act.isoG γ.1 ∈ Formalism.L2.SG.Saturated.AutF t.lam' (lf D (X.Fu u'))`. Rewrite using `[ht]`. Conclude with `(isoG_lift Y q γ).2`. Establish `hkt : Formalism.L2.SG.Pf.SatGramActL.kB (Y.cs u') t.lam' γ.1 ∈ X.B.I.Kset`. Rewrite using `[ht]`.

Conclude with `kB_mem q γ`. Unfold `act`. Rewrite using `[Formalism.L2.SG.Pf.SatGramRep.iotaOf_of_mk (hIR D X Y u u') (Formalism.L2.SG.Pf.SatGramActR.tmap (γ.1 : X.B.I.GA) (Formalism.L2.SG.Pf.Act.isoG γ.1) Formalism.L2.SG.Pf.SatGramActR.autFConjN_holds (isoG_lift Y q γ).1 t) (Formalism.L2.SG.Pf.SatGramActR.rmul (γ.1 : X.B.I.GA) _ (isoG …`. Rewrite using `[Formalism.L2.SG.Pf.SatGramRep.iotaOf_of_mk (hIR D X Y u u') t t.rep (Quot.out_eq t.cls).symm]`. Establish `e2 : ((((Y.cs u').h ((Y.cs u').base t.lam') : X.B.I.Gf) * X.xu u')⁻¹ * ((γ.1 : X.B.I.GA)⁻¹).2 * (((Y.cs u').h ((Y.cs u').base t.lam') : X.B.I.Gf) * X.xu u')) = (Formalism.L2.SG.Pf.SatGramActL.kB (Y.cs u') t.lam' γ.1)⁻¹`.

Establish `eg : (γ.1 : X.B.I.GA).2 = (iotaF X u' γ.1 : X.B.I.Gf)` using `rfl`. Rewrite using `[Prod.snd_inv, eg]`. Unfold `Formalism.L2.SG.Pf.SatGramActL.kB`. Use `group`. Establish `hG1 : Good X (kOf X u u' ((Y.cs u).h ((Y.cs u).base t.lam) : X.B.I.Gf) ((Y.cs u').h ((Y.cs u').base t.lam') : X.B.I.Gf) t.rep.1.1)` using `Formalism.L2.SG.Closed.AdmPar_holds (Y.cs u) (Y.cs u') (Formalism.L2.SG.Full.Full.frameTie (X := X) u u') t`.

Establish `hG2 : Good X (Formalism.L2.SG.Pf.SatGramActL.kB (Y.cs u') t.lam' γ.1)` using `Formalism.L2.SG.Pf.SatGramActL.satGramActLIota_kB_good (Y.cs u') t.lam' γ.1 hkt`. Use `show levi Y.TR (kOf X u u' ((Y.cs u).h ((Y.cs u).base t.lam) : X.B.I.Gf) ((Y.cs u').h ((Y.cs u').base t.lam') : X.B.I.Gf) (t.rep.1.1 * (γ.1 : X.B.I.GA)⁻¹)) = _`. Rewrite using `[Formalism.L2.SG.Pf.SatGramActR.kOf_mul_right, e2, levi_mul Y.TR hG1 (good_inv X hG2), levi_inv Y.TR hG2]`. Establish `hq2 : Formalism.L2.SG.Pf.SatGramActL.kB (Y.cs u') t.lam' γ.1 = Formalism.L2.SG.Pf.SatGramActL.kB (Y.cs u') q.1 γ.1`. Rewrite using `[ht]`.

Rewrite using `[hq2]`.
-/
theorem iota_act (hIR : Formalism.L2.SG.Pf.SatGramRep.IotaRepC) (q : {Λ // Λ ∈ Y.what₂ u'})
    (γ : Formalism.L2.SG.Pf.Act.GamL (Y.cs u') q) (t : TT Y u u') (ht : t.lam' = q.1) :
    iotaOf Y.TR (Y.cs u) (Y.cs u') (act Y q γ t) =
      iotaOf Y.TR (Y.cs u) (Y.cs u') t * (levi Y.TR (Formalism.L2.SG.Pf.SatGramActL.kB (Y.cs u') q.1 γ.1))⁻¹ := by
  have hβt : Formalism.L2.SG.Pf.Act.isoG γ.1 ∈ Formalism.L2.SG.Saturated.AutF t.lam' (lf D (X.Fu u')) := by
    rw [ht]; exact (isoG_lift Y q γ).2
  have hkt : Formalism.L2.SG.Pf.SatGramActL.kB (Y.cs u') t.lam' γ.1 ∈ X.B.I.Kset := by
    rw [ht]; exact kB_mem q γ
  unfold act
  rw [Formalism.L2.SG.Pf.SatGramRep.iotaOf_of_mk (hIR D X Y u u') (Formalism.L2.SG.Pf.SatGramActR.tmap (γ.1 : X.B.I.GA) (Formalism.L2.SG.Pf.Act.isoG γ.1) Formalism.L2.SG.Pf.SatGramActR.autFConjN_holds (isoG_lift Y q γ).1 t)
    (Formalism.L2.SG.Pf.SatGramActR.rmul (γ.1 : X.B.I.GA) _ (isoG_lift Y q γ).1 hβt t.rep)
    (Formalism.L2.SG.Pf.SatGramActR.tmap_cls _ _ _ _ t hβt)]
  rw [Formalism.L2.SG.Pf.SatGramRep.iotaOf_of_mk (hIR D X Y u u') t t.rep (Quot.out_eq t.cls).symm]
  have e2 : ((((Y.cs u').h ((Y.cs u').base t.lam') : X.B.I.Gf) * X.xu u')⁻¹ * ((γ.1 : X.B.I.GA)⁻¹).2 *
      (((Y.cs u').h ((Y.cs u').base t.lam') : X.B.I.Gf) * X.xu u')) =
      (Formalism.L2.SG.Pf.SatGramActL.kB (Y.cs u') t.lam' γ.1)⁻¹ := by
    have eg : (γ.1 : X.B.I.GA).2 = (iotaF X u' γ.1 : X.B.I.Gf) := rfl
    rw [Prod.snd_inv, eg]
    unfold Formalism.L2.SG.Pf.SatGramActL.kB
    group
  have hG1 : Good X (kOf X u u' ((Y.cs u).h ((Y.cs u).base t.lam) : X.B.I.Gf)
      ((Y.cs u').h ((Y.cs u').base t.lam') : X.B.I.Gf) t.rep.1.1) :=
    Formalism.L2.SG.Closed.AdmPar_holds (Y.cs u) (Y.cs u') (Formalism.L2.SG.Full.Full.frameTie (X := X) u u') t
  have hG2 : Good X (Formalism.L2.SG.Pf.SatGramActL.kB (Y.cs u') t.lam' γ.1) :=
    Formalism.L2.SG.Pf.SatGramActL.satGramActLIota_kB_good (Y.cs u') t.lam' γ.1 hkt
  show levi Y.TR (kOf X u u' ((Y.cs u).h ((Y.cs u).base t.lam) : X.B.I.Gf)
      ((Y.cs u').h ((Y.cs u').base t.lam') : X.B.I.Gf) (t.rep.1.1 * (γ.1 : X.B.I.GA)⁻¹)) = _
  rw [Formalism.L2.SG.Pf.SatGramActR.kOf_mul_right, e2, levi_mul Y.TR hG1 (good_inv X hG2), levi_inv Y.TR hG2]
  have hq2 : Formalism.L2.SG.Pf.SatGramActL.kB (Y.cs u') t.lam' γ.1 = Formalism.L2.SG.Pf.SatGramActL.kB (Y.cs u') q.1 γ.1 := by
    rw [ht]
  rw [hq2]

/- English proof (translation)
Establish `hβt : Formalism.L2.SG.Pf.Act.isoG γ.1 ∈ Formalism.L2.SG.Saturated.AutF t.lam' (lf D (X.Fu u'))`. Rewrite using `[ht]`. Conclude with `(isoG_lift Y q γ).2`. Establish `hkt : Formalism.L2.SG.Pf.SatGramActL.kB (Y.cs u') t.lam' γ.1 ∈ X.B.I.Kset`. Rewrite using `[ht]`.

Conclude with `kB_mem q γ`. Establish `hF` using `Formalism.L2.SG.Pf.fundExistsC_holds D X Y u u'`. Establish `hft` using `Formalism.L2.SG.Pf.SatGramActL.fundOf_spec hF t`. Establish `hΩ : IsSFund X.B.I (ROset X (X.Fu u) (X.Fu u') t.lam t.lam' (Formalism.L2.SG.Pf.SatGramActR.rmul (γ.1 : X.B.I.GA) _ (isoG_lift Y q γ).1 hβt t.rep).1.2) (FundOf t)`. Establish `e` using `Formalism.L2.SG.Pf.SatGramActR.roset_mul_aut (X := X) (F0 := X.Fu u) (Λ := t.lam) hβt t.rep.1.2`.

Use `hft using 2` and compare the differences between its conclusion and the goal. Conclude with `e`. Use `show ampN (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') (act Y q γ t) = (ampN (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') t).comp (X.piU u' ((γ.1 : X.B.I.GA).1)⁻¹)`. Unfold `act`. Rewrite using `[Formalism.L2.SG.Pf.SatGramRep.ampN_of_mk (Y.FN u) (Y.FN u') (hAR D X Y u u') hF hOI (Formalism.L2.SG.Pf.SatGramActR.tmap (γ.1 : X.B.I.GA) (Formalism.L2.SG.Pf.Act.isoG γ.1) Formalism.L2.SG.Pf.SatGramActR.autFConjN_holds (isoG_lift Y q γ).1 t) (Formalism.L2.SG.Pf.SatGramActR.rmul …`.

Rewrite using `[Formalism.L2.SG.Pf.SatGramRep.ampN_of_mk (Y.FN u) (Y.FN u') (hAR D X Y u u') hF hOI t t.rep (Quot.out_eq t.cls).symm (FundOf t) hft]`. Establish `e2 : ((((Y.cs u').h ((Y.cs u').base t.lam') : X.B.I.Gf) * X.xu u')⁻¹ * ((γ.1 : X.B.I.GA)⁻¹).2 * (((Y.cs u').h ((Y.cs u').base t.lam') : X.B.I.Gf) * X.xu u')) = (Formalism.L2.SG.Pf.SatGramActL.kB (Y.cs u') t.lam' γ.1)⁻¹`. Establish `eg : (γ.1 : X.B.I.GA).2 = (iotaF X u' γ.1 : X.B.I.Gf)` using `rfl`. Rewrite using `[Prod.snd_inv, eg]`. Unfold `Formalism.L2.SG.Pf.SatGramActL.kB`.

Use `group`. Establish `hκ` using `Formalism.L2.SG.Pf.SatGramActL.ChiLeft.kBB_mem Y u u' t.mem t.mem' t.rep`. Establish `eχ : chiN X (kOf X u u' ((Y.cs u).h ((Y.cs u).base t.lam) : X.B.I.Gf) ((Y.cs u').h ((Y.cs u').base t.lam') : X.B.I.Gf) (t.rep.1.1 * (γ.1 : X.B.I.GA)⁻¹)) = chiN X (kOf X u u' ((Y.cs u).h ((Y.cs u).base t.lam) : X.B.I.Gf) ((Y.cs u').h ((Y.cs u').base t.lam') : X.B.I.Gf) t.rep.1.1)`. Rewrite using `[Formalism.L2.SG.Pf.SatGramActR.kOf_mul_right, e2]`. Conclude with `Formalism.L2.SG.Pf.SatGramActR.chiNR_holds hB D X u' ((Y.cs u').h ((Y.cs u').base t.lam')) γ.1 _ hκ hkt`.

Use `show ((scl (Y.FN u) (Y.FN u') (X := X) (u := u) (u' := u') * X.volK2 : ℝ) : ℂ) • (chiN X (kOf X u u' ((Y.cs u).h ((Y.cs u).base t.lam) : X.B.I.Gf) ((Y.cs u').h ((Y.cs u').base t.lam') : X.B.I.Gf) (t.rep.1.1 * (γ.1 : X.B.I.GA)⁻¹)) • (haveI := FiniteDimensional.complete ℂ (X.Vpi u) …`. Rewrite using `[eχ, Formalism.L2.SG.Pf.SatGramActR.ooR_holds D X u u' γ.1 (FundOf t) t.rep.1.1.1]`. Rewrite using `[ContinuousLinearMap.smul_comp, ContinuousLinearMap.smul_comp]`.
-/
theorem amp_act (hB : Formalism.L2.SG.Pf.SatGramActL.ChiNBiAll) (hAR : Formalism.L2.SG.Pf.SatGramRep.AmpRepNC)
    (hOI : OOIntAll X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')) (q : {Λ // Λ ∈ Y.what₂ u'})
    (γ : Formalism.L2.SG.Pf.Act.GamL (Y.cs u') q) (t : TT Y u u') (ht : t.lam' = q.1) :
    amp Y (act Y q γ t) = (amp Y t).comp (X.piU u' ((γ.1 : X.B.I.GA).1)⁻¹) := by
  have hβt : Formalism.L2.SG.Pf.Act.isoG γ.1 ∈ Formalism.L2.SG.Saturated.AutF t.lam' (lf D (X.Fu u')) := by
    rw [ht]; exact (isoG_lift Y q γ).2
  have hkt : Formalism.L2.SG.Pf.SatGramActL.kB (Y.cs u') t.lam' γ.1 ∈ X.B.I.Kset := by
    rw [ht]; exact kB_mem q γ
  have hF := Formalism.L2.SG.Pf.fundExistsC_holds D X Y u u'
  have hft := Formalism.L2.SG.Pf.SatGramActL.fundOf_spec hF t
  have hΩ : IsSFund X.B.I (ROset X (X.Fu u) (X.Fu u') t.lam t.lam'
      (Formalism.L2.SG.Pf.SatGramActR.rmul (γ.1 : X.B.I.GA) _ (isoG_lift Y q γ).1 hβt t.rep).1.2) (FundOf t) := by
    have e := Formalism.L2.SG.Pf.SatGramActR.roset_mul_aut (X := X) (F0 := X.Fu u) (Λ := t.lam) hβt t.rep.1.2
    convert hft using 2
    exact e
  show ampN (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') (act Y q γ t) =
    (ampN (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') t).comp (X.piU u' ((γ.1 : X.B.I.GA).1)⁻¹)
  unfold act
  rw [Formalism.L2.SG.Pf.SatGramRep.ampN_of_mk (Y.FN u) (Y.FN u') (hAR D X Y u u') hF hOI (Formalism.L2.SG.Pf.SatGramActR.tmap (γ.1 : X.B.I.GA) (Formalism.L2.SG.Pf.Act.isoG γ.1) Formalism.L2.SG.Pf.SatGramActR.autFConjN_holds (isoG_lift Y q γ).1 t)
    (Formalism.L2.SG.Pf.SatGramActR.rmul (γ.1 : X.B.I.GA) _ (isoG_lift Y q γ).1 hβt t.rep)
    (Formalism.L2.SG.Pf.SatGramActR.tmap_cls _ _ _ _ t hβt) (FundOf t) hΩ]
  rw [Formalism.L2.SG.Pf.SatGramRep.ampN_of_mk (Y.FN u) (Y.FN u') (hAR D X Y u u') hF hOI t t.rep
    (Quot.out_eq t.cls).symm (FundOf t) hft]
  have e2 : ((((Y.cs u').h ((Y.cs u').base t.lam') : X.B.I.Gf) * X.xu u')⁻¹ * ((γ.1 : X.B.I.GA)⁻¹).2 *
      (((Y.cs u').h ((Y.cs u').base t.lam') : X.B.I.Gf) * X.xu u')) =
      (Formalism.L2.SG.Pf.SatGramActL.kB (Y.cs u') t.lam' γ.1)⁻¹ := by
    have eg : (γ.1 : X.B.I.GA).2 = (iotaF X u' γ.1 : X.B.I.Gf) := rfl
    rw [Prod.snd_inv, eg]
    unfold Formalism.L2.SG.Pf.SatGramActL.kB
    group
  have hκ := Formalism.L2.SG.Pf.SatGramActL.ChiLeft.kBB_mem Y u u' t.mem t.mem' t.rep
  have eχ : chiN X (kOf X u u' ((Y.cs u).h ((Y.cs u).base t.lam) : X.B.I.Gf)
      ((Y.cs u').h ((Y.cs u').base t.lam') : X.B.I.Gf) (t.rep.1.1 * (γ.1 : X.B.I.GA)⁻¹)) =
      chiN X (kOf X u u' ((Y.cs u).h ((Y.cs u).base t.lam) : X.B.I.Gf)
        ((Y.cs u').h ((Y.cs u').base t.lam') : X.B.I.Gf) t.rep.1.1) := by
    rw [Formalism.L2.SG.Pf.SatGramActR.kOf_mul_right, e2]
    exact Formalism.L2.SG.Pf.SatGramActR.chiNR_holds hB D X u' ((Y.cs u').h ((Y.cs u').base t.lam')) γ.1 _ hκ hkt
  show ((scl (Y.FN u) (Y.FN u') (X := X) (u := u) (u' := u') * X.volK2 : ℝ) : ℂ) •
      (chiN X (kOf X u u' ((Y.cs u).h ((Y.cs u).base t.lam) : X.B.I.Gf)
        ((Y.cs u').h ((Y.cs u').base t.lam') : X.B.I.Gf) (t.rep.1.1 * (γ.1 : X.B.I.GA)⁻¹)) •
        (haveI := FiniteDimensional.complete ℂ (X.Vpi u)
         OO (Formalism.L2.SG.ProjRows.muInf X.B.I) (FundOf t) (X.Wu u) (X.Wu u')
          (t.rep.1.1.1 * ((γ.1 : X.B.I.GA).1)⁻¹))) = _
  rw [eχ, Formalism.L2.SG.Pf.SatGramActR.ooR_holds D X u u' γ.1 (FundOf t) t.rep.1.1.1]
  rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.smul_comp]

/- English proof (translation)
Take `⟨c, hc, hg, hfix, n, hn, ν, hν, he⟩` from `Formalism.L2.SG.Pf.FibreCounting.fib_c h`. Establish `hst` using `Formalism.L2.SG.Pf.FibreCounting.stabF_of_fix (X.Fu u') hc hfix`. Take `⟨g, hgq⟩` from `(Formalism.L2.SG.Pf.Act.gamL_autLz_bij (Y.cs u') Y.hK hN ⟨s.lam', s.mem'⟩).2 ⟨Formalism.L2.SG.Pf.Act.indW c hst, Formalism.L2.SG.Pf.Act.indW_mem s.lam' c hst hg⟩`. Establish `hW : (Formalism.L2.SG.Pf.Act.indW (Formalism.L2.SG.Pf.Act.isoG g.1) (Formalism.L2.SG.Pf.Act.isoG_stab g.1) : Formalism.MainNotions.S.WbQ D (X.Fu u') → Formalism.MainNotions.S.WbQ D (X.Fu u')) = Formalism.L2.SG.Pf.Act.indW c hst` using `congrArg Subtype.val hgq`. Establish `hq : ∀ y ∈ perpS (VS D) (X.Fu u').X, c y - Formalism.L2.SG.Pf.Act.isoG g.1 y ∈ (X.Fu u').X`.

Introduce `y hy`. Establish `e` using `congrFun hW.symm (Submodule.Quotient.mk ⟨y, hy⟩)`. Rewrite `e` using `[Formalism.L2.SG.Pf.Act.indW_mk, Formalism.L2.SG.Pf.Act.indW_mk, Submodule.Quotient.eq]`. Simplify using `using e`. Establish `hfixg : ∀ a, Formalism.L2.SG.Pf.Act.isoG g.1 ((X.Fu u').fvec a) = (X.Fu u').fvec a`.

Introduce `a`. Use `Fin.lastCases ?_ (fun i => ?_) a` and prove the remaining obligations. Simplify using `only [FlagG.fvec, Fin.snoc_last]`. Rewrite using `[X.flagZVector u']`. Conclude with `Formalism.L2.SG.Pf.Act.isoG_fix g.1 _ (Or.inr rfl)`.

Simplify using `only [FlagG.fvec, Fin.snoc_castSucc]`. Rewrite using `[X.Fu_e u']`. Conclude with `Formalism.L2.SG.Pf.Act.isoG_e g.1 i`. Establish `hA : IsAutLam (VS D) s.lam' c` using `⟨hc, hg⟩`. Establish `hA' : IsAutLam (VS D) s.lam' (Formalism.L2.SG.Pf.Act.isoG g.1)` using `⟨(Formalism.L2.SG.Pf.Act.isoG_stab g.1).1, Formalism.L2.SG.Pf.Act.isoG_lat (Y.cs u') ⟨s.lam', s.mem'⟩ g⟩`.

Establish `hm` using `Formalism.L2.SG.Pf.FibreCounting.nlam_of_sub (X.Fu u') hA hA' hfix hfixg hq`. Establish `hkinv : colD ((Y.cs u').h ((Y.cs u').base s.lam')) (iotaF X u' g.1⁻¹ * (Y.cs u').h ((Y.cs u').base s.lam')) ∈ X.B.I.Kset`. Rewrite using `[← Formalism.L2.SG.Pf.Act.aK_eq]`. Establish `h1` using `K_inv X.B.I (kB_mem (Y := Y) ⟨s.lam', s.mem'⟩ g)`. Unfold `Formalism.L2.SG.Pf.SatGramActL.kB at h1`.

Rewrite using `[map_inv]`. Use `h1 using 1` and compare the differences between its conclusion and the goal. Use `push_cast`. Use `group`. Set `γ : Formalism.L2.SG.Pf.Act.GamL (Y.cs u') ⟨s.lam', s.mem'⟩` to `⟨g.1⁻¹, hkinv⟩`.

Establish `hxg` using `(isoG_lift Y ⟨s.lam', s.mem'⟩ g).1`. Establish `hxi : RatLink X (γ.1 : X.B.I.GA) (Formalism.L2.SG.Pf.Act.isoG g.1)⁻¹`. Use `Formalism.L2.SG.Pf.ratLink_inv X hxg` as an intermediate fact. Simplify `this` using `[γ]`. Establish `hiso : Formalism.L2.SG.Pf.Act.isoG γ.1 = (Formalism.L2.SG.Pf.Act.isoG g.1)⁻¹` using `(eq_isoG hxi).symm`.

Use `⟨γ, ?_⟩` and prove the remaining obligations. Establish `hl : s.lam = s'.lam` using `(Formalism.L2.SG.Pf.FibreCounting.fib_dec h).1`. Establish `hl' : s.lam' = s'.lam'` using `Formalism.L2.SG.Pf.FibreCounting.lam'_eq h`. Establish `hβt : Formalism.L2.SG.Pf.Act.isoG γ.1 ∈ Formalism.L2.SG.Saturated.AutF s.lam' (lf D (X.Fu u'))` using `(isoG_lift Y ⟨s.lam', s.mem'⟩ γ).2`. Establish `hcls` using `Formalism.L2.SG.Pf.SatGramActR.tmap_cls (γ.1 : X.B.I.GA) (Formalism.L2.SG.Pf.Act.isoG γ.1) Formalism.L2.SG.Pf.SatGramActR.autFConjN_holds (isoG_lift Y ⟨s.lam', s.mem'⟩ γ).1 s hβt`.

Use `set G := Formalism.L2.SG.Pf.Act.isoG g.1 with hG`. Establish `hGA : G⁻¹ ∈ Formalism.L2.SG.Saturated.AutF s.lam' (lf D (X.Fu u'))` using `by rw [← hiso]; exact hβt`. Establish `hν2 : G⁻¹ * ν * G⁻¹⁻¹ ∈ NLam s.lam' (lf D (X.Fu u'))` using `Formalism.L2.SG.Pf.SatGramActL.nlam_conj hGA hν`. Establish `hν3 : (G⁻¹ * ν * G⁻¹⁻¹) * (c⁻¹ * G)⁻¹ ∈ NLam s.lam' (lf D (X.Fu u'))` using `Formalism.L2.SG.Pf.nlamPf_mul hν2 (Formalism.L2.SG.Pf.nlamPf_inv hm)`. Break down `s' with ⟨k, hk, k', hk', q'⟩` into its components or cases.

Simplify using `only at hl hl' he`. Substitute `hl hl'` using the available equality. Use `show (⟨s.lam, hk, s.lam', hk', q'⟩ : TT Y u u') = ⟨s.lam, s.mem, s.lam', s.mem', (Formalism.L2.SG.Pf.SatGramActR.tmap (γ.1 : X.B.I.GA) (Formalism.L2.SG.Pf.Act.isoG γ.1) Formalism.L2.SG.Pf.SatGramActR.autFConjN_holds (isoG_lift Y ⟨s.lam', s.mem'⟩ γ).1 s).cls⟩`. Rewrite using `[hcls]`. Use `congr 1`.

Rewrite using `[← Quot.out_eq q']`. Use `(Quot.sound ⟨n, hn, (G⁻¹ * ν * G⁻¹⁻¹) * (c⁻¹ * G)⁻¹, hν3, ?_⟩).symm` and prove the remaining obligations. Use `show GTerm.lin (⟨s.lam, hk, s.lam', hk', q'⟩ : TT Y u u') = n * (GTerm.lin s * (Formalism.L2.SG.Pf.Act.isoG γ.1)⁻¹) * ((G⁻¹ * ν * G⁻¹⁻¹) * (c⁻¹ * G)⁻¹)`. Rewrite using `[he, hiso]`. Use `group`.
-/
theorem fib_gam (hN : Formalism.L2.SG.PoincareInHH.Cut.NeatKu X u' Y.hK) {s s' : TT Y u u'} (h : s.toTerm = s'.toTerm) :
    ∃ γ : Formalism.L2.SG.Pf.Act.GamL (Y.cs u') ⟨s.lam', s.mem'⟩, s' = act Y ⟨s.lam', s.mem'⟩ γ s := by
  obtain ⟨c, hc, hg, hfix, n, hn, ν, hν, he⟩ := Formalism.L2.SG.Pf.FibreCounting.fib_c h
  have hst := Formalism.L2.SG.Pf.FibreCounting.stabF_of_fix (X.Fu u') hc hfix
  obtain ⟨g, hgq⟩ := (Formalism.L2.SG.Pf.Act.gamL_autLz_bij (Y.cs u') Y.hK hN ⟨s.lam', s.mem'⟩).2
    ⟨Formalism.L2.SG.Pf.Act.indW c hst, Formalism.L2.SG.Pf.Act.indW_mem s.lam' c hst hg⟩
  have hW : (Formalism.L2.SG.Pf.Act.indW (Formalism.L2.SG.Pf.Act.isoG g.1) (Formalism.L2.SG.Pf.Act.isoG_stab g.1) :
      Formalism.MainNotions.S.WbQ D (X.Fu u') → Formalism.MainNotions.S.WbQ D (X.Fu u')) = Formalism.L2.SG.Pf.Act.indW c hst :=
    congrArg Subtype.val hgq
  have hq : ∀ y ∈ perpS (VS D) (X.Fu u').X, c y - Formalism.L2.SG.Pf.Act.isoG g.1 y ∈ (X.Fu u').X := by
    intro y hy
    have e := congrFun hW.symm (Submodule.Quotient.mk ⟨y, hy⟩)
    rw [Formalism.L2.SG.Pf.Act.indW_mk, Formalism.L2.SG.Pf.Act.indW_mk, Submodule.Quotient.eq] at e
    simpa using e
  have hfixg : ∀ a, Formalism.L2.SG.Pf.Act.isoG g.1 ((X.Fu u').fvec a) = (X.Fu u').fvec a := by
    intro a
    refine Fin.lastCases ?_ (fun i => ?_) a
    · simp only [FlagG.fvec, Fin.snoc_last]
      rw [X.flagZVector u']
      exact Formalism.L2.SG.Pf.Act.isoG_fix g.1 _ (Or.inr rfl)
    · simp only [FlagG.fvec, Fin.snoc_castSucc]
      rw [X.Fu_e u']
      exact Formalism.L2.SG.Pf.Act.isoG_e g.1 i
  have hA : IsAutLam (VS D) s.lam' c := ⟨hc, hg⟩
  have hA' : IsAutLam (VS D) s.lam' (Formalism.L2.SG.Pf.Act.isoG g.1) :=
    ⟨(Formalism.L2.SG.Pf.Act.isoG_stab g.1).1, Formalism.L2.SG.Pf.Act.isoG_lat (Y.cs u') ⟨s.lam', s.mem'⟩ g⟩
  have hm := Formalism.L2.SG.Pf.FibreCounting.nlam_of_sub (X.Fu u') hA hA' hfix hfixg hq

  have hkinv : colD ((Y.cs u').h ((Y.cs u').base s.lam')) (iotaF X u' g.1⁻¹ * (Y.cs u').h ((Y.cs u').base s.lam'))
      ∈ X.B.I.Kset := by
    rw [← Formalism.L2.SG.Pf.Act.aK_eq]
    have h1 := K_inv X.B.I (kB_mem (Y := Y) ⟨s.lam', s.mem'⟩ g)
    unfold Formalism.L2.SG.Pf.SatGramActL.kB at h1
    rw [map_inv]
    convert h1 using 1
    push_cast
    group
  let γ : Formalism.L2.SG.Pf.Act.GamL (Y.cs u') ⟨s.lam', s.mem'⟩ := ⟨g.1⁻¹, hkinv⟩
  have hxg := (isoG_lift Y ⟨s.lam', s.mem'⟩ g).1
  have hxi : RatLink X (γ.1 : X.B.I.GA) (Formalism.L2.SG.Pf.Act.isoG g.1)⁻¹ := by
    have := Formalism.L2.SG.Pf.ratLink_inv X hxg
    simpa [γ] using this
  have hiso : Formalism.L2.SG.Pf.Act.isoG γ.1 = (Formalism.L2.SG.Pf.Act.isoG g.1)⁻¹ := (eq_isoG hxi).symm
  refine ⟨γ, ?_⟩
  have hl : s.lam = s'.lam := (Formalism.L2.SG.Pf.FibreCounting.fib_dec h).1
  have hl' : s.lam' = s'.lam' := Formalism.L2.SG.Pf.FibreCounting.lam'_eq h
  have hβt : Formalism.L2.SG.Pf.Act.isoG γ.1 ∈ Formalism.L2.SG.Saturated.AutF s.lam' (lf D (X.Fu u')) :=
    (isoG_lift Y ⟨s.lam', s.mem'⟩ γ).2
  have hcls := Formalism.L2.SG.Pf.SatGramActR.tmap_cls (γ.1 : X.B.I.GA) (Formalism.L2.SG.Pf.Act.isoG γ.1)
    Formalism.L2.SG.Pf.SatGramActR.autFConjN_holds (isoG_lift Y ⟨s.lam', s.mem'⟩ γ).1 s hβt

  set G := Formalism.L2.SG.Pf.Act.isoG g.1 with hG
  have hGA : G⁻¹ ∈ Formalism.L2.SG.Saturated.AutF s.lam' (lf D (X.Fu u')) := by rw [← hiso]; exact hβt
  have hν2 : G⁻¹ * ν * G⁻¹⁻¹ ∈ NLam s.lam' (lf D (X.Fu u')) :=
    Formalism.L2.SG.Pf.SatGramActL.nlam_conj hGA hν
  have hν3 : (G⁻¹ * ν * G⁻¹⁻¹) * (c⁻¹ * G)⁻¹ ∈ NLam s.lam' (lf D (X.Fu u')) :=
    Formalism.L2.SG.Pf.nlamPf_mul hν2 (Formalism.L2.SG.Pf.nlamPf_inv hm)
  rcases s' with ⟨k, hk, k', hk', q'⟩
  simp only at hl hl' he
  subst hl hl'
  show (⟨s.lam, hk, s.lam', hk', q'⟩ : TT Y u u') =
    ⟨s.lam, s.mem, s.lam', s.mem', (Formalism.L2.SG.Pf.SatGramActR.tmap (γ.1 : X.B.I.GA) (Formalism.L2.SG.Pf.Act.isoG γ.1)
      Formalism.L2.SG.Pf.SatGramActR.autFConjN_holds (isoG_lift Y ⟨s.lam', s.mem'⟩ γ).1 s).cls⟩
  rw [hcls]
  congr 1
  rw [← Quot.out_eq q']
  refine (Quot.sound ⟨n, hn, (G⁻¹ * ν * G⁻¹⁻¹) * (c⁻¹ * G)⁻¹, hν3, ?_⟩).symm
  show GTerm.lin (⟨s.lam, hk, s.lam', hk', q'⟩ : TT Y u u') =
    n * (GTerm.lin s * (Formalism.L2.SG.Pf.Act.isoG γ.1)⁻¹) * ((G⁻¹ * ν * G⁻¹⁻¹) * (c⁻¹ * G)⁻¹)
  rw [he, hiso]
  group

end Act

end Formalism.L2.SG.Pf.KernelOfEmbedding
