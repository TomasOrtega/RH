import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ParamsEx
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaProjectionIntertwinesLevelLifts
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftTwistsByLevelCharacter
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteGroupLiftsToParahoricLevelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypePlacesNotPairwiseConjugateStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanPOfGiven
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryEqRealMulFiniteSplit
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

namespace GlobalTheory.GoodLift

/- English proof (translation)
Use function extensionality and compare the values at `h`. Use `sub_eq_zero.1 ((Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun l => ?_)` and prove the remaining obligations. Rewrite using `[map_sub, sub_eq_zero, ← hy l h, map_sum, Finset.sum_apply, map_sum]`. Use `Finset.sum_congr rfl fun g _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, Pi.smul_apply, map_smul, hext g h, map_smul, smul_eq_mul, smul_eq_mul]`.
-/
theorem sum_translates {H X W ι : Type} [AddCommGroup H] [Module ℂ H] [AddCommGroup W] [Module ℂ W] [Mul X] [Fintype ι]
    (E : H →ₗ[ℂ] (X → W)) (y : H) (yg : ι → H) (a c : ι → ℂ) (κ : ι → X)
    (hext : ∀ g h, E (yg g) h = (c g)⁻¹ • E y (h * κ g))
    (hy : ∀ (l : W →ₗ[ℂ] ℂ) h, ∑ g, a g * ((c g)⁻¹ * l (E y (h * κ g))) = l (E y h)) :
    E (∑ g, a g • yg g) = E y := by
  funext h
  refine sub_eq_zero.1 ((Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun l => ?_)
  rw [map_sub, sub_eq_zero, ← hy l h, map_sum, Finset.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [map_smul, Pi.smul_apply, map_smul, hext g h, map_smul, smul_eq_mul, smul_eq_mul]

/- English proof (translation)
Unfold `gaL`. Rewrite using `[LinearMap.sum_apply, Finset.sum_apply]`. Use `Finset.sum_congr rfl fun g _ => ?_` and prove the remaining obligations. Use `show c g * actG0 V β L (eG g) F h = _`. Unfold `actG0`.

Rewrite using `[dif_pos (hk g)]`.
-/
theorem gaL_apply_choose {D : D7} {G : Type} [Group G] [Fintype G] (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D))
    (L : LevDat D.host.E ℂ V.rank) (eG : G ≃* G0 L.Pg L.r) (c : G → ℂ) (hk : ∀ g, ∃ κ, IsLevelLift V β L (eG g) κ)
    (F : GA D V → ℂ) (h : GA D V) :
    gaL V β L eG c F h = ∑ g, c g * ((levChi V β (flagL L) (hk g).choose)⁻¹ * F (h * (hk g).choose)) := by
  unfold gaL
  rw [LinearMap.sum_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun g _ => ?_
  show c g * actG0 V β L (eG g) F h = _
  unfold actG0
  rw [dif_pos (hk g)]

end GlobalTheory.GoodLift

namespace GlobalTheory.GoodLift

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)

set_option maxHeartbeats 4000000 in

/- English proof (translation)
Take `⟨c, hc⟩` from `hR.lev.βW i`. Conclude with `GlobalTheory.T.finite_group_lifts_to_parahoric_level _ _ _ _ _ hc rfl (GlobalTheory.T.typePlaces_not_pairwise_conjugate R.C.P R.Pg hR.lev.Pg)`.
-/
theorem liftsW_of_core (hR : GlobalTheory.Hk3.Core R F) (i : Fin D.R.m) : LiftsExist (Wc D i) (R.βW i) (R.datWp i R.triv) := by
  obtain ⟨c, hc⟩ := hR.lev.βW i
  exact GlobalTheory.T.finite_group_lifts_to_parahoric_level _ _ _ _ _ hc rfl (GlobalTheory.T.typePlaces_not_pairwise_conjugate R.C.P R.Pg hR.lev.Pg)

set_option maxHeartbeats 4000000 in

/- English proof (translation)
Take `⟨q, hq⟩` from `(R.B.L i t).act_tie.red_surj g`. Establish `h1` using `hR.grp.red_L i t q`. Take `⟨⟨_, h, rfl⟩, hq2⟩` from `q`. Take `⟨a, ha, k, hk, rfl⟩` from `(GlobalTheory.UnitarySplit.real_finite_split D (Vc D i)).1 h`. Establish `e : finHom (Vc D i) (a * k) = finHom (Vc D i) k`.

Rewrite using `[map_mul, show finHom (Vc D i) a = 1 from ha, one_mul]`. Use `⟨k, hk, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[finE_eq, ← e]`. Conclude with `hq2.1`. Rewrite using `[finE_eq, ← e, ← hq]`.

Conclude with `h1.symm`.
-/
theorem liftsV_of_core (hR : GlobalTheory.Hk3.Core R F) (i : Fin D.R.m) (t : T) (g : G) :
    ∃ κ, IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) (R.eG g) κ := by
  obtain ⟨q, hq⟩ := (R.B.L i t).act_tie.red_surj g
  have h1 := hR.grp.red_L i t q
  obtain ⟨⟨_, h, rfl⟩, hq2⟩ := q
  obtain ⟨a, ha, k, hk, rfl⟩ := (GlobalTheory.UnitarySplit.real_finite_split D (Vc D i)).1 h
  have e : finHom (Vc D i) (a * k) = finHom (Vc D i) k := by
    rw [map_mul, show finHom (Vc D i) a = 1 from ha, one_mul]
  refine ⟨k, hk, ?_, ?_⟩
  · rw [finE_eq, ← e]; exact hq2.1
  · rw [finE_eq, ← e, ← hq]; exact h1.symm

set_option maxHeartbeats 4000000 in

/- English proof (translation)
Take `⟨y', hy', -⟩` from `GlobalTheory.RowClassSum.exists_translate (Vc D i) (R.βV i) (R.datVt i t) (R.cV i) (hR.models.cV i) (R.HV i t) _ (R.B.L i t).pres.reps (hR.models.HV i t) g0 κ hκ y`. Establish `hc0 : levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ ≠ 0` using `levChi_ne_zero _ _`. Use `⟨y', hy', fun h => ?_⟩` and prove the remaining obligations. Establish `e` using `GlobalTheory.ThetaProjEquiv.extV_shift R hR.models.cV i t κ hκ.1 _ hc0 y y' hy' h`. Rewrite `e` using `[LinearMap.map_smul, Pi.smul_apply]`.

Rewrite using `[← e, smul_smul, inv_mul_cancel₀ hc0, one_smul]`.
-/
theorem translate_of_core (hR : GlobalTheory.Hk3.Core R F) (i : Fin D.R.m) (t : T) (g0 : G0 R.Pg D.R.r) (κ : GA D (Vc D i))
    (hκ : IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) g0 κ) (y : (R.HV i t).H) :
    ∃ y' : (R.HV i t).H, (∀ h, (R.HV i t).e y' h = (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ)⁻¹ •
        (R.HV i t).e y (h * (finHom (Vc D i)).rangeRestrict κ)) ∧
      ∀ h, R.extV i t y' h = (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ)⁻¹ • R.extV i t y (h * κ) := by
  obtain ⟨y', hy', -⟩ := GlobalTheory.RowClassSum.exists_translate (Vc D i) (R.βV i) (R.datVt i t) (R.cV i) (hR.models.cV i)
    (R.HV i t) _ (R.B.L i t).pres.reps (hR.models.HV i t) g0 κ hκ y
  have hc0 : levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ ≠ 0 := levChi_ne_zero _ _
  refine ⟨y', hy', fun h => ?_⟩
  have e := GlobalTheory.ThetaProjEquiv.extV_shift R hR.models.cV i t κ hκ.1 _ hc0 y y' hy' h
  rw [LinearMap.map_smul, Pi.smul_apply] at e
  rw [← e, smul_smul, inv_mul_cancel₀ hc0, one_smul]

set_option maxHeartbeats 4000000 in

/- English proof (translation)
Take `⟨κ', hκ'⟩` from `liftsW_of_core R F hR i (R.eG g)`. Use function extensionality and compare the values at `x`. Conclude with `(GlobalTheory.ThetaProjEquiv.thF_shift_core R F hR i t (R.eG g) κ κ' hκ hκ'.1 y y' _ (levChi_ne_zero _ _) (GlobalTheory.T.weilAction_liftPair_stepVector_invLevelChar R hR.lev hR.models.inf hR.thP.ωP hR.thP.vP i t (R.eG g) κ κ' hκ hκ') hy v x).trans (GlobalTheory.ThetaProjEquiv.fi …`.
-/
theorem thF_translate_low (hR : GlobalTheory.Hk3.Core R F) (i : Fin D.R.m) (t : T) (g : G) (κ : GA D (Vc D i))
    (hκ : IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) (R.eG g) κ) (y y' : (R.HV i t).H)
    (hy : ∀ h, (R.HV i t).e y' h = (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ)⁻¹ •
        (R.HV i t).e y (h * (finHom (Vc D i)).rangeRestrict κ))
    (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) :
    R.thF i t y' (fun ρ => v ρ) = actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) (R.thF i t y (fun ρ => v ρ)) := by
  obtain ⟨κ', hκ'⟩ := liftsW_of_core R F hR i (R.eG g)
  funext x
  exact (GlobalTheory.ThetaProjEquiv.thF_shift_core R F hR i t (R.eG g) κ κ' hκ hκ'.1 y y' _ (levChi_ne_zero _ _)
    (GlobalTheory.T.weilAction_liftPair_stepVector_invLevelChar R hR.lev hR.models.inf hR.thP.ωP hR.thP.vP i t (R.eG g) κ κ' hκ hκ') hy v x).trans
    (GlobalTheory.ThetaProjEquiv.finiteGroup_acts_by_lift_translation_principalType R i (R.eG g) κ' hκ' _ (GlobalTheory.ThetaProjEquiv.thF_type R hR.thP.thF_mem i t y _) x).symm

set_option maxHeartbeats 4000000 in

/- English proof (translation)
Take `⟨thP, hthP, hthF⟩` from `hP.thF i t`. Use function extensionality and compare the values at `w`. Use `((congrFun (hthF _ v) w).trans (hthP.eq _ (PiTensorProduct.tprod ℂ v) w)).trans ?_` and prove the remaining obligations. Use `Eq.trans ?_ ((congrFun (hthF y v) w).trans (hthP.eq _ (PiTensorProduct.tprod ℂ v) w)).symm` and prove the remaining obligations. Establish `e1 : (((R.extV i t).rangeRestrict z : LinearMap.range (R.extV i t)) : GA D (Vc D i) → (R.cV i).W) = R.extV i t y` using `hz`.

Establish `e2 : (((R.extV i t).rangeRestrict y : LinearMap.range (R.extV i t)) : GA D (Vc D i) → (R.cV i).W) = R.extV i t y` using `rfl`. Unfold `Formalism.IndefR.Lift.thetaPInt`. Rewrite using `[e1, e2]`.
-/
theorem thF_low_eq (hP : R.IsThP) (i : Fin D.R.m) (t : T) (y z : (R.HV i t).H) (hz : R.extV i t z = R.extV i t y)
    (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) : R.thF i t z (fun ρ => v ρ) = R.thF i t y (fun ρ => v ρ) := by
  obtain ⟨thP, hthP, hthF⟩ := hP.thF i t
  funext w
  refine ((congrFun (hthF _ v) w).trans (hthP.eq _ (PiTensorProduct.tprod ℂ v) w)).trans ?_
  refine Eq.trans ?_ ((congrFun (hthF y v) w).trans (hthP.eq _ (PiTensorProduct.tprod ℂ v) w)).symm
  have e1 : (((R.extV i t).rangeRestrict z : LinearMap.range (R.extV i t)) : GA D (Vc D i) → (R.cV i).W) =
      R.extV i t y := hz
  have e2 : (((R.extV i t).rangeRestrict y : LinearMap.range (R.extV i t)) : GA D (Vc D i) → (R.cV i).W) =
      R.extV i t y := rfl
  unfold Formalism.IndefR.Lift.thetaPInt
  rw [e1, e2]

set_option maxHeartbeats 4000000 in

/- English proof (translation)
Unfold `RealDat.eWf gaL`. Rewrite using `[LinearMap.sum_apply]`. Both sides reduce to the same expression.
-/
theorem eWf_apply_sum (i : Fin D.R.m) (f : GA D (Wc D i) → ℂ) :
    R.eWf i (sg0 D A) f = ∑ g, RealDat.eC (A := A) (sg0 D A) g • actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) f := by
  unfold RealDat.eWf gaL
  rw [LinearMap.sum_apply]
  rfl

end GlobalTheory.GoodLift

namespace GlobalTheory.GoodLift

set_option maxHeartbeats 8000000 in

/- English proof (translation)
Introduce `D G _ _ Pl0 T A Ks _ _ _ R F hG _ i t y hy`. Establish `hR` using `hG.core`. Establish `hLV` using `liftsV_of_core R F hR i t`. Use `choose yg hyg hext using fun g : G => translate_of_core R F hR i t (R.eG g) _ (hLV g).choose_spec y`. Establish `hz : R.extV i t (∑ g, RealDat.eC (A` using `A) (sg0 D A) g • yg g) = R.extV i t y := sum_translates (R.extV i t) y yg _ _ (fun g => (hLV g).choose) hext (fun l h => (gaL_apply_choose (Vc D i) (R.βV i) (R.datVt i t) R.eG _ hLV _ h).symm.trans (congrFun (hy l) h))`.

Establish `hmem : (R.HW i (sg0 D A)).e (R.thG i t y) ∈ R.Wall i (sg0 D A)`. Rewrite using `[← (hR.models.HW i (sg0 D A)).2.1]`. Conclude with `⟨_, rfl⟩`. Use `sub_eq_zero.1 (GlobalTheory.LiftRows.spanP_of_given R F hG i _ (Submodule.sub_mem _ hmem (hR.thP.thF_mem i t y)) fun v => ?_)` and prove the remaining obligations. Use `sub_eq_zero.2 ?_` and prove the remaining obligations.

Rewrite using `[hR.thP.thG i t y]`. Use `show R.eWf i (sg0 D A) (R.thF i t y (fun ρ => v ρ)) = _`. Rewrite using `[eWf_apply_sum R i]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[thF_translate_low R F hR i t g _ (hLV g).choose_spec y (yg g) (hyg g) v]`.

Use `_ = R.thF i t (∑ g, RealDat.eC (A := A) (sg0 D A) g • yg g) (fun ρ => v ρ) := by`. Rewrite using `[map_sum, MultilinearMap.sum_apply]`. Simplify using `only [map_smul, MultilinearMap.smul_apply]`. Use `_ = R.thF i t y (fun ρ => v ρ) := thF_low_eq R hR.thP i t y _ hz v`.
-/
theorem goodMem_of_given : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A),
    GlobalTheory.LiftRows.Given R F → R.FullP → ∀ i t, GoodMem R i t := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG _ i t y hy
  have hR := hG.core
  have hLV := liftsV_of_core R F hR i t
  choose yg hyg hext using fun g : G => translate_of_core R F hR i t (R.eG g) _ (hLV g).choose_spec y
  have hz : R.extV i t (∑ g, RealDat.eC (A := A) (sg0 D A) g • yg g) = R.extV i t y :=
    sum_translates (R.extV i t) y yg _ _ (fun g => (hLV g).choose) hext
      (fun l h => (gaL_apply_choose (Vc D i) (R.βV i) (R.datVt i t) R.eG _ hLV _ h).symm.trans (congrFun (hy l) h))
  have hmem : (R.HW i (sg0 D A)).e (R.thG i t y) ∈ R.Wall i (sg0 D A) := by
    rw [← (hR.models.HW i (sg0 D A)).2.1]; exact ⟨_, rfl⟩
  refine sub_eq_zero.1 (GlobalTheory.LiftRows.spanP_of_given R F hG i _ (Submodule.sub_mem _ hmem (hR.thP.thF_mem i t y))
    fun v => ?_)
  refine sub_eq_zero.2 ?_
  rw [hR.thP.thG i t y]
  show R.eWf i (sg0 D A) (R.thF i t y (fun ρ => v ρ)) = _
  rw [eWf_apply_sum R i]
  calc ∑ g, RealDat.eC (A := A) (sg0 D A) g •
        actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) (R.thF i t y (fun ρ => v ρ))
      = ∑ g, RealDat.eC (A := A) (sg0 D A) g • R.thF i t (yg g) (fun ρ => v ρ) :=
        Finset.sum_congr rfl fun g _ => by
          rw [thF_translate_low R F hR i t g _ (hLV g).choose_spec y (yg g) (hyg g) v]
    _ = R.thF i t (∑ g, RealDat.eC (A := A) (sg0 D A) g • yg g) (fun ρ => v ρ) := by
        rw [map_sum, MultilinearMap.sum_apply]
        simp only [map_smul, MultilinearMap.smul_apply]
    _ = R.thF i t y (fun ρ => v ρ) := thF_low_eq R hR.thP i t y _ hz v

end GlobalTheory.GoodLift
