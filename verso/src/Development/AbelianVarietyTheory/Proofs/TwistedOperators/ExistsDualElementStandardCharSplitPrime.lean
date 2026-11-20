import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousSingleAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousTraceMul
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdditiveCharConductorExists
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEqMulOfResSNeOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNsmulMemStdHom
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SuppInd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LocalIntegralGL
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
open Formalism.L2.DIV (kP Pl LevelP)
open Classical

noncomputable section

set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.SplitDualElt

open GlobalTheory.IdemModTwo GlobalTheory.SplitChart

variable {D : D7}

def lift (D : D7) (r : Formalism.IndefR.Datum.EAf D) : AE D :=
  GlobalTheory.LatticeStable.liftFin D ((Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E).symm r)

/- English proof (translation)
The claim follows from `GlobalTheory.AdForm.toEAf_liftFin r`.
-/
theorem toEAf_lift (r : Formalism.IndefR.Datum.EAf D) : toEAf D (lift D r) = r := GlobalTheory.AdForm.toEAf_liftFin r

/- English proof (translation)
Unfold `lift`. Rewrite using `[map_add, map_add]`.
-/
theorem lift_add (r s : Formalism.IndefR.Datum.EAf D) : lift D (r + s) = lift D r + lift D s := by
  unfold lift
  rw [map_add, map_add]

/- English proof (translation)
Rewrite `h` using `[GlobalTheory.AdForm.toEAf_eq_comm]`. Conclude with `(Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E).injective (h.trans (map_zero _).symm)`.
-/
theorem finPart_eq_zero_of_toEAf {z : AE D} (h : toEAf D z = 0) : finPart D z = 0 := by
  rw [GlobalTheory.AdForm.toEAf_eq_comm] at h
  exact (Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E).injective (h.trans (map_zero _).symm)

/- English proof (translation)
Use `sub_eq_zero.1 (GlobalTheory.LatVac.eq_zero_of_parts _ ?_ ?_)` and prove the remaining obligations. Rewrite using `[RingHom.map_sub, hx, hy, sub_zero]`. Conclude with `finPart_eq_zero_of_toEAf (by rw [RingHom.map_sub, h, sub_self])`.
-/
theorem eq_of_toEAf {x y : AE D} (hx : infPart D x = 0) (hy : infPart D y = 0) (h : toEAf D x = toEAf D y) : x = y := by
  refine sub_eq_zero.1 (GlobalTheory.LatVac.eq_zero_of_parts _ ?_ ?_)
  · rw [RingHom.map_sub, hx, hy, sub_zero]
  · exact finPart_eq_zero_of_toEAf (by rw [RingHom.map_sub, h, sub_self])

/- English proof (translation)
Use `show (fstA D.host.F (pairA D.host.F 0 α)) ⊗ₜ[D.host.F] (1 : D.host.E) = 0`. Establish `: fstA D.host.F (pairA D.host.F 0 α) = 0` using `rfl`. Rewrite using `[this, TensorProduct.zero_tmul]`.
-/
theorem infPart_fj (α : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) : infPart D (fj D α) = 0 := by
  show (fstA D.host.F (pairA D.host.F 0 α)) ⊗ₜ[D.host.F] (1 : D.host.E) = 0
  have : fstA D.host.F (pairA D.host.F 0 α) = 0 := rfl
  rw [this, TensorProduct.zero_tmul]

variable {v : HeightOneSpectrum (𝓞 D.host.F)} {e : AE D}

/- English proof (translation)
Rewrite using `[← he.pl_mul, map_mul, infPart_fj, zero_mul]`.
-/
theorem infPart_idem (he : SplitAt D v e) : infPart D e = 0 := by
  rw [← he.pl_mul, map_mul, infPart_fj, zero_mul]

/- English proof (translation)
Rewrite using `[← sub_eq_zero, ← RingHom.map_sub]`. Use `((chart_comp he).2.1 _).2 ?_` and prove the remaining obligations. Use `GlobalTheory.LatVac.eq_zero_of_parts _ ?_ ?_` and prove the remaining obligations. Rewrite using `[RingHom.map_mul, infPart_idem he, zero_mul]`. Rewrite using `[RingHom.map_mul, finPart_eq_zero_of_toEAf (z := x - y) (by rw [RingHom.map_sub, h, sub_self]), mul_zero]`.
-/
theorem comp_eq_of_toEAf (he : SplitAt D v e) {x y : AE D} (h : toEAf D x = toEAf D y) :
    comp he x = comp he y := by
  rw [← sub_eq_zero, ← RingHom.map_sub]
  refine ((chart_comp he).2.1 _).2 ?_
  refine GlobalTheory.LatVac.eq_zero_of_parts _ ?_ ?_
  · rw [RingHom.map_mul, infPart_idem he, zero_mul]
  · rw [RingHom.map_mul, finPart_eq_zero_of_toEAf (z := x - y) (by rw [RingHom.map_sub, h, sub_self]), mul_zero]

/- English proof (translation)
Rewrite using `[GlobalTheory.FinPl.SplitPoint.sec_apply, map_mul, infPart_fj, zero_mul]`.
-/
theorem infPart_sec (a : Fv D.host.F v) : infPart D (GlobalTheory.FinPl.SplitPoint.sec D v e a) = 0 := by
  rw [GlobalTheory.FinPl.SplitPoint.sec_apply, map_mul, infPart_fj, zero_mul]

/- English proof (translation)
Rewrite using `[GlobalTheory.FinPl.SplitPoint.sec_apply, map_mul, comp_fj, comp_self, mul_one, GlobalTheory.SplitIdem.evalV_singleV_same]`.
-/
theorem comp_sec (he : SplitAt D v e) (a : Fv D.host.F v) : comp he (GlobalTheory.FinPl.SplitPoint.sec D v e a) = a := by
  rw [GlobalTheory.FinPl.SplitPoint.sec_apply, map_mul, comp_fj, comp_self, mul_one, GlobalTheory.SplitIdem.evalV_singleV_same]

/- English proof (translation)
Rewrite using `[GlobalTheory.FinPl.SplitPoint.sec_apply, sc_spec he z]`. Both sides reduce to the same expression.
-/
theorem sec_comp (he : SplitAt D v e) (z : AE D) : GlobalTheory.FinPl.SplitPoint.sec D v e (comp he z) = e * z := by
  rw [GlobalTheory.FinPl.SplitPoint.sec_apply, sc_spec he z]
  rfl

/- English proof (translation)
Break down `eq_or_ne x 0 with rfl | h0` into its components or cases. Conclude with `zero_le'`. Rewrite `hx`, the goal using `[← WithZero.exp_log h0]`. Rewrite `hx` using `[← WithZero.exp_zero, WithZero.exp_lt_exp]`. Conclude with `WithZero.exp_le_exp.2 (by omega)`.
-/
theorem le_exp_neg_one {x : WithZero (Multiplicative ℤ)} (hx : x < 1) : x ≤ WithZero.exp (-1) := by
  rcases eq_or_ne x 0 with rfl | h0
  · exact zero_le'
  · rw [← WithZero.exp_log h0] at hx ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hx
    exact WithZero.exp_le_exp.2 (by omega)

end GlobalTheory.SplitDualElt

namespace GlobalTheory.SplitDualElt

open GlobalTheory.IdemModTwo GlobalTheory.SplitChart

variable {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} {e : AE D}

/- English proof (translation)
Rewrite using `[← RingHom.map_mul]`. Conclude with `comp_eq_of_toEAf he (by rw [RingHom.map_mul, toEAf_lift, toEAf_lift, toEAf_lift])`.
-/
theorem comp_lift_mul (he : SplitAt D v e) (r s : Formalism.IndefR.Datum.EAf D) :
    comp he (lift D (r * s)) = comp he (lift D r) * comp he (lift D s) := by
  rw [← RingHom.map_mul]
  exact comp_eq_of_toEAf he (by rw [RingHom.map_mul, toEAf_lift, toEAf_lift, toEAf_lift])

/- English proof (translation)
Rewrite using `[lift_add, RingHom.map_add]`.
-/
theorem comp_lift_add (he : SplitAt D v e) (r s : Formalism.IndefR.Datum.EAf D) :
    comp he (lift D (r + s)) = comp he (lift D r) + comp he (lift D s) := by
  rw [lift_add, RingHom.map_add]

/- English proof (translation)
Establish `hmem : r ∈ Formalism.L2.DIV.idS D.host.F PP.asIdeal`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `(map_eq_zero_iff _ (RingEquiv.ofBijective (Formalism.L2.DIV.cmpS D.host.F PP.asIdeal) (Formalism.L2.DIV.cmpS_bij (F := D.host.F) PP.asIdeal PP.ne_bot)).symm.injective).1 hr`. Establish `he1 : toEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E` using `(GlobalTheory.IdemRes.resS_idem_eq_one D e PP hI).1`. Establish `hint : ∀ s : Formalism.L2.Herm.intAf D.host.F D.host.E, comp he (lift D (s : Formalism.IndefR.Datum.EAf D)) ∈ v.adicCompletionIntegers D.host.F`.

Introduce `s`. Use `GlobalTheory.SplitHecke.isInt_Ov.1 (((chart_comp he).2.2.2 _).1 ?_)` and prove the remaining obligations. Use `GlobalTheory.PlaceDatum.finPart_mem_of_toEAf ?_` and prove the remaining obligations. Rewrite using `[RingHom.map_mul, toEAf_lift]`. Conclude with `mul_mem he1 s.2`.

Set `I : Ideal (Formalism.L2.Herm.intAf D.host.F D.host.E)` to `{ carrier := {s | Valued.v (comp he (lift D (s : Formalism.IndefR.Datum.EAf D))) < 1} add_mem' := by`. Introduce `a b ha hb`. Simplify using `only [Set.mem_setOf_eq, Subring.coe_add, comp_lift_add] at ha hb ⊢`. Conclude with `Valuation.map_add_lt _ ha hb`. Use the proof step `zero_mem' := by`.

Simplify using `only [Set.mem_setOf_eq, ZeroMemClass.coe_zero]`. Establish `: lift D (0 : Formalism.IndefR.Datum.EAf D) = 0`. Establish `h` using `lift_add (D := D) 0 0`. Rewrite `h` using `[add_zero]`. Conclude with `left_eq_add.1 h`.

Rewrite using `[this, RingHom.map_zero, Valuation.map_zero]`. Conclude with `zero_lt_one`. Use the proof step `smul_mem' := by`. Introduce `c a ha`. Simplify using `only [Set.mem_setOf_eq, smul_eq_mul, Subring.coe_mul, comp_lift_mul] at ha ⊢`.

Rewrite using `[Valuation.map_mul]`. Establish `hc` using `hint c`. Rewrite `hc` using `[HeightOneSpectrum.mem_adicCompletionIntegers]`. Conclude with `(mul_le_of_le_one_left' hc).trans_lt ha }`. Establish `hle : Formalism.L2.DIV.idS D.host.F PP.asIdeal ≤ I`.

Use `Ideal.map_le_iff_le_comap.2 fun p hp => ?_` and prove the remaining obligations. Use `show Valued.v (comp he (lift D ((Formalism.L2.DIV.oToS D.host.F D.host.E p : Formalism.L2.Herm.intAf D.host.F D.host.E) : Formalism.IndefR.Datum.EAf D))) < 1`. Break down `eq_or_ne p 0 with rfl | hp0` into its components or cases. Rewrite using `[map_zero]`. Establish `: lift D (0 : Formalism.IndefR.Datum.EAf D) = 0`.

Establish `h` using `lift_add (D := D) 0 0`. Rewrite `h` using `[add_zero]`. Conclude with `left_eq_add.1 h`. Rewrite using `[ZeroMemClass.coe_zero, this, RingHom.map_zero, Valuation.map_zero]`. Conclude with `zero_lt_one`.

Establish `hx : comp he (lift D ((Formalism.L2.DIV.oToS D.host.F D.host.E p : Formalism.L2.Herm.intAf D.host.F D.host.E) : Formalism.IndefR.Datum.EAf D)) = comp he (incA D (p : D.host.E))` using `comp_eq_of_toEAf he (by rw [toEAf_lift, Formalism.L2.DIV.oToS_coe]; rfl)`. Rewrite using `[hx]`. Establish `hx0 : (p : D.host.E) ≠ 0` using `fun h => hp0 (RingOfIntegers.coe_eq_zero_iff.1 h)`. Establish `h1 : comp he (incA D (p : D.host.E)) ∈ v.adicCompletionIntegers D.host.F`. Use `GlobalTheory.SplitHecke.isInt_Ov.1 (((chart_comp he).2.2.2 _).1 ?_)` and prove the remaining obligations.

Use `GlobalTheory.PlaceDatum.finPart_mem_of_toEAf ?_` and prove the remaining obligations. Rewrite using `[RingHom.map_mul]`. Use `mul_mem he1 ?_` and prove the remaining obligations. Establish `: toEAf D (incA D (p : D.host.E)) = ((Formalism.L2.DIV.oToS D.host.F D.host.E p : Formalism.L2.Herm.intAf D.host.F D.host.E) : Formalism.IndefR.Datum.EAf D)` using `by rw [Formalism.L2.DIV.oToS_coe]; rfl`. Rewrite using `[this]`.

Conclude with `Subtype.prop _`. Establish `h2 : comp he (incA D (p : D.host.E)⁻¹) ∉ v.adicCompletionIntegers D.host.F`. Introduce `h`. Conclude with `(hI.2 p hp0).1 hp (((chart_comp he).2.2.2 _).2 (GlobalTheory.SplitHecke.isInt_Ov.2 h))`. Establish `h3 : comp he (incA D (p : D.host.E)) * comp he (incA D (p : D.host.E)⁻¹) = 1`.

Rewrite using `[← RingHom.map_mul, ← RingHom.map_mul, mul_inv_cancel₀ hx0, RingHom.map_one, RingHom.map_one]`. Rewrite `h1`, `h2` using `[HeightOneSpectrum.mem_adicCompletionIntegers]`. Assume the negation of the conclusion as `hn`. Establish `ha : Valued.v (comp he (incA D (p : D.host.E))) = 1` using `le_antisymm h1 (not_lt.1 hn)`. Establish `hb` using `congrArg Valued.v h3`.

Rewrite `hb` using `[Valuation.map_mul, ha, one_mul, Valuation.map_one]`. Conclude with `h2 hb.le`. Conclude with `hle hmem`.
-/
theorem val_lt_one (PP : Pl D.host.E) (hI : Formalism.L2.NTheta.IsIdemAt e PP) (he : SplitAt D v e)
    (r : Formalism.L2.Herm.intAf D.host.F D.host.E) (hr : Formalism.L2.DIV.resS D.host.F PP r = 0) :
    Valued.v (comp he (lift D (r : Formalism.IndefR.Datum.EAf D))) < 1 := by
  have hmem : r ∈ Formalism.L2.DIV.idS D.host.F PP.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    exact (map_eq_zero_iff _ (RingEquiv.ofBijective (Formalism.L2.DIV.cmpS D.host.F PP.asIdeal)
      (Formalism.L2.DIV.cmpS_bij (F := D.host.F) PP.asIdeal PP.ne_bot)).symm.injective).1 hr
  have he1 : toEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := (GlobalTheory.IdemRes.resS_idem_eq_one D e PP hI).1
  have hint : ∀ s : Formalism.L2.Herm.intAf D.host.F D.host.E,
      comp he (lift D (s : Formalism.IndefR.Datum.EAf D)) ∈ v.adicCompletionIntegers D.host.F := by
    intro s
    refine GlobalTheory.SplitHecke.isInt_Ov.1 (((chart_comp he).2.2.2 _).1 ?_)
    refine GlobalTheory.PlaceDatum.finPart_mem_of_toEAf ?_
    rw [RingHom.map_mul, toEAf_lift]
    exact mul_mem he1 s.2
  let I : Ideal (Formalism.L2.Herm.intAf D.host.F D.host.E) :=
    { carrier := {s | Valued.v (comp he (lift D (s : Formalism.IndefR.Datum.EAf D))) < 1}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq, Subring.coe_add, comp_lift_add] at ha hb ⊢
        exact Valuation.map_add_lt _ ha hb
      zero_mem' := by
        simp only [Set.mem_setOf_eq, ZeroMemClass.coe_zero]
        have : lift D (0 : Formalism.IndefR.Datum.EAf D) = 0 := by
          have h := lift_add (D := D) 0 0
          rw [add_zero] at h
          exact left_eq_add.1 h
        rw [this, RingHom.map_zero, Valuation.map_zero]
        exact zero_lt_one
      smul_mem' := by
        intro c a ha
        simp only [Set.mem_setOf_eq, smul_eq_mul, Subring.coe_mul, comp_lift_mul] at ha ⊢
        rw [Valuation.map_mul]
        have hc := hint c
        rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hc
        exact (mul_le_of_le_one_left' hc).trans_lt ha }
  have hle : Formalism.L2.DIV.idS D.host.F PP.asIdeal ≤ I := by
    refine Ideal.map_le_iff_le_comap.2 fun p hp => ?_
    show Valued.v (comp he (lift D ((Formalism.L2.DIV.oToS D.host.F D.host.E p : Formalism.L2.Herm.intAf D.host.F D.host.E) :
      Formalism.IndefR.Datum.EAf D))) < 1
    rcases eq_or_ne p 0 with rfl | hp0
    · rw [map_zero]
      have : lift D (0 : Formalism.IndefR.Datum.EAf D) = 0 := by
        have h := lift_add (D := D) 0 0
        rw [add_zero] at h
        exact left_eq_add.1 h
      rw [ZeroMemClass.coe_zero, this, RingHom.map_zero, Valuation.map_zero]
      exact zero_lt_one
    have hx : comp he (lift D ((Formalism.L2.DIV.oToS D.host.F D.host.E p : Formalism.L2.Herm.intAf D.host.F D.host.E) :
        Formalism.IndefR.Datum.EAf D)) = comp he (incA D (p : D.host.E)) :=
      comp_eq_of_toEAf he (by rw [toEAf_lift, Formalism.L2.DIV.oToS_coe]; rfl)
    rw [hx]
    have hx0 : (p : D.host.E) ≠ 0 := fun h => hp0 (RingOfIntegers.coe_eq_zero_iff.1 h)
    have h1 : comp he (incA D (p : D.host.E)) ∈ v.adicCompletionIntegers D.host.F := by
      refine GlobalTheory.SplitHecke.isInt_Ov.1 (((chart_comp he).2.2.2 _).1 ?_)
      refine GlobalTheory.PlaceDatum.finPart_mem_of_toEAf ?_
      rw [RingHom.map_mul]
      refine mul_mem he1 ?_
      have : toEAf D (incA D (p : D.host.E)) = ((Formalism.L2.DIV.oToS D.host.F D.host.E p : Formalism.L2.Herm.intAf D.host.F D.host.E) :
        Formalism.IndefR.Datum.EAf D) := by rw [Formalism.L2.DIV.oToS_coe]; rfl
      rw [this]
      exact Subtype.prop _
    have h2 : comp he (incA D (p : D.host.E)⁻¹) ∉ v.adicCompletionIntegers D.host.F := by
      intro h
      exact (hI.2 p hp0).1 hp (((chart_comp he).2.2.2 _).2 (GlobalTheory.SplitHecke.isInt_Ov.2 h))
    have h3 : comp he (incA D (p : D.host.E)) * comp he (incA D (p : D.host.E)⁻¹) = 1 := by
      rw [← RingHom.map_mul, ← RingHom.map_mul, mul_inv_cancel₀ hx0, RingHom.map_one, RingHom.map_one]
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h1 h2
    by_contra hn
    have ha : Valued.v (comp he (incA D (p : D.host.E))) = 1 := le_antisymm h1 (not_lt.1 hn)
    have hb := congrArg Valued.v h3
    rw [Valuation.map_mul, ha, one_mul, Valuation.map_one] at hb
    exact h2 hb.le
  exact hle hmem

end GlobalTheory.SplitDualElt

namespace GlobalTheory.SplitDualElt

open GlobalTheory.IdemModTwo GlobalTheory.SplitChart

variable {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} {e : AE D}

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Apply `tmul_one_inj (F := D.host.F) (A := AF D.host.F) (E := D.host.E)` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `algebraMap (AF D.host.F) (AE D) (Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * GlobalTheory.FinPl.SplitPoint.sec D v e a)) = fj D (singleV D.host.F v (comp he (incA D D.host.xi0) * a))`. Rewrite using `[GlobalTheory.FockCompare.SymplVal.trace_AE, GlobalTheory.FinPl.SplitPoint.sec_apply]`. Establish `h1 : e * incA D D.host.xi0 = fj D (singleV D.host.F v (comp he (incA D D.host.xi0))) * e` using `sc_spec he _`. Establish `h2 : singleV D.host.F v a * singleV D.host.F v (comp he (incA D D.host.xi0)) * singleV D.host.F v 1 = singleV D.host.F v (comp he (incA D D.host.xi0) * a)`.

Rewrite using `[singleV_mul D v _ (singleV D.host.F v a), GlobalTheory.SplitIdem.evalV_singleV_same, singleV_mul D v 1, GlobalTheory.SplitIdem.evalV_singleV_same, mul_one, mul_comm]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_comm (incA D D.host.xi0), mul_assoc]`. Use `_ = fj D (singleV D.host.F v a) * fj D (singleV D.host.F v (comp he (incA D D.host.xi0))) * (e + cA D e) := by`. Rewrite using `[h1, RingHom.map_mul, RingHom.map_mul, cA_fj, cA_fj, ← mul_add, ← mul_add, ← mul_assoc]`.

Use `_ = fj D (singleV D.host.F v (comp he (incA D D.host.xi0) * a)) := by`. Establish `h3 : e + cA D e = fj D (singleV D.host.F v 1)` using `he.2.2`. Rewrite using `[h3, ← map_mul (fj D) (singleV D.host.F v a), ← map_mul (fj D) (singleV D.host.F v a * singleV D.host.F v (comp he (incA D D.host.xi0))) (singleV D.host.F v 1), h2]`.
-/
theorem trace_generator_split_section (he : SplitAt D v e) (a : Fv D.host.F v) :
    Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * GlobalTheory.FinPl.SplitPoint.sec D v e a) =
      pairA D.host.F 0 (singleV D.host.F v (comp he (incA D D.host.xi0) * a)) := by
  apply tmul_one_inj (F := D.host.F) (A := AF D.host.F) (E := D.host.E)
  change algebraMap (AF D.host.F) (AE D) (Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * GlobalTheory.FinPl.SplitPoint.sec D v e a)) =
    fj D (singleV D.host.F v (comp he (incA D D.host.xi0) * a))
  rw [GlobalTheory.FockCompare.SymplVal.trace_AE, GlobalTheory.FinPl.SplitPoint.sec_apply]
  have h1 : e * incA D D.host.xi0 = fj D (singleV D.host.F v (comp he (incA D D.host.xi0))) * e := sc_spec he _
  have h2 : singleV D.host.F v a * singleV D.host.F v (comp he (incA D D.host.xi0)) * singleV D.host.F v 1 =
      singleV D.host.F v (comp he (incA D D.host.xi0) * a) := by
    rw [singleV_mul D v _ (singleV D.host.F v a), GlobalTheory.SplitIdem.evalV_singleV_same, singleV_mul D v 1,
      GlobalTheory.SplitIdem.evalV_singleV_same, mul_one, mul_comm]
  calc incA D D.host.xi0 * (fj D (singleV D.host.F v a) * e) + cA D (incA D D.host.xi0 * (fj D (singleV D.host.F v a) * e))
      = fj D (singleV D.host.F v a) * (e * incA D D.host.xi0) +
          cA D (fj D (singleV D.host.F v a) * (e * incA D D.host.xi0)) := by
        rw [mul_comm (incA D D.host.xi0), mul_assoc]
    _ = fj D (singleV D.host.F v a) * fj D (singleV D.host.F v (comp he (incA D D.host.xi0))) * (e + cA D e) := by
        rw [h1, RingHom.map_mul, RingHom.map_mul, cA_fj, cA_fj, ← mul_add, ← mul_add, ← mul_assoc]
    _ = fj D (singleV D.host.F v (comp he (incA D D.host.xi0) * a)) := by
        have h3 : e + cA D e = fj D (singleV D.host.F v 1) := he.2.2
        rw [h3, ← map_mul (fj D) (singleV D.host.F v a), ← map_mul (fj D) (singleV D.host.F v a * singleV D.host.F v (comp he (incA D D.host.xi0))) (singleV D.host.F v 1), h2]

end GlobalTheory.SplitDualElt

namespace GlobalTheory.SplitDualElt

open GlobalTheory.IdemModTwo GlobalTheory.SplitChart

/- English proof (translation)
Take `⟨n, hn⟩` from `GlobalTheory.CharConductor.exists_exponent_of_valued χ hχ hne`. Take `⟨ϖ, hϖ⟩` from `HeightOneSpectrum.valuation_exists_uniformizer F v`. Establish `hv : Valued.v (ϖ : v.adicCompletion F) = WithZero.exp (-1)`. Rewrite using `[HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hϖ]`. Use `set t₀ : v.adicCompletion F := (ϖ : v.adicCompletion F) ^ (-(n + 1)) with ht₀`.

Establish `hvt : Valued.v t₀ = WithZero.exp (n + 1)`. Rewrite using `[ht₀, map_zpow₀, hv, ← WithZero.exp_zsmul]`. Use `congr 1`. Simplify using the standard rewrite rules. Establish `hnot : ¬ Valued.v t₀ ≤ WithZero.exp n`.

Rewrite using `[hvt, WithZero.exp_le_exp]`. Use linear arithmetic over natural numbers and integers. Choose the witnesses or unpack the hypotheses as in `⟨s, hs1, hs⟩ : ∃ s : v.adicCompletion F, Valued.v s ≤ 1 ∧ χ (t₀ * s) ≠ 1 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`.

Conclude with `hnot ((hn t₀).1 h)`. Use `⟨t₀ * s, hs, fun m hm => ?_⟩` and prove the remaining obligations. Establish `hm'` using `le_exp_neg_one hm`. Establish `hle : Valued.v (t₀ * s * m) ≤ WithZero.exp n`. Rewrite using `[map_mul, map_mul, hvt]`.

Combine the equalities or inequalities in the displayed calculation. Use `(hn (t₀ * s * m)).2 hle 1 (by rw [map_one])` as an intermediate fact. Rewrite `this` using `[mul_one]`. Then use the resulting hypothesis.
-/
theorem exists_edge {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (χ : AddChar (v.adicCompletion F) ℂ)
    (hχ : Continuous χ) (hne : ∃ a, χ a ≠ 1) :
    ∃ c₀ : v.adicCompletion F, χ c₀ ≠ 1 ∧ ∀ m : v.adicCompletion F, Valued.v m < 1 → χ (c₀ * m) = 1 := by
  obtain ⟨n, hn⟩ := GlobalTheory.CharConductor.exists_exponent_of_valued χ hχ hne
  obtain ⟨ϖ, hϖ⟩ := HeightOneSpectrum.valuation_exists_uniformizer F v
  have hv : Valued.v (ϖ : v.adicCompletion F) = WithZero.exp (-1) := by
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hϖ]
  set t₀ : v.adicCompletion F := (ϖ : v.adicCompletion F) ^ (-(n + 1)) with ht₀
  have hvt : Valued.v t₀ = WithZero.exp (n + 1) := by
    rw [ht₀, map_zpow₀, hv, ← WithZero.exp_zsmul]
    congr 1
    simp
  have hnot : ¬ Valued.v t₀ ≤ WithZero.exp n := by
    rw [hvt, WithZero.exp_le_exp]
    omega
  obtain ⟨s, hs1, hs⟩ : ∃ s : v.adicCompletion F, Valued.v s ≤ 1 ∧ χ (t₀ * s) ≠ 1 := by
    by_contra h
    push_neg at h
    exact hnot ((hn t₀).1 h)
  refine ⟨t₀ * s, hs, fun m hm => ?_⟩
  have hm' := le_exp_neg_one hm
  have hle : Valued.v (t₀ * s * m) ≤ WithZero.exp n := by
    rw [map_mul, map_mul, hvt]
    calc WithZero.exp (n + 1) * Valued.v s * Valued.v m ≤ WithZero.exp (n + 1) * 1 * WithZero.exp (-1) :=
          mul_le_mul' (mul_le_mul' le_rfl hs1) hm'
      _ = WithZero.exp n := by rw [mul_one, ← WithZero.exp_add]; congr 1; ring
  have := (hn (t₀ * s * m)).2 hle 1 (by rw [map_one])
  rwa [mul_one] at this

end GlobalTheory.SplitDualElt

namespace GlobalTheory.SplitDualElt

open GlobalTheory.IdemModTwo GlobalTheory.SplitChart

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `D ψ hψ e PP hI`. Take `⟨v, he⟩` from `(isSplitIdem_iff e).1 hI.1`. Set `T : AE D →+ AF D.host.F` to `(Algebra.trace (AF D.host.F) (AE D)).toAddMonoidHom.comp (AddMonoidHom.mulLeft (incA D D.host.xi0))`. Set `χ : AddChar (Fv D.host.F v) ℂ` to `ψ.compAddMonoidHom (T.comp (GlobalTheory.FinPl.SplitPoint.sec D v e))`. Establish `hχa : ∀ a, χ a = ψ (Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * GlobalTheory.FinPl.SplitPoint.sec D v e a))` using `fun a => rfl`.

Establish `hχ : Continuous χ` using `hψ.1.1.comp ((GlobalTheory.Core.Rk.SplitPsi.continuous_trace_mul D (incA D D.host.xi0)).comp GlobalTheory.FinPl.SplitPoint.continuous_sec)`. Establish `hκ : comp he (incA D D.host.xi0) ≠ 0`. Introduce `h0`. Establish `h1 : comp he (incA D D.host.xi0) * comp he (incA D D.host.xi0⁻¹) = 1`. Rewrite using `[← RingHom.map_mul, ← RingHom.map_mul, mul_inv_cancel₀ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D), RingHom.map_one, RingHom.map_one]`.

Rewrite `h1` using `[h0, zero_mul]`. Conclude with `zero_ne_one h1`. Establish `hne : ∃ a, χ a ≠ 1`. Take `⟨y, hy⟩` from `GlobalTheory.StdCharLocal.psiV_ne_one D ψ hψ v`. Use `⟨(comp he (incA D D.host.xi0))⁻¹ * y, ?_⟩` and prove the remaining obligations.

Rewrite using `[hχa, trace_generator_split_section he, mul_inv_cancel_left₀ hκ]`. Conclude with `hy`. Take `⟨c₀, hc₀, hc₀m⟩` from `exists_edge v χ hχ hne`. Use `⟨toEAf D (GlobalTheory.FinPl.SplitPoint.sec D v e c₀), ?_, ?_⟩` and prove the remaining obligations. Introduce `Z hZ r hr hZr`.

Establish `hZ' : Z = GlobalTheory.FinPl.SplitPoint.sec D v e c₀ * lift D (r : Formalism.IndefR.Datum.EAf D)` using `eq_of_toEAf hZ (by rw [RingHom.map_mul, infPart_sec, zero_mul]) (by rw [hZr, RingHom.map_mul, toEAf_lift])`. Establish `heZ : e * Z = Z`. Rewrite using `[hZ', GlobalTheory.FinPl.SplitPoint.sec_apply]`. Generalize the expression as in `fj D (singleV D.host.F v c₀) = f`. Generalize the expression as in `lift D (r : Formalism.IndefR.Datum.EAf D) = R`.

Rewrite using `[← mul_assoc, ← mul_assoc, mul_comm e f, mul_assoc f e e, he.1]`. Establish `hsec : GlobalTheory.FinPl.SplitPoint.sec D v e (comp he Z) = Z`. Rewrite using `[sec_comp he, heZ]`. Establish `hcomp : comp he Z = c₀ * comp he (lift D (r : Formalism.IndefR.Datum.EAf D))`. Rewrite using `[hZ', RingHom.map_mul, comp_sec he]`.

Establish `h` using `hc₀m _ (val_lt_one PP hI he r hr)`. Rewrite `h` using `[← hcomp, hχa, hsec]`. Conclude with `h`. Introduce `Z hZ hZc`. Establish `hZ' : Z = GlobalTheory.FinPl.SplitPoint.sec D v e c₀` using `eq_of_toEAf hZ (infPart_sec c₀) hZc`.

Rewrite using `[hZ', ← hχa]`. Conclude with `hc₀`.
-/
theorem exists_dual_elt : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (e₁ : AE D) (PP : Pl D.host.E), Formalism.L2.NTheta.IsIdemAt e₁ PP → ∃ c : Datum.EAf D, (∀ Z : AE D, infPart D Z = 0 → ∀ r : Formalism.L2.Herm.intAf D.host.F D.host.E, resS D.host.F PP r = 0 → toEAf D Z = c * r → ψ (Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * Z)) = 1) ∧ (∀ Z : AE D, infPart D Z = 0 → toEAf D Z = c → ψ (Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * Z)) ≠ 1) := by
  intro D ψ hψ e PP hI
  obtain ⟨v, he⟩ := (isSplitIdem_iff e).1 hI.1
  let T : AE D →+ AF D.host.F :=
    (Algebra.trace (AF D.host.F) (AE D)).toAddMonoidHom.comp (AddMonoidHom.mulLeft (incA D D.host.xi0))
  let χ : AddChar (Fv D.host.F v) ℂ := ψ.compAddMonoidHom (T.comp (GlobalTheory.FinPl.SplitPoint.sec D v e))
  have hχa : ∀ a, χ a = ψ (Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * GlobalTheory.FinPl.SplitPoint.sec D v e a)) :=
    fun a => rfl
  have hχ : Continuous χ :=
    hψ.1.1.comp ((GlobalTheory.Core.Rk.SplitPsi.continuous_trace_mul D (incA D D.host.xi0)).comp
      GlobalTheory.FinPl.SplitPoint.continuous_sec)
  have hκ : comp he (incA D D.host.xi0) ≠ 0 := by
    intro h0
    have h1 : comp he (incA D D.host.xi0) * comp he (incA D D.host.xi0⁻¹) = 1 := by
      rw [← RingHom.map_mul, ← RingHom.map_mul, mul_inv_cancel₀ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D), RingHom.map_one,
        RingHom.map_one]
    rw [h0, zero_mul] at h1
    exact zero_ne_one h1
  have hne : ∃ a, χ a ≠ 1 := by
    obtain ⟨y, hy⟩ := GlobalTheory.StdCharLocal.psiV_ne_one D ψ hψ v
    refine ⟨(comp he (incA D D.host.xi0))⁻¹ * y, ?_⟩
    rw [hχa, trace_generator_split_section he, mul_inv_cancel_left₀ hκ]
    exact hy
  obtain ⟨c₀, hc₀, hc₀m⟩ := exists_edge v χ hχ hne
  refine ⟨toEAf D (GlobalTheory.FinPl.SplitPoint.sec D v e c₀), ?_, ?_⟩
  · intro Z hZ r hr hZr
    have hZ' : Z = GlobalTheory.FinPl.SplitPoint.sec D v e c₀ * lift D (r : Formalism.IndefR.Datum.EAf D) :=
      eq_of_toEAf hZ (by rw [RingHom.map_mul, infPart_sec, zero_mul])
        (by rw [hZr, RingHom.map_mul, toEAf_lift])
    have heZ : e * Z = Z := by
      rw [hZ', GlobalTheory.FinPl.SplitPoint.sec_apply]
      generalize fj D (singleV D.host.F v c₀) = f
      generalize lift D (r : Formalism.IndefR.Datum.EAf D) = R
      rw [← mul_assoc, ← mul_assoc, mul_comm e f, mul_assoc f e e, he.1]
    have hsec : GlobalTheory.FinPl.SplitPoint.sec D v e (comp he Z) = Z := by
      rw [sec_comp he, heZ]
    have hcomp : comp he Z = c₀ * comp he (lift D (r : Formalism.IndefR.Datum.EAf D)) := by
      rw [hZ', RingHom.map_mul, comp_sec he]
    have h := hc₀m _ (val_lt_one PP hI he r hr)
    rw [← hcomp, hχa, hsec] at h
    exact h
  · intro Z hZ hZc
    have hZ' : Z = GlobalTheory.FinPl.SplitPoint.sec D v e c₀ := eq_of_toEAf hZ (infPart_sec c₀) hZc
    rw [hZ', ← hχa]
    exact hc₀

end GlobalTheory.SplitDualElt
