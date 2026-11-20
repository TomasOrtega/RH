import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.IsoWGen
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.BordMulSM
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.LeftInvResHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.HRSmulERight
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.AriEta

noncomputable section

namespace PI.OmVf

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain PI.OmLocU PI.OmVd
open Formalism.L2.SG.Pf.NcVal.OmVSt Formalism.L2.SG.Pf.NcVal.OmVSt.OmW Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.TypedSets
open scoped TensorProduct

variable {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

/- English proof (translation)
Simplify using `[zi]`.
-/
theorem zi_val' : (zi (D := D)).val = D.R.rS := by simp [zi]

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h => Fin.ext (by rw [h, zi_val']), fun h => by rw [h, zi_val']⟩`.
-/
theorem zi_iff (i : Fin (D.R.rS + 1 + D.R.rS)) : i.val = D.R.rS ↔ i = zi (D := D) :=
  ⟨fun h => Fin.ext (by rw [h, zi_val']), fun h => by rw [h, zi_val']⟩

/- English proof (translation)
Rewrite using `[omVGram_holds X u' v]`. Simplify using `only [localGramMatrixFrame, Matrix.map_apply]`. Apply the tactic sequence `rw [gramE_entry X u' i k, apply_ite (inclR (F := X.B.I.F) (Fv X.B.I.F v)), map_zero]`.
-/
theorem gram_yTup (v : PlX X) (i k : Fin (D.R.rS + 1 + D.R.rS)) :
    gramR (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J (yTup X u' v) i k =
      if k = piv D.R.rS i then inclR (F := X.B.I.F) (Fv X.B.I.F v) (cD X u' i) else 0 := by
  rw [omVGram_holds X u' v]
  simp only [localGramMatrixFrame, Matrix.map_apply]
  rw [gramE_entry X u' i k, apply_ite (inclR (F := X.B.I.F) (Fv X.B.I.F v)), map_zero]

/- English proof (translation)
Establish `h : (zi (D` using `D)).val = D.R.rS := zi_val'`. Simplify using `only [cD, h, if_true, map_neg, map_natCast, PI.OmLocU.NormOneUnitFixedPoints.sc_eq]`.
-/
theorem inclR_apply' (v : PlX X) :
    inclR (F := X.B.I.F) (Fv X.B.I.F v) (cD X u' (zi (D := D))) =
      sc (E := X.B.I.E) v (-((Tw u' : ℕ) : Fv X.B.I.F v)) := by
  have h : (zi (D := D)).val = D.R.rS := zi_val'
  simp only [cD, h, if_true, map_neg, map_natCast, PI.OmLocU.NormOneUnitFixedPoints.sc_eq]

/- English proof (translation)
Establish `h` using `Formalism.L2.SG.Pf.NcVal.AriEta.val_int v ((Tw u' : ℕ) : 𝓞 X.B.I.F)`. Establish `e : (((((Tw u' : ℕ) : 𝓞 X.B.I.F) : X.B.I.F) : v.adicCompletion X.B.I.F)) = ((Tw u' : ℕ) : Fv X.B.I.F v)`. Rewrite using `[show (((Tw u' : ℕ) : 𝓞 X.B.I.F) : X.B.I.F) = ((Tw u' : ℕ) : X.B.I.F) by simp]`. Conclude with `map_natCast (algebraMap X.B.I.F (v.adicCompletion X.B.I.F)) _`. Rewrite `h` using `[e]`.

Conclude with `neg_mem ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 h)`.
-/
theorem gam_int (v : PlX X) : -((Tw u' : ℕ) : Fv X.B.I.F v) ∈ v.adicCompletionIntegers X.B.I.F := by
  have h := Formalism.L2.SG.Pf.NcVal.AriEta.val_int v ((Tw u' : ℕ) : 𝓞 X.B.I.F)
  have e : (((((Tw u' : ℕ) : 𝓞 X.B.I.F) : X.B.I.F) : v.adicCompletion X.B.I.F)) = ((Tw u' : ℕ) : Fv X.B.I.F v) := by
    rw [show (((Tw u' : ℕ) : 𝓞 X.B.I.F) : X.B.I.F) = ((Tw u' : ℕ) : X.B.I.F) by simp]
    exact map_natCast (algebraMap X.B.I.F (v.adicCompletion X.B.I.F)) _
  rw [e] at h
  exact neg_mem ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 h)

/- English proof (translation)
Establish `h` using `Formalism.L2.SG.Pf.NcVal.AriEta.val_int_lt v ((Tw u' : ℕ) : 𝓞 X.B.I.F) hv`. Establish `e : (((((Tw u' : ℕ) : 𝓞 X.B.I.F) : X.B.I.F) : v.adicCompletion X.B.I.F)) = ((Tw u' : ℕ) : Fv X.B.I.F v)`. Rewrite using `[show (((Tw u' : ℕ) : 𝓞 X.B.I.F) : X.B.I.F) = ((Tw u' : ℕ) : X.B.I.F) by simp]`. Conclude with `map_natCast (algebraMap X.B.I.F (v.adicCompletion X.B.I.F)) _`. Rewrite `h` using `[e]`.

Rewrite using `[Valuation.map_neg]`. Conclude with `h`.
-/
theorem gam_lt (v : PlX X) (hv : ((Tw u' : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal) :
    Valued.v (-((Tw u' : ℕ) : Fv X.B.I.F v)) < 1 := by
  have h := Formalism.L2.SG.Pf.NcVal.AriEta.val_int_lt v ((Tw u' : ℕ) : 𝓞 X.B.I.F) hv
  have e : (((((Tw u' : ℕ) : 𝓞 X.B.I.F) : X.B.I.F) : v.adicCompletion X.B.I.F)) = ((Tw u' : ℕ) : Fv X.B.I.F v) := by
    rw [show (((Tw u' : ℕ) : 𝓞 X.B.I.F) : X.B.I.F) = ((Tw u' : ℕ) : X.B.I.F) by simp]
    exact map_natCast (algebraMap X.B.I.F (v.adicCompletion X.B.I.F)) _
  rw [e] at h
  rw [Valuation.map_neg]
  exact h

/- English proof (translation)
Use `set γ : Fv X.B.I.F v := -((Tw u' : ℕ) : Fv X.B.I.F v) with hγ`. Establish `hγO` using `gam_int X u' v`. Establish `hgO : sc (E` using `X.B.I.E) v γ ∈ OEv (E := X.B.I.E) v := PI.OmLocU.NormOneUnitFixedPoints.sc_mem v hγO`. Establish `hpz : piv D.R.rS (zi (D` using `D)) = zi (D := D) := pivot_castAdd_last D.R.rS`. Establish `hpe : ∀ i, zi (D` using `D) = piv D.R.rS i ↔ i = zi (D := D) := fun i => ⟨fun h => by rw [← piv_invol D.R.rS i, ← h, hpz], fun h => by rw [h, hpz]⟩`.

Establish `hd : ∀ i, i ≠ zi (D` using `D) → inclR (F := X.B.I.F) (Fv X.B.I.F v) (cD X u' i) = 1 := by`. Introduce `i hi`. Establish `: ¬ i.val = D.R.rS` using `fun h => hi ((zi_iff i).1 h)`. Simplify using `only [cD, this, if_false, map_one]`. Use `isoW_gen X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (yTup X u' v) (zi (D := D)) γ hγO (gam_lt X u' v hv) (fun i => ?_) (primDual_of_left _ _ _ _ _ _ (leftInvO_holds _ _ _ _ _)) ?_` and prove the remaining obligations.

Rewrite using `[gram_yTup]`. Distinguish the cases in `hi : i = zi (D := D)`. Rewrite using `[if_pos ((hpe i).2 hi), if_pos hi, hi, inclR_apply']`. Rewrite using `[if_neg (fun h => hi ((hpe i).1 h)), if_neg hi]`. Use `⟨sM v (piv D.R.rS) (zi (D := D)) (sc (E := X.B.I.E) v γ), fun i j => ?_, bord_mul_sM v _ (piv D.R.rS) (piv_invol D.R.rS) (zi (D := D)) hpz _ (fun i => inclR (F := X.B.I.F) (Fv X.B.I.F v) (cD X u' i)) hd (inclR_apply' X u' v) (gram_yTup X u' v)⟩` and prove the remaining obligations.

Proceed by induction on `i using Fin.lastCases with`. Consider the case `last`. Proceed by induction on `j using Fin.lastCases with`. Consider the case `last => simp only [sM, Fin.snoc_last]`. Conclude with `oEv_neg v hgO`.

Consider the case `cast j`. Simplify using `only [sM, Fin.snoc_last, Fin.snoc_castSucc]`. Use `split_ifs`. Conclude with `oEv_one v`. Conclude with `oEv_zero v`.

Consider the case `cast i`. Proceed by induction on `j using Fin.lastCases with`. Consider the case `last`. Simplify using `only [sM, Fin.snoc_last, Fin.snoc_castSucc]`. Use `split_ifs`.

Conclude with `oEv_one v`. Conclude with `oEv_zero v`. Consider the case `cast j`. Simplify using `only [sM, Fin.snoc_castSucc]`. Use `split_ifs`.

Conclude with `oEv_zero v`. Conclude with `oEv_one v`. Conclude with `oEv_zero v`.
-/
theorem isoW_holds (v : PlX X) (hv : ((Tw u' : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal) :
    IsoW X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS) (yTup X u' v) := by
  classical
  set γ : Fv X.B.I.F v := -((Tw u' : ℕ) : Fv X.B.I.F v) with hγ
  have hγO := gam_int X u' v
  have hgO : sc (E := X.B.I.E) v γ ∈ OEv (E := X.B.I.E) v := PI.OmLocU.NormOneUnitFixedPoints.sc_mem v hγO
  have hpz : piv D.R.rS (zi (D := D)) = zi (D := D) := pivot_castAdd_last D.R.rS
  have hpe : ∀ i, zi (D := D) = piv D.R.rS i ↔ i = zi (D := D) := fun i =>
    ⟨fun h => by rw [← piv_invol D.R.rS i, ← h, hpz], fun h => by rw [h, hpz]⟩
  have hd : ∀ i, i ≠ zi (D := D) → inclR (F := X.B.I.F) (Fv X.B.I.F v) (cD X u' i) = 1 := by
    intro i hi
    have : ¬ i.val = D.R.rS := fun h => hi ((zi_iff i).1 h)
    simp only [cD, this, if_false, map_one]
  refine isoW_gen X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (yTup X u' v) (zi (D := D)) γ hγO (gam_lt X u' v hv)
    (fun i => ?_) (primDual_of_left _ _ _ _ _ _ (leftInvO_holds _ _ _ _ _)) ?_
  · rw [gram_yTup]
    by_cases hi : i = zi (D := D)
    · rw [if_pos ((hpe i).2 hi), if_pos hi, hi, inclR_apply']
    · rw [if_neg (fun h => hi ((hpe i).1 h)), if_neg hi]
  · refine ⟨sM v (piv D.R.rS) (zi (D := D)) (sc (E := X.B.I.E) v γ), fun i j => ?_,
      bord_mul_sM v _ (piv D.R.rS) (piv_invol D.R.rS) (zi (D := D)) hpz _
        (fun i => inclR (F := X.B.I.F) (Fv X.B.I.F v) (cD X u' i)) hd (inclR_apply' X u' v) (gram_yTup X u' v)⟩
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => simp only [sM, Fin.snoc_last]; exact oEv_neg v hgO
      | cast j =>
        simp only [sM, Fin.snoc_last, Fin.snoc_castSucc]
        split_ifs
        · exact oEv_one v
        · exact oEv_zero v
    | cast i =>
      induction j using Fin.lastCases with
      | last =>
        simp only [sM, Fin.snoc_last, Fin.snoc_castSucc]
        split_ifs
        · exact oEv_one v
        · exact oEv_zero v
      | cast j =>
        simp only [sM, Fin.snoc_castSucc]
        split_ifs
        · exact oEv_zero v
        · exact oEv_one v
        · exact oEv_zero v

/- English proof (translation)
The claim follows from `extP_of _ _ _ _ _ _ _ (a_succ_le_n X) (isoExt_of _ _ _ _ _ _ _ (isoW_holds X u' ψ v hv))`.
-/
theorem extP_holds (v : PlX X) (hv : ((Tw u' : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal) :
    ExtP X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS) (yTup X u' v) :=
  extP_of _ _ _ _ _ _ _ (a_succ_le_n X) (isoExt_of _ _ _ _ _ _ _ (isoW_holds X u' ψ v hv))

end PI.OmVf
