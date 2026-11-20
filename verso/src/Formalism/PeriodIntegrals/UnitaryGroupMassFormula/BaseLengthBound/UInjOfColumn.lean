import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BaseLengthBound.EqZeroOfOrdTop

noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.EtaleWeightGaps

namespace PoleLengthBounds

/- English proof (translation)
Unfold `UInj`. Introduce `D B P j X ka wL wF G la Q S CRm T c hOk hw α b hb`. Establish `hC : Q.InCurve` using `hOk.2.1`. Establish `hU` using `isUnif_of_curve Q hC`. Establish `: ∀ ζ : PtsG G la, IsDVRAt ζ` using `fun ζ => isDVRAt_of_curve Q hC ζ`.

Establish `hco : (coord Q.e b : OsK X la G.w) = 0`. Use `eq_zero_of_ord_top hU fun ζ => ?_` and prove the remaining obligations. Take `⟨jj, hjj⟩` from `(hCol G la Q S CRm T c hOk hw ζ).2`. Establish `h1` using `congrArg (ordV (unifO X la G.N) ζ Q.e Q.c) (hb jj)`. Rewrite `h1` using `[ordV_smul Q.c ζ hU hC.2.2, ord_uC_eq_zero Q hC ζ jj α hjj, zero_add, ordV_zero Q.c ζ hU hC.2.2, ordV, WithTop.add_eq_top]`.

Break down `h1 with h1 | h1` into its components or cases. Conclude with `h1`. Conclude with `absurd h1 WithTop.coe_ne_top`. Rewrite using `[← coord_smul_self hC.2.2 b, hco, zero_smul]`.
-/
theorem uInj_of_column (hCol : Column) : UInj := by
  unfold UInj
  intro D B P j X ka wL wF G la Q S CRm T c hOk hw α b hb
  have hC : Q.InCurve := hOk.2.1
  have hU := isUnif_of_curve Q hC
  have : ∀ ζ : PtsG G la, IsDVRAt ζ := fun ζ => isDVRAt_of_curve Q hC ζ
  have hco : (coord Q.e b : OsK X la G.w) = 0 := by
    refine eq_zero_of_ord_top hU fun ζ => ?_
    obtain ⟨jj, hjj⟩ := (hCol G la Q S CRm T c hOk hw ζ).2
    have h1 := congrArg (ordV (unifO X la G.N) ζ Q.e Q.c) (hb jj)
    rw [ordV_smul Q.c ζ hU hC.2.2, ord_uC_eq_zero Q hC ζ jj α hjj, zero_add,
      ordV_zero Q.c ζ hU hC.2.2, ordV, WithTop.add_eq_top] at h1
    rcases h1 with h1 | h1
    · exact h1
    · exact absurd h1 WithTop.coe_ne_top
  rw [← coord_smul_self hC.2.2 b, hco, zero_smul]

end PoleLengthBounds
