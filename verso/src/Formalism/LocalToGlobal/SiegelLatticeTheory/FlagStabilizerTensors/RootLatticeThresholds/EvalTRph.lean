import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.RowsBij
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSchur
import Formalism.SharpRestriction.CuspSpanNormBounds.ExpansionFromLemmaB
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.ProjRows
open scoped InnerProductSpace

namespace Formalism.L2.SG.EvalTRph

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

/- English proof (translation)
Take `⟨d, hd⟩` from `Formalism.MainNotions.BridgeCSchur.fdeg_of_DS (X.B.lam v) (X.B.σ v) (X.ds v)`. Establish `hw : X.B.w v ≠ 0`. Introduce `h0`. Establish `h1` using `(X.low v).1`. Rewrite `h1` using `[h0, norm_zero]`.

Conclude with `zero_ne_one h1`. Establish `e : X.dv v = d` using `Formalism.MainNotions.DiscreteSeriesInnerProducts.fdegOf_eq hd hw`. Rewrite using `[e]`. Conclude with `hd`.
-/
theorem isFdeg_dv (v : InfinitePlace X.B.I.F) :
    IsFdeg (Formalism.REAL.muG (X.B.I.ε v)) (X.B.σ v) (X.dv v) := by
  obtain ⟨d, hd⟩ := Formalism.MainNotions.BridgeCSchur.fdeg_of_DS (X.B.lam v) (X.B.σ v) (X.ds v)
  have hw : X.B.w v ≠ 0 := by
    intro h0
    have h1 := (X.low v).1
    rw [h0, norm_zero] at h1
    exact zero_ne_one h1
  have e : X.dv v = d := Formalism.MainNotions.DiscreteSeriesInnerProducts.fdegOf_eq hd hw
  rw [e]
  exact hd

/- English proof (translation)
Apply `ext_inner_left ℂ` to reduce the goal to its premises. Introduce `a`. Establish `hU : ∀ v, IsURepOn (UJset (X.B.I.ε v)) (X.B.σ v)` using `fun v => (X.ds v).2.2.1`. Establish `hw : ∀ v, ‖X.B.w v‖ = 1` using `fun v => (X.low v).1`. Establish `hs` using `(Formalism.L2.SG.Pf.glob_schur X.B.I X.B.σ X.dv X.B.w hU (isFdeg_dv X) hw hL X.B.σs X.B.tens X.B.tens_spec (ContinuousLinearMap.adjoint Φ a)).2`.

Rewrite using `[X.Rph_spec a (Φ (X.B.tens X.B.w))]`. Establish `hg : ∀ g : X.B.I.Ginf, X.B.R (g, 1) (Φ (X.B.tens X.B.w)) = Φ (X.B.σs g (X.B.tens X.B.w))`. Introduce `g`. Use `congrArg (fun L : X.B.Hs →L[ℂ] X.B.I.L2 X.B.μf X.B.fund => L (X.B.tens X.B.w)) (hΦ g)` as an intermediate fact. Simplify using `using this.symm`.

Establish `hi : ∀ x : X.B.Hs, ⟪a, Φ x⟫_ℂ = ⟪ContinuousLinearMap.adjoint Φ a, x⟫_ℂ` using `fun x => (ContinuousLinearMap.adjoint_inner_left Φ x a).symm`. Rewrite using `[hi, ← hs]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)` and prove the remaining obligations. Use `show _ * _ = _ * _`. Rewrite using `[hg g, hi]`.

Both sides reduce to the same expression.
-/
theorem rph_fix_hom
    (hL : ∀ v, Integrable (phLoc (ε := X.B.I.ε v) (X.B.σ v) (X.B.w v) (X.dv v)) (Formalism.REAL.muG (X.B.I.ε v)))
    (Φ : X.B.Hs →L[ℂ] X.B.I.L2 X.B.μf X.B.fund) (hΦ : Φ ∈ X.B.I.HomS X.B.σs X.B.μf X.B.fund X.B.R) :
    X.Rph (Φ (X.B.tens X.B.w)) = Φ (X.B.tens X.B.w) := by
  apply ext_inner_left ℂ
  intro a
  have hU : ∀ v, IsURepOn (UJset (X.B.I.ε v)) (X.B.σ v) := fun v => (X.ds v).2.2.1
  have hw : ∀ v, ‖X.B.w v‖ = 1 := fun v => (X.low v).1
  have hs := (Formalism.L2.SG.Pf.glob_schur X.B.I X.B.σ X.dv X.B.w hU (isFdeg_dv X) hw hL X.B.σs X.B.tens
    X.B.tens_spec (ContinuousLinearMap.adjoint Φ a)).2
  rw [X.Rph_spec a (Φ (X.B.tens X.B.w))]
  have hg : ∀ g : X.B.I.Ginf, X.B.R (g, 1) (Φ (X.B.tens X.B.w)) = Φ (X.B.σs g (X.B.tens X.B.w)) := by
    intro g
    have := congrArg (fun L : X.B.Hs →L[ℂ] X.B.I.L2 X.B.μf X.B.fund => L (X.B.tens X.B.w)) (hΦ g)
    simpa using this.symm
  have hi : ∀ x : X.B.Hs, ⟪a, Φ x⟫_ℂ = ⟪ContinuousLinearMap.adjoint Φ a, x⟫_ℂ := fun x =>
    (ContinuousLinearMap.adjoint_inner_left Φ x a).symm
  rw [hi, ← hs]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  show _ * _ = _ * _
  rw [hg g, hi]
  rfl

/- English proof (translation)
Rewrite using `[Formalism.L2.SG.Pf.orbit_eq X.B.I X.B.σ X.B.σs X.B.tens X.B.tens_spec X.B.w g, X.B.tens_spec.1]`. Both sides reduce to the same expression.
-/
theorem inner_tens_orbit (g : X.B.I.Ginf) :
    ⟪X.B.tens X.B.w, X.B.σs g (X.B.tens X.B.w)⟫_ℂ = mInf X.B.I X.B.σ X.B.w g := by
  rw [Formalism.L2.SG.Pf.orbit_eq X.B.I X.B.σ X.B.σs X.B.tens X.B.tens_spec X.B.w g, X.B.tens_spec.1]
  rfl

/- English proof (translation)
Rewrite using `[X.B.tens_spec.1]`. Use `Finset.prod_eq_one fun v _ => ?_` and prove the remaining obligations. Rewrite using `[inner_self_eq_norm_sq_to_K, (X.low v).1]`. Simplify using the standard rewrite rules.
-/
theorem inner_tens_self : ⟪X.B.tens X.B.w, X.B.tens X.B.w⟫_ℂ = 1 := by
  rw [X.B.tens_spec.1]
  refine Finset.prod_eq_one fun v _ => ?_
  rw [inner_self_eq_norm_sq_to_K, (X.low v).1]
  simp

/- English proof (translation)
Establish `hU : ∀ v, IsURepOn (UJset (X.B.I.ε v)) (X.B.σ v)` using `fun v => (X.ds v).2.2.1`. Establish `hw : ∀ v, ‖X.B.w v‖ = 1` using `fun v => (X.low v).1`. Establish `hs` using `Formalism.L2.SG.Pf.glob_schur X.B.I X.B.σ X.dv X.B.w hU (isFdeg_dv X) hw hL X.B.σs X.B.tens X.B.tens_spec (X.B.tens X.B.w)`. Rewrite `hs` using `[inner_tens_orbit X]`. Rewrite `hs` using `[inner_tens_self X]`.

Conclude with `hs`.
-/
theorem integral_ph_m
    (hL : ∀ v, Integrable (phLoc (ε := X.B.I.ε v) (X.B.σ v) (X.B.w v) (X.dv v)) (Formalism.REAL.muG (X.B.I.ε v))) :
    Integrable (fun g => X.ph g * mInf X.B.I X.B.σ X.B.w g) (muInf X.B.I) ∧
      ∫ g, X.ph g * mInf X.B.I X.B.σ X.B.w g ∂(muInf X.B.I) = 1 := by
  have hU : ∀ v, IsURepOn (UJset (X.B.I.ε v)) (X.B.σ v) := fun v => (X.ds v).2.2.1
  have hw : ∀ v, ‖X.B.w v‖ = 1 := fun v => (X.low v).1
  have hs := Formalism.L2.SG.Pf.glob_schur X.B.I X.B.σ X.dv X.B.w hU (isFdeg_dv X) hw hL X.B.σs X.B.tens
    X.B.tens_spec (X.B.tens X.B.w)
  simp_rw [inner_tens_orbit X] at hs
  rw [inner_tens_self X] at hs
  exact hs

/- English proof (translation)
The claim follows from `Formalism.L2.SG.Closed.ProjRowsR_holds X.B.I X.B.μf X.B.fund X.B.fund_spec X.B.R X.B.R_spec X.B.H X.B.σ X.dv X.B.w (fun v => (X.ds v).2.2.1) (isFdeg_dv X) (fun v => (X.low v).1) hL X.Rph X.Rph_spec`.
-/
theorem rph_isRowProj
    (hL : ∀ v, Integrable (phLoc (ε := X.B.I.ε v) (X.B.σ v) (X.B.w v) (X.dv v)) (Formalism.REAL.muG (X.B.I.ε v))) :
    IsRowProj (fun g => X.B.R (g, 1)) (mInf X.B.I X.B.σ X.B.w) X.Rph :=
  Formalism.L2.SG.Closed.ProjRowsR_holds X.B.I X.B.μf X.B.fund X.B.fund_spec X.B.R X.B.R_spec X.B.H X.B.σ X.dv X.B.w
    (fun v => (X.ds v).2.2.1) (isFdeg_dv X) (fun v => (X.low v).1) hL X.Rph X.Rph_spec

/- English proof (translation)
Establish `hP` using `rph_isRowProj X hL`. Establish `h1 : ⟪f, X.Rph f⟫_ℂ = ((‖f‖ ^ 2 : ℝ) : ℂ)`. Rewrite using `[X.Rph_spec f f]`. Establish `e : ∀ g, Formalism.L2.SG.ProjRows.phInf X.B.I X.B.σ X.B.w (fun v => fdegOf (Formalism.REAL.muG (X.B.I.ε v)) (X.B.σ v) (X.B.w v)) g * ⟪f, X.B.R (g, 1) f⟫_ℂ = ((‖f‖ ^ 2 : ℝ) : ℂ) * (X.ph g * mInf X.B.I X.B.σ X.B.w g)`. Introduce `g`.

Rewrite using `[hc g]`. Use `show X.ph g * _ = _`. Expand and normalize the polynomial expressions, which then agree. Repeatedly rewrite using `[e]`. Rewrite using `[integral_const_mul, (integral_ph_m X hL).2, mul_one]`.

Establish `h2 : ⟪X.Rph f, X.Rph f⟫_ℂ = ⟪f, X.Rph f⟫_ℂ`. Rewrite using `[hP.1 f (X.Rph f)]`. Use `congr 1`. Conclude with `congrArg (fun L : X.B.I.L2 X.B.μf X.B.fund →L[ℂ] X.B.I.L2 X.B.μf X.B.fund => L f) hP.2.1`. Establish `h3 : ⟪X.Rph f, f⟫_ℂ = ⟪f, X.Rph f⟫_ℂ` using `hP.1 f f`.

Establish `h0 : ⟪f - X.Rph f, f - X.Rph f⟫_ℂ = 0`. Rewrite using `[inner_sub_left, inner_sub_right, inner_sub_right, h2, h3, h1, inner_self_eq_norm_sq_to_K]`. Simplify using the standard rewrite rules. Conclude with `(sub_eq_zero.1 (inner_self_eq_zero.1 h0)).symm`.
-/
theorem rph_fix_of_coef
    (hL : ∀ v, Integrable (phLoc (ε := X.B.I.ε v) (X.B.σ v) (X.B.w v) (X.dv v)) (Formalism.REAL.muG (X.B.I.ε v)))
    (f : X.B.I.L2 X.B.μf X.B.fund)
    (hc : ∀ g : X.B.I.Ginf, ⟪f, X.B.R (g, 1) f⟫_ℂ = ((‖f‖ ^ 2 : ℝ) : ℂ) * mInf X.B.I X.B.σ X.B.w g) :
    X.Rph f = f := by
  have hP := rph_isRowProj X hL
  have h1 : ⟪f, X.Rph f⟫_ℂ = ((‖f‖ ^ 2 : ℝ) : ℂ) := by
    rw [X.Rph_spec f f]
    have e : ∀ g, Formalism.L2.SG.ProjRows.phInf X.B.I X.B.σ X.B.w
        (fun v => fdegOf (Formalism.REAL.muG (X.B.I.ε v)) (X.B.σ v) (X.B.w v)) g * ⟪f, X.B.R (g, 1) f⟫_ℂ =
        ((‖f‖ ^ 2 : ℝ) : ℂ) * (X.ph g * mInf X.B.I X.B.σ X.B.w g) := by
      intro g
      rw [hc g]
      show X.ph g * _ = _
      ring
    simp_rw [e]
    rw [integral_const_mul, (integral_ph_m X hL).2, mul_one]
  have h2 : ⟪X.Rph f, X.Rph f⟫_ℂ = ⟪f, X.Rph f⟫_ℂ := by
    rw [hP.1 f (X.Rph f)]
    congr 1
    exact congrArg (fun L : X.B.I.L2 X.B.μf X.B.fund →L[ℂ] X.B.I.L2 X.B.μf X.B.fund => L f) hP.2.1
  have h3 : ⟪X.Rph f, f⟫_ℂ = ⟪f, X.Rph f⟫_ℂ := hP.1 f f
  have h0 : ⟪f - X.Rph f, f - X.Rph f⟫_ℂ = 0 := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right, h2, h3, h1, inner_self_eq_norm_sq_to_K]
    simp
  exact (sub_eq_zero.1 (inner_self_eq_zero.1 h0)).symm

end Formalism.L2.SG.EvalTRph

end
