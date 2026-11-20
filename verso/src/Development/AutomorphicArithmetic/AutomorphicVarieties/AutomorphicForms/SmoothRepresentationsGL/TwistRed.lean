import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.ExistsCombComb

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Supply the required witnesses or components. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.

A detailed English derivation is pending.
-/
theorem UpperTheory.V.Af.Smo.twistRed :
    UpperTheory.V.Af.Smo.TwistRed := by
  intro E _ _ _ n π π' χ
  refine ⟨fun hs => ?_, fun h => ?_⟩
  · filter_upwards [hs, Filter.eventually_cofinite.2 (GlobalTheory.Mem.UnrAe.finite_ramified χ)] with w ⟨B, h1, h2⟩ hu
    exact ⟨_, h1.twist hu, h2.twist hu⟩
  · have h' := h.twist χ⁻¹
    rwa [← CuspSub.twist_mul, ← CuspSub.twist_mul, mul_inv_cancel, CuspSub.twist_one, CuspSub.twist_one] at h'
