import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.ExistsCombComb

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact.

Apply an available result and prove the equalities needed to match it to the conclusion. Apply function extensionality and compare values at an arbitrary argument. Apply the first step, then apply the next step to every resulting obligation. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Chain the equalities or inequalities of the calculation. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Use the polynomial consequences of the given equalities and inequalities. Use the polynomial consequences of the given equalities and inequalities. Introduce a local definition for the expression. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Apply an available result and prove the equalities needed to match it to the conclusion. Apply function extensionality and compare values at an arbitrary argument. Both sides reduce to the same expression. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Simplify using the standard rewrite rules. Combine the linear equalities and inequalities to obtain the conclusion. Reduce the conclusion to the remaining proof obligations.

Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem UpperTheory.V.Af.Smo.betaSch :
    UpperTheory.V.Af.Smo.PftSch → UpperTheory.V.Af.Smo.BetaSch := by
  intro hP V M _ _ _ _ _ _ _ _ B hB K
  set Φ : V × M → V × M := fun z => (z.1, z.2 - B z.1 z.2) with hΦdef
  have hΦ : Function.HasTemperateGrowth Φ := by
    let B2 : V →L[ℝ] M →L[ℝ] V × M :=
      (ContinuousLinearMap.compL ℝ M M (V × M) (ContinuousLinearMap.inr ℝ V M)).comp B
    have h1 : Function.HasTemperateGrowth (fun z : V × M => B2 z.1 z.2) :=
      B2.bilinear_hasTemperateGrowth (ContinuousLinearMap.fst ℝ V M).hasTemperateGrowth
        (ContinuousLinearMap.snd ℝ V M).hasTemperateGrowth
    have h2 := (ContinuousLinearMap.id ℝ (V × M)).hasTemperateGrowth.add h1.neg
    convert h2 using 1
    funext z
    ext <;> simp [Φ, B2, sub_eq_add_neg]
  have hbd : ∃ (k : ℕ) (C : ℝ), ∀ z : V × M, ‖z‖ ≤ C * (1 + ‖Φ z‖) ^ k := by
    refine ⟨2, 1 + ‖B‖, fun z => ?_⟩
    obtain ⟨u, x⟩ := z
    set t := ‖Φ (u, x)‖ with ht
    have hu : ‖u‖ ≤ t := norm_fst_le (Φ (u, x))
    have hy : ‖x - B u x‖ ≤ t := norm_snd_le (Φ (u, x))
    have hx : x = (x - B u x) + B u (x - B u x) := by
      rw [map_sub, hB, sub_zero, sub_add_cancel]
    have hBu : ‖B u (x - B u x)‖ ≤ ‖B‖ * ‖u‖ * ‖x - B u x‖ := B.le_opNorm₂ _ _
    have hxle : ‖x‖ ≤ t + ‖B‖ * t * t := by
      calc ‖x‖ = ‖(x - B u x) + B u (x - B u x)‖ := by rw [← hx]
        _ ≤ ‖x - B u x‖ + ‖B u (x - B u x)‖ := norm_add_le _ _
        _ ≤ t + ‖B‖ * t * t := by
          have := norm_nonneg B
          have := norm_nonneg u
          have := norm_nonneg (x - B u x)
          nlinarith [mul_le_mul hu hy (norm_nonneg _) (le_trans (norm_nonneg _) hu)]
    have ht0 : 0 ≤ t := norm_nonneg _
    have hB0 := norm_nonneg B
    rw [Prod.norm_def]
    refine max_le ?_ ?_
    · nlinarith
    · nlinarith
  let K' : 𝓢(V × M, ℂ) := SchwartzMap.compCLM ℂ hΦ hbd K
  obtain ⟨L, hL⟩ := hP V M K'
  have hι : Function.HasTemperateGrowth (fun x : M => ((0 : V), x)) := by
    convert (ContinuousLinearMap.inr ℝ V M).hasTemperateGrowth using 1
    funext x
    rfl
  have hιb : ∃ (k : ℕ) (C : ℝ), ∀ x : M, ‖x‖ ≤ C * (1 + ‖((0 : V), x)‖) ^ k := by
    refine ⟨1, 1, fun x => ?_⟩
    have h := norm_snd_le ((0 : V), x)
    simp only [pow_one, one_mul]
    linarith
  refine ⟨K', SchwartzMap.compCLM ℂ hι hιb L, fun u x => rfl, fun x => ?_⟩
  change L ((0 : V), x) = _
  rw [hL]
  simp only [UpperTheory.V.Af.Smo.pft, Real.fourier_eq, inner_zero_right, neg_zero, AddChar.map_zero_eq_one, one_smul]
