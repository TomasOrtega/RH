import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.ExistsCombComb

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

/- English proof (translation)
Introduce `hP V M _ _ _ _ _ _ _ _ B hB K`. Use `set Φ : V × M → V × M := fun z => (z.1, z.2 - B z.1 z.2) with hΦdef`. Establish `hΦ : Function.HasTemperateGrowth Φ`. Set `B2 : V →L[ℝ] M →L[ℝ] V × M` to `(ContinuousLinearMap.compL ℝ M M (V × M) (ContinuousLinearMap.inr ℝ V M)).comp B`. Establish `h1 : Function.HasTemperateGrowth (fun z : V × M => B2 z.1 z.2)` using `B2.bilinear_hasTemperateGrowth (ContinuousLinearMap.fst ℝ V M).hasTemperateGrowth (ContinuousLinearMap.snd ℝ V M).hasTemperateGrowth`.

Establish `h2` using `(ContinuousLinearMap.id ℝ (V × M)).hasTemperateGrowth.add h1.neg`. Use `h2 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `z`. Apply the tactic sequence `ext <;> simp [Φ, B2, sub_eq_add_neg]`. Establish `hbd : ∃ (k : ℕ) (C : ℝ), ∀ z : V × M, ‖z‖ ≤ C * (1 + ‖Φ z‖) ^ k`.

Use `⟨2, 1 + ‖B‖, fun z => ?_⟩` and prove the remaining obligations. Take `⟨u, x⟩` from `z`. Use `set t := ‖Φ (u, x)‖ with ht`. Establish `hu : ‖u‖ ≤ t` using `norm_fst_le (Φ (u, x))`. Establish `hy : ‖x - B u x‖ ≤ t` using `norm_snd_le (Φ (u, x))`.

Establish `hx : x = (x - B u x) + B u (x - B u x)`. Rewrite using `[map_sub, hB, sub_zero, sub_add_cancel]`. Establish `hBu : ‖B u (x - B u x)‖ ≤ ‖B‖ * ‖u‖ * ‖x - B u x‖` using `B.le_opNorm₂ _ _`. Establish `hxle : ‖x‖ ≤ t + ‖B‖ * t * t`. Combine the equalities or inequalities in the displayed calculation.

Use `norm_nonneg B` as an intermediate fact. Use `norm_nonneg u` as an intermediate fact. Use `norm_nonneg (x - B u x)` as an intermediate fact. Use polynomial arithmetic with `[mul_le_mul hu hy (norm_nonneg _) (le_trans (norm_nonneg _) hu)]`. Establish `ht0 : 0 ≤ t` using `norm_nonneg _`.

Establish `hB0` using `norm_nonneg B`. Rewrite using `[Prod.norm_def]`. Use `max_le ?_ ?_` and prove the remaining obligations. Use the polynomial consequences of the given equalities and inequalities. Use the polynomial consequences of the given equalities and inequalities.

Set `K' : 𝓢(V × M, ℂ)` to `SchwartzMap.compCLM ℂ hΦ hbd K`. Take `⟨L, hL⟩` from `hP V M K'`. Establish `hι : Function.HasTemperateGrowth (fun x : M => ((0 : V), x))`. Use `(ContinuousLinearMap.inr ℝ V M).hasTemperateGrowth using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `x`.

Both sides reduce to the same expression. Establish `hιb : ∃ (k : ℕ) (C : ℝ), ∀ x : M, ‖x‖ ≤ C * (1 + ‖((0 : V), x)‖) ^ k`. Use `⟨1, 1, fun x => ?_⟩` and prove the remaining obligations. Establish `h` using `norm_snd_le ((0 : V), x)`. Simplify using `only [pow_one, one_mul]`.

Combine the linear equalities and inequalities to obtain the conclusion. Use `⟨K', SchwartzMap.compCLM ℂ hι hιb L, fun u x => rfl, fun x => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `L ((0 : V), x) = _`. Rewrite using `[hL]`. Simplify using `only [UpperTheory.V.Af.Smo.pft, Real.fourier_eq, inner_zero_right, neg_zero, AddChar.map_zero_eq_one, one_smul]`.
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
