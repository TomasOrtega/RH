import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheet
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterOsgood
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterFS
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FrechetDerivEvaluation
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology

noncomputable section

namespace NefOnGenericOfSemipos

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.FrechetDerivEvaluation.hasFDerivAt_eval g z`.
-/
theorem hasFDerivAt_eval {σ : Type*} [Fintype σ] (g : MvPolynomial σ ℂ) (z : σ → ℂ) :
    HasFDerivAt (fun x : σ → ℂ => eval x g)
      (∑ i, eval z (pderiv i g) • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ℂ) i) z :=
  _root_.UpperTheory.Reformulated.B.FrechetDerivEvaluation.hasFDerivAt_eval g z

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

/- English proof (translation)
Establish `hA : AnalyticAt ℂ γ y` using `sheet_analyticAt osgood h`. Establish `hz : γ y ∈ mcPts W` using `h.2.self_of_nhds.2.1`. Establish `hne : ∀ k, ∃ i, γ y ⟨k, i⟩ ≠ 0` using `hz.1`. Establish `hzP : γ y ∈ mcPts P` using `⟨hz.1, fun f hf => hz.2 f (hPW hf)⟩`. Establish `hφ : ContDiffAt ℝ 2 (fun z => Real.log (A.h z)) (γ y)` using `((hs.1.contDiffAt (isOpen_blockNonzero.mem_nhds hne)).of_le (WithTop.coe_le_coe.mpr le_top)).log (A.pos _ hne).ne'`.

Establish `htan : IsConeTangent (Int.castRingHom ℂ) P0 (γ y) (fderiv ℂ γ y (Pi.single 0 1))`. Introduce `f hf`. Establish `h0 : (fun y' => eval (γ y') (map (Int.castRingHom ℂ) f)) =ᶠ[𝓝 y] fun _ => (0 : ℂ)` using `by filter_upwards [h.2] with y' hy'`. Conclude with `hy'.2.1.2 f (hPW (hP0 hf))`. Establish `hd` using `(hasFDerivAt_eval (map (Int.castRingHom ℂ) f) (γ y)).comp y hA.differentiableAt.hasFDerivAt`.

Establish `h00` using `(hasFDerivAt_const (𝕜 := ℂ) (0 : ℂ) y).congr_of_eventuallyEq h0`. Use `congrArg (fun L => L (Pi.single 0 1)) (hd.unique h00)` as an intermediate fact. Simplify using `using this`. Establish `hlevi : 0 ≤ ReciprocityTheory.AnForm.levi (fun z => Real.log (A.h z)) (γ y) (fderiv ℂ γ y (Pi.single 0 1))` using `hs.2 (γ y) hzP _ htan`. Establish `key` using `ReciprocityTheory.AnForm.levi_comp (Pi.single 0 1) hA hφ`.

Rewrite `hlevi` using `[← key]`. Unfold `ReciprocityTheory.AnForm.levi at hlevi`. Simplify using `only [Function.comp_def] at hlevi`. Rewrite using `[maDensity_one]`. Apply `div_nonneg _ (by positivity)` to reduce the goal to its premises.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem maDensity_nonneg {P P0 W : Ideal (MRing ι)} {A : HermLine ι} (hP0 : P0 ≤ P) (hPW : P ≤ W)
    (hs : IsSemipositiveRel P0 P A) {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (1 + 1) → ℂ)}
    {y : Fin 1 → ℂ} {w : ((k : K) → ι k) → ℂ} {γ : (Fin 1 → ℂ) → (Σ k, ι k) → ℂ}
    (h : IsSheet W Ψ y w γ) :
    0 ≤ maDensity (fun _ y' => Real.log (A.h (γ y'))) y := by
  have hA : AnalyticAt ℂ γ y := sheet_analyticAt osgood h
  have hz : γ y ∈ mcPts W := h.2.self_of_nhds.2.1
  have hne : ∀ k, ∃ i, γ y ⟨k, i⟩ ≠ 0 := hz.1
  have hzP : γ y ∈ mcPts P := ⟨hz.1, fun f hf => hz.2 f (hPW hf)⟩
  have hφ : ContDiffAt ℝ 2 (fun z => Real.log (A.h z)) (γ y) :=
    ((hs.1.contDiffAt (isOpen_blockNonzero.mem_nhds hne)).of_le
      (WithTop.coe_le_coe.mpr le_top)).log (A.pos _ hne).ne'
  have htan : IsConeTangent (Int.castRingHom ℂ) P0 (γ y) (fderiv ℂ γ y (Pi.single 0 1)) := by
    intro f hf
    have h0 : (fun y' => eval (γ y') (map (Int.castRingHom ℂ) f)) =ᶠ[𝓝 y] fun _ => (0 : ℂ) := by
      filter_upwards [h.2] with y' hy'
      exact hy'.2.1.2 f (hPW (hP0 hf))
    have hd := (hasFDerivAt_eval (map (Int.castRingHom ℂ) f) (γ y)).comp y
      hA.differentiableAt.hasFDerivAt
    have h00 := (hasFDerivAt_const (𝕜 := ℂ) (0 : ℂ) y).congr_of_eventuallyEq h0
    have := congrArg (fun L => L (Pi.single 0 1)) (hd.unique h00)
    simpa using this
  have hlevi : 0 ≤ ReciprocityTheory.AnForm.levi (fun z => Real.log (A.h z)) (γ y)
      (fderiv ℂ γ y (Pi.single 0 1)) := hs.2 (γ y) hzP _ htan
  have key := ReciprocityTheory.AnForm.levi_comp (Pi.single 0 1) hA hφ
  rw [← key] at hlevi
  unfold ReciprocityTheory.AnForm.levi at hlevi
  simp only [Function.comp_def] at hlevi
  rw [maDensity_one]
  apply div_nonneg _ (by positivity)
  linarith

/- English proof (translation)
Unfold `geomDeg ptsIntegral`. Use `split_ifs with hΨ`. Unfold `ptsIntegralAt`. Use `MeasureTheory.integral_nonneg fun y => ?_` and prove the remaining obligations. Use `finsum_nonneg fun w => finsum_nonneg fun _ => ?_` and prove the remaining obligations.

Unfold `sheetDensity`. Use `split_ifs with hγ`. Simplify `maDensity_nonneg hP0 hPW hs hγ.choose_spec` using `only [one_mul]`. Conclude with `le_rfl`. Conclude with `le_rfl`.
-/
theorem geomDeg_one_nonneg {P P0 W : Ideal (MRing ι)} {A : HermLine ι} (hP0 : P0 ≤ P)
    (hs : IsSemipositiveRel P0 P A) (hPW : P ≤ W) : 0 ≤ geomDeg W A 1 := by
  classical
  unfold geomDeg ptsIntegral
  split_ifs with hΨ
  · unfold ptsIntegralAt
    refine MeasureTheory.integral_nonneg fun y => ?_
    refine finsum_nonneg fun w => finsum_nonneg fun _ => ?_
    unfold sheetDensity
    split_ifs with hγ
    · simpa only [one_mul] using maDensity_nonneg hP0 hPW hs hγ.choose_spec
    · exact le_rfl
  · exact le_rfl

end NefOnGenericOfSemipos

/- English proof (translation)
Introduce `_ _ _ _ _ _ _ hP0 hs _ _ hPW` and use `NefOnGenericOfSemipos.geomDeg_one_nonneg hP0 hs hPW`.
-/
theorem NefOnGenericOfSemipos.proof : NefOnGenericOfSemipos.Statement :=
  fun _ _ _ _ _ _ _ hP0 hs _ _ hPW => NefOnGenericOfSemipos.geomDeg_one_nonneg hP0 hs hPW

/- English proof (translation)
The claim follows from `ArithmeticVolumeBig.of_moriwakiBig NefOnGenericOfSemipos.proof hM`.
-/
theorem ArithmeticVolumeBig.of_moriwakiBig_only (hM : MoriwakiBigStatement) : ArithmeticVolumeBig.Statement :=
  ArithmeticVolumeBig.of_moriwakiBig NefOnGenericOfSemipos.proof hM

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
