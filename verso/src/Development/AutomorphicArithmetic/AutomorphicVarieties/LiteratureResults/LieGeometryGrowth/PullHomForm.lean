import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullHomPt
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullHkSmooth
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.ParamDeriv

open UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Dr
open Set ContinuousAlternatingMap
open scoped ContDiff

/- English proof (translation)
A detailed English derivation is pending.
-/
private theorem extDeriv_smooth {V F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {Y : Set V} (hY : IsOpen Y) {q : ℕ} {w : V → V [⋀^Fin q]→L[ℝ] F}
    (hw : ContDiffOn ℝ ∞ w Y) : ContDiffOn ℝ ∞ (extDeriv w) Y :=
  (alternatizeUncurryFinCLM ℝ V F).contDiff.comp_contDiffOn
    (hw.fderiv_of_isOpen hY (by simp))

/- English proof (translation)
Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
private theorem pb_flow_zero {V F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (W : V → V) {q : ℕ} (w : V → V [⋀^Fin q]→L[ℝ] F) (p : V) :
    pb (flow W 0) w p = w p := by
  have h : flow W 0 = id := by
    funext x
    simp [flow]
  ext v
  simp [pb_apply, h]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Simplify by unfolding definitions. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

A detailed English derivation is pending.
-/
private theorem homForm_of (hP : HomPt) (hS : HkSmooth) : HomForm := by
  intro V F _ _ _ _ _ _ Y hY W hW p hp
  have hWp : ContDiffAt ℝ ∞ W p := hW.1.contDiffAt (hY.mem_nhds hp)
  refine ⟨fun w hw => ?_, fun q w hw => ?_⟩
  · have hI := ((hS V F Y hY W hW 0 _ (extDeriv_smooth hY hw)).2.2.1 p hp).intervalIntegrable_of_Icc
      (μ := MeasureTheory.volume) zero_le_one
    have hder : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun r => pb (flow W r) w p) (hk W t (extDeriv w) p) t := by
      intro t ht
      rw [uIcc_of_le zero_le_one] at ht
      exact (hP V F W p t hWp).1 w (hw.contDiffAt (hY.mem_nhds (hW.2 p hp t ht)))
    have h3 := intervalIntegral.integral_eq_sub_of_hasDerivAt hder hI
    rw [pb_flow_zero] at h3
    exact h3.symm
  · have hI := ((hS V F Y hY W hW (q + 1) _ (extDeriv_smooth hY hw)).2.2.1 p hp).intervalIntegrable_of_Icc
      (μ := MeasureTheory.volume) zero_le_one
    obtain ⟨hU, hΦ, -, -⟩ := hS V F Y hY W hW q w hw
    obtain ⟨hc, hD⟩ := paramDeriv V _ p _ _ hU (fun t ht => ⟨hp, hW.2 p hp t ht⟩) hΦ
    dsimp only at hc hD
    have hJ := hc.intervalIntegrable_of_Icc (μ := MeasureTheory.volume) zero_le_one
    have hJ' : IntervalIntegrable (fun t => alternatizeUncurryFinCLM ℝ V F (fderiv ℝ (fun x => hk W t w x) p))
        MeasureTheory.volume 0 1 :=
      ((alternatizeUncurryFinCLM ℝ V F).continuous.comp_continuousOn hc).intervalIntegrable_of_Icc
      (μ := MeasureTheory.volume) zero_le_one
    have hder : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun r => pb (flow W r) w p)
        (alternatizeUncurryFinCLM ℝ V F (fderiv ℝ (fun x => hk W t w x) p) + hk W t (extDeriv w) p) t := by
      intro t ht
      rw [uIcc_of_le zero_le_one] at ht
      exact (hP V F W p t hWp).2 q w (hw.contDiffAt (hY.mem_nhds (hW.2 p hp t ht)))
    have h3 := intervalIntegral.integral_eq_sub_of_hasDerivAt hder (hJ'.add hI)
    rw [pb_flow_zero, intervalIntegral.integral_add hJ' hI,
      (alternatizeUncurryFinCLM ℝ V F).intervalIntegral_comp_comm hJ, ← hD.fderiv] at h3
    exact h3.symm

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem UpperTheory.V.Lit.Geo.homForm :
    HomForm :=
  homForm_of homPt hkSmooth
