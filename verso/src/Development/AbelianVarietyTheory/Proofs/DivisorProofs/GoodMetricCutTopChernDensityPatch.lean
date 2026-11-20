import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EndValuedForm11Coeffs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopFormIntegralOfSupportInHolomorphicChartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnCutoffTopChernFormPoincareGrowthStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousMulTopChernFormIsTopDegreeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopChernDensityHolomorphicChartEtaleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodPatchChartImagePropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramMatrixSmoothIsUnitInHolomorphicChartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffAtHolomorphicComplexChartOfSmoothAtStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableOnHolomorphicChartTransEtaleChartStatement
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option autoImplicit false
noncomputable section

/- English proof (translation)
Introduce `F _ σ X m E O H H₀ hH hH₀ e S A W c hP ρ hρ hρW`. Take `⟨hU, himg, hcpt⟩` from `GlobalTheory.T.goodPatch_chart_image_properties E O H hP`. Establish `hS : MeasurableSet (ptsIn X.str σ O)` using `(isOpen_ptsIn O).measurableSet`. Establish `hd : ∀ i j : AlgChart X.str σ X.dim, DifferentiableOn ℂ (j.e ∘ i.e.symm) (i.e.target ∩ i.e.symm ⁻¹' j.e.source)` using `fun i j => i.holo_trans j`. Establish `hcov : ∀ y, ∃ i : AlgChart X.str σ X.dim, y ∈ i.e.source` using `fun y => AlgChart.exists_mem_source y`.

Establish `hρc : Continuous ρ` using `continuous_iff_continuousAt.2 fun y => (hρ y).continuousAt`. Establish `hρ0 : ∀ y, y ∉ W → ρ y = 0` using `fun y hy => image_eq_zero_of_notMem_tsupport (fun h => hy (hρW h))`. Use `set f : V X.dim → ℂ := fun v => (ρ (e.symm v) : ℂ) * mixTop fun _ => curvAt (fun v => H A (e.symm v) ()) v with hf`. Establish `hint : IntegrableOn f (offHyp S (e '' W))`. Use `GlobalTheory.T.integrableOn_cutoff_topChernForm_poincareGrowth S (e '' W) (e '' tsupport ρ) (fun v => H₀ A (e.symm v) ()) (fun v => H A (e.symm v) ()) (fun v => ρ (e.symm v)) c hU (hcpt _ (isClosed_tsupport ρ) hρW) (Set.image_mono hρW) ?_ ?_ ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨z, hz, rfl⟩ a ha`. Conclude with `hP.small z hz a ha`. Introduce and unpack `_ ⟨z, hz, rfl⟩`. Conclude with `GlobalTheory.T.gramMatrix_smooth_isUnit_in_holomorphicChart E ⊤ H₀ hH₀ hP.holo mem_ptsIn_top (hP.sub hz) (hP.frame z hz)`. Introduce `v hv`.

Rewrite `hv` using `[← himg]`. Take `⟨z, ⟨hzO, hz⟩, rfl⟩` from `hv`. Conclude with `GlobalTheory.T.gramMatrix_smooth_isUnit_in_holomorphicChart E O H hH hP.holo hzO (hP.sub hz) (hP.frame z hz)`. Introduce `v hv`. Rewrite `hv` using `[← himg]`.

Take `⟨z, ⟨hzO, hz⟩, rfl⟩` from `hv`. Conclude with `hP.form z hz hzO`. Introduce `v hv`. Rewrite `hv` using `[← himg]`. Take `⟨z, ⟨hzO, hz⟩, rfl⟩` from `hv`.

Conclude with `hP.dbar z hz hzO`. Introduce and unpack `_ ⟨z, hz, rfl⟩`. Conclude with `(GlobalTheory.T.contDiffAt_holomorphicComplexChart_of_smoothAt hP.holo (hP.sub hz) (hρ z)).contDiffWithinAt`. Introduce and unpack `_ ⟨z, hz, rfl⟩ hK`. Establish `hzK : z ∉ tsupport ρ` using `fun h => hK ⟨z, h, rfl⟩`.

Use `show ρ (e.symm (e z)) = 0`. Rewrite using `[e.left_inv (hP.sub hz)]`. Conclude with `image_eq_zero_of_notMem_tsupport hzK`. Establish `hre : IntegrableOn (fun v => (Real.pi ^ X.dim)⁻¹ * (f v).re) (offHyp S (e '' W))` using `(Integrable.re hint).const_mul _`. Establish `key` using `GlobalTheory.T.topFormIntegral_of_support_in_holomorphicChart (fun c : AlgChart X.str σ X.dim => c.e) hd hcov hS (d := fun c y => ρ y * topDens E H c y) e W (fun v => (Real.pi ^ X.dim)⁻¹ * (f v).re) hP.isOpen hP.sub (fun j => GlobalTheory.T.differentiableOn_holomorphicChart_trans …`.

Rewrite `key` using `[himg, integral_const_mul]`. Establish `h2 : ∫ v in offHyp S (e '' W), (f v).re = (∫ v in offHyp S (e '' W), f v).re` using `integral_re hint`. Rewrite `key` using `[h2]`. Conclude with `key`. Introduce `i y _ hy _`.

Simplify using `[hρ0 y hy]`. Introduce `j y hyO hy hj`. Establish `h1` using `GlobalTheory.T.top_chern_density_holomorphic_chart_etale E O H hH hP.holo j hyO (hP.sub hy) hj (hP.frame y hy)`. Simplify using `only [hf, e.left_inv (hP.sub hy), Complex.re_ofReal_mul]`. Rewrite using `[mul_left_comm, h1]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem GlobalTheory.GoodTop.hasInt_mul_topDens_goodPatch : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ} (E : Fr (ratOf X) (fun _ : Unit => m) 0) (O : X.X.Opens) (H H₀ : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ), IsMetricOn E O H → IsMetricOn E ⊤ H₀ → ∀ {e : OpenPartialHomeomorph (CxPts X.str σ) (V X.dim)} {S : Finset (Fin X.dim)} {A : Mat (fun _ : Unit => m) X.Fn} {W : Set (CxPts X.str σ)} {c : ℝ}, GoodPatch E O H e S A W c → ∀ {ρ : CxPts X.str σ → ℝ}, (∀ y, CInfAt ρ y) → tsupport ρ ⊆ W → HasInt (fun c : AlgChart X.str σ X.dim => c.e) (fun c y => ρ y * topDens E H c y) (ptsIn X.str σ O) ((Real.pi ^ X.dim)⁻¹ * (∫ v in offHyp S (e '' W), (ρ (e.symm v) : ℂ) * mixTop fun _ => curvAt (fun v => H A (e.symm v) ()) v).re) := by
  intro F _ σ X m E O H H₀ hH hH₀ e S A W c hP ρ hρ hρW
  obtain ⟨hU, himg, hcpt⟩ := GlobalTheory.T.goodPatch_chart_image_properties E O H hP
  have hS : MeasurableSet (ptsIn X.str σ O) := (isOpen_ptsIn O).measurableSet
  have hd : ∀ i j : AlgChart X.str σ X.dim,
      DifferentiableOn ℂ (j.e ∘ i.e.symm) (i.e.target ∩ i.e.symm ⁻¹' j.e.source) := fun i j => i.holo_trans j
  have hcov : ∀ y, ∃ i : AlgChart X.str σ X.dim, y ∈ i.e.source := fun y => AlgChart.exists_mem_source y
  have hρc : Continuous ρ := continuous_iff_continuousAt.2 fun y => (hρ y).continuousAt
  have hρ0 : ∀ y, y ∉ W → ρ y = 0 := fun y hy => image_eq_zero_of_notMem_tsupport (fun h => hy (hρW h))
  set f : V X.dim → ℂ := fun v => (ρ (e.symm v) : ℂ) * mixTop fun _ => curvAt (fun v => H A (e.symm v) ()) v with hf
  have hint : IntegrableOn f (offHyp S (e '' W)) := by
    refine GlobalTheory.T.integrableOn_cutoff_topChernForm_poincareGrowth S (e '' W) (e '' tsupport ρ) (fun v => H₀ A (e.symm v) ()) (fun v => H A (e.symm v) ())
      (fun v => ρ (e.symm v)) c hU (hcpt _ (isClosed_tsupport ρ) hρW) (Set.image_mono hρW) ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · rintro _ ⟨z, hz, rfl⟩ a ha
      exact hP.small z hz a ha
    · rintro _ ⟨z, hz, rfl⟩
      exact GlobalTheory.T.gramMatrix_smooth_isUnit_in_holomorphicChart E ⊤ H₀ hH₀ hP.holo mem_ptsIn_top (hP.sub hz) (hP.frame z hz)
    · intro v hv
      rw [← himg] at hv
      obtain ⟨z, ⟨hzO, hz⟩, rfl⟩ := hv
      exact GlobalTheory.T.gramMatrix_smooth_isUnit_in_holomorphicChart E O H hH hP.holo hzO (hP.sub hz) (hP.frame z hz)
    · intro v hv
      rw [← himg] at hv
      obtain ⟨z, ⟨hzO, hz⟩, rfl⟩ := hv
      exact hP.form z hz hzO
    · intro v hv
      rw [← himg] at hv
      obtain ⟨z, ⟨hzO, hz⟩, rfl⟩ := hv
      exact hP.dbar z hz hzO
    · rintro _ ⟨z, hz, rfl⟩
      exact (GlobalTheory.T.contDiffAt_holomorphicComplexChart_of_smoothAt hP.holo (hP.sub hz) (hρ z)).contDiffWithinAt
    · rintro _ ⟨z, hz, rfl⟩ hK
      have hzK : z ∉ tsupport ρ := fun h => hK ⟨z, h, rfl⟩
      show ρ (e.symm (e z)) = 0
      rw [e.left_inv (hP.sub hz)]
      exact image_eq_zero_of_notMem_tsupport hzK
  have hre : IntegrableOn (fun v => (Real.pi ^ X.dim)⁻¹ * (f v).re) (offHyp S (e '' W)) :=
    (Integrable.re hint).const_mul _
  have key := GlobalTheory.T.topFormIntegral_of_support_in_holomorphicChart (fun c : AlgChart X.str σ X.dim => c.e) hd hcov hS
    (d := fun c y => ρ y * topDens E H c y) e W (fun v => (Real.pi ^ X.dim)⁻¹ * (f v).re) hP.isOpen hP.sub
    (fun j => GlobalTheory.T.differentiableOn_holomorphicChart_trans_etaleChart hP.holo j) (GlobalTheory.T.continuous_mul_top_chern_form_isTopDegree E O H hH hρc) ?_ ?_ (by rw [himg]; exact hre)
  · rw [himg, integral_const_mul] at key
    have h2 : ∫ v in offHyp S (e '' W), (f v).re = (∫ v in offHyp S (e '' W), f v).re := integral_re hint
    rw [h2] at key
    exact key
  · intro i y _ hy _
    simp [hρ0 y hy]
  · intro j y hyO hy hj
    have h1 := GlobalTheory.T.top_chern_density_holomorphic_chart_etale E O H hH hP.holo j hyO (hP.sub hy) hj (hP.frame y hy)
    simp only [hf, e.left_inv (hP.sub hy), Complex.re_ofReal_mul]
    rw [mul_left_comm, h1]
    ring
