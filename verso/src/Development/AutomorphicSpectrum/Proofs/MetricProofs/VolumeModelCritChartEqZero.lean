import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsPtsBddConv
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FlagIndices
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StLemmaETailMass
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PModelFibreSumAeSheet
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PModelFibreFinite
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.LintegralFibSum
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeI
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedDensityNonnegOffNullSet
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LocDensDivJacN
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeM
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PModelFibreSumAeFibres

set_option maxSynthPendingDepth 1

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Giv.Push.Crit

open MvPolynomial MeasureTheory Filter Topology Set ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo
  GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.LowerBoundFree.ModelFibreSumAlmostEverywhere

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (MRing ι)} {e : ℕ}
  (M : CxModel P e)

/- English proof (translation)
Use `Set.Finite.of_finite_image (f := modelW M Ψ) ((fibreFinite K ι P e Ψ hP hΨ y).subset ?_) ((modelW_injOn M Ψ).mono fun x hx => hx.2)` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Use `modelW_mem_fibre M Ψ hP.1 hP.2.1.2.1 hx.2` as an intermediate fact. Rewrite `this` using `[show modelQ M Ψ x = y from hx.1]`. Then use the resulting hypothesis.
-/
theorem fib_finite (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) (y : Fin e → ℂ) :
    (modelQ M Ψ ⁻¹' {y} ∩ {x | Ψ (segre (modelLift M x x)) 0 ≠ 0}).Finite := by
  refine Set.Finite.of_finite_image (f := modelW M Ψ) ((fibreFinite K ι P e Ψ hP hΨ y).subset ?_)
    ((modelW_injOn M Ψ).mono fun x hx => hx.2)
  rintro _ ⟨x, hx, rfl⟩
  have := modelW_mem_fibre M Ψ hP.1 hP.2.1.2.1 hx.2
  rwa [show modelQ M Ψ x = y from hx.1] at this

/- English proof (translation)
Take `⟨c, hc, hzc⟩` from `lift_compat M hz`. Conclude with `⟨∏ k, c k, Finset.prod_ne_zero_iff.mpr fun k _ => hc k, by rw [hzc, segre_smul, map_smul]⟩`.
-/
theorem psi_lift_eq {x z : M.Xc} (hz : z ∈ modelU M x)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) :
    ∃ μ : ℂ, μ ≠ 0 ∧ Ψ (segre (modelLift M z z)) = μ • Ψ (segre (modelLift M x z)) := by
  obtain ⟨c, hc, hzc⟩ := lift_compat M hz
  exact ⟨∏ k, c k, Finset.prod_ne_zero_iff.mpr fun k _ => hc k, by rw [hzc, segre_smul, map_smul]⟩

/- English proof (translation)
Take `⟨y, hy⟩` from `exists_infinite_fibre hO hne han hdet`. Use `(fib_finite M Ψ hP hΨ y).not_infinite ((Set.Infinite.image ((M.atlas.chart j).symm.injOn.mono fun u hu => hOt hu.1) hy).mono ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨u, ⟨huO, hqu⟩, rfl⟩`. Conclude with `⟨hqu, h0 u huO⟩`.
-/
theorem not_flat (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) (j : Fin M.atlas.n) {O : Set (Fin e → ℂ)}
    (hO : IsOpen O) (hOt : O ⊆ (M.atlas.chart j).target) (hne : O.Nonempty)
    (h0 : ∀ u ∈ O, Ψ (segre (modelLift M ((M.atlas.chart j).symm u) ((M.atlas.chart j).symm u))) 0 ≠ 0)
    (han : AnalyticOnNhd ℂ (modelQ M Ψ ∘ (M.atlas.chart j).symm) O)
    (hdet : ∀ u ∈ O, LinearMap.det (fderiv ℂ (modelQ M Ψ ∘ (M.atlas.chart j).symm) u :
      (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) = 0) : False := by
  obtain ⟨y, hy⟩ := exists_infinite_fibre hO hne han hdet
  refine (fib_finite M Ψ hP hΨ y).not_infinite ((Set.Infinite.image
    ((M.atlas.chart j).symm.injOn.mono fun u hu => hOt hu.1) hy).mono ?_)
  rintro _ ⟨u, ⟨huO, hqu⟩, rfl⟩
  exact ⟨hqu, h0 u huO⟩

/- English proof (translation)
Use `set u := M.atlas.chart j x`. Establish `hsu : (M.atlas.chart j).symm u = x` using `(M.atlas.chart j).left_inv hj`. Use `set T := M.atlas.chart k ∘ (M.atlas.chart j).symm with hTdef`. Establish `huk : u ∈ (M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' (M.atlas.chart k).source` using `⟨(M.atlas.chart j).map_source hj, by rw [mem_preimage, hsu]; exact hk⟩`. Establish `hT : AnalyticAt ℂ T u` using `M.atlas.holo j k u huk`.

Establish `hTu : T u = M.atlas.chart k x` using `by simp only [hTdef, Function.comp_apply, hsu]`. Establish `hQk` using `analyticAt_modelQ M Ψ x k hk h0`. Establish `heq : modelQ M Ψ ∘ (M.atlas.chart j).symm =ᶠ[𝓝 u] (modelQ M Ψ ∘ (M.atlas.chart k).symm) ∘ T` using `by filter_upwards [((M.atlas.chart j).isOpen_inter_preimage_symm (M.atlas.chart k).open_source).mem_nhds huk] with v hv`. Simplify using `only [hTdef, Function.comp_apply, (M.atlas.chart k).left_inv hv.2]`. Rewrite using `[heq.fderiv_eq, fderiv_comp u (by rw [hTu]; exact hQk.differentiableAt) hT.differentiableAt, hTu]`.

Conclude with `LinearMap.det_comp _ _`.
-/
theorem det_chart (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) {x : M.Xc}
    {j k : Fin M.atlas.n} (hj : x ∈ (M.atlas.chart j).source) (hk : x ∈ (M.atlas.chart k).source)
    (h0 : Ψ (segre (modelLift M x x)) 0 ≠ 0) :
    LinearMap.det (fderiv ℂ (modelQ M Ψ ∘ (M.atlas.chart j).symm) (M.atlas.chart j x) :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) =
      LinearMap.det (fderiv ℂ (modelQ M Ψ ∘ (M.atlas.chart k).symm) (M.atlas.chart k x) :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) *
      LinearMap.det (fderiv ℂ (M.atlas.chart k ∘ (M.atlas.chart j).symm) (M.atlas.chart j x) :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) := by
  set u := M.atlas.chart j x
  have hsu : (M.atlas.chart j).symm u = x := (M.atlas.chart j).left_inv hj
  set T := M.atlas.chart k ∘ (M.atlas.chart j).symm with hTdef
  have huk : u ∈ (M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' (M.atlas.chart k).source :=
    ⟨(M.atlas.chart j).map_source hj, by rw [mem_preimage, hsu]; exact hk⟩
  have hT : AnalyticAt ℂ T u := M.atlas.holo j k u huk
  have hTu : T u = M.atlas.chart k x := by simp only [hTdef, Function.comp_apply, hsu]
  have hQk := analyticAt_modelQ M Ψ x k hk h0
  have heq : modelQ M Ψ ∘ (M.atlas.chart j).symm =ᶠ[𝓝 u] (modelQ M Ψ ∘ (M.atlas.chart k).symm) ∘ T := by
    filter_upwards [((M.atlas.chart j).isOpen_inter_preimage_symm (M.atlas.chart k).open_source).mem_nhds
      huk] with v hv
    simp only [hTdef, Function.comp_apply, (M.atlas.chart k).left_inv hv.2]
  rw [heq.fderiv_eq, fderiv_comp u (by rw [hTu]; exact hQk.differentiableAt) hT.differentiableAt,
    hTu]
  exact LinearMap.det_comp _ _

/- English proof (translation)
Apply `ReciprocityTheory.AnForm.volume_eq_zero_of_locally_in_analytic_zero_set` to reduce the goal to its premises. Introduce and unpack `u0 ⟨hu0, h00, -⟩`. Use `set x0 := (M.atlas.chart j).symm u0`. Use `set V := (M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' modelU M x0 with hVdef`. Establish `hV : IsOpen V` using `(M.atlas.chart j).isOpen_inter_preimage_symm (modelU_isOpen M x0)`.

Establish `hgc : ContinuousOn (fun u => Ψ (segre (modelLift M x0 ((M.atlas.chart j).symm u))) 0) V` using `fun u hu => (analyticAt_pi_iff.mp (analyticAt_segre_lift M Ψ x0 j hu) 0).continuousAt.continuousWithinAt`. Use `set O := V ∩ (fun u => Ψ (segre (modelLift M x0 ((M.atlas.chart j).symm u))) 0) ⁻¹' {0}ᶜ with hOdef`. Establish `hO : IsOpen O` using `hgc.isOpen_inter_preimage hV isOpen_compl_singleton`. Establish `hl0 : Ψ (segre (modelLift M x0 ((M.atlas.chart j).symm u0))) 0 ≠ 0` using `h00`. Establish `hu0O : u0 ∈ O` using `⟨⟨hu0, mem_modelU M x0⟩, hl0⟩`.

Take `⟨r, hr, hball⟩` from `Metric.isOpen_iff.mp hO u0 hu0O`. Establish `h0 : ∀ u ∈ Metric.ball u0 r, Ψ (segre (modelLift M ((M.atlas.chart j).symm u) ((M.atlas.chart j).symm u))) 0 ≠ 0`. Introduce `u hu`. Take `⟨μ, hμ, hμeq⟩` from `psi_lift_eq M (hball hu).1.2 Ψ`. Rewrite using `[hμeq, Pi.smul_apply, smul_eq_mul]`.

Conclude with `mul_ne_zero hμ (hball hu).2`. Establish `hQa : AnalyticOnNhd ℂ (modelQ M Ψ ∘ (M.atlas.chart j).symm) (Metric.ball u0 r)`. Introduce `u hu`. Use `analyticAt_modelQ M Ψ _ j ((M.atlas.chart j).map_target (hball hu).1.1) (h0 u hu)` as an intermediate fact. Rewrite `this` using `[(M.atlas.chart j).right_inv (hball hu).1.1]`. Then use the resulting hypothesis.

Use `⟨Metric.ball u0 r, Metric.isOpen_ball, Metric.mem_ball_self hr, (convex_ball u0 r).isPreconnected, fun u => LinearMap.det (fderiv ℂ (modelQ M Ψ ∘ (M.atlas.chart j).symm) u : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)), fun u hu => analyticAt_det_fderiv (hQa u hu), ?_, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hall push Not at hall`. Conclude with `not_flat M Ψ hP hΨ j Metric.isOpen_ball (fun u hu => (hball hu).1.1) ⟨u0, Metric.mem_ball_self hr⟩ h0 hQa hall`. Introduce and unpack `w ⟨⟨hwt, hw0, k, hk, hdk⟩, -⟩`. Use `det_chart M Ψ (j := j) ((M.atlas.chart j).map_target hwt) hk hw0` as an intermediate fact.

Rewrite `this` using `[(M.atlas.chart j).right_inv hwt]`. Use `show LinearMap.det (fderiv ℂ (modelQ M Ψ ∘ (M.atlas.chart j).symm) w : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) = 0`. Rewrite using `[this, hdk, zero_mul]`.
-/
theorem ram_null (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) (j : Fin M.atlas.n) :
    volume ((M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' {x | Ψ (segre (modelLift M x x)) 0 ≠ 0 ∧
      ∃ k, x ∈ (M.atlas.chart k).source ∧
        LinearMap.det (fderiv ℂ (modelQ M Ψ ∘ (M.atlas.chart k).symm) (M.atlas.chart k x) :
          (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) = 0}) = 0 := by
  apply ReciprocityTheory.AnForm.volume_eq_zero_of_locally_in_analytic_zero_set
  rintro u0 ⟨hu0, h00, -⟩
  set x0 := (M.atlas.chart j).symm u0
  set V := (M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' modelU M x0 with hVdef
  have hV : IsOpen V := (M.atlas.chart j).isOpen_inter_preimage_symm (modelU_isOpen M x0)
  have hgc : ContinuousOn (fun u => Ψ (segre (modelLift M x0 ((M.atlas.chart j).symm u))) 0) V :=
    fun u hu => (analyticAt_pi_iff.mp (analyticAt_segre_lift M Ψ x0 j hu) 0).continuousAt.continuousWithinAt
  set O := V ∩ (fun u => Ψ (segre (modelLift M x0 ((M.atlas.chart j).symm u))) 0) ⁻¹' {0}ᶜ with hOdef
  have hO : IsOpen O := hgc.isOpen_inter_preimage hV isOpen_compl_singleton
  have hl0 : Ψ (segre (modelLift M x0 ((M.atlas.chart j).symm u0))) 0 ≠ 0 := h00
  have hu0O : u0 ∈ O := ⟨⟨hu0, mem_modelU M x0⟩, hl0⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hO u0 hu0O
  have h0 : ∀ u ∈ Metric.ball u0 r,
      Ψ (segre (modelLift M ((M.atlas.chart j).symm u) ((M.atlas.chart j).symm u))) 0 ≠ 0 := by
    intro u hu
    obtain ⟨μ, hμ, hμeq⟩ := psi_lift_eq M (hball hu).1.2 Ψ
    rw [hμeq, Pi.smul_apply, smul_eq_mul]
    exact mul_ne_zero hμ (hball hu).2
  have hQa : AnalyticOnNhd ℂ (modelQ M Ψ ∘ (M.atlas.chart j).symm) (Metric.ball u0 r) := by
    intro u hu
    have := analyticAt_modelQ M Ψ _ j ((M.atlas.chart j).map_target (hball hu).1.1) (h0 u hu)
    rwa [(M.atlas.chart j).right_inv (hball hu).1.1] at this
  refine ⟨Metric.ball u0 r, Metric.isOpen_ball, Metric.mem_ball_self hr,
    (convex_ball u0 r).isPreconnected, fun u => LinearMap.det (fderiv ℂ (modelQ M Ψ ∘ (M.atlas.chart j).symm) u :
      (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)), fun u hu => analyticAt_det_fderiv (hQa u hu), ?_, ?_⟩
  · by_contra hall
    push Not at hall
    exact not_flat M Ψ hP hΨ j Metric.isOpen_ball (fun u hu => (hball hu).1.1)
      ⟨u0, Metric.mem_ball_self hr⟩ h0 hQa hall
  · rintro w ⟨⟨hwt, hw0, k, hk, hdk⟩, -⟩
    have := det_chart M Ψ (j := j) ((M.atlas.chart j).map_target hwt) hk hw0
    rw [(M.atlas.chart j).right_inv hwt] at this
    show LinearMap.det (fderiv ℂ (modelQ M Ψ ∘ (M.atlas.chart j).symm) w :
      (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) = 0
    rw [this, hdk, zero_mul]

/- English proof (translation)
Apply `ReciprocityTheory.AnForm.volume_eq_zero_of_locally_in_analytic_zero_set` to reduce the goal to its premises. Introduce and unpack `u0 ⟨hu0, -⟩`. Use `set x0 := (M.atlas.chart j).symm u0`. Use `set V := (M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' modelU M x0 with hVdef`. Establish `hV : IsOpen V` using `(M.atlas.chart j).isOpen_inter_preimage_symm (modelU_isOpen M x0)`.

Establish `hu0V : u0 ∈ V` using `⟨hu0, mem_modelU M x0⟩`. Take `⟨r, hr, hball⟩` from `Metric.isOpen_iff.mp hV u0 hu0V`. Use `set f : (Fin e → ℂ) → ℂ := fun u => Ψ (segre (modelLift M x0 ((M.atlas.chart j).symm u))) 0 with hfdef`. Establish `hfa : AnalyticOnNhd ℂ f V` using `fun u hu => analyticAt_pi_iff.mp (analyticAt_segre_lift M Ψ x0 j hu) 0`. Use `⟨Metric.ball u0 r, Metric.isOpen_ball, Metric.mem_ball_self hr, (convex_ball u0 r).isPreconnected, f, hfa.mono hball, ?_, ?_⟩` and prove the remaining obligations.

Assume the negation of the conclusion as `hall push Not at hall`. Establish `hgood` using `hΨ _ (lift_mem M x0)`. Choose the witnesses or unpack the hypotheses as in `⟨i0, hi0⟩ : ∃ i0, Ψ (segre (modelLift M x0 x0)) i0 ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push Not at h`.

Conclude with `hgood (funext h)`. Establish `hi0ne : i0 ≠ 0`. Introduce and unpack `rfl`. Conclude with `hi0 (hall u0 (Metric.mem_ball_self hr))`. Use `set m : Fin e := i0.pred hi0ne`.

Establish `hm : m.succ = i0` using `Fin.succ_pred i0 hi0ne`. Use `set Ψ' : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ) := (LinearMap.funLeft ℂ ℂ (Equiv.swap (0 : Fin (e + 1)) i0)).comp Ψ with hΨ'def`. Establish `hΨ'app : ∀ w i, Ψ' w i = Ψ w (Equiv.swap 0 i0 i)` using `fun w i => rfl`. Establish `hΨ' : IsGoodProj P Ψ'`. Introduce `z hz h`.

Use `hΨ z hz (funext fun i => ?_)` and prove the remaining obligations. Use `congrFun h (Equiv.swap 0 i0 i)` as an intermediate fact. Rewrite `this` using `[hΨ'app, Equiv.swap_apply_self]`. Conclude with `this`. Establish `hg'c : ContinuousOn (fun u => Ψ' (segre (modelLift M x0 ((M.atlas.chart j).symm u))) 0) (Metric.ball u0 r)` using `fun u hu => (analyticAt_pi_iff.mp (analyticAt_segre_lift M Ψ' x0 j (hball hu)) 0).continuousAt.continuousWithinAt`.

Use `set O := Metric.ball u0 r ∩ (fun u => Ψ' (segre (modelLift M x0 ((M.atlas.chart j).symm u))) 0) ⁻¹' {0}ᶜ with hOdef`. Establish `hO : IsOpen O` using `hg'c.isOpen_inter_preimage Metric.isOpen_ball isOpen_compl_singleton`. Establish `hu0O : u0 ∈ O`. Use `⟨Metric.mem_ball_self hr, ?_⟩` and prove the remaining obligations. Use `show Ψ' (segre (modelLift M x0 x0)) 0 ≠ 0`.

Rewrite using `[hΨ'app, Equiv.swap_apply_left]`. Conclude with `hi0`. Establish `h0O : ∀ u ∈ O, Ψ' (segre (modelLift M ((M.atlas.chart j).symm u) ((M.atlas.chart j).symm u))) 0 ≠ 0`. Introduce `u hu`. Take `⟨μ, hμ, hμeq⟩` from `psi_lift_eq M (hball hu.1).2 Ψ'`.

Rewrite using `[hμeq, Pi.smul_apply, smul_eq_mul]`. Conclude with `mul_ne_zero hμ hu.2`. Establish `hanO : AnalyticOnNhd ℂ (modelQ M Ψ' ∘ (M.atlas.chart j).symm) O`. Introduce `u hu`. Use `analyticAt_modelQ M Ψ' _ j ((M.atlas.chart j).map_target (hball hu.1).1) (h0O u hu)` as an intermediate fact.

Rewrite `this` using `[(M.atlas.chart j).right_inv (hball hu.1).1]`. Then use the resulting hypothesis. Establish `hzero : ∀ u ∈ O, (modelQ M Ψ' ∘ (M.atlas.chart j).symm) u m = 0`. Introduce `u hu`. Simplify using `only [Function.comp_apply, modelQ]`. Rewrite using `[hm, hΨ'app, Equiv.swap_apply_right]`.

Take `⟨μ, hμ, hμeq⟩` from `psi_lift_eq M (hball hu.1).2 Ψ`. Rewrite using `[hμeq, Pi.smul_apply, smul_eq_mul]`. Establish `: f u = 0` using `hall u hu.1`. Simplify using `only [hfdef] at this`. Rewrite using `[this, mul_zero, zero_div]`.

Establish `hdetO : ∀ u ∈ O, LinearMap.det (fderiv ℂ (modelQ M Ψ' ∘ (M.atlas.chart j).symm) u : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) = 0`. Introduce `u hu`. Establish `hcoord : (fun v => (modelQ M Ψ' ∘ (M.atlas.chart j).symm) v m) =ᶠ[𝓝 u] fun _ => 0` using `by filter_upwards [hO.mem_nhds hu] with v hv`. Conclude with `hzero v hv`. Establish `hd : HasFDerivAt (fun v => (modelQ M Ψ' ∘ (M.atlas.chart j).symm) v m) ((ContinuousLinearMap.proj m).comp (fderiv ℂ (modelQ M Ψ' ∘ (M.atlas.chart j).symm) u)) u` using `(ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin e => ℂ) m).hasFDerivAt.comp u (hanO u hu).differentiableAt.hasFDerivAt`.

Establish `hd0 : HasFDerivAt (fun v => (modelQ M Ψ' ∘ (M.atlas.chart j).symm) v m) (0 : (Fin e → ℂ) →L[ℂ] ℂ) u` using `(hasFDerivAt_const (0 : ℂ) u).congr_of_eventuallyEq hcoord`. Establish `hrow` using `hd.unique hd0`. Use `det_eq_zero_of_coord m fun v => ?_` and prove the remaining obligations. Use `congrArg (fun T : (Fin e → ℂ) →L[ℂ] ℂ => T v) hrow` as an intermediate fact. Simplify using `using this`.

Conclude with `not_flat M Ψ' hP hΨ' j hO (fun u hu => (hball hu.1).1) ⟨u0, hu0O⟩ h0O hanO hdetO`. Introduce and unpack `w ⟨⟨hwt, hw0⟩, hwb⟩`. Take `⟨μ, hμ, hμeq⟩` from `psi_lift_eq M (hball hwb).2 Ψ`. Use `congrFun hμeq 0` as an intermediate fact. Rewrite `this` using `[Pi.smul_apply, smul_eq_mul]`.

Establish `hw0' : Ψ (segre (modelLift M ((M.atlas.chart j).symm w) ((M.atlas.chart j).symm w))) 0 = 0` using `hw0`. Rewrite `this` using `[hw0']`. Conclude with `(mul_eq_zero.mp this.symm).resolve_left hμ`.
-/
theorem psi0_null (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) (j : Fin M.atlas.n) :
    volume ((M.atlas.chart j).target ∩
      (M.atlas.chart j).symm ⁻¹' {x | Ψ (segre (modelLift M x x)) 0 = 0}) = 0 := by
  classical
  apply ReciprocityTheory.AnForm.volume_eq_zero_of_locally_in_analytic_zero_set
  rintro u0 ⟨hu0, -⟩
  set x0 := (M.atlas.chart j).symm u0
  set V := (M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' modelU M x0 with hVdef
  have hV : IsOpen V := (M.atlas.chart j).isOpen_inter_preimage_symm (modelU_isOpen M x0)
  have hu0V : u0 ∈ V := ⟨hu0, mem_modelU M x0⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hV u0 hu0V
  set f : (Fin e → ℂ) → ℂ := fun u => Ψ (segre (modelLift M x0 ((M.atlas.chart j).symm u))) 0 with hfdef
  have hfa : AnalyticOnNhd ℂ f V := fun u hu =>
    analyticAt_pi_iff.mp (analyticAt_segre_lift M Ψ x0 j hu) 0
  refine ⟨Metric.ball u0 r, Metric.isOpen_ball, Metric.mem_ball_self hr,
    (convex_ball u0 r).isPreconnected, f, hfa.mono hball, ?_, ?_⟩
  · by_contra hall
    push Not at hall
    have hgood := hΨ _ (lift_mem M x0)
    obtain ⟨i0, hi0⟩ : ∃ i0, Ψ (segre (modelLift M x0 x0)) i0 ≠ 0 := by
      by_contra h
      push Not at h
      exact hgood (funext h)
    have hi0ne : i0 ≠ 0 := by
      rintro rfl
      exact hi0 (hall u0 (Metric.mem_ball_self hr))
    set m : Fin e := i0.pred hi0ne
    have hm : m.succ = i0 := Fin.succ_pred i0 hi0ne
    set Ψ' : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ) :=
      (LinearMap.funLeft ℂ ℂ (Equiv.swap (0 : Fin (e + 1)) i0)).comp Ψ with hΨ'def
    have hΨ'app : ∀ w i, Ψ' w i = Ψ w (Equiv.swap 0 i0 i) := fun w i => rfl
    have hΨ' : IsGoodProj P Ψ' := by
      intro z hz h
      refine hΨ z hz (funext fun i => ?_)
      have := congrFun h (Equiv.swap 0 i0 i)
      rw [hΨ'app, Equiv.swap_apply_self] at this
      exact this
    have hg'c : ContinuousOn (fun u => Ψ' (segre (modelLift M x0 ((M.atlas.chart j).symm u))) 0)
        (Metric.ball u0 r) := fun u hu =>
      (analyticAt_pi_iff.mp (analyticAt_segre_lift M Ψ' x0 j (hball hu)) 0).continuousAt.continuousWithinAt
    set O := Metric.ball u0 r ∩
      (fun u => Ψ' (segre (modelLift M x0 ((M.atlas.chart j).symm u))) 0) ⁻¹' {0}ᶜ with hOdef
    have hO : IsOpen O := hg'c.isOpen_inter_preimage Metric.isOpen_ball isOpen_compl_singleton
    have hu0O : u0 ∈ O := by
      refine ⟨Metric.mem_ball_self hr, ?_⟩
      show Ψ' (segre (modelLift M x0 x0)) 0 ≠ 0
      rw [hΨ'app, Equiv.swap_apply_left]
      exact hi0
    have h0O : ∀ u ∈ O,
        Ψ' (segre (modelLift M ((M.atlas.chart j).symm u) ((M.atlas.chart j).symm u))) 0 ≠ 0 := by
      intro u hu
      obtain ⟨μ, hμ, hμeq⟩ := psi_lift_eq M (hball hu.1).2 Ψ'
      rw [hμeq, Pi.smul_apply, smul_eq_mul]
      exact mul_ne_zero hμ hu.2
    have hanO : AnalyticOnNhd ℂ (modelQ M Ψ' ∘ (M.atlas.chart j).symm) O := by
      intro u hu
      have := analyticAt_modelQ M Ψ' _ j ((M.atlas.chart j).map_target (hball hu.1).1) (h0O u hu)
      rwa [(M.atlas.chart j).right_inv (hball hu.1).1] at this
    have hzero : ∀ u ∈ O, (modelQ M Ψ' ∘ (M.atlas.chart j).symm) u m = 0 := by
      intro u hu
      simp only [Function.comp_apply, modelQ]
      rw [hm, hΨ'app, Equiv.swap_apply_right]
      obtain ⟨μ, hμ, hμeq⟩ := psi_lift_eq M (hball hu.1).2 Ψ
      rw [hμeq, Pi.smul_apply, smul_eq_mul]
      have : f u = 0 := hall u hu.1
      simp only [hfdef] at this
      rw [this, mul_zero, zero_div]
    have hdetO : ∀ u ∈ O, LinearMap.det (fderiv ℂ (modelQ M Ψ' ∘ (M.atlas.chart j).symm) u :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) = 0 := by
      intro u hu
      have hcoord : (fun v => (modelQ M Ψ' ∘ (M.atlas.chart j).symm) v m) =ᶠ[𝓝 u] fun _ => 0 := by
        filter_upwards [hO.mem_nhds hu] with v hv
        exact hzero v hv
      have hd : HasFDerivAt (fun v => (modelQ M Ψ' ∘ (M.atlas.chart j).symm) v m)
          ((ContinuousLinearMap.proj m).comp (fderiv ℂ (modelQ M Ψ' ∘ (M.atlas.chart j).symm) u)) u :=
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin e => ℂ) m).hasFDerivAt.comp u
          (hanO u hu).differentiableAt.hasFDerivAt
      have hd0 : HasFDerivAt (fun v => (modelQ M Ψ' ∘ (M.atlas.chart j).symm) v m)
          (0 : (Fin e → ℂ) →L[ℂ] ℂ) u :=
        (hasFDerivAt_const (0 : ℂ) u).congr_of_eventuallyEq hcoord
      have hrow := hd.unique hd0
      refine det_eq_zero_of_coord m fun v => ?_
      have := congrArg (fun T : (Fin e → ℂ) →L[ℂ] ℂ => T v) hrow
      simpa using this
    exact not_flat M Ψ' hP hΨ' j hO (fun u hu => (hball hu.1).1) ⟨u0, hu0O⟩ h0O hanO hdetO
  · rintro w ⟨⟨hwt, hw0⟩, hwb⟩
    obtain ⟨μ, hμ, hμeq⟩ := psi_lift_eq M (hball hwb).2 Ψ
    have := congrFun hμeq 0
    rw [Pi.smul_apply, smul_eq_mul] at this
    have hw0' : Ψ (segre (modelLift M ((M.atlas.chart j).symm w) ((M.atlas.chart j).symm w))) 0 = 0 := hw0
    rw [hw0'] at this
    exact (mul_eq_zero.mp this.symm).resolve_left hμ

/- English proof (translation)
Introduce `K _ ι _ P n M Q j hP hQ`. Use `measure_mono_null ?_ (measure_union_null (psi0_null M Q hP hQ j) (ram_null M Q hP hQ j))` and prove the remaining obligations. Introduce and unpack `u ⟨hu, hc⟩`. Distinguish the cases in `h0 : Q (segre (modelLift M ((M.atlas.chart j).symm u) ((M.atlas.chart j).symm u))) 0 = 0`. Conclude with `Or.inl ⟨hu, h0⟩`.

Use `Or.inr ⟨hu, h0, ?_⟩` and prove the remaining obligations. Break down `hc with h | ⟨k, hk, hbad⟩` into its components or cases. Conclude with `absurd h h0`. Use `⟨k, hk, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hd`.

Conclude with `hbad ⟨analyticAt_modelQ M Q _ k hk h0, hd⟩`.
-/
theorem modelCrit_null : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι))
    (n : ℕ) (M : CxModel P n) (Q : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) (j : Fin M.atlas.n),
    IsArithVar P (n + 1) → IsGoodProj P Q →
      volume ((M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' modelCrit M Q) = 0 := by
  intro K _ ι _ P n M Q j hP hQ
  refine measure_mono_null ?_ (measure_union_null (psi0_null M Q hP hQ j) (ram_null M Q hP hQ j))
  rintro u ⟨hu, hc⟩
  by_cases h0 : Q (segre (modelLift M ((M.atlas.chart j).symm u) ((M.atlas.chart j).symm u))) 0 = 0
  · exact Or.inl ⟨hu, h0⟩
  · refine Or.inr ⟨hu, h0, ?_⟩
    rcases hc with h | ⟨k, hk, hbad⟩
    · exact absurd h h0
    · refine ⟨k, hk, ?_⟩
      by_contra hd
      exact hbad ⟨analyticAt_modelQ M Q _ k hk h0, hd⟩

end GlobalTheory.CompanionTheory.Ar.Giv.Push.Crit
