import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SectionBoundaryClosedAndCodense

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P Filter Topology
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.FlatBound

/- English proof (translation)
Set `L : ℂ →L[ℝ] (Fin n → ℂ)` to `((ContinuousLinearMap.id ℂ ℂ).smulRight e).restrictScalars ℝ`. Establish `hLw : ∀ w : ℂ, L w = w • e` using `fun _ => rfl`. Establish `hline : ∀ t : ℂ, HasFDerivAt (fun w : ℂ => z₀ + w • e) L t` using `fun t => L.hasFDerivAt.const_add z₀`. Establish `hcont : Continuous (fun t : ℂ => z₀ + t • e)` using `by fun_prop`. Establish `hU : IsOpen ((fun t : ℂ => z₀ + t • e) ⁻¹' O)` using `hO.preimage hcont`.

Apply the tactic sequence `have hφ2 : ∀ y ∈ O, ContDiffAt ℝ 2 φ y := fun y hy => ((hφ y hy).contDiffAt (hO.mem_nhds hy)).of_le (by first | exact WithTop.coe_le_coe.mpr le_top | simp)`. Establish `hlap : ∀ t ∈ (fun t : ℂ => z₀ + t • e) ⁻¹' O, Laplacian.laplacian (fun t : ℂ => φ (z₀ + t • e)) t = 0`. Introduce `t ht`. Establish `hy : z₀ + t • e ∈ O` using `ht`. Establish `h1 : fderiv ℝ (fun w : ℂ => φ (z₀ + w • e)) =ᶠ[𝓝 t] fun w : ℂ => (fderiv ℝ φ (z₀ + w • e)).comp L` using `by filter_upwards [hU.mem_nhds ht] with w hw`.

Conclude with `(((hφ2 _ hw).differentiableAt (by simp)).hasFDerivAt.comp w (hline w)).fderiv`. Establish `hD : HasFDerivAt (fderiv ℝ φ) (fderiv ℝ (fderiv ℝ φ) (z₀ + t • e)) (z₀ + t • e)` using `(((hφ2 _ hy).fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)).hasFDerivAt`. Establish `h2` using `((hD.comp t (hline t)).clm_comp (hasFDerivAt_const L t)).fderiv`. Simplify using `only [Function.comp_def] at h2`. Establish `hle` using `hl _ hy e`.

Unfold `levi at hle`. Rewrite using `[InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]`. Simplify using `only [iteratedFDeriv_two_apply]`. Rewrite using `[h1.fderiv_eq, h2]`. Simplify using `[hLw]`.

Combine the linear equalities and inequalities to obtain the conclusion. Introduce `t ht`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `hA : ContDiffAt ℝ 2 (fun t : ℂ => z₀ + t • e) t`. Establish `: ContDiff ℝ 2 (fun t : ℂ => z₀ + L t)` using `contDiff_const.add L.contDiff`.

Conclude with `this.contDiffAt`. Conclude with `(hφ2 _ ht).comp t hA`. Use `filter_upwards [hU.mem_nhds ht] with s hs`. Simplify using `using hlap s hs`.
-/
theorem harmonicOnNhd_line {n : ℕ} {φ : (Fin n → ℂ) → ℝ} {O : Set (Fin n → ℂ)} (hO : IsOpen O)
    (hφ : ContDiffOn ℝ ∞ φ O) (hl : ∀ z ∈ O, ∀ w, levi φ z w = 0) (z₀ e : Fin n → ℂ) :
    InnerProductSpace.HarmonicOnNhd (fun t : ℂ => φ (z₀ + t • e))
      ((fun t : ℂ => z₀ + t • e) ⁻¹' O) := by
  let L : ℂ →L[ℝ] (Fin n → ℂ) := ((ContinuousLinearMap.id ℂ ℂ).smulRight e).restrictScalars ℝ
  have hLw : ∀ w : ℂ, L w = w • e := fun _ => rfl
  have hline : ∀ t : ℂ, HasFDerivAt (fun w : ℂ => z₀ + w • e) L t := fun t =>
    L.hasFDerivAt.const_add z₀
  have hcont : Continuous (fun t : ℂ => z₀ + t • e) := by fun_prop
  have hU : IsOpen ((fun t : ℂ => z₀ + t • e) ⁻¹' O) := hO.preimage hcont
  have hφ2 : ∀ y ∈ O, ContDiffAt ℝ 2 φ y := fun y hy =>
    ((hφ y hy).contDiffAt (hO.mem_nhds hy)).of_le (by first | exact WithTop.coe_le_coe.mpr le_top | simp)
  have hlap : ∀ t ∈ (fun t : ℂ => z₀ + t • e) ⁻¹' O,
      Laplacian.laplacian (fun t : ℂ => φ (z₀ + t • e)) t = 0 := by
    intro t ht
    have hy : z₀ + t • e ∈ O := ht
    have h1 : fderiv ℝ (fun w : ℂ => φ (z₀ + w • e)) =ᶠ[𝓝 t]
        fun w : ℂ => (fderiv ℝ φ (z₀ + w • e)).comp L := by
      filter_upwards [hU.mem_nhds ht] with w hw
      exact (((hφ2 _ hw).differentiableAt (by simp)).hasFDerivAt.comp w (hline w)).fderiv
    have hD : HasFDerivAt (fderiv ℝ φ) (fderiv ℝ (fderiv ℝ φ) (z₀ + t • e)) (z₀ + t • e) :=
      (((hφ2 _ hy).fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)).hasFDerivAt
    have h2 := ((hD.comp t (hline t)).clm_comp (hasFDerivAt_const L t)).fderiv
    simp only [Function.comp_def] at h2
    have hle := hl _ hy e
    unfold levi at hle
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
    simp only [iteratedFDeriv_two_apply]
    rw [h1.fderiv_eq, h2]
    simp [hLw]
    linarith
  intro t ht
  refine ⟨?_, ?_⟩
  · have hA : ContDiffAt ℝ 2 (fun t : ℂ => z₀ + t • e) t := by
      have : ContDiff ℝ 2 (fun t : ℂ => z₀ + L t) := contDiff_const.add L.contDiff
      exact this.contDiffAt
    exact (hφ2 _ ht).comp t hA
  · filter_upwards [hU.mem_nhds ht] with s hs
    simpa using hlap s hs

/- English proof (translation)
Take `⟨r, hr, hrO⟩` from `Metric.isOpen_iff.1 hO z₀ hz₀`. Use `filter_upwards [Metric.ball_mem_nhds z₀ hr] with z hz`. Use `set e : Fin n → ℂ := z - z₀ with he`. Distinguish the cases in `he0 : e = 0`. Rewrite using `[sub_eq_zero.1 he0]`.

Establish `hepos : 0 < ‖e‖` using `norm_pos_iff.2 he0`. Establish `hlt : ‖e‖ < r` using `by simpa [he, dist_eq_norm] using hz`. Use `set R : ℝ := r / ‖e‖ with hR`. Establish `hR1 : 1 < R` using `(one_lt_div hepos).2 hlt`. Establish `hsub : Metric.ball (0 : ℂ) R ⊆ (fun t : ℂ => z₀ + t • e) ⁻¹' O`.

Introduce `t ht`. Apply `hrO` to reduce the goal to its premises. Establish `ht' : ‖t‖ < R` using `by simpa using ht`. Establish `: ‖t‖ * ‖e‖ < r` using `(lt_div_iff₀ hepos).1 ht'`. Simplify `this` using `[dist_eq_norm, norm_smul]`.

Establish `hh` using `(harmonicOnNhd_line hO hφ hl z₀ e).mono hsub`. Take `⟨F, hF, hre⟩` from `InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq hh`. Establish `h0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) R` using `Metric.mem_ball_self (by linarith)`. Establish `h1 : (1 : ℂ) ∈ Metric.ball (0 : ℂ) R` using `by simpa using hR1`. Establish `hnorm : ∀ t ∈ Metric.ball (0 : ℂ) R, ‖Complex.exp (F t)‖ = Real.exp (φ (z₀ + t • e))` using `fun t ht => by`.

Rewrite using `[Complex.norm_exp]`. Conclude with `congrArg Real.exp (hre ht)`. Establish `hdiff : DifferentiableOn ℂ (fun t => Complex.exp (F t)) (Metric.ball (0 : ℂ) R)` using `fun t ht => (hF t ht).differentiableAt.cexp.differentiableWithinAt`. Establish `hM : IsMaxOn (norm ∘ fun t => Complex.exp (F t)) (Metric.ball (0 : ℂ) R) 0`. Introduce `t ht`.

Simplify using `only [Set.mem_setOf_eq, Function.comp_apply]`. Rewrite using `[hnorm t ht, hnorm 0 h0]`. Simplify using `using hmax _ (hsub ht)`. Establish `hEq` using `Complex.norm_eqOn_of_isPreconnected_of_isMaxOn (convex_ball (0 : ℂ) R).isPreconnected Metric.isOpen_ball hdiff h0 hM h1`. Simplify using `only [Function.comp_apply, Function.const_apply] at hEq`.

Rewrite `hEq` using `[hnorm 1 h1, hnorm 0 h0]`. Use `Real.exp_injective hEq` as an intermediate fact. Simplify `this` using `[he]`.
-/
theorem eventually_eq_of_isMax {n : ℕ} {φ : (Fin n → ℂ) → ℝ} {O : Set (Fin n → ℂ)} (hO : IsOpen O)
    (hφ : ContDiffOn ℝ ∞ φ O) (hl : ∀ z ∈ O, ∀ w, levi φ z w = 0) {z₀ : Fin n → ℂ} (hz₀ : z₀ ∈ O)
    (hmax : ∀ z ∈ O, φ z ≤ φ z₀) : ∀ᶠ z in 𝓝 z₀, φ z = φ z₀ := by
  obtain ⟨r, hr, hrO⟩ := Metric.isOpen_iff.1 hO z₀ hz₀
  filter_upwards [Metric.ball_mem_nhds z₀ hr] with z hz
  set e : Fin n → ℂ := z - z₀ with he
  by_cases he0 : e = 0
  · rw [sub_eq_zero.1 he0]
  have hepos : 0 < ‖e‖ := norm_pos_iff.2 he0
  have hlt : ‖e‖ < r := by simpa [he, dist_eq_norm] using hz
  set R : ℝ := r / ‖e‖ with hR
  have hR1 : 1 < R := (one_lt_div hepos).2 hlt
  have hsub : Metric.ball (0 : ℂ) R ⊆ (fun t : ℂ => z₀ + t • e) ⁻¹' O := by
    intro t ht
    apply hrO
    have ht' : ‖t‖ < R := by simpa using ht
    have : ‖t‖ * ‖e‖ < r := (lt_div_iff₀ hepos).1 ht'
    simpa [dist_eq_norm, norm_smul] using this
  have hh := (harmonicOnNhd_line hO hφ hl z₀ e).mono hsub
  obtain ⟨F, hF, hre⟩ := InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq hh
  have h0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) R := Metric.mem_ball_self (by linarith)
  have h1 : (1 : ℂ) ∈ Metric.ball (0 : ℂ) R := by simpa using hR1
  have hnorm : ∀ t ∈ Metric.ball (0 : ℂ) R, ‖Complex.exp (F t)‖ = Real.exp (φ (z₀ + t • e)) :=
    fun t ht => by
      rw [Complex.norm_exp]
      exact congrArg Real.exp (hre ht)
  have hdiff : DifferentiableOn ℂ (fun t => Complex.exp (F t)) (Metric.ball (0 : ℂ) R) :=
    fun t ht => (hF t ht).differentiableAt.cexp.differentiableWithinAt
  have hM : IsMaxOn (norm ∘ fun t => Complex.exp (F t)) (Metric.ball (0 : ℂ) R) 0 := by
    intro t ht
    simp only [Set.mem_setOf_eq, Function.comp_apply]
    rw [hnorm t ht, hnorm 0 h0]
    simpa using hmax _ (hsub ht)
  have hEq := Complex.norm_eqOn_of_isPreconnected_of_isMaxOn
    (convex_ball (0 : ℂ) R).isPreconnected Metric.isOpen_ball hdiff h0 hM h1
  simp only [Function.comp_apply, Function.const_apply] at hEq
  rw [hnorm 1 h1, hnorm 0 h0] at hEq
  have := Real.exp_injective hEq
  simpa [he] using this

/- English proof (translation)
Establish `hKo : IsOpen (connectedComponent x)` using `isOpen_connectedComponent`. Establish `hKc : IsClosed (connectedComponent x)` using `isClosed_connectedComponent`. Take `⟨m, hmK, hm⟩` from `hKc.isCompact.exists_isMaxOn ⟨x, mem_connectedComponent⟩ hv.continuousOn`. Establish `hKm : connectedComponent m = connectedComponent x` using `(connectedComponent_eq hmK).symm`. Establish `hTc : IsClosed (connectedComponent x ∩ v ⁻¹' {v m})` using `hKc.inter (isClosed_singleton.preimage hv)`.

Establish `hTo : IsOpen (connectedComponent x ∩ v ⁻¹' {v m})`. Rewrite using `[isOpen_iff_mem_nhds]`. Introduce and unpack `y ⟨hyK, hyv⟩`. Establish `hyv' : v y = v m` using `hyv`. Establish `hev` using `hloc y _ hKo hyK (fun z hz => by rw [hyv']; exact hm hz)`.

Use `filter_upwards [hev, hKo.mem_nhds hyK] with z hz hzK`. Conclude with `⟨hzK, by simp [hz, hyv']⟩`. Establish `hsub : connectedComponent m ⊆ connectedComponent x ∩ v ⁻¹' {v m}` using `IsClopen.connectedComponent_subset ⟨hTc, hTo⟩ ⟨hmK, rfl⟩`. Rewrite `hsub` using `[hKm]`. Establish `h1 : v y = v m` using `(hsub hxy).2`.

Establish `h2 : v x = v m` using `(hsub mem_connectedComponent).2`. Rewrite using `[h1, h2]`.
-/
theorem eq_of_mem_connectedComponent {X : Type} [TopologicalSpace X] [CompactSpace X]
    [LocallyConnectedSpace X] {v : X → ℝ} (hv : Continuous v)
    (hloc : ∀ (x : X) (V : Set X), IsOpen V → x ∈ V → (∀ y ∈ V, v y ≤ v x) →
      ∀ᶠ y in 𝓝 x, v y = v x) {x y : X} (hxy : y ∈ connectedComponent x) : v y = v x := by
  have hKo : IsOpen (connectedComponent x) := isOpen_connectedComponent
  have hKc : IsClosed (connectedComponent x) := isClosed_connectedComponent
  obtain ⟨m, hmK, hm⟩ := hKc.isCompact.exists_isMaxOn ⟨x, mem_connectedComponent⟩ hv.continuousOn
  have hKm : connectedComponent m = connectedComponent x := (connectedComponent_eq hmK).symm
  have hTc : IsClosed (connectedComponent x ∩ v ⁻¹' {v m}) :=
    hKc.inter (isClosed_singleton.preimage hv)
  have hTo : IsOpen (connectedComponent x ∩ v ⁻¹' {v m}) := by
    rw [isOpen_iff_mem_nhds]
    rintro y ⟨hyK, hyv⟩
    have hyv' : v y = v m := hyv
    have hev := hloc y _ hKo hyK (fun z hz => by rw [hyv']; exact hm hz)
    filter_upwards [hev, hKo.mem_nhds hyK] with z hz hzK
    exact ⟨hzK, by simp [hz, hyv']⟩
  have hsub : connectedComponent m ⊆ connectedComponent x ∩ v ⁻¹' {v m} :=
    IsClopen.connectedComponent_subset ⟨hTc, hTo⟩ ⟨hmK, rfl⟩
  rw [hKm] at hsub
  have h1 : v y = v m := (hsub hxy).2
  have h2 : v x = v m := (hsub mem_connectedComponent).2
  rw [h1, h2]

/- English proof (translation)
Rewrite using `[continuous_iff_continuousAt]`. Introduce `x`. Take `⟨j, hj⟩` from `A.cover x`. Establish `hmem : (A.chart j).target ∩ (A.chart j).symm ⁻¹' Set.univ ∈ 𝓝 (A.chart j x)`. Simplify using `using (A.chart j).open_target.mem_nhds ((A.chart j).map_source hj)`.

Establish `h1 : ContinuousAt (f ∘ (A.chart j).symm) (A.chart j x)` using `(h j).continuousOn.continuousAt hmem`. Establish `h2 : ContinuousAt ((f ∘ (A.chart j).symm) ∘ (A.chart j)) x` using `ContinuousAt.comp (f := A.chart j) h1 ((A.chart j).continuousAt hj)`. Use `h2.congr ?_` and prove the remaining obligations. Use `filter_upwards [(A.chart j).open_source.mem_nhds hj] with y hy`. Simplify using `[(A.chart j).left_inv hy]`.
-/
theorem continuous_of_smooth {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X}
    {f : X → ℝ} (h : A.Smooth f) : Continuous f := by
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨j, hj⟩ := A.cover x
  have hmem : (A.chart j).target ∩ (A.chart j).symm ⁻¹' Set.univ ∈ 𝓝 (A.chart j x) := by
    simpa using (A.chart j).open_target.mem_nhds ((A.chart j).map_source hj)
  have h1 : ContinuousAt (f ∘ (A.chart j).symm) (A.chart j x) :=
    (h j).continuousOn.continuousAt hmem
  have h2 : ContinuousAt ((f ∘ (A.chart j).symm) ∘ (A.chart j)) x :=
    ContinuousAt.comp (f := A.chart j) h1 ((A.chart j).continuousAt hj)
  refine h2.congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hj] with y hy
  simp [(A.chart j).left_inv hy]

section System

variable {e : ℕ} {σ : Type} (S : PB.AnSys e σ) (a : σ)

/- English proof (translation)
Establish `hs` using `((S.reg a).2.2 t ht ht').1 j`. Establish `hmem : (S.A.chart j).target ∩ (S.A.chart j).symm ⁻¹' Set.univ ∈ 𝓝 y`. Simplify using `using (S.A.chart j).open_target.mem_nhds hy`. Apply the tactic sequence `exact (hs.contDiffAt hmem).of_le (by first | exact WithTop.coe_le_coe.mpr le_top | simp)`.
-/
theorem contDiffAt_phT {t : ℝ} (ht : 0 < t) (ht' : t ≤ S.t₀) (j : Fin S.A.n) {y : Fin e → ℂ}
    (hy : y ∈ (S.A.chart j).target) : ContDiffAt ℝ 2 (S.phT a t ∘ (S.A.chart j).symm) y := by
  have hs := ((S.reg a).2.2 t ht ht').1 j
  have hmem : (S.A.chart j).target ∩ (S.A.chart j).symm ⁻¹' Set.univ ∈ 𝓝 y := by
    simpa using (S.A.chart j).open_target.mem_nhds hy
  exact (hs.contDiffAt hmem).of_le (by first | exact WithTop.coe_le_coe.mpr le_top | simp)

/- English proof (translation)
Use `set p : S.X := (S.A.chart j).symm y with hp`. Establish `hU : p ∈ (S.th a).U p` using `(S.th a).mem_U p`. Establish `hth : ContDiffAt ℝ 2 ((S.th a).φ p ∘ (S.A.chart j).symm) y`. Establish `hs` using `(S.sing a).1.1 p j`. Establish `hmem : (S.A.chart j).target ∩ (S.A.chart j).symm ⁻¹' (S.th a).U p ∈ 𝓝 y` using `((S.A.chart j).isOpen_inter_preimage_symm ((S.th a).isOpen_U p)).mem_nhds ⟨hy, hU⟩`.

Apply the tactic sequence `exact (hs.contDiffAt hmem).of_le (by first | exact WithTop.coe_le_coe.mpr le_top | simp)`. Establish `hG : ContDiffAt ℝ 2 ((S.potT a t).φ p ∘ (S.A.chart j).symm) y` using `hth.add (contDiffAt_phT S a ht ht' j hy)`. Use `⟨hG, ?_⟩` and prove the remaining obligations. Establish `hmemU : y ∈ (S.A.chart j).target ∩ (S.A.chart j).symm ⁻¹' (S.potT a t).U p` using `⟨hy, hU, trivial⟩`. Establish `h1` using `(h t).2 p j y hmemU w`.

Establish `h2` using `(h t).1 p j y hmemU w`. Establish `heq : ((S.potT a t).rsmul (-1)).φ p ∘ (S.A.chart j).symm = fun z => (fun _ => (0 : ℝ)) z + (-1) * ((S.potT a t).φ p ∘ (S.A.chart j).symm) z`. Use function extensionality and compare the values at `z`. Simplify using `[LocPot.rsmul]`. Rewrite `h2` using `[heq, levi_add_smul (-1) contDiffAt_const hG w]`.

Establish `h0 : levi (fun _ : Fin e → ℂ => (0 : ℝ)) y w = 0` using `by simp [levi]`. Rewrite `h2` using `[h0]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem levi_potT_eq_zero (h : ∀ t, IsPsh S.A ((S.potT a t).rsmul (-1)) ∧ IsPsh S.A (S.potT a t))
    {t : ℝ} (ht : 0 < t) (ht' : t ≤ S.t₀) (j : Fin S.A.n) {y : Fin e → ℂ}
    (hy : y ∈ (S.A.chart j).target) (w : Fin e → ℂ) :
    ContDiffAt ℝ 2 ((S.potT a t).φ ((S.A.chart j).symm y) ∘ (S.A.chart j).symm) y ∧
      levi ((S.potT a t).φ ((S.A.chart j).symm y) ∘ (S.A.chart j).symm) y w = 0 := by
  set p : S.X := (S.A.chart j).symm y with hp
  have hU : p ∈ (S.th a).U p := (S.th a).mem_U p
  have hth : ContDiffAt ℝ 2 ((S.th a).φ p ∘ (S.A.chart j).symm) y := by
    have hs := (S.sing a).1.1 p j
    have hmem : (S.A.chart j).target ∩ (S.A.chart j).symm ⁻¹' (S.th a).U p ∈ 𝓝 y :=
      ((S.A.chart j).isOpen_inter_preimage_symm ((S.th a).isOpen_U p)).mem_nhds ⟨hy, hU⟩
    exact (hs.contDiffAt hmem).of_le (by first | exact WithTop.coe_le_coe.mpr le_top | simp)
  have hG : ContDiffAt ℝ 2 ((S.potT a t).φ p ∘ (S.A.chart j).symm) y :=
    hth.add (contDiffAt_phT S a ht ht' j hy)
  refine ⟨hG, ?_⟩
  have hmemU : y ∈ (S.A.chart j).target ∩ (S.A.chart j).symm ⁻¹' (S.potT a t).U p :=
    ⟨hy, hU, trivial⟩
  have h1 := (h t).2 p j y hmemU w
  have h2 := (h t).1 p j y hmemU w
  have heq : ((S.potT a t).rsmul (-1)).φ p ∘ (S.A.chart j).symm =
      fun z => (fun _ => (0 : ℝ)) z + (-1) * ((S.potT a t).φ p ∘ (S.A.chart j).symm) z := by
    funext z
    simp [LocPot.rsmul]
  rw [heq, levi_add_smul (-1) contDiffAt_const hG w] at h2
  have h0 : levi (fun _ : Fin e → ℂ => (0 : ℝ)) y w = 0 := by simp [levi]
  rw [h0] at h2
  linarith

/- English proof (translation)
Take `⟨hG, h1⟩` from `levi_potT_eq_zero S a h ht ht₀ j hy w`. Take `⟨hG', h2⟩` from `levi_potT_eq_zero S a h ht' ht₀' j hy w`. Establish `heq : (fun x => S.phT a t x - S.phT a t' x) ∘ (S.A.chart j).symm = fun z => ((S.potT a t).φ ((S.A.chart j).symm y) ∘ (S.A.chart j).symm) z + (-1) * ((S.potT a t').φ ((S.A.chart j).symm y) ∘ (S.A.chart j).symm) z`. Use function extensionality and compare the values at `z`. Establish `e1 : ∀ s, (S.potT a s).φ ((S.A.chart j).symm y) ((S.A.chart j).symm z) = (S.th a).φ ((S.A.chart j).symm y) ((S.A.chart j).symm z) + S.phT a s ((S.A.chart j).symm z)` using `fun _ => rfl`.

Simplify using `only [Function.comp_apply, e1]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[heq, levi_add_smul (-1) hG hG' w, h1, h2]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem levi_sub_eq_zero (h : ∀ t, IsPsh S.A ((S.potT a t).rsmul (-1)) ∧ IsPsh S.A (S.potT a t))
    {t t' : ℝ} (ht : 0 < t) (ht₀ : t ≤ S.t₀) (ht' : 0 < t') (ht₀' : t' ≤ S.t₀) (j : Fin S.A.n)
    {y : Fin e → ℂ} (hy : y ∈ (S.A.chart j).target) (w : Fin e → ℂ) :
    levi ((fun x => S.phT a t x - S.phT a t' x) ∘ (S.A.chart j).symm) y w = 0 := by
  obtain ⟨hG, h1⟩ := levi_potT_eq_zero S a h ht ht₀ j hy w
  obtain ⟨hG', h2⟩ := levi_potT_eq_zero S a h ht' ht₀' j hy w
  have heq : (fun x => S.phT a t x - S.phT a t' x) ∘ (S.A.chart j).symm =
      fun z => ((S.potT a t).φ ((S.A.chart j).symm y) ∘ (S.A.chart j).symm) z +
        (-1) * ((S.potT a t').φ ((S.A.chart j).symm y) ∘ (S.A.chart j).symm) z := by
    funext z
    have e1 : ∀ s, (S.potT a s).φ ((S.A.chart j).symm y) ((S.A.chart j).symm z) =
        (S.th a).φ ((S.A.chart j).symm y) ((S.A.chart j).symm z) +
          S.phT a s ((S.A.chart j).symm z) := fun _ => rfl
    simp only [Function.comp_apply, e1]
    ring
  rw [heq, levi_add_smul (-1) hG hG' w, h1, h2]
  ring

/- English proof (translation)
Take `⟨j, hj⟩` from `S.A.cover x`. Establish `hO : IsOpen ((S.A.chart j).target ∩ (S.A.chart j).symm ⁻¹' V)` using `(S.A.chart j).isOpen_inter_preimage_symm hV`. Establish `hxO : S.A.chart j x ∈ (S.A.chart j).target ∩ (S.A.chart j).symm ⁻¹' V` using `⟨(S.A.chart j).map_source hj, by`. Simplify `hx⟩` using `[Set.mem_preimage, (S.A.chart j).left_inv hj]`. Establish `hsm : ContDiffOn ℝ ∞ ((fun x => S.phT a t x - S.phT a t' x) ∘ (S.A.chart j).symm) ((S.A.chart j).target ∩ (S.A.chart j).symm ⁻¹' V)`.

Establish `h1` using `((S.reg a).2.2 t ht ht₀).1 j`. Establish `h2` using `((S.reg a).2.2 t' ht' ht₀').1 j`. Conclude with `(h1.sub h2).mono fun z hz => ⟨hz.1, trivial⟩`. Establish `hev` using `eventually_eq_of_isMax hO hsm (fun z hz w => levi_sub_eq_zero S a h ht ht₀ ht' ht₀' j hz.1 w) hxO (fun z hz => by`. Simplify `hmax _ hz.2)` using `[Function.comp_apply, (S.A.chart j).left_inv hj]`.

Establish `hev2` using `((S.A.chart j).continuousAt hj).eventually hev`. Use `filter_upwards [hev2, (S.A.chart j).open_source.mem_nhds hj] with y hy hys`. Simplify `hy` using `[Function.comp_apply, (S.A.chart j).left_inv hj, (S.A.chart j).left_inv hys]`.
-/
theorem eventually_eq_sub (h : ∀ t, IsPsh S.A ((S.potT a t).rsmul (-1)) ∧ IsPsh S.A (S.potT a t))
    {t t' : ℝ} (ht : 0 < t) (ht₀ : t ≤ S.t₀) (ht' : 0 < t') (ht₀' : t' ≤ S.t₀)
    (x : S.X) (V : Set S.X) (hV : IsOpen V) (hx : x ∈ V)
    (hmax : ∀ y ∈ V, S.phT a t y - S.phT a t' y ≤ S.phT a t x - S.phT a t' x) :
    ∀ᶠ y in 𝓝 x, S.phT a t y - S.phT a t' y = S.phT a t x - S.phT a t' x := by
  obtain ⟨j, hj⟩ := S.A.cover x
  have hO : IsOpen ((S.A.chart j).target ∩ (S.A.chart j).symm ⁻¹' V) :=
    (S.A.chart j).isOpen_inter_preimage_symm hV
  have hxO : S.A.chart j x ∈ (S.A.chart j).target ∩ (S.A.chart j).symm ⁻¹' V :=
    ⟨(S.A.chart j).map_source hj, by
      simpa [Set.mem_preimage, (S.A.chart j).left_inv hj] using hx⟩
  have hsm : ContDiffOn ℝ ∞ ((fun x => S.phT a t x - S.phT a t' x) ∘ (S.A.chart j).symm)
      ((S.A.chart j).target ∩ (S.A.chart j).symm ⁻¹' V) := by
    have h1 := ((S.reg a).2.2 t ht ht₀).1 j
    have h2 := ((S.reg a).2.2 t' ht' ht₀').1 j
    exact (h1.sub h2).mono fun z hz => ⟨hz.1, trivial⟩
  have hev := eventually_eq_of_isMax hO hsm
    (fun z hz w => levi_sub_eq_zero S a h ht ht₀ ht' ht₀' j hz.1 w) hxO
    (fun z hz => by
      simpa [Function.comp_apply, (S.A.chart j).left_inv hj] using hmax _ hz.2)
  have hev2 := ((S.A.chart j).continuousAt hj).eventually hev
  filter_upwards [hev2, (S.A.chart j).open_source.mem_nhds hj] with y hy hys
  simpa [Function.comp_apply, (S.A.chart j).left_inv hj, (S.A.chart j).left_inv hys] using hy

end System

/- English proof (translation)
Introduce `e σ S a h`. Set `_ : ChartedSpace (Fin e → ℂ) S.X` to `{ atlas := Set.range S.A.chart chartAt := fun x => S.A.chart (S.A.cover x).choose mem_chart_source := fun x => (S.A.cover x).choose_spec chart_mem_atlas := fun _ => ⟨_, rfl⟩ }`. Use `haveI : LocallyConnectedSpace S.X := ChartedSpace.locallyConnectedSpace (Fin e → ℂ) S.X`. Take `⟨ht₀, -, hreg⟩` from `S.reg a`. Establish `hdense` using `(GlobalTheory.CompanionTheory.Ar.Bdry.bdry_isClosed_dense_compl e S.X S.A S.L S.s S.nb S.m S.W S.sec S.snc).2`.

Establish `hc₀ : Continuous (S.phT a S.t₀)` using `continuous_of_smooth (hreg S.t₀ ht₀ le_rfl).1`. Take `⟨M, hM⟩` from `isCompact_univ.exists_bound_of_continuousOn hc₀.continuousOn`. Establish `hM' : ∀ x, |S.phT a S.t₀ x| ≤ M` using `fun x => by simpa using hM x (Set.mem_univ x)`. Establish `hpt : ∀ x : S.X, ∃ y, y ∈ connectedComponent x ∧ y ∈ (bdry S.s)ᶜ` using `fun x => by`. Take `⟨y, hy1, hy2⟩` from `hdense.inter_open_nonempty _ isOpen_connectedComponent ⟨x, mem_connectedComponent⟩`.

Conclude with `⟨y, hy1, hy2⟩`. Use `choose y hyc hyb using hpt`. Take `⟨T, hT⟩` from `isCompact_univ.elim_finite_subcover (fun x : S.X => connectedComponent x) (fun _ => isOpen_connectedComponent) (fun x _ => Set.mem_iUnion.2 ⟨x, mem_connectedComponent⟩)`. Take `⟨B, hB⟩` from `(T.image fun x => -S.ph a (y x)).exists_le`. Use `⟨|S.C| + |B| + 2 * M, fun t ht ht' x => ?_⟩` and prove the remaining obligations.

Establish `hM0 : 0 ≤ M` using `(abs_nonneg _).trans (hM' x)`. Choose the witnesses or unpack the hypotheses as in `⟨x₁, hx₁, hxc⟩ : ∃ x₁ ∈ T, x ∈ connectedComponent x₁ := by`. Simplify using `using hT (Set.mem_univ x)`. Establish `hcv : Continuous fun x => S.phT a t x - S.phT a S.t₀ x` using `(continuous_of_smooth (hreg t ht ht').1).sub hc₀`. Establish `hloc` using `fun (z : S.X) (V : Set S.X) (hV : IsOpen V) (hz : z ∈ V) hm => eventually_eq_sub S a h ht ht' ht₀ le_rfl z V hV hz hm`.

Establish `e1` using `eq_of_mem_connectedComponent hcv hloc hxc`. Establish `e2` using `eq_of_mem_connectedComponent hcv hloc (hyc x₁)`. Establish `hlow : S.ph a (y x₁) ≤ S.phT a t (y x₁)` using `(hreg t ht ht').2.2.1 _ (hyb x₁)`. Establish `hup : S.phT a t x ≤ S.C` using `(hreg t ht ht').2.1 x`. Establish `hb : -S.ph a (y x₁) ≤ B` using `hB _ (Finset.mem_image_of_mem _ hx₁)`.

Establish `b1` using `abs_le.1 (hM' x)`. Establish `b2` using `abs_le.1 (hM' (y x₁))`. Rewrite using `[abs_le]`. Prove the components needed by the constructor for the conclusion. Use `neg_abs_le B` as an intermediate fact.

Use `le_abs_self B` as an intermediate fact. Use `abs_nonneg S.C` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Use `le_abs_self S.C` as an intermediate fact. Use `abs_nonneg B` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem flat_phT_bounded : ∀ (e : ℕ) (σ : Type) (S : PB.AnSys e σ) (a : σ),
    (∀ t, ReciprocityTheory.AnForm.M.IsPsh S.A ((S.potT a t).rsmul (-1)) ∧
      ReciprocityTheory.AnForm.M.IsPsh S.A (S.potT a t)) →
    ∃ C : ℝ, ∀ t, 0 < t → t ≤ S.t₀ → ∀ x, |S.phT a t x| ≤ C := by
  intro e σ S a h
  let _ : ChartedSpace (Fin e → ℂ) S.X :=
    { atlas := Set.range S.A.chart
      chartAt := fun x => S.A.chart (S.A.cover x).choose
      mem_chart_source := fun x => (S.A.cover x).choose_spec
      chart_mem_atlas := fun _ => ⟨_, rfl⟩ }
  haveI : LocallyConnectedSpace S.X := ChartedSpace.locallyConnectedSpace (Fin e → ℂ) S.X
  obtain ⟨ht₀, -, hreg⟩ := S.reg a
  have hdense := (GlobalTheory.CompanionTheory.Ar.Bdry.bdry_isClosed_dense_compl e S.X S.A S.L S.s S.nb S.m S.W
    S.sec S.snc).2
  have hc₀ : Continuous (S.phT a S.t₀) := continuous_of_smooth (hreg S.t₀ ht₀ le_rfl).1
  obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn hc₀.continuousOn
  have hM' : ∀ x, |S.phT a S.t₀ x| ≤ M := fun x => by simpa using hM x (Set.mem_univ x)
  have hpt : ∀ x : S.X, ∃ y, y ∈ connectedComponent x ∧ y ∈ (bdry S.s)ᶜ := fun x => by
    obtain ⟨y, hy1, hy2⟩ := hdense.inter_open_nonempty _ isOpen_connectedComponent
      ⟨x, mem_connectedComponent⟩
    exact ⟨y, hy1, hy2⟩
  choose y hyc hyb using hpt
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover (fun x : S.X => connectedComponent x)
    (fun _ => isOpen_connectedComponent) (fun x _ => Set.mem_iUnion.2 ⟨x, mem_connectedComponent⟩)
  obtain ⟨B, hB⟩ := (T.image fun x => -S.ph a (y x)).exists_le
  refine ⟨|S.C| + |B| + 2 * M, fun t ht ht' x => ?_⟩
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM' x)
  obtain ⟨x₁, hx₁, hxc⟩ : ∃ x₁ ∈ T, x ∈ connectedComponent x₁ := by
    simpa using hT (Set.mem_univ x)
  have hcv : Continuous fun x => S.phT a t x - S.phT a S.t₀ x :=
    (continuous_of_smooth (hreg t ht ht').1).sub hc₀
  have hloc := fun (z : S.X) (V : Set S.X) (hV : IsOpen V) (hz : z ∈ V) hm =>
    eventually_eq_sub S a h ht ht' ht₀ le_rfl z V hV hz hm
  have e1 := eq_of_mem_connectedComponent hcv hloc hxc
  have e2 := eq_of_mem_connectedComponent hcv hloc (hyc x₁)
  have hlow : S.ph a (y x₁) ≤ S.phT a t (y x₁) := (hreg t ht ht').2.2.1 _ (hyb x₁)
  have hup : S.phT a t x ≤ S.C := (hreg t ht ht').2.1 x
  have hb : -S.ph a (y x₁) ≤ B := hB _ (Finset.mem_image_of_mem _ hx₁)
  have b1 := abs_le.1 (hM' x)
  have b2 := abs_le.1 (hM' (y x₁))
  rw [abs_le]
  constructor
  · have := neg_abs_le B
    have := le_abs_self B
    have := abs_nonneg S.C
    linarith
  · have := le_abs_self S.C
    have := abs_nonneg B
    linarith

end GlobalTheory.CompanionTheory.Ar.FlatBound
