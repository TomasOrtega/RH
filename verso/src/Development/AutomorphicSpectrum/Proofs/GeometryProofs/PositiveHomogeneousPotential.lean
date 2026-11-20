import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSmoothHermTrivLine
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MemAbLocusIff
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SmoothFunctionAsDegreeZeroMetricStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ConjugationInvariantHermitianMetricStatement
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PFsInvPow
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Chg.FlatExt

open Filter Topology Set

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

/- English proof (translation)
Establish `e : {z : (Σ k, J k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} = ⋂ k, ⋃ i, {z | z ⟨k, i⟩ ≠ 0}`. Use extensionality with `z`. Simplify using the standard rewrite rules. Rewrite using `[e]`. Conclude with `isOpen_iInter_of_finite fun k => isOpen_iUnion fun i => isOpen_ne_fun (continuous_apply _) continuous_const`.
-/
theorem isOpen_blockNz : IsOpen {z : (Σ k, J k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  have e : {z : (Σ k, J k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} = ⋂ k, ⋃ i, {z | z ⟨k, i⟩ ≠ 0} := by
    ext z
    simp
  rw [e]
  exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
    isOpen_ne_fun (continuous_apply _) continuous_const

/- English proof (translation)
Use `⟨fun k => ?_, fun f hf => ?_⟩` and prove the remaining obligations. Take `⟨i, hi⟩` from `hz.1 k`. Conclude with `⟨i, by simpa using hi⟩`. Establish `h` using `hz.2 f hf`. Rewrite `h`, the goal using `[MvPolynomial.eval_map]`.

Establish `e` using `MvPolynomial.eval₂_comp_left (starRingEnd ℂ) (Int.castRingHom ℂ) z f`. Rewrite `e` using `[h, map_zero, Subsingleton.elim ((starRingEnd ℂ).comp (Int.castRingHom ℂ)) (Int.castRingHom ℂ)]`. Conclude with `e.symm`.
-/
theorem conj_mem_mcPts {P : Ideal (MRing J)} {z : (Σ k, J k) → ℂ} (hz : z ∈ mcPts P) :
    (fun p => starRingEnd ℂ (z p)) ∈ mcPts P := by
  refine ⟨fun k => ?_, fun f hf => ?_⟩
  · obtain ⟨i, hi⟩ := hz.1 k
    exact ⟨i, by simpa using hi⟩
  · have h := hz.2 f hf
    rw [MvPolynomial.eval_map] at h ⊢
    have e := MvPolynomial.eval₂_comp_left (starRingEnd ℂ) (Int.castRingHom ℂ) z f
    rw [h, map_zero, Subsingleton.elim ((starRingEnd ℂ).comp (Int.castRingHom ℂ)) (Int.castRingHom ℂ)] at e
    exact e.symm

/- English proof (translation)
Introduce `y hy`. Take `⟨j, hj⟩` from `A.cover y`. Establish `hc` using `(A.chart j).continuousAt hj`. Establish `hsy : (A.chart j).symm (A.chart j y) = y` using `(A.chart j).left_inv hj`. Establish `han : ContinuousAt (g ∘ (A.chart j).symm) (A.chart j y)` using `(h j _ ⟨(A.chart j).map_source hj, by simpa [hsy] using hy⟩).continuousAt`.

Establish `hcomp : ContinuousAt ((g ∘ (A.chart j).symm) ∘ (A.chart j)) y` using `ContinuousAt.comp han hc`. Use `(hcomp.congr ?_).continuousWithinAt` and prove the remaining obligations. Use `filter_upwards [(A.chart j).open_source.mem_nhds hj] with w hw`. Simplify using `[(A.chart j).left_inv hw]`.
-/
theorem continuousOn_of_holoOn {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) {U : Set X}
    {g : X → ℂ} (h : A.HoloOn U g) : ContinuousOn g U := by
  intro y hy
  obtain ⟨j, hj⟩ := A.cover y
  have hc := (A.chart j).continuousAt hj
  have hsy : (A.chart j).symm (A.chart j y) = y := (A.chart j).left_inv hj
  have han : ContinuousAt (g ∘ (A.chart j).symm) (A.chart j y) :=
    (h j _ ⟨(A.chart j).map_source hj, by simpa [hsy] using hy⟩).continuousAt
  have hcomp : ContinuousAt ((g ∘ (A.chart j).symm) ∘ (A.chart j)) y := ContinuousAt.comp han hc
  refine (hcomp.congr ?_).continuousWithinAt
  filter_upwards [(A.chart j).open_source.mem_nhds hj] with w hw
  simp [(A.chart j).left_inv hw]

/- English proof (translation)
The claim follows from `AnalyticAt.pi fun p => R.holo x p j t ⟨ht, hx⟩`.
-/
theorem analyticAt_lift {P Jd : Ideal (MRing J)} {D : ℕ} (R : AnLogRes P Jd D) (x : R.X) (j : Fin R.A.n)
    {t : Fin D → ℂ} (ht : t ∈ (R.A.chart j).target) (hx : (R.A.chart j).symm t ∈ R.U x) :
    AnalyticAt ℂ (fun t' => R.lift x ((R.A.chart j).symm t')) t :=
  AnalyticAt.pi fun p => R.holo x p j t ⟨ht, hx⟩

/- English proof (translation)
Take `⟨c, hc, e⟩` from `R.compat y x y ⟨R.mem_U y, hy⟩`. Establish `hne : (∏ k, ‖c k‖ ^ a k) ≠ 0` using `Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.2 (hc k))`. Rewrite using `[e, hsm _ (R.mem x y hy) c hc, H.smul c _ hc, hHa, mul_div_mul_left _ _ hne]`.
-/
theorem ratio_eq {P Jd : Ideal (MRing J)} {D : ℕ} (R : AnLogRes P Jd D) {a : K → ℤ}
    {φ : ((Σ k, J k) → ℂ) → ℝ}
    (hsm : ∀ z ∈ mcPts P, ∀ c : K → ℂ, (∀ k, c k ≠ 0) →
      φ (fun p => c p.1 * z p) = (∏ k, ‖c k‖ ^ a k) * φ z)
    (H : HermLine J) (hHa : H.a = a) {x y : R.X} (hy : y ∈ R.U x) :
    φ (R.lift y y) / H.h (R.lift y y) = φ (R.lift x y) / H.h (R.lift x y) := by
  obtain ⟨c, hc, e⟩ := R.compat y x y ⟨R.mem_U y, hy⟩
  have hne : (∏ k, ‖c k‖ ^ a k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.2 (hc k))
  rw [e, hsm _ (R.mem x y hy) c hc, H.smul c _ hc, hHa, mul_div_mul_left _ _ hne]

/- English proof (translation)
Introduce `j t ht`. Establish `ht : t ∈ (R.A.chart j).target` using `ht.1`. Take `⟨x₀, hx₀⟩ : ∃ x₀, x₀ = (R.A.chart j).symm t` from `⟨_, rfl⟩`. Establish `hm₀ : R.lift x₀ x₀ ∈ mcPts P` using `R.mem _ _ (R.mem_U _)`. Take `⟨V, F, hV, hzV, hF, hFφ⟩` from `hloc _ hm₀`.

Establish `hγ : AnalyticAt ℂ (fun t' => R.lift x₀ ((R.A.chart j).symm t')) t` using `analyticAt_lift R x₀ j ht (hx₀ ▸ R.mem_U _)`. Establish `hγt : R.lift x₀ ((R.A.chart j).symm t) = R.lift x₀ x₀` using `by rw [hx₀]`. Establish `hsc : ContinuousAt (R.A.chart j).symm t` using `(R.A.chart j).continuousAt_symm ht`. Establish `hev : ∀ᶠ t' in 𝓝 t, (R.A.chart j).symm t' ∈ R.U x₀ ∧ R.lift x₀ ((R.A.chart j).symm t') ∈ V`. Use `(hsc.eventually ((R.isOpen_U x₀).mem_nhds (hx₀ ▸ R.mem_U _))).and (hγ.continuousAt.eventually (hV.mem_nhds ?_))` and prove the remaining obligations.

Use `show R.lift x₀ ((R.A.chart j).symm t) ∈ V`. Rewrite using `[hγt]`. Conclude with `hzV`. Establish `hne : F (R.lift x₀ ((R.A.chart j).symm t)) ≠ 0`. Rewrite using `[hγt]`.

Conclude with `(hFφ _ ⟨hzV, hm₀⟩).1`. Establish `hFa : AnalyticAt ℂ (fun t' => F (R.lift x₀ ((R.A.chart j).symm t'))) t` using `AnalyticAt.comp' (hF _ (by rw [hγt]; exact hzV)) hγ`. Establish `e1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t' => F (R.lift x₀ ((R.A.chart j).symm t'))) t` using `hFa.contDiffAt.restrict_scalars ℝ`. Establish `e2` using `(e1.norm ℝ hne).log (norm_ne_zero_iff.2 hne)`. Establish `hγr : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t' => R.lift x₀ ((R.A.chart j).symm t')) t` using `hγ.contDiffAt.restrict_scalars ℝ`.

Establish `hmem : R.lift x₀ ((R.A.chart j).symm t) ∈ {z : (Σ k, J k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}`. Rewrite using `[hγt]`. Conclude with `hm₀.1`. Establish `e3 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t' => H.h (R.lift x₀ ((R.A.chart j).symm t'))) t` using `ContDiffAt.comp t (hH.contDiffAt (isOpen_blockNz.mem_nhds hmem)) hγr`. Establish `e4` using `e3.log (H.pos _ hmem).ne'`.

Use `((e2.sub e4).congr_of_eventuallyEq ?_).contDiffWithinAt` and prove the remaining obligations. Use `filter_upwards [hev] with t' ht'`. Take `⟨h1, h2⟩` from `ht'`. Establish `hm` using `R.mem _ _ h1`. Take `⟨h0, hφ⟩` from `hFφ _ ⟨h2, hm⟩`.

Use `show Real.log (φ (R.lift _ _) / H.h (R.lift _ _)) = _`. Rewrite using `[ratio_eq R hsm H hHa h1, hφ, Real.log_div (norm_ne_zero_iff.2 h0) (H.pos _ hm.1).ne']`.
-/
theorem smooth_ratio {P Jd : Ideal (MRing J)} {D : ℕ} (R : AnLogRes P Jd D) {a : K → ℤ}
    {φ : ((Σ k, J k) → ℂ) → ℝ}
    (hsm : ∀ z ∈ mcPts P, ∀ c : K → ℂ, (∀ k, c k ≠ 0) →
      φ (fun p => c p.1 * z p) = (∏ k, ‖c k‖ ^ a k) * φ z)
    (hloc : ∀ z ∈ mcPts P, ∃ (V : Set ((Σ k, J k) → ℂ)) (F : ((Σ k, J k) → ℂ) → ℂ), IsOpen V ∧ z ∈ V ∧
      AnalyticOnNhd ℂ F V ∧ ∀ z' ∈ V ∩ mcPts P, F z' ≠ 0 ∧ φ z' = ‖F z'‖)
    (H : HermLine J) (hHa : H.a = a) (hH : IsSmoothHerm H) :
    R.A.Smooth fun x => Real.log (φ (R.lift x x) / H.h (R.lift x x)) := by
  intro j t ht
  have ht : t ∈ (R.A.chart j).target := ht.1
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, x₀ = (R.A.chart j).symm t := ⟨_, rfl⟩
  have hm₀ : R.lift x₀ x₀ ∈ mcPts P := R.mem _ _ (R.mem_U _)
  obtain ⟨V, F, hV, hzV, hF, hFφ⟩ := hloc _ hm₀
  have hγ : AnalyticAt ℂ (fun t' => R.lift x₀ ((R.A.chart j).symm t')) t :=
    analyticAt_lift R x₀ j ht (hx₀ ▸ R.mem_U _)
  have hγt : R.lift x₀ ((R.A.chart j).symm t) = R.lift x₀ x₀ := by rw [hx₀]
  have hsc : ContinuousAt (R.A.chart j).symm t := (R.A.chart j).continuousAt_symm ht
  have hev : ∀ᶠ t' in 𝓝 t, (R.A.chart j).symm t' ∈ R.U x₀ ∧
      R.lift x₀ ((R.A.chart j).symm t') ∈ V := by
    refine (hsc.eventually ((R.isOpen_U x₀).mem_nhds (hx₀ ▸ R.mem_U _))).and
      (hγ.continuousAt.eventually (hV.mem_nhds ?_))
    show R.lift x₀ ((R.A.chart j).symm t) ∈ V
    rw [hγt]
    exact hzV
  have hne : F (R.lift x₀ ((R.A.chart j).symm t)) ≠ 0 := by
    rw [hγt]
    exact (hFφ _ ⟨hzV, hm₀⟩).1
  have hFa : AnalyticAt ℂ (fun t' => F (R.lift x₀ ((R.A.chart j).symm t'))) t :=
    AnalyticAt.comp' (hF _ (by rw [hγt]; exact hzV)) hγ
  have e1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t' => F (R.lift x₀ ((R.A.chart j).symm t'))) t :=
    hFa.contDiffAt.restrict_scalars ℝ
  have e2 := (e1.norm ℝ hne).log (norm_ne_zero_iff.2 hne)
  have hγr : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t' => R.lift x₀ ((R.A.chart j).symm t')) t :=
    hγ.contDiffAt.restrict_scalars ℝ
  have hmem : R.lift x₀ ((R.A.chart j).symm t) ∈ {z : (Σ k, J k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
    rw [hγt]
    exact hm₀.1
  have e3 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t' => H.h (R.lift x₀ ((R.A.chart j).symm t'))) t :=
    ContDiffAt.comp t (hH.contDiffAt (isOpen_blockNz.mem_nhds hmem)) hγr
  have e4 := e3.log (H.pos _ hmem).ne'
  refine ((e2.sub e4).congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [hev] with t' ht'
  obtain ⟨h1, h2⟩ := ht'
  have hm := R.mem _ _ h1
  obtain ⟨h0, hφ⟩ := hFφ _ ⟨h2, hm⟩
  show Real.log (φ (R.lift _ _) / H.h (R.lift _ _)) = _
  rw [ratio_eq R hsm H hHa h1, hφ, Real.log_div (norm_ne_zero_iff.2 h0) (H.pos _ hm.1).ne']

/- English proof (translation)
Introduce `x _`. Establish `hm₀ : R.lift x x ∈ mcPts P` using `R.mem _ _ (R.mem_U _)`. Take `⟨V, F, hV, hzV, hF, hFφ⟩` from `hloc _ hm₀`. Establish `hcl : ContinuousOn (R.lift x) (R.U x)` using `continuousOn_pi.2 fun p => continuousOn_of_holoOn R.A (R.holo x p)`. Establish `hW₁ : IsOpen (R.U x ∩ R.lift x ⁻¹' V)` using `hcl.isOpen_inter_preimage (R.isOpen_U x) hV`.

Establish `hf0 : F (R.lift x x) ≠ 0` using `(hFφ _ ⟨hzV, hm₀⟩).1`. Establish `hfc : ContinuousOn (fun y => F (R.lift x y) / F (R.lift x x)) (R.U x ∩ R.lift x ⁻¹' V)` using `(hF.continuousOn.comp (hcl.mono inter_subset_left) fun y hy => hy.2).div_const _`. Establish `hW` using `hfc.isOpen_inter_preimage hW₁ Complex.isOpen_slitPlane`. Use `⟨_, hW, ⟨⟨R.mem_U x, hzV⟩, by simp [hf0]⟩, fun y => Complex.log (F (R.lift x y) / F (R.lift x x)) + (Real.log ‖F (R.lift x x)‖ : ℂ), ?_, ?_⟩` and prove the remaining obligations. Introduce `j t ht`.

Establish `hγ` using `analyticAt_lift R x j ht.1 ht.2.1.1`. Establish `hFa : AnalyticAt ℂ (fun t' => F (R.lift x ((R.A.chart j).symm t'))) t` using `AnalyticAt.comp' (hF _ ht.2.1.2) hγ`. Establish `hga : AnalyticAt ℂ (fun t' => F (R.lift x ((R.A.chart j).symm t')) / F (R.lift x x)) t` using `hFa.div analyticAt_const hf0`. Conclude with `(hga.clog ht.2.2).add analyticAt_const`. Introduce `y hy`.

Establish `hm : R.lift x y ∈ V ∩ mcPts P` using `⟨hy.1.2, R.mem x y hy.1.1⟩`. Take `⟨h0, h1⟩` from `hFφ _ hm`. Use `show Real.log (T.h (R.lift x y)) - 0 = _`. Rewrite using `[hT _ hm.2, h1, Complex.add_re, Complex.log_re, Complex.ofReal_re, norm_div, Real.log_div (norm_ne_zero_iff.2 h0) (norm_ne_zero_iff.2 hf0)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem isFlatOn_of_local {P Jd : Ideal (MRing J)} {D : ℕ} (R : AnLogRes P Jd D) (T : HermLine J)
    {φ : ((Σ k, J k) → ℂ) → ℝ} (hT : ∀ z ∈ mcPts P, T.h z = φ z)
    (hloc : ∀ z ∈ mcPts P, ∃ (V : Set ((Σ k, J k) → ℂ)) (F : ((Σ k, J k) → ℂ) → ℂ), IsOpen V ∧ z ∈ V ∧
      AnalyticOnNhd ℂ F V ∧ ∀ z' ∈ V ∩ mcPts P, F z' ≠ 0 ∧ φ z' = ‖F z'‖) :
    IsFlatOn R T := by
  intro x _
  have hm₀ : R.lift x x ∈ mcPts P := R.mem _ _ (R.mem_U _)
  obtain ⟨V, F, hV, hzV, hF, hFφ⟩ := hloc _ hm₀
  have hcl : ContinuousOn (R.lift x) (R.U x) :=
    continuousOn_pi.2 fun p => continuousOn_of_holoOn R.A (R.holo x p)
  have hW₁ : IsOpen (R.U x ∩ R.lift x ⁻¹' V) := hcl.isOpen_inter_preimage (R.isOpen_U x) hV
  have hf0 : F (R.lift x x) ≠ 0 := (hFφ _ ⟨hzV, hm₀⟩).1
  have hfc : ContinuousOn (fun y => F (R.lift x y) / F (R.lift x x)) (R.U x ∩ R.lift x ⁻¹' V) :=
    (hF.continuousOn.comp (hcl.mono inter_subset_left) fun y hy => hy.2).div_const _
  have hW := hfc.isOpen_inter_preimage hW₁ Complex.isOpen_slitPlane
  refine ⟨_, hW, ⟨⟨R.mem_U x, hzV⟩, by simp [hf0]⟩,
    fun y => Complex.log (F (R.lift x y) / F (R.lift x x)) + (Real.log ‖F (R.lift x x)‖ : ℂ), ?_, ?_⟩
  · intro j t ht
    have hγ := analyticAt_lift R x j ht.1 ht.2.1.1
    have hFa : AnalyticAt ℂ (fun t' => F (R.lift x ((R.A.chart j).symm t'))) t :=
      AnalyticAt.comp' (hF _ ht.2.1.2) hγ
    have hga : AnalyticAt ℂ (fun t' => F (R.lift x ((R.A.chart j).symm t')) / F (R.lift x x)) t :=
      hFa.div analyticAt_const hf0
    exact (hga.clog ht.2.2).add analyticAt_const
  · intro y hy
    have hm : R.lift x y ∈ V ∩ mcPts P := ⟨hy.1.2, R.mem x y hy.1.1⟩
    obtain ⟨h0, h1⟩ := hFφ _ hm
    show Real.log (T.h (R.lift x y)) - 0 = _
    rw [hT _ hm.2, h1, Complex.add_re, Complex.log_re, Complex.ofReal_re, norm_div,
      Real.log_div (norm_ne_zero_iff.2 h0) (norm_ne_zero_iff.2 hf0)]
    ring

/- English proof (translation)
Introduce `K _ J _ P D R a φ hpos hconj hsm hloc`. Establish `hHs : IsSmoothHerm (GroundTheory.Heights₂.Heights.LowerBoundFree.fsHerm J a)` using `GroundTheory.Heights₂.Heights.LowerBoundFree.FsInvPow.isSmoothHerm_fsHerm a`. Take `⟨H, hHdef⟩ : ∃ H, H = GroundTheory.Heights₂.Heights.LowerBoundFree.fsHerm J a` from `⟨_, rfl⟩`. Establish `hHa : H.a = a` using `by rw [hHdef]; rfl`. Rewrite `hHs` using `[← hHdef]`.

Take `⟨B, hBa, hBs, hB⟩` from `GlobalTheory.T.smooth_function_as_degree_zero_metric K J P D R _ (smooth_ratio R hsm hloc H hHa hHs)`. Establish `hT₀s : IsSmoothHerm (H.tensor B)` using `ContDiffOn.mul hHs hBs`. Establish `hT₀a : (H.tensor B).a = a` using `by show H.a + B.a = a`. Rewrite using `[hHa, hBa, add_zero]`. Establish `hpt : ∀ x, (H.tensor B).h (R.lift x x) = φ (R.lift x x)`.

Introduce `x`. Establish `hm` using `R.mem x x (R.mem_U x)`. Establish `hHp` using `H.pos _ hm.1`. Establish `hBp` using `B.pos _ hm.1`. Establish `hq : 0 < φ (R.lift x x) / H.h (R.lift x x)` using `div_pos (hpos _ hm) hHp`.

Establish `e` using `Real.log_injOn_pos (Set.mem_Ioi.2 hBp) (Set.mem_Ioi.2 hq) (hB x)`. Use `show H.h _ * B.h _ = _`. Rewrite using `[e]`. Clear the denominators using the available nonvanishing facts. Establish `hT₀ : ∀ z ∈ mcPts P, (H.tensor B).h z = φ z`.

Introduce `z hz`. Establish `hnt : z ∉ mcPts (⊤ : Ideal (MRing J))` using `fun h => by`. Establish `h1` using `h.2 1 trivial`. Simplify using `at h1`. Take `⟨x, c, hc, e⟩` from `R.surj z hz hnt`.

Establish `hne : (∏ k, ‖c k‖ ^ a k) ≠ 0` using `Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.2 (hc k))`. Establish `h1` using `hpt x`. Rewrite `h1` using `[e, (H.tensor B).smul c z hc, hT₀a, hsm z hz c hc]`. Conclude with `mul_left_cancel₀ hne h1`. Take `⟨T, hTa, hTs, hTc, hT⟩` from `GlobalTheory.T.conjugation_invariant_hermitian_metric K J (H.tensor B) hT₀s`.

Establish `hTφ : ∀ z ∈ mcPts P, T.h z = φ z`. Introduce `z hz`. Establish `hc` using `conj_mem_mcPts hz`. Establish `e` using `hT z hz.1`. Rewrite `e` using `[hT₀ z hz, hT₀ _ hc, hconj z hz, add_self_div_two]`.

Conclude with `Real.log_injOn_pos (Set.mem_Ioi.2 (T.pos z hz.1)) (Set.mem_Ioi.2 (hpos z hz)) e`. Conclude with `⟨T, hTa.trans hT₀a, hTs, hTc, hTφ, isFlatOn_of_local R T hTφ hloc⟩`.
-/
theorem exists_flat_line : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (P : Ideal (MRing J)) (D : ℕ) (R : AnLogRes P ⊤ D) (a : K → ℤ) (φ : ((Σ k, J k) → ℂ) → ℝ), (∀ z ∈ mcPts P, 0 < φ z) → (∀ z ∈ mcPts P, φ (fun p => starRingEnd ℂ (z p)) = φ z) → (∀ z ∈ mcPts P, ∀ c : K → ℂ, (∀ k, c k ≠ 0) → φ (fun p => c p.1 * z p) = (∏ k, ‖c k‖ ^ a k) * φ z) → (∀ z ∈ mcPts P, ∃ (V : Set ((Σ k, J k) → ℂ)) (F : ((Σ k, J k) → ℂ) → ℂ), IsOpen V ∧ z ∈ V ∧ AnalyticOnNhd ℂ F V ∧ ∀ z' ∈ V ∩ mcPts P, F z' ≠ 0 ∧ φ z' = ‖F z'‖) → ∃ T : HermLine J, T.a = a ∧ IsSmoothHerm T ∧ IsConjInvariantH T ∧ (∀ z ∈ mcPts P, T.h z = φ z) ∧ IsFlatOn R T := by
  intro K _ J _ P D R a φ hpos hconj hsm hloc
  have hHs : IsSmoothHerm (GroundTheory.Heights₂.Heights.LowerBoundFree.fsHerm J a) :=
    GroundTheory.Heights₂.Heights.LowerBoundFree.FsInvPow.isSmoothHerm_fsHerm a
  obtain ⟨H, hHdef⟩ : ∃ H, H = GroundTheory.Heights₂.Heights.LowerBoundFree.fsHerm J a := ⟨_, rfl⟩
  have hHa : H.a = a := by rw [hHdef]; rfl
  rw [← hHdef] at hHs
  obtain ⟨B, hBa, hBs, hB⟩ := GlobalTheory.T.smooth_function_as_degree_zero_metric K J P D R _ (smooth_ratio R hsm hloc H hHa hHs)
  have hT₀s : IsSmoothHerm (H.tensor B) := ContDiffOn.mul hHs hBs
  have hT₀a : (H.tensor B).a = a := by
    show H.a + B.a = a
    rw [hHa, hBa, add_zero]
  have hpt : ∀ x, (H.tensor B).h (R.lift x x) = φ (R.lift x x) := by
    intro x
    have hm := R.mem x x (R.mem_U x)
    have hHp := H.pos _ hm.1
    have hBp := B.pos _ hm.1
    have hq : 0 < φ (R.lift x x) / H.h (R.lift x x) := div_pos (hpos _ hm) hHp
    have e := Real.log_injOn_pos (Set.mem_Ioi.2 hBp) (Set.mem_Ioi.2 hq) (hB x)
    show H.h _ * B.h _ = _
    rw [e]
    field_simp
  have hT₀ : ∀ z ∈ mcPts P, (H.tensor B).h z = φ z := by
    intro z hz
    have hnt : z ∉ mcPts (⊤ : Ideal (MRing J)) := fun h => by
      have h1 := h.2 1 trivial
      simp at h1
    obtain ⟨x, c, hc, e⟩ := R.surj z hz hnt
    have hne : (∏ k, ‖c k‖ ^ a k) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.2 (hc k))
    have h1 := hpt x
    rw [e, (H.tensor B).smul c z hc, hT₀a, hsm z hz c hc] at h1
    exact mul_left_cancel₀ hne h1
  obtain ⟨T, hTa, hTs, hTc, hT⟩ := GlobalTheory.T.conjugation_invariant_hermitian_metric K J (H.tensor B) hT₀s
  have hTφ : ∀ z ∈ mcPts P, T.h z = φ z := by
    intro z hz
    have hc := conj_mem_mcPts hz
    have e := hT z hz.1
    rw [hT₀ z hz, hT₀ _ hc, hconj z hz, add_self_div_two] at e
    exact Real.log_injOn_pos (Set.mem_Ioi.2 (T.pos z hz.1)) (Set.mem_Ioi.2 (hpos z hz)) e
  exact ⟨T, hTa.trans hT₀a, hTs, hTc, hTφ, isFlatOn_of_local R T hTφ hloc⟩

end GlobalTheory.CompanionTheory.Ar.Chg.FlatExt
