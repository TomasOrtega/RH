import Mathlib
import GroundTheory.AutomorphicForms.PartialDifferential.EllipticLocalRegularity

namespace GroundTheory.Automorphic.Sobolev

open TemperedDistribution MeasureTheory FourierTransform LineDeriv
open scoped SchwartzMap ENNReal ContDiff

noncomputable section

set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/- English proof (translation)
Establish `hae` using `ae_eq_of_integral_schwartz_smul_eq hg.locallyIntegrable hh.locallyIntegrable H`. Conclude with `(hg.ae_eq_iff_eq volume hh).1 hae`.
-/
theorem eq_of_integral_smul_eq {g h : E → ℂ} (hg : Continuous g) (hh : Continuous h)
    (H : ∀ φ : 𝓢(E, ℂ), HasCompactSupport φ → ∫ x, φ x • g x = ∫ x, φ x • h x) : g = h := by
  have hae := ae_eq_of_integral_schwartz_smul_eq hg.locallyIntegrable hh.locallyIntegrable H
  exact (hg.ae_eq_iff_eq volume hh).1 hae

/- English proof (translation)
Introduce `y hy`. Take `⟨ε, hε, hball⟩` from `Metric.isOpen_iff.1 hV y hy`. Establish `hr : 0 < ε / 4` using `by positivity`. Take `⟨θ, hθ⟩ : ∃ θ : 𝓢(E, ℂ), θ = bump y hr` from `⟨_, rfl⟩`. Establish `hθV : tsupport (θ : E → ℂ) ⊆ V` using `hθ ▸ (tsupport_bump y hr).trans fun x hx ↦ hball (by rw [Metric.mem_closedBall] at hx; rw [Metric.mem_ball]; linarith)`.

Establish `key : (fun x ↦ θ x * g x) = fun x ↦ θ x * h x`. Use `eq_of_integral_smul_eq (θ.continuous.mul hg) (θ.continuous.mul hh) fun φ hφ ↦ ?_` and prove the remaining obligations. Establish `h1` using `H (SchwartzMap.smulLeftCLM ℂ (θ : E → ℂ) φ) (by`. Rewrite using `[SchwartzMap.smulLeftCLM_apply θ.hasTemperateGrowth]`. Conclude with `HasCompactSupport.smul_left (f := (θ : E → ℂ)) hφ)`.

Use the proof step `(by`. Rewrite using `[SchwartzMap.smulLeftCLM_apply θ.hasTemperateGrowth]`. Conclude with `(tsupport_smul_subset_left (θ : E → ℂ) (φ : E → ℂ)).trans hθV)`. Simplify using `only [SchwartzMap.smulLeftCLM_apply_apply θ.hasTemperateGrowth, smul_eq_mul] at h1`. Simplify using `only [smul_eq_mul]`.

Combine the equalities or inequalities in the displayed calculation. Use `congrFun key y` as an intermediate fact. Establish `hθy : θ y = 1` using `by rw [hθ]; exact bump_eq_one y hr (Metric.mem_closedBall_self hr.le)`. Simplify using `only [hθy, one_mul] at this`. Conclude with `this`.
-/
theorem eqOn_of_integral_smul_eq {g h : E → ℂ} (hg : Continuous g) (hh : Continuous h) {V : Set E}
    (hV : IsOpen V) (H : ∀ φ : 𝓢(E, ℂ), HasCompactSupport φ → tsupport φ ⊆ V →
      ∫ x, φ x • g x = ∫ x, φ x • h x) : Set.EqOn g h V := by
  intro y hy
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hV y hy
  have hr : 0 < ε / 4 := by positivity
  obtain ⟨θ, hθ⟩ : ∃ θ : 𝓢(E, ℂ), θ = bump y hr := ⟨_, rfl⟩
  have hθV : tsupport (θ : E → ℂ) ⊆ V := hθ ▸ (tsupport_bump y hr).trans fun x hx ↦
    hball (by rw [Metric.mem_closedBall] at hx; rw [Metric.mem_ball]; linarith)
  have key : (fun x ↦ θ x * g x) = fun x ↦ θ x * h x := by
    refine eq_of_integral_smul_eq (θ.continuous.mul hg) (θ.continuous.mul hh) fun φ hφ ↦ ?_
    have h1 := H (SchwartzMap.smulLeftCLM ℂ (θ : E → ℂ) φ)
      (by
        rw [SchwartzMap.smulLeftCLM_apply θ.hasTemperateGrowth]
        exact HasCompactSupport.smul_left (f := (θ : E → ℂ)) hφ)
      (by
        rw [SchwartzMap.smulLeftCLM_apply θ.hasTemperateGrowth]
        exact (tsupport_smul_subset_left (θ : E → ℂ) (φ : E → ℂ)).trans hθV)
    simp only [SchwartzMap.smulLeftCLM_apply_apply θ.hasTemperateGrowth, smul_eq_mul] at h1
    simp only [smul_eq_mul]
    calc ∫ x, φ x * (θ x * g x) = ∫ x, θ x * φ x * g x := by congr 1; ext x; ring
      _ = ∫ x, θ x * φ x * h x := h1
      _ = ∫ x, φ x * (θ x * h x) := by congr 1; ext x; ring
  have := congrFun key y
  have hθy : θ y = 1 := by rw [hθ]; exact bump_eq_one y hr (Metric.mem_closedBall_self hr.le)
  simp only [hθy, one_mul] at this
  exact this

/- English proof (translation)
Establish `hk : ∀ k : ℕ, ∃ g : E → ℂ, ContDiff ℝ k g ∧ ∀ φ : 𝓢(E, ℂ), u φ = ∫ x, φ x • g x`. Introduce `k`. Take `⟨g, hg, -, hrep⟩` from `sobolev_embedding k (s := k + (Module.finrank ℝ E : ℝ) / 2 + 1) (by linarith) (SobolevSpace.mk u (hu (k + (Module.finrank ℝ E : ℝ) / 2 + 1)))`. Conclude with `⟨g, hg, fun φ ↦ by simpa using hrep φ⟩`. Use `choose g hg hrep using hk`.

Use `⟨g 0, contDiff_infty.2 fun k ↦ ?_, hrep 0⟩` and prove the remaining obligations. Establish `: g k = g 0` using `eq_of_integral_smul_eq ((hg k).continuous) ((hg 0).continuous) fun φ _ ↦ by rw [← hrep k, ← hrep 0]`. Rewrite using `[← this]`. Conclude with `hg k`.
-/
theorem exists_contDiff_of_memSobolev {u : 𝓢'(E, ℂ)} (hu : ∀ t, MemSobolev t 2 u) :
    ∃ g : E → ℂ, ContDiff ℝ ∞ g ∧ ∀ φ : 𝓢(E, ℂ), u φ = ∫ x, φ x • g x := by
  have hk : ∀ k : ℕ, ∃ g : E → ℂ, ContDiff ℝ k g ∧ ∀ φ : 𝓢(E, ℂ), u φ = ∫ x, φ x • g x := by
    intro k
    obtain ⟨g, hg, -, hrep⟩ := sobolev_embedding k
      (s := k + (Module.finrank ℝ E : ℝ) / 2 + 1) (by linarith)
      (SobolevSpace.mk u (hu (k + (Module.finrank ℝ E : ℝ) / 2 + 1)))
    exact ⟨g, hg, fun φ ↦ by simpa using hrep φ⟩
  choose g hg hrep using hk
  refine ⟨g 0, contDiff_infty.2 fun k ↦ ?_, hrep 0⟩
  have : g k = g 0 := eq_of_integral_smul_eq ((hg k).continuous) ((hg 0).continuous)
    fun φ _ ↦ by rw [← hrep k, ← hrep 0]
  rw [← this]; exact hg k

/- English proof (translation)
Establish `hr : ∀ x ∈ K, ∃ r > 0, Metric.closedBall x (2 * r) ⊆ V x`. Introduce `x hx`. Take `⟨ε, hε, hsub⟩` from `Metric.mem_nhds_iff.1 (hV x hx)`. Conclude with `⟨ε / 4, by positivity, fun y hy ↦ hsub (by`. Rewrite `hy` using `[Metric.mem_closedBall]`.

Rewrite using `[Metric.mem_ball]`. Use the proof step `linarith)⟩`. Use `choose! r hr0 hrV using hr`. Take `⟨S, hSK, hcover⟩` from `hK.elim_nhds_subcover (fun x ↦ Metric.ball x (r x)) (fun x hx ↦ Metric.ball_mem_nhds x (hr0 x hx))`. Establish `claim : ∀ T : Finset E, (∀ c ∈ T, c ∈ K) → ∀ ψ : 𝓢(E, ℂ), tsupport ψ ⊆ K → tsupport ψ ⊆ ⋃ c ∈ T, Metric.ball c (r c) → Λ ψ = 0`.

Introduce `T`. Proceed by induction on `T using Finset.induction_on with`. Consider the case `empty`. Introduce `_ ψ hψK hψ`. Establish `hψ0 : ψ = 0`.

Use extensionality with `x`. Assume the negation of the conclusion as `hx`. Use `hψ (subset_tsupport _ hx)` as an intermediate fact. Simplify using `at this`. Establish `h0` using `hadd 0 0 (by rw [hψ0] at hψK; exact hψK)`.

Simplify using `only [map_zero, sub_zero] at h0`. Rewrite using `[hψ0]`. Take the linear combination `(-1 : ℂ) * h0`. Consider the case `insert c T hc ih`. Introduce `hTK ψ hψK hψ`.

Establish `hcK : c ∈ K` using `hTK c (Finset.mem_insert_self c T)`. Take `⟨β, hβ⟩ : ∃ β : 𝓢(E, ℂ), β = bump c (hr0 c hcK)` from `⟨_, rfl⟩`. Rewrite using `[hadd ψ β hψK]`. Establish `h1 : Λ (SchwartzMap.smulLeftCLM ℂ (β : E → ℂ) ψ) = 0`. Apply `hloc c hcK` to reduce the goal to its premises.

Rewrite using `[SchwartzMap.smulLeftCLM_apply β.hasTemperateGrowth]`. Conclude with `(tsupport_smul_subset_left (β : E → ℂ) (ψ : E → ℂ)).trans (hβ ▸ (tsupport_bump c _).trans (hrV c hcK))`. Rewrite using `[SchwartzMap.smulLeftCLM_apply β.hasTemperateGrowth]`. Conclude with `(tsupport_smul_subset_right (β : E → ℂ) (ψ : E → ℂ)).trans hψK`. Establish `h2 : Λ (ψ - SchwartzMap.smulLeftCLM ℂ (β : E → ℂ) ψ) = 0`.

Establish `hsupp : tsupport (ψ - SchwartzMap.smulLeftCLM ℂ (β : E → ℂ) ψ : E → ℂ) ⊆ tsupport ψ ∩ (Metric.ball c (r c))ᶜ`. Establish `e : (ψ - SchwartzMap.smulLeftCLM ℂ (β : E → ℂ) ψ : E → ℂ) = fun x ↦ (1 - β x) * ψ x`. Use extensionality with `x`. Simplify using `only [Pi.sub_apply, SchwartzMap.smulLeftCLM_apply_apply β.hasTemperateGrowth, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e]`. Use `Set.subset_inter (tsupport_mul_subset_right) ?_` and prove the remaining obligations. Use `(tsupport_mul_subset_left).trans (closure_minimal ?_ Metric.isOpen_ball.isClosed_compl)` and prove the remaining obligations. Introduce `x hx hxb`. Apply `hx` to reduce the goal to its premises.

Use `show 1 - β x = 0`. Rewrite using `[hβ, bump_eq_one c (hr0 c hcK) (Metric.ball_subset_closedBall hxb), sub_self]`. Use `ih (fun c' hc' ↦ hTK c' (Finset.mem_insert_of_mem hc')) _ (hsupp.trans (Set.inter_subset_left.trans hψK)) ?_` and prove the remaining obligations. Introduce `x hx`. Take `⟨hx1, hx2⟩` from `hsupp hx`.

Use `hψ hx1` as an intermediate fact. Simplify using `only [Finset.set_biUnion_insert, Set.mem_union] at this`. Break down `this with h | h` into its components or cases. Conclude with `absurd h hx2`. Conclude with `h`.

Rewrite using `[h1, h2, add_zero]`. Conclude with `claim S hSK φ hφ (hφ.trans hcover)`.
-/
theorem eq_zero_of_local {Λ : 𝓢(E, ℂ) → ℂ} {K : Set E} (hK : IsCompact K) {V : E → Set E}
    (hV : ∀ x ∈ K, V x ∈ nhds x)
    (hloc : ∀ x ∈ K, ∀ φ : 𝓢(E, ℂ), tsupport φ ⊆ V x → tsupport φ ⊆ K → Λ φ = 0)
    (hadd : ∀ φ β : 𝓢(E, ℂ), tsupport φ ⊆ K →
      Λ φ = Λ (SchwartzMap.smulLeftCLM ℂ (β : E → ℂ) φ) + Λ (φ - SchwartzMap.smulLeftCLM ℂ (β : E → ℂ) φ))
    {φ : 𝓢(E, ℂ)} (hφ : tsupport φ ⊆ K) : Λ φ = 0 := by
  classical

  have hr : ∀ x ∈ K, ∃ r > 0, Metric.closedBall x (2 * r) ⊆ V x := by
    intro x hx
    obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.1 (hV x hx)
    exact ⟨ε / 4, by positivity, fun y hy ↦ hsub (by
      rw [Metric.mem_closedBall] at hy; rw [Metric.mem_ball]; linarith)⟩
  choose! r hr0 hrV using hr
  obtain ⟨S, hSK, hcover⟩ := hK.elim_nhds_subcover (fun x ↦ Metric.ball x (r x))
    (fun x hx ↦ Metric.ball_mem_nhds x (hr0 x hx))
  have claim : ∀ T : Finset E, (∀ c ∈ T, c ∈ K) → ∀ ψ : 𝓢(E, ℂ), tsupport ψ ⊆ K →
      tsupport ψ ⊆ ⋃ c ∈ T, Metric.ball c (r c) → Λ ψ = 0 := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro _ ψ hψK hψ
      have hψ0 : ψ = 0 := by
        ext x
        by_contra hx
        have := hψ (subset_tsupport _ hx)
        simp at this
      have h0 := hadd 0 0 (by rw [hψ0] at hψK; exact hψK)
      simp only [map_zero, sub_zero] at h0
      rw [hψ0]; linear_combination (-1 : ℂ) * h0
    | insert c T hc ih =>
      intro hTK ψ hψK hψ
      have hcK : c ∈ K := hTK c (Finset.mem_insert_self c T)
      obtain ⟨β, hβ⟩ : ∃ β : 𝓢(E, ℂ), β = bump c (hr0 c hcK) := ⟨_, rfl⟩
      rw [hadd ψ β hψK]
      have h1 : Λ (SchwartzMap.smulLeftCLM ℂ (β : E → ℂ) ψ) = 0 := by
        apply hloc c hcK
        · rw [SchwartzMap.smulLeftCLM_apply β.hasTemperateGrowth]
          exact (tsupport_smul_subset_left (β : E → ℂ) (ψ : E → ℂ)).trans
            (hβ ▸ (tsupport_bump c _).trans (hrV c hcK))
        · rw [SchwartzMap.smulLeftCLM_apply β.hasTemperateGrowth]
          exact (tsupport_smul_subset_right (β : E → ℂ) (ψ : E → ℂ)).trans hψK
      have h2 : Λ (ψ - SchwartzMap.smulLeftCLM ℂ (β : E → ℂ) ψ) = 0 := by
        have hsupp : tsupport (ψ - SchwartzMap.smulLeftCLM ℂ (β : E → ℂ) ψ : E → ℂ) ⊆
            tsupport ψ ∩ (Metric.ball c (r c))ᶜ := by
          have e : (ψ - SchwartzMap.smulLeftCLM ℂ (β : E → ℂ) ψ : E → ℂ) =
              fun x ↦ (1 - β x) * ψ x := by
            ext x
            simp only [Pi.sub_apply, SchwartzMap.smulLeftCLM_apply_apply β.hasTemperateGrowth,
              smul_eq_mul]
            ring
          rw [e]
          refine Set.subset_inter (tsupport_mul_subset_right) ?_
          refine (tsupport_mul_subset_left).trans (closure_minimal ?_
            Metric.isOpen_ball.isClosed_compl)
          intro x hx hxb
          apply hx
          show 1 - β x = 0
          rw [hβ, bump_eq_one c (hr0 c hcK) (Metric.ball_subset_closedBall hxb), sub_self]
        refine ih (fun c' hc' ↦ hTK c' (Finset.mem_insert_of_mem hc')) _
          (hsupp.trans (Set.inter_subset_left.trans hψK)) ?_
        intro x hx
        obtain ⟨hx1, hx2⟩ := hsupp hx
        have := hψ hx1
        simp only [Finset.set_biUnion_insert, Set.mem_union] at this
        rcases this with h | h
        · exact absurd h hx2
        · exact h
      rw [h1, h2, add_zero]
  exact claim S hSK φ hφ (hφ.trans hcover)

/- English proof (translation)
Rewrite using `[continuous_iff_continuousAt]`. Introduce `x`. Distinguish the cases in `hx : x ∈ Ω`. Conclude with `hφ.continuousAt.smul (hg.continuousAt (hΩ.mem_nhds hx))`. Establish `hx' : x ∉ tsupport φ` using `fun h ↦ hx (hφΩ h)`.

Establish `hev : ∀ᶠ y in nhds x, φ y • g y = 0` using `by filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hx'] with y hy`. Rewrite using `[hy, Pi.zero_apply, zero_smul]`. Establish `h0 : φ x • g x = 0` using `hev.self_of_nhds`. Conclude with `(continuousAt_const.congr (hev.mono fun y hy ↦ by rw [hy, ← h0])).congr (Filter.Eventually.of_forall fun _ ↦ rfl)`.
-/
theorem continuous_smul_of_tsupport_subset {g : E → ℂ} {Ω : Set E} (hΩ : IsOpen Ω)
    (hg : ContinuousOn g Ω) {φ : E → ℂ} (hφ : Continuous φ) (hφΩ : tsupport φ ⊆ Ω) :
    Continuous fun x ↦ φ x • g x := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x ∈ Ω
  · exact hφ.continuousAt.smul (hg.continuousAt (hΩ.mem_nhds hx))
  · have hx' : x ∉ tsupport φ := fun h ↦ hx (hφΩ h)
    have hev : ∀ᶠ y in nhds x, φ y • g y = 0 := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hx'] with y hy
      rw [hy, Pi.zero_apply, zero_smul]
    have h0 : φ x • g x = 0 := hev.self_of_nhds
    exact (continuousAt_const.congr (hev.mono fun y hy ↦ by rw [hy, ← h0])).congr
      (Filter.Eventually.of_forall fun _ ↦ rfl)

/- English proof (translation)
The claim follows from `(continuous_smul_of_tsupport_subset hΩ hg φ.continuous hφΩ).integrable_of_hasCompactSupport (IsCompact.of_isClosed_subset hφc.isCompact (isClosed_tsupport _) (tsupport_smul_subset_left (φ : E → ℂ) g))`.
-/
theorem integrable_smul_of_tsupport_subset {g : E → ℂ} {Ω : Set E} (hΩ : IsOpen Ω)
    (hg : ContinuousOn g Ω) {φ : 𝓢(E, ℂ)} (hφc : HasCompactSupport φ) (hφΩ : tsupport φ ⊆ Ω) :
    Integrable (fun y ↦ φ y • g y) :=
  (continuous_smul_of_tsupport_subset hΩ hg φ.continuous hφΩ).integrable_of_hasCompactSupport
    (IsCompact.of_isClosed_subset hφc.isCompact (isClosed_tsupport _)
      (tsupport_smul_subset_left (φ : E → ℂ) g))

/- English proof (translation)
Use `choose! W G hWo hxW hWΩ hG hrep using h`. Establish `hcons : ∀ x ∈ Ω, ∀ y ∈ Ω, Set.EqOn (G x) (G y) (W x ∩ W y)`. Introduce `x hx y hy`. Use `eqOn_of_integral_smul_eq (hG x hx).continuous (hG y hy).continuous ((hWo x hx).inter (hWo y hy)) fun φ hφc hφ ↦ ?_` and prove the remaining obligations. Rewrite using `[← hrep x hx φ hφc (hφ.trans Set.inter_subset_left), hrep y hy φ hφc (hφ.trans Set.inter_subset_right)]`.

Use `set g : E → ℂ := fun y ↦ G y y`. Establish `hgW : ∀ x ∈ Ω, Set.EqOn g (G x) (W x)`. Introduce `x hx y hy`. Conclude with `(hcons x hx y (hWΩ x hx hy) ⟨hy, hxW y (hWΩ x hx hy)⟩).symm`. Establish `hgsmooth : ContDiffOn ℝ ∞ g Ω`.

Use `contDiffOn_of_locally_contDiffOn fun x hx ↦ ⟨W x, hWo x hx, hxW x hx, ?_⟩` and prove the remaining obligations. Conclude with `((hG x hx).contDiffOn.mono Set.inter_subset_right).congr fun y hy ↦ hgW x hx hy.2`. Use `⟨g, hgsmooth, fun φ hφc hφΩ ↦ ?_⟩` and prove the remaining obligations. Use `set Λ' : 𝓢(E, ℂ) → ℂ := fun ψ ↦ Λ ψ - ∫ y, ψ y • g y`. Establish `hcs : ∀ ψ : 𝓢(E, ℂ), tsupport ψ ⊆ tsupport φ → HasCompactSupport ψ` using `fun ψ hψ ↦ IsCompact.of_isClosed_subset hφc.isCompact (isClosed_tsupport _) hψ`.

Establish `key : Λ' φ = 0`. Use `eq_zero_of_local (V := W) hφc.isCompact (fun x hx ↦ (hWo x (hφΩ hx)).mem_nhds (hxW x (hφΩ hx))) (fun x hx ψ hψ hψK ↦ ?_) (fun ψ β hψ ↦ ?_) subset_rfl` and prove the remaining obligations. Establish `hxΩ` using `hφΩ hx`. Simplify using `only [Λ', sub_eq_zero]`. Rewrite using `[hrep x hxΩ ψ (hcs ψ hψK) hψ]`.

Use `congr 1`. Use extensionality with `y`. Distinguish the cases in `hy : ψ y = 0`. Rewrite using `[hy, zero_smul, zero_smul]`. Rewrite using `[hgW x hxΩ (hψ (subset_tsupport _ hy))]`.

Establish `h1 : tsupport (SchwartzMap.smulLeftCLM ℂ (β : E → ℂ) ψ : E → ℂ) ⊆ tsupport ψ`. Rewrite using `[SchwartzMap.smulLeftCLM_apply β.hasTemperateGrowth]`. Conclude with `tsupport_smul_subset_right (β : E → ℂ) (ψ : E → ℂ)`. Take `⟨a, ha⟩ : ∃ a : 𝓢(E, ℂ), a = SchwartzMap.smulLeftCLM ℂ (β : E → ℂ) ψ` from `⟨_, rfl⟩`. Rewrite `h1`, the goal using `[← ha]`.

Take `⟨b, hb⟩ : ∃ b : 𝓢(E, ℂ), b = ψ - a` from `⟨_, rfl⟩`. Rewrite using `[← hb]`. Establish `hab : a + b = ψ` using `by rw [hb]; abel`. Establish `h2 : tsupport (b : E → ℂ) ⊆ tsupport ψ`. Use `closure_minimal (fun y hy ↦ ?_) (isClosed_tsupport _)` and prove the remaining obligations.

Assume the negation of the conclusion as `hy'`. Apply `hy` to reduce the goal to its premises. Establish `: ψ y = 0` using `image_eq_zero_of_notMem_tsupport hy'`. Establish `ha0 : a y = 0`. Rewrite using `[ha, SchwartzMap.smulLeftCLM_apply_apply β.hasTemperateGrowth, this, smul_zero]`.

Rewrite using `[hb, sub_apply, this, ha0, sub_zero]`. Establish `hi : ∀ χ : 𝓢(E, ℂ), tsupport χ ⊆ tsupport ψ → Integrable (fun y ↦ χ y • g y)` using `fun χ hχ ↦ integrable_smul_of_tsupport_subset hΩ hgsmooth.continuousOn (hcs χ (hχ.trans hψ)) (hχ.trans (hψ.trans hφΩ))`. Establish `hΛ : Λ ψ = Λ a + Λ b`. Rewrite using `[← hab]`. Conclude with `hadd a b (hcs _ (h1.trans hψ)) (h1.trans (hψ.trans hφΩ)) (hcs _ (h2.trans hψ)) (h2.trans (hψ.trans hφΩ))`.

Establish `hI : ∫ y, ψ y • g y = (∫ y, a y • g y) + ∫ y, b y • g y`. Rewrite using `[← integral_add (hi _ h1) (hi _ h2)]`. Use `congr 1`. Use extensionality with `y`. Rewrite using `[← hab, add_apply, add_smul]`.

Use `show Λ ψ - ∫ y, ψ y • g y = (Λ a - ∫ y, a y • g y) + (Λ b - ∫ y, b y • g y)`. Rewrite using `[hΛ, hI]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [Λ', sub_eq_zero] at key`. Conclude with `key`.
-/
theorem exists_contDiffOn_of_local {Λ : 𝓢(E, ℂ) → ℂ} {Ω : Set E} (hΩ : IsOpen Ω)
    (hadd : ∀ φ ψ : 𝓢(E, ℂ), HasCompactSupport φ → tsupport φ ⊆ Ω → HasCompactSupport ψ →
      tsupport ψ ⊆ Ω → Λ (φ + ψ) = Λ φ + Λ ψ)
    (h : ∀ x ∈ Ω, ∃ W : Set E, ∃ G : E → ℂ, IsOpen W ∧ x ∈ W ∧ W ⊆ Ω ∧ ContDiff ℝ ∞ G ∧
      ∀ φ : 𝓢(E, ℂ), HasCompactSupport φ → tsupport φ ⊆ W → Λ φ = ∫ y, φ y • G y) :
    ∃ g : E → ℂ, ContDiffOn ℝ ∞ g Ω ∧ ∀ φ : 𝓢(E, ℂ), HasCompactSupport φ → tsupport φ ⊆ Ω →
      Λ φ = ∫ x, φ x • g x := by
  choose! W G hWo hxW hWΩ hG hrep using h
  have hcons : ∀ x ∈ Ω, ∀ y ∈ Ω, Set.EqOn (G x) (G y) (W x ∩ W y) := by
    intro x hx y hy
    refine eqOn_of_integral_smul_eq (hG x hx).continuous (hG y hy).continuous
      ((hWo x hx).inter (hWo y hy)) fun φ hφc hφ ↦ ?_
    rw [← hrep x hx φ hφc (hφ.trans Set.inter_subset_left),
      hrep y hy φ hφc (hφ.trans Set.inter_subset_right)]
  set g : E → ℂ := fun y ↦ G y y
  have hgW : ∀ x ∈ Ω, Set.EqOn g (G x) (W x) := by
    intro x hx y hy
    exact (hcons x hx y (hWΩ x hx hy) ⟨hy, hxW y (hWΩ x hx hy)⟩).symm
  have hgsmooth : ContDiffOn ℝ ∞ g Ω := by
    refine contDiffOn_of_locally_contDiffOn fun x hx ↦ ⟨W x, hWo x hx, hxW x hx, ?_⟩
    exact ((hG x hx).contDiffOn.mono Set.inter_subset_right).congr fun y hy ↦ hgW x hx hy.2
  refine ⟨g, hgsmooth, fun φ hφc hφΩ ↦ ?_⟩
  set Λ' : 𝓢(E, ℂ) → ℂ := fun ψ ↦ Λ ψ - ∫ y, ψ y • g y
  have hcs : ∀ ψ : 𝓢(E, ℂ), tsupport ψ ⊆ tsupport φ → HasCompactSupport ψ := fun ψ hψ ↦
    IsCompact.of_isClosed_subset hφc.isCompact (isClosed_tsupport _) hψ
  have key : Λ' φ = 0 := by
    refine eq_zero_of_local (V := W) hφc.isCompact
      (fun x hx ↦ (hWo x (hφΩ hx)).mem_nhds (hxW x (hφΩ hx))) (fun x hx ψ hψ hψK ↦ ?_)
      (fun ψ β hψ ↦ ?_) subset_rfl
    · have hxΩ := hφΩ hx
      simp only [Λ', sub_eq_zero]
      rw [hrep x hxΩ ψ (hcs ψ hψK) hψ]
      congr 1; ext y
      by_cases hy : ψ y = 0
      · rw [hy, zero_smul, zero_smul]
      · rw [hgW x hxΩ (hψ (subset_tsupport _ hy))]
    · have h1 : tsupport (SchwartzMap.smulLeftCLM ℂ (β : E → ℂ) ψ : E → ℂ) ⊆ tsupport ψ := by
        rw [SchwartzMap.smulLeftCLM_apply β.hasTemperateGrowth]
        exact tsupport_smul_subset_right (β : E → ℂ) (ψ : E → ℂ)
      obtain ⟨a, ha⟩ : ∃ a : 𝓢(E, ℂ), a = SchwartzMap.smulLeftCLM ℂ (β : E → ℂ) ψ := ⟨_, rfl⟩
      rw [← ha] at h1 ⊢
      obtain ⟨b, hb⟩ : ∃ b : 𝓢(E, ℂ), b = ψ - a := ⟨_, rfl⟩
      rw [← hb]
      have hab : a + b = ψ := by rw [hb]; abel
      have h2 : tsupport (b : E → ℂ) ⊆ tsupport ψ := by
        refine closure_minimal (fun y hy ↦ ?_) (isClosed_tsupport _)
        by_contra hy'
        apply hy
        have : ψ y = 0 := image_eq_zero_of_notMem_tsupport hy'
        have ha0 : a y = 0 := by
          rw [ha, SchwartzMap.smulLeftCLM_apply_apply β.hasTemperateGrowth, this, smul_zero]
        rw [hb, sub_apply, this, ha0, sub_zero]
      have hi : ∀ χ : 𝓢(E, ℂ), tsupport χ ⊆ tsupport ψ → Integrable (fun y ↦ χ y • g y) :=
        fun χ hχ ↦ integrable_smul_of_tsupport_subset hΩ hgsmooth.continuousOn
          (hcs χ (hχ.trans hψ)) (hχ.trans (hψ.trans hφΩ))
      have hΛ : Λ ψ = Λ a + Λ b := by
        rw [← hab]
        exact hadd a b (hcs _ (h1.trans hψ)) (h1.trans (hψ.trans hφΩ)) (hcs _ (h2.trans hψ))
          (h2.trans (hψ.trans hφΩ))
      have hI : ∫ y, ψ y • g y = (∫ y, a y • g y) + ∫ y, b y • g y := by
        rw [← integral_add (hi _ h1) (hi _ h2)]
        congr 1; ext y; rw [← hab, add_apply, add_smul]
      show Λ ψ - ∫ y, ψ y • g y = (Λ a - ∫ y, a y • g y) + (Λ b - ∫ y, b y • g y)
      rw [hΛ, hI]; ring
  simp only [Λ', sub_eq_zero] at key
  exact key

/- English proof (translation)
Use `exists_contDiffOn_of_local hΩ (fun φ ψ _ _ _ _ ↦ map_add u φ ψ) fun x hx ↦ ?_` and prove the remaining obligations. Take `⟨ψ, hψ1, hψ⟩` from `h x hx`. Take `⟨t, ht1, htopen, hxt⟩` from `eventually_nhds_iff.1 hψ1`. Take `⟨G, hG, hrep⟩` from `exists_contDiff_of_memSobolev hψ`. Use `⟨t ∩ Ω, G, htopen.inter hΩ, ⟨hxt, hx⟩, Set.inter_subset_right, hG, fun φ _ hφ ↦ ?_⟩` and prove the remaining obligations.

Rewrite using `[← hrep φ, smulLeftCLM_apply_apply]`. Use `congr 1`. Use extensionality with `y`. Rewrite using `[SchwartzMap.smulLeftCLM_apply_apply ψ.hasTemperateGrowth, smul_eq_mul]`. Distinguish the cases in `hy : φ y = 0`.

Rewrite using `[hy, mul_zero]`. Rewrite using `[ht1 y (hφ (subset_tsupport _ hy)).1, one_mul]`.
-/
theorem exists_contDiffOn_of_locally_memSobolev {u : 𝓢'(E, ℂ)} {Ω : Set E} (hΩ : IsOpen Ω)
    (h : ∀ x ∈ Ω, ∃ ψ : 𝓢(E, ℂ), (∀ᶠ y in nhds x, ψ y = 1) ∧
      ∀ t, MemSobolev t 2 (smulLeftCLM ℂ (ψ : E → ℂ) u)) :
    ∃ g : E → ℂ, ContDiffOn ℝ ∞ g Ω ∧ ∀ φ : 𝓢(E, ℂ), HasCompactSupport φ → tsupport φ ⊆ Ω →
      u φ = ∫ x, φ x • g x := by
  refine exists_contDiffOn_of_local hΩ (fun φ ψ _ _ _ _ ↦ map_add u φ ψ) fun x hx ↦ ?_
  obtain ⟨ψ, hψ1, hψ⟩ := h x hx
  obtain ⟨t, ht1, htopen, hxt⟩ := eventually_nhds_iff.1 hψ1
  obtain ⟨G, hG, hrep⟩ := exists_contDiff_of_memSobolev hψ
  refine ⟨t ∩ Ω, G, htopen.inter hΩ, ⟨hxt, hx⟩, Set.inter_subset_right, hG, fun φ _ hφ ↦ ?_⟩
  rw [← hrep φ, smulLeftCLM_apply_apply]
  congr 1
  ext y
  rw [SchwartzMap.smulLeftCLM_apply_apply ψ.hasTemperateGrowth, smul_eq_mul]
  by_cases hy : φ y = 0
  · rw [hy, mul_zero]
  · rw [ht1 y (hφ (subset_tsupport _ hy)).1, one_mul]

/- English proof (translation)
Take `⟨δ, hδ, hstep⟩` from `hT.exists_regularity_radius hm`. Use `⟨δ, hδ, fun δ' ⟨hδ'0, hδ'δ⟩ u s₀ hu F hF hTF ↦ ?_⟩` and prove the remaining obligations. Establish `claim : ∀ j : ℕ, ∀ ψ : 𝓢(E, ℂ), tsupport (ψ : E → ℂ) ⊆ Metric.ball x₀ δ' → MemSobolev (s₀ + j) 2 (smulLeftCLM ℂ (ψ : E → ℂ) u)`. Introduce `j`. Proceed by induction on `j with`.

Consider the case `zero => intro ψ _`. Simplify using `using memSobolev_smulLeft ψ hu`. Consider the case `succ j ih`. Introduce `ψ hψ`. Take `⟨ρ, ⟨hρ0, hρδ⟩, hsub⟩` from `exists_pos_lt_subset_ball hδ'0 (isClosed_tsupport _) hψ`.

Establish `hr₁ : 0 < (2 * ρ + δ') / 3` using `by linarith`. Establish `hr₁R : (2 * ρ + δ') / 3 < (ρ + 2 * δ') / 3` using `by linarith`. Use `set ψ₁ := bumpG x₀ hr₁ hr₁R`. Establish `hψ₁ : tsupport (ψ₁ : E → ℂ) ⊆ Metric.ball x₀ δ'`. Use `(tsupport_bumpG x₀ hr₁ hr₁R).trans fun x hx ↦ ?_` and prove the remaining obligations.

Rewrite `hx` using `[Metric.mem_closedBall]`. Rewrite using `[Metric.mem_ball]`. Combine the linear equalities and inequalities to obtain the conclusion. Use `set w := smulLeftCLM ℂ (ψ : E → ℂ) u`. Establish `hw : MemSobolev (s₀ + j) 2 w` using `ih ψ hψ`.

Establish `hvan : Distribution.IsVanishingOn w (Metric.closedBall x₀ ρ)ᶜ` using `(isVanishingOn_smulLeftCLM_compl ψ.hasTemperateGrowth u).mono (Set.compl_subset_compl.2 (hsub.trans Metric.ball_subset_closedBall))`. Establish `hψT : smulLeftCLM ℂ (ψ : E → ℂ) (T u) = smulLeftCLM ℂ (ψ : E → ℂ) F`. Establish `h0` using `smulLeftCLM_eq_zero_of_isVanishingOn ψ.hasTemperateGrowth hTF hψ`. Rewrite `h0` using `[map_sub, sub_eq_zero]`. Conclude with `h0`.

Establish `hψψ₁ : smulLeftCLM ℂ (ψ : E → ℂ) (smulLeftCLM ℂ (ψ₁ : E → ℂ) u) = smulLeftCLM ℂ (ψ : E → ℂ) u`. Establish `hfun : ((ψ₁ : E → ℂ) * (ψ : E → ℂ)) = (ψ : E → ℂ)`. Use extensionality with `x`. Simplify using `only [Pi.mul_apply]`. Distinguish the cases in `hx : ψ x = 0`.

Rewrite using `[hx, mul_zero]`. Rewrite using `[bumpG_eq_one x₀ hr₁ hr₁R, one_mul]`. Use `hsub (subset_tsupport _ hx)` as an intermediate fact. Rewrite `this` using `[Metric.mem_ball]`. Rewrite using `[Metric.mem_closedBall]`.

Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[smulLeftCLM_smulLeftCLM_apply ψ₁.hasTemperateGrowth ψ.hasTemperateGrowth, hfun]`. Establish `hcomm : comm T ψ u = comm T ψ (smulLeftCLM ℂ (ψ₁ : E → ℂ) u)`. Establish `hz1 : smulLeftCLM ℂ (ψ : E → ℂ) (u - smulLeftCLM ℂ (ψ₁ : E → ℂ) u) = 0`. Rewrite using `[map_sub, hψψ₁, sub_self]`.

Establish `hz2 : Distribution.IsVanishingOn (u - smulLeftCLM ℂ (ψ₁ : E → ℂ) u) (Metric.ball x₀ ((2 * ρ + δ') / 3))`. Use `isVanishingOn_smulLeftCLM_sub ψ₁.hasTemperateGrowth (V := Metric.ball x₀ ((2 * ρ + δ') / 3)) (fun x hx ↦ bumpG_eq_one x₀ hr₁ hr₁R (Metric.ball_subset_closedBall hx)) u` as an intermediate fact. Establish `h2` using `isVanishingOn_neg this`. Rewrite `h2` using `[neg_sub]`. Then use the resulting hypothesis. Establish `hz3 : smulLeftCLM ℂ (ψ : E → ℂ) (T (u - smulLeftCLM ℂ (ψ₁ : E → ℂ) u)) = 0` using `smulLeftCLM_eq_zero_of_isVanishingOn ψ.hasTemperateGrowth (hT.isLocal _ Metric.isOpen_ball _ hz2) (hsub.trans (Metric.ball_subset_ball (by linarith)))`.

Establish `: comm T ψ (u - smulLeftCLM ℂ (ψ₁ : E → ℂ) u) = 0`. Rewrite using `[comm_apply, hz1, map_zero, hz3, sub_zero]`. Rewrite `this` using `[map_sub, sub_eq_zero]`. Conclude with `this`. Establish `hTw : MemSobolev (s₀ + j - m + 1) 2 (T w)`.

Establish `e : T w = smulLeftCLM ℂ (ψ : E → ℂ) F + comm T ψ (smulLeftCLM ℂ (ψ₁ : E → ℂ) u)`. Rewrite using `[← hcomm, ← hψT, comm_apply]`. Normalize the expressions using the abelian group laws. Rewrite using `[e]`. Use `(memSobolev_smulLeft ψ (hF _)).add ?_` and prove the remaining obligations.

Conclude with `(hT.hasOrder_comm ψ).memSobolev' (by ring) (ih ψ₁ hψ₁)`. Use `hstep (s₀ + j) w hw ⟨ρ, hρδ.trans_le hδ'δ, hvan⟩ hTw` as an intermediate fact. Simplify `this` using `[add_assoc]`. Introduce `ψ hψ t`. Establish `hj : t ≤ s₀ + (⌈t - s₀⌉₊ : ℕ)`.

Use `Nat.le_ceil (t - s₀)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `(claim _ ψ hψ).mono hj`.
-/
theorem IsEllipticAt.regularity_le {T : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ)} {m : ℕ} {x₀ : E}
    (hT : IsEllipticAt T m x₀) (hm : 1 ≤ m) :
    ∃ δ > 0, ∀ δ' ∈ Set.Ioc 0 δ, ∀ (u : 𝓢'(E, ℂ)) (s₀ : ℝ), MemSobolev s₀ 2 u → ∀ F : 𝓢'(E, ℂ),
      (∀ t, MemSobolev t 2 F) → Distribution.IsVanishingOn (T u - F) (Metric.ball x₀ δ') →
      ∀ ψ : 𝓢(E, ℂ), tsupport (ψ : E → ℂ) ⊆ Metric.ball x₀ δ' →
        ∀ t, MemSobolev t 2 (smulLeftCLM ℂ (ψ : E → ℂ) u) := by
  obtain ⟨δ, hδ, hstep⟩ := hT.exists_regularity_radius hm
  refine ⟨δ, hδ, fun δ' ⟨hδ'0, hδ'δ⟩ u s₀ hu F hF hTF ↦ ?_⟩
  have claim : ∀ j : ℕ, ∀ ψ : 𝓢(E, ℂ), tsupport (ψ : E → ℂ) ⊆ Metric.ball x₀ δ' →
      MemSobolev (s₀ + j) 2 (smulLeftCLM ℂ (ψ : E → ℂ) u) := by
    intro j
    induction j with
    | zero => intro ψ _; simpa using memSobolev_smulLeft ψ hu
    | succ j ih =>
      intro ψ hψ
      obtain ⟨ρ, ⟨hρ0, hρδ⟩, hsub⟩ := exists_pos_lt_subset_ball hδ'0 (isClosed_tsupport _) hψ
      have hr₁ : 0 < (2 * ρ + δ') / 3 := by linarith
      have hr₁R : (2 * ρ + δ') / 3 < (ρ + 2 * δ') / 3 := by linarith
      set ψ₁ := bumpG x₀ hr₁ hr₁R
      have hψ₁ : tsupport (ψ₁ : E → ℂ) ⊆ Metric.ball x₀ δ' := by
        refine (tsupport_bumpG x₀ hr₁ hr₁R).trans fun x hx ↦ ?_
        rw [Metric.mem_closedBall] at hx; rw [Metric.mem_ball]; linarith
      set w := smulLeftCLM ℂ (ψ : E → ℂ) u
      have hw : MemSobolev (s₀ + j) 2 w := ih ψ hψ
      have hvan : Distribution.IsVanishingOn w (Metric.closedBall x₀ ρ)ᶜ :=
        (isVanishingOn_smulLeftCLM_compl ψ.hasTemperateGrowth u).mono
          (Set.compl_subset_compl.2 (hsub.trans Metric.ball_subset_closedBall))
      have hψT : smulLeftCLM ℂ (ψ : E → ℂ) (T u) = smulLeftCLM ℂ (ψ : E → ℂ) F := by
        have h0 := smulLeftCLM_eq_zero_of_isVanishingOn ψ.hasTemperateGrowth hTF hψ
        rw [map_sub, sub_eq_zero] at h0
        exact h0
      have hψψ₁ : smulLeftCLM ℂ (ψ : E → ℂ) (smulLeftCLM ℂ (ψ₁ : E → ℂ) u) =
          smulLeftCLM ℂ (ψ : E → ℂ) u := by
        have hfun : ((ψ₁ : E → ℂ) * (ψ : E → ℂ)) = (ψ : E → ℂ) := by
          ext x
          simp only [Pi.mul_apply]
          by_cases hx : ψ x = 0
          · rw [hx, mul_zero]
          · rw [bumpG_eq_one x₀ hr₁ hr₁R, one_mul]
            have := hsub (subset_tsupport _ hx)
            rw [Metric.mem_ball] at this; rw [Metric.mem_closedBall]; linarith
        rw [smulLeftCLM_smulLeftCLM_apply ψ₁.hasTemperateGrowth ψ.hasTemperateGrowth, hfun]
      have hcomm : comm T ψ u = comm T ψ (smulLeftCLM ℂ (ψ₁ : E → ℂ) u) := by
        have hz1 : smulLeftCLM ℂ (ψ : E → ℂ) (u - smulLeftCLM ℂ (ψ₁ : E → ℂ) u) = 0 := by
          rw [map_sub, hψψ₁, sub_self]
        have hz2 : Distribution.IsVanishingOn (u - smulLeftCLM ℂ (ψ₁ : E → ℂ) u)
            (Metric.ball x₀ ((2 * ρ + δ') / 3)) := by
          have := isVanishingOn_smulLeftCLM_sub ψ₁.hasTemperateGrowth
            (V := Metric.ball x₀ ((2 * ρ + δ') / 3))
            (fun x hx ↦ bumpG_eq_one x₀ hr₁ hr₁R (Metric.ball_subset_closedBall hx)) u
          have h2 := isVanishingOn_neg this
          rwa [neg_sub] at h2
        have hz3 : smulLeftCLM ℂ (ψ : E → ℂ) (T (u - smulLeftCLM ℂ (ψ₁ : E → ℂ) u)) = 0 :=
          smulLeftCLM_eq_zero_of_isVanishingOn ψ.hasTemperateGrowth
            (hT.isLocal _ Metric.isOpen_ball _ hz2)
            (hsub.trans (Metric.ball_subset_ball (by linarith)))
        have : comm T ψ (u - smulLeftCLM ℂ (ψ₁ : E → ℂ) u) = 0 := by
          rw [comm_apply, hz1, map_zero, hz3, sub_zero]
        rw [map_sub, sub_eq_zero] at this
        exact this
      have hTw : MemSobolev (s₀ + j - m + 1) 2 (T w) := by
        have e : T w = smulLeftCLM ℂ (ψ : E → ℂ) F + comm T ψ (smulLeftCLM ℂ (ψ₁ : E → ℂ) u) := by
          rw [← hcomm, ← hψT, comm_apply]; abel
        rw [e]
        refine (memSobolev_smulLeft ψ (hF _)).add ?_
        exact (hT.hasOrder_comm ψ).memSobolev' (by ring) (ih ψ₁ hψ₁)
      have := hstep (s₀ + j) w hw ⟨ρ, hρδ.trans_le hδ'δ, hvan⟩ hTw
      simpa [add_assoc] using this
  intro ψ hψ t
  have hj : t ≤ s₀ + (⌈t - s₀⌉₊ : ℕ) := by
    have := Nat.le_ceil (t - s₀); linarith
  exact (claim _ ψ hψ).mono hj

/- English proof (translation)
Use `exists_contDiffOn_of_locally_memSobolev hΩ fun x hx ↦ ?_` and prove the remaining obligations. Take `⟨δ, hδ, hreg⟩` from `(hT x hx).regularity_le hm`. Take `⟨ε, hε, hball⟩` from `Metric.isOpen_iff.1 hΩ x hx`. Use `set δ' := min δ ε`. Establish `hδ' : 0 < δ'` using `lt_min hδ hε`.

Establish `hr : 0 < δ' / 4` using `by positivity`. Use `⟨bump x hr, ?_, fun t ↦ hreg δ' ⟨hδ', min_le_left _ _⟩ u s₀ hu F hF (hTF.mono ((Metric.ball_subset_ball (min_le_right _ _)).trans hball)) _ ?_ t⟩` and prove the remaining obligations. Use `filter_upwards [Metric.ball_mem_nhds x hr] with y hy`. Conclude with `bump_eq_one x hr (Metric.ball_subset_closedBall hy)`. Use `(tsupport_bump x hr).trans fun y hy ↦ ?_` and prove the remaining obligations.

Rewrite `hy` using `[Metric.mem_closedBall]`. Rewrite using `[Metric.mem_ball]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem contDiffOn_of_isEllipticAt {T : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ)} {m : ℕ} (hm : 1 ≤ m)
    {Ω : Set E} (hΩ : IsOpen Ω) (hT : ∀ x ∈ Ω, IsEllipticAt T m x) {u : 𝓢'(E, ℂ)} {s₀ : ℝ}
    (hu : MemSobolev s₀ 2 u) {F : 𝓢'(E, ℂ)} (hF : ∀ t, MemSobolev t 2 F)
    (hTF : Distribution.IsVanishingOn (T u - F) Ω) :
    ∃ g : E → ℂ, ContDiffOn ℝ ∞ g Ω ∧ ∀ φ : 𝓢(E, ℂ), HasCompactSupport φ → tsupport φ ⊆ Ω →
      u φ = ∫ x, φ x • g x := by
  refine exists_contDiffOn_of_locally_memSobolev hΩ fun x hx ↦ ?_
  obtain ⟨δ, hδ, hreg⟩ := (hT x hx).regularity_le hm
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hΩ x hx
  set δ' := min δ ε
  have hδ' : 0 < δ' := lt_min hδ hε
  have hr : 0 < δ' / 4 := by positivity
  refine ⟨bump x hr, ?_, fun t ↦ hreg δ' ⟨hδ', min_le_left _ _⟩ u s₀ hu F hF
    (hTF.mono ((Metric.ball_subset_ball (min_le_right _ _)).trans hball)) _ ?_ t⟩
  · filter_upwards [Metric.ball_mem_nhds x hr] with y hy
    exact bump_eq_one x hr (Metric.ball_subset_closedBall hy)
  · refine (tsupport_bump x hr).trans fun y hy ↦ ?_
    rw [Metric.mem_closedBall] at hy; rw [Metric.mem_ball]; linarith

end

end GroundTheory.Automorphic.Sobolev
