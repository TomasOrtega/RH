import Mathlib
import ReciprocityTheory.ThetaQuasiPeriods.ThetaQuasiPeriodStatement
import ReciprocityTheory.ThetaQuasiPeriods.Transl
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsEventuallyNormRiemannThetaTermLe

open Complex Matrix Filter Topology ReciprocityTheory.PTheta

namespace GlobalTheory

variable {ι : Type*} [Fintype ι]

/- English proof (translation)
Introduce `τ hτ`. Take `⟨hs, hp⟩` from `hτ`. Establish `ht : (τ.map Complex.im)ᵀ = τ.map Complex.im`. Rewrite using `[← Matrix.transpose_map, hs.eq]`. Use `show (τ.map Complex.im + (τ.map Complex.im)ᵀ).PosDef`.

Rewrite using `[ht]`. Conclude with `hp.add hp`.
-/
theorem siegelH_subset_thetaDomain : SiegelH ι ⊆ ThetaDomain ι := by
  intro τ hτ
  obtain ⟨hs, hp⟩ := hτ
  have ht : (τ.map Complex.im)ᵀ = τ.map Complex.im := by
    rw [← Matrix.transpose_map, hs.eq]
  show (τ.map Complex.im + (τ.map Complex.im)ᵀ).PosDef
  rw [ht]
  exact hp.add hp

/- English proof (translation)
Use `set S : Matrix ι ι ℂ → Matrix ι ι ℝ := fun τ => τ.map Complex.im + (τ.map Complex.im)ᵀ with hS`. Establish `hherm : ∀ τ, (S τ).IsHermitian`. Introduce `τ`. Use extensionality with `i j`. Simplify using `[hS, add_comm]`.

Establish `hscale : ∀ τ (c : ℝ) (x : ι → ℝ), (c • x) ⬝ᵥ (S τ *ᵥ (c • x)) = c * c * (x ⬝ᵥ (S τ *ᵥ x))`. Introduce `τ c x`. Simplify using `only [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `key : ∀ τ, τ ∈ ThetaDomain ι ↔ ∀ x ∈ Metric.sphere (0 : ι → ℝ) 1, 0 < x ⬝ᵥ (S τ *ᵥ x)`.

Introduce `τ`. Express the relevant statement in the definitionally equal form `(S τ).PosDef ↔ _`. Rewrite using `[Matrix.posDef_iff_dotProduct_mulVec]`. Simplify using `only [star_trivial]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨-, h⟩ x hx`. Apply `h` to reduce the goal to its premises. Introduce and unpack `rfl`. Simplify using `at hx`. Introduce `h`.

Use `⟨hherm τ, fun x hx => ?_⟩` and prove the remaining obligations. Establish `hn : 0 < ‖x‖` using `norm_pos_iff.mpr hx`. Establish `hy : ‖x‖⁻¹ • x ∈ Metric.sphere (0 : ι → ℝ) 1`. Rewrite using `[mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ hn.ne']`. Establish `h1` using `h _ hy`.

Rewrite `h1` using `[hscale]`. Assume the negation of the conclusion as `hle`. Establish `: ‖x‖⁻¹ * ‖x‖⁻¹ * (x ⬝ᵥ (S τ *ᵥ x)) ≤ 0` using `mul_nonpos_of_nonneg_of_nonpos (by positivity) (not_lt.mp hle)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hcont : Continuous fun p : Matrix ι ι ℂ × (ι → ℝ) => p.2 ⬝ᵥ (S p.1 *ᵥ p.2)`.

Establish `hm : Continuous fun p : Matrix ι ι ℂ × (ι → ℝ) => p.1.map Complex.im` using `continuous_fst.matrix_map Complex.continuous_im`. Conclude with `continuous_snd.dotProduct ((hm.add hm.matrix_transpose).matrix_mulVec continuous_snd)`. Rewrite using `[isOpen_iff_eventually]`. Introduce `τ₀ h₀`. Establish `hev : ∀ᶠ τ in 𝓝 τ₀, ∀ x ∈ Metric.sphere (0 : ι → ℝ) 1, 0 < x ⬝ᵥ (S τ *ᵥ x)`.

Use `(isCompact_sphere (0 : ι → ℝ) 1).eventually_forall_of_forall_eventually (P := fun τ x => 0 < x ⬝ᵥ (S τ *ᵥ x)) fun x hx => ?_` and prove the remaining obligations. Conclude with `(hcont.continuousAt (x := (τ₀, x))).eventually (lt_mem_nhds ((key τ₀).1 h₀ x hx))`. Use `filter_upwards [hev] with τ hτ`. Conclude with `(key τ).2 hτ`.
-/
theorem isOpen_thetaDomain : IsOpen (ThetaDomain ι) := by
  set S : Matrix ι ι ℂ → Matrix ι ι ℝ :=
    fun τ => τ.map Complex.im + (τ.map Complex.im)ᵀ with hS
  have hherm : ∀ τ, (S τ).IsHermitian := by
    intro τ
    ext i j
    simp [hS, add_comm]
  have hscale : ∀ τ (c : ℝ) (x : ι → ℝ),
      (c • x) ⬝ᵥ (S τ *ᵥ (c • x)) = c * c * (x ⬝ᵥ (S τ *ᵥ x)) := by
    intro τ c x
    simp only [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
    ring
  have key : ∀ τ, τ ∈ ThetaDomain ι ↔
      ∀ x ∈ Metric.sphere (0 : ι → ℝ) 1, 0 < x ⬝ᵥ (S τ *ᵥ x) := by
    intro τ
    change (S τ).PosDef ↔ _
    rw [Matrix.posDef_iff_dotProduct_mulVec]
    simp only [star_trivial]
    constructor
    · rintro ⟨-, h⟩ x hx
      apply h
      rintro rfl
      simp at hx
    · intro h
      refine ⟨hherm τ, fun x hx => ?_⟩
      have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
      have hy : ‖x‖⁻¹ • x ∈ Metric.sphere (0 : ι → ℝ) 1 := by
        rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm,
          inv_mul_cancel₀ hn.ne']
      have h1 := h _ hy
      rw [hscale] at h1
      by_contra hle
      have : ‖x‖⁻¹ * ‖x‖⁻¹ * (x ⬝ᵥ (S τ *ᵥ x)) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) (not_lt.mp hle)
      linarith
  have hcont : Continuous fun p : Matrix ι ι ℂ × (ι → ℝ) => p.2 ⬝ᵥ (S p.1 *ᵥ p.2) := by
    have hm : Continuous fun p : Matrix ι ι ℂ × (ι → ℝ) => p.1.map Complex.im :=
      continuous_fst.matrix_map Complex.continuous_im
    exact continuous_snd.dotProduct ((hm.add hm.matrix_transpose).matrix_mulVec continuous_snd)
  rw [isOpen_iff_eventually]
  intro τ₀ h₀
  have hev : ∀ᶠ τ in 𝓝 τ₀, ∀ x ∈ Metric.sphere (0 : ι → ℝ) 1, 0 < x ⬝ᵥ (S τ *ᵥ x) := by
    refine (isCompact_sphere (0 : ι → ℝ) 1).eventually_forall_of_forall_eventually
      (P := fun τ x => 0 < x ⬝ᵥ (S τ *ᵥ x)) fun x hx => ?_
    exact (hcont.continuousAt (x := (τ₀, x))).eventually (lt_mem_nhds ((key τ₀).1 h₀ x hx))
  filter_upwards [hev] with τ hτ
  exact (key τ).2 hτ

/- English proof (translation)
Use `⟨fun κ _ => siegelH_subset_thetaDomain, fun κ _ => ?_⟩` and prove the remaining obligations. Conclude with `isOpen_thetaDomain`.
-/
theorem siegelSubDomain_and_domainOpen : SiegelSubDomainStatement ∧ DomainOpenStatement := by
  refine ⟨fun κ _ => siegelH_subset_thetaDomain, fun κ _ => ?_⟩
  exact isOpen_thetaDomain

end GlobalTheory
