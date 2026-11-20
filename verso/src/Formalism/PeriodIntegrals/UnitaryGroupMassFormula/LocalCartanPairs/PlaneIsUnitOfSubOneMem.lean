import Mathlib

noncomputable section

namespace PI.SqPair.LCP

open Polynomial IsLocalRing Matrix

/- English proof (translation)
Assume the negation of the conclusion as `hx`. Establish `hxm : x ∈ maximalIdeal A` using `(mem_maximalIdeal x).2 hx`. Establish `h1 : (1 : A) ∈ maximalIdeal A`. Establish `h2` using `sub_mem hxm h`. Rewrite `h2` using `[sub_sub_cancel]`. Then use the resulting hypothesis.

Conclude with `(maximalIdeal.isMaximal A).ne_top ((Ideal.eq_top_iff_one _).2 h1)`.
-/
theorem plane_isUnit_of_sub_one_mem {A : Type*} [CommRing A] [IsLocalRing A] {x : A}
    (h : x - 1 ∈ maximalIdeal A) : IsUnit x := by
  by_contra hx
  have hxm : x ∈ maximalIdeal A := (mem_maximalIdeal x).2 hx
  have h1 : (1 : A) ∈ maximalIdeal A := by
    have h2 := sub_mem hxm h
    rwa [sub_sub_cancel] at h2
  exact (maximalIdeal.isMaximal A).ne_top ((Ideal.eq_top_iff_one _).2 h1)

/- English proof (translation)
Establish `h3σ : σ c * (1 + σ t * α) = 1`. Establish `h4` using `congrArg σ h3`. Simplify `h4` using `only [map_mul, map_add, map_one, hα]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `ext i j fin_cases i <;> fin_cases j <;>`.

Simplify using `[Matrix.mul_apply, Fin.sum_univ_two, map_add, map_mul, map_one]`. Take the linear combination `h2 + σ s * s * h1`. Take the linear combination `h3 + σ s * c * h1`. Take the linear combination `h3σ + σ c * s * h1`. Take the linear combination `σ c * c * h1`.

Simplify using `[Matrix.det_fin_two]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem plane_core {R : Type*} [CommRing R] (σ : R ≃+* R) (α β t s c : R)
    (hα : σ α = α) (h1 : β + t + σ t + t * σ t * α = 0)
    (h2 : s * (1 + t * α) + σ s * (1 + σ t * α) = -α) (h3 : c * (1 + t * α) = 1) :
    ((!![1 + s * t, c * t; s, c] : Matrix (Fin 2) (Fin 2) R).map σ)ᵀ * !![α, 1; 1, β]
        * !![1 + s * t, c * t; s, c] = !![0, 1; 1, 0] ∧
      (!![1 + s * t, c * t; s, c] : Matrix (Fin 2) (Fin 2) R).det = c := by
  have h3σ : σ c * (1 + σ t * α) = 1 := by
    have h4 := congrArg σ h3
    simpa only [map_mul, map_add, map_one, hα] using h4
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, map_add, map_mul, map_one]
    · linear_combination h2 + σ s * s * h1
    · linear_combination h3 + σ s * c * h1
    · linear_combination h3σ + σ c * s * h1
    · linear_combination σ c * c * h1
  · simp [Matrix.det_fin_two]
    ring

/- English proof (translation)
Establish `hfix : ∀ x : R₀, σ (x : R) = x` using `fun x => (hR₀ x).1 x.2`. Establish `hNfix : σ (τ * σ τ) = τ * σ τ` using `by rw [map_mul, hσ, mul_comm]`. Set `N : R₀` to `⟨τ * σ τ, (hR₀ _).2 hNfix⟩`. Establish `hN : (N : R) = τ * σ τ` using `rfl`. Take `⟨w, hwroot, hw1⟩` from `HenselianLocalRing.is_henselian (X ^ 2 - X + C (α * N * β)) (by monicity!) 1 (by`.

Simplify using `only [eval_add, eval_sub, eval_pow, eval_X, eval_C, one_pow, sub_self, zero_add]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ hα))`. Use the proof step `(by`. Simplify using `only [derivative_add, derivative_sub, derivative_X_pow, derivative_X, derivative_C, eval_add, eval_sub, eval_mul, eval_C, eval_pow, eval_X, eval_one, eval_zero]`. Use the proof step `norm_num)`.

Establish `hr : w ^ 2 - w + α * N * β = 0`. Establish `h0` using `hwroot.eq_zero`. Simplify `h0` using `only [eval_add, eval_sub, eval_pow, eval_X, eval_C]`. Take `⟨wu, rfl⟩` from `plane_isUnit_of_sub_one_mem hw1`. Establish `hwv : (wu : R₀) * ↑wu⁻¹ = 1` using `wu.mul_inv`.

Set `x : R₀` to `-β * ↑wu⁻¹`. Establish `hx : β + x + α * N * x ^ 2 = 0`. Take the linear combination `(β * (↑wu⁻¹ : R₀) ^ 2) * hr - (β + β * ↑wu⁻¹ * ↑wu - β * ↑wu⁻¹) * hwv`. Establish `hxR : (β : R) + x + α * (τ * σ τ) * (x : R) ^ 2 = 0`. Establish `h0` using `congrArg (fun y : R₀ => (y : R)) hx`.

Simplify `h0` using `only [Subring.coe_add, Subring.coe_mul, Subring.coe_pow, hN, ZeroMemClass.coe_zero]`. Set `nR : R₀` to `1 + x * α + N * x ^ 2 * α ^ 2`. Establish `hnm : nR - 1 ∈ maximalIdeal R₀`. Establish `e : nR - 1 = α * (x + N * x ^ 2 * α)` using `by ring`. Rewrite using `[e]`.

Conclude with `Ideal.mul_mem_right _ _ hα`. Take `⟨nu, hnu⟩` from `plane_isUnit_of_sub_one_mem hnm`. Establish `hninv : ((nR : R₀) : R) * ((↑nu⁻¹ : R₀) : R) = 1`. Establish `h0` using `congrArg (fun y : R₀ => (y : R)) nu.mul_inv`. Simplify `h0` using `only [hnu, Subring.coe_mul, OneMemClass.coe_one]`.

Use `set t : R := τ * x with ht`. Establish `hσt : σ t = σ τ * x` using `by rw [ht, map_mul, hfix]`. Establish `hnR : (1 + t * α) * (1 + σ t * α) = ((nR : R₀) : R)`. Rewrite using `[hσt, ht]`. Simplify using `only [nR]`.

Use `push_cast`. Take the linear combination `((x : R) * α) * hτ - ((x : R) ^ 2 * (α : R) ^ 2) * hN`. Use `set c : R := (1 + σ t * α) * ((↑nu⁻¹ : R₀) : R) with hc`. Establish `h3 : c * (1 + t * α) = 1`. Rewrite using `[hc]`.

Take the linear combination `((↑nu⁻¹ : R₀) : R) * hnR + hninv`. Establish `hσc : σ c = (1 + t * α) * ((↑nu⁻¹ : R₀) : R)`. Rewrite using `[hc, map_mul, map_add, map_one, map_mul, hσ, hfix, hfix]`. Use `⟨t, -((α : R) * τ * c), c, ?_, ?_, h3, -(τ * c), by ring⟩` and prove the remaining obligations. Rewrite using `[hσt, ht]`.

Take the linear combination `hxR + (x : R) * hτ`. Rewrite using `[map_neg, map_mul, map_mul, hfix, hσc]`. Take the linear combination `(-((α : R) * τ)) * h3 + (-((α : R) * σ τ * ((↑nu⁻¹ : R₀) : R))) * hnR + (-((α : R) * σ τ)) * hninv + (-(α : R)) * hτ`.
-/
theorem plane_exists {R : Type*} [CommRing R] (σ : R ≃+* R) (hσ : ∀ x, σ (σ x) = x)
    (R₀ : Subring R) (hR₀ : ∀ x, x ∈ R₀ ↔ σ x = x) [HenselianLocalRing R₀]
    (τ : R) (hτ : τ + σ τ = 1) (α β : R₀) (hα : α ∈ maximalIdeal R₀) :
    ∃ t s c : R, β + t + σ t + t * σ t * α = 0 ∧
      s * (1 + t * α) + σ s * (1 + σ t * α) = -α ∧ c * (1 + t * α) = 1 ∧ ∃ s', s = α * s' := by
  have hfix : ∀ x : R₀, σ (x : R) = x := fun x => (hR₀ x).1 x.2
  have hNfix : σ (τ * σ τ) = τ * σ τ := by rw [map_mul, hσ, mul_comm]
  let N : R₀ := ⟨τ * σ τ, (hR₀ _).2 hNfix⟩
  have hN : (N : R) = τ * σ τ := rfl
  obtain ⟨w, hwroot, hw1⟩ := HenselianLocalRing.is_henselian (X ^ 2 - X + C (α * N * β))
    (by monicity!) 1
    (by
      simp only [eval_add, eval_sub, eval_pow, eval_X, eval_C, one_pow, sub_self, zero_add]
      exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ hα))
    (by
      simp only [derivative_add, derivative_sub, derivative_X_pow, derivative_X, derivative_C,
        eval_add, eval_sub, eval_mul, eval_C, eval_pow, eval_X, eval_one, eval_zero]
      norm_num)
  have hr : w ^ 2 - w + α * N * β = 0 := by
    have h0 := hwroot.eq_zero
    simpa only [eval_add, eval_sub, eval_pow, eval_X, eval_C] using h0
  obtain ⟨wu, rfl⟩ := plane_isUnit_of_sub_one_mem hw1
  have hwv : (wu : R₀) * ↑wu⁻¹ = 1 := wu.mul_inv
  let x : R₀ := -β * ↑wu⁻¹
  have hx : β + x + α * N * x ^ 2 = 0 := by
    linear_combination (β * (↑wu⁻¹ : R₀) ^ 2) * hr -
      (β + β * ↑wu⁻¹ * ↑wu - β * ↑wu⁻¹) * hwv
  have hxR : (β : R) + x + α * (τ * σ τ) * (x : R) ^ 2 = 0 := by
    have h0 := congrArg (fun y : R₀ => (y : R)) hx
    simpa only [Subring.coe_add, Subring.coe_mul, Subring.coe_pow, hN, ZeroMemClass.coe_zero]
      using h0
  let nR : R₀ := 1 + x * α + N * x ^ 2 * α ^ 2
  have hnm : nR - 1 ∈ maximalIdeal R₀ := by
    have e : nR - 1 = α * (x + N * x ^ 2 * α) := by ring
    rw [e]
    exact Ideal.mul_mem_right _ _ hα
  obtain ⟨nu, hnu⟩ := plane_isUnit_of_sub_one_mem hnm
  have hninv : ((nR : R₀) : R) * ((↑nu⁻¹ : R₀) : R) = 1 := by
    have h0 := congrArg (fun y : R₀ => (y : R)) nu.mul_inv
    simpa only [hnu, Subring.coe_mul, OneMemClass.coe_one] using h0
  set t : R := τ * x with ht
  have hσt : σ t = σ τ * x := by rw [ht, map_mul, hfix]
  have hnR : (1 + t * α) * (1 + σ t * α) = ((nR : R₀) : R) := by
    rw [hσt, ht]
    simp only [nR]
    push_cast
    linear_combination ((x : R) * α) * hτ - ((x : R) ^ 2 * (α : R) ^ 2) * hN
  set c : R := (1 + σ t * α) * ((↑nu⁻¹ : R₀) : R) with hc
  have h3 : c * (1 + t * α) = 1 := by
    rw [hc]
    linear_combination ((↑nu⁻¹ : R₀) : R) * hnR + hninv
  have hσc : σ c = (1 + t * α) * ((↑nu⁻¹ : R₀) : R) := by
    rw [hc, map_mul, map_add, map_one, map_mul, hσ, hfix, hfix]
  refine ⟨t, -((α : R) * τ * c), c, ?_, ?_, h3, -(τ * c), by ring⟩
  · rw [hσt, ht]
    linear_combination hxR + (x : R) * hτ
  · rw [map_neg, map_mul, map_mul, hfix, hσc]
    linear_combination (-((α : R) * τ)) * h3 + (-((α : R) * σ τ * ((↑nu⁻¹ : R₀) : R))) * hnR +
      (-((α : R) * σ τ)) * hninv + (-(α : R)) * hτ

/- English proof (translation)
Take `⟨t, s, c, h1, h2, h3, s', hs'⟩` from `plane_exists σ hσ R₀ hR₀ τ hτ α β hα`. Take `⟨hform, hdet⟩` from `plane_core σ (α : R) (β : R) t s c ((hR₀ _).1 α.2) h1 h2 h3`. Use `⟨!![1 + s * t, c * t; s, c], ?_, hform, s', ?_⟩` and prove the remaining obligations. Rewrite using `[hdet]`. Conclude with `IsUnit.of_mul_eq_one _ h3`.

Simplify using `[hs']`.
-/
theorem plane_w {R : Type*} [CommRing R] (σ : R ≃+* R) (hσ : ∀ x, σ (σ x) = x)
    (R₀ : Subring R) (hR₀ : ∀ x, x ∈ R₀ ↔ σ x = x) [HenselianLocalRing R₀]
    (τ : R) (hτ : τ + σ τ = 1) (α β : R₀) (hα : α ∈ maximalIdeal R₀) :
    ∃ w : Matrix (Fin 2) (Fin 2) R, IsUnit w.det ∧
      (w.map σ)ᵀ * !![(α : R), 1; 1, (β : R)] * w = !![0, 1; 1, 0] ∧ ∃ s', w 1 0 = (α : R) * s' := by
  obtain ⟨t, s, c, h1, h2, h3, s', hs'⟩ := plane_exists σ hσ R₀ hR₀ τ hτ α β hα
  obtain ⟨hform, hdet⟩ := plane_core σ (α : R) (β : R) t s c ((hR₀ _).1 α.2) h1 h2 h3
  refine ⟨!![1 + s * t, c * t; s, c], ?_, hform, s', ?_⟩
  · rw [hdet]
    exact IsUnit.of_mul_eq_one _ h3
  · simp [hs']

/- English proof (translation)
Take `⟨u, hu⟩` from `hθ`. Use `⟨θ * ↑u⁻¹, ?_⟩` and prove the remaining obligations. Establish `hσu : σ (↑u : R) = -↑u` using `by rw [hu, map_sub, hσ]; ring`. Establish `h2 : (↑u : R) * ↑u⁻¹ = 1` using `Units.mul_inv u`. Establish `hσinv : σ (↑u⁻¹ : R) = -↑u⁻¹`.

Establish `h1 : σ (↑u : R) * σ (↑u⁻¹ : R) = 1` using `by rw [← map_mul, Units.mul_inv, map_one]`. Rewrite `h1` using `[hσu]`. Take the linear combination `(-σ (↑u⁻¹ : R)) * h2 + (-(↑u⁻¹ : R)) * h1`. Rewrite using `[map_mul, hσinv]`. Rewrite `h2` using `[hu]`.

Take the linear combination `h2`.
-/
theorem tau_of_theta {R : Type*} [CommRing R] (σ : R ≃+* R) (hσ : ∀ x, σ (σ x) = x) (θ : R)
    (hθ : IsUnit (θ - σ θ)) : ∃ τ : R, τ + σ τ = 1 := by
  obtain ⟨u, hu⟩ := hθ
  refine ⟨θ * ↑u⁻¹, ?_⟩
  have hσu : σ (↑u : R) = -↑u := by rw [hu, map_sub, hσ]; ring
  have h2 : (↑u : R) * ↑u⁻¹ = 1 := Units.mul_inv u
  have hσinv : σ (↑u⁻¹ : R) = -↑u⁻¹ := by
    have h1 : σ (↑u : R) * σ (↑u⁻¹ : R) = 1 := by rw [← map_mul, Units.mul_inv, map_one]
    rw [hσu] at h1
    linear_combination (-σ (↑u⁻¹ : R)) * h2 + (-(↑u⁻¹ : R)) * h1
  rw [map_mul, hσinv]
  rw [hu] at h2
  linear_combination h2

end PI.SqPair.LCP
