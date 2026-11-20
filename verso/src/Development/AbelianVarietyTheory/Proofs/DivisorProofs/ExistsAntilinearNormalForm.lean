import Mathlib

namespace GlobalTheory

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Establish `h1 : ‖a * y‖ = ‖b * starRingEnd ℂ y‖`. Rewrite using `[eq_neg_of_add_eq_zero_left hy, norm_neg]`. Rewrite `h1` using `[norm_mul, norm_mul, Complex.norm_conj]`. Establish `hy' : 0 < ‖y‖` using `norm_pos_iff.mpr hne`.

Establish `h2` using `mul_right_cancel₀ hy'.ne' h1`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem coordsDiag_key (a b y : ℂ) (h : ‖b‖ < ‖a‖) (hy : a * y + b * starRingEnd ℂ y = 0) : y = 0 := by
  by_contra hne
  have h1 : ‖a * y‖ = ‖b * starRingEnd ℂ y‖ := by
    rw [eq_neg_of_add_eq_zero_left hy, norm_neg]
  rw [norm_mul, norm_mul, Complex.norm_conj] at h1
  have hy' : 0 < ‖y‖ := norm_pos_iff.mpr hne
  have h2 := mul_right_cancel₀ hy'.ne' h1
  linarith

/- English proof (translation)
Introduce `g T hq α β hαβ hT`. Use `choose q hq using hq`. Establish `hα : ∀ j, α j ≠ 0` using `fun j h => by`. Use `hαβ j` as an intermediate fact. Rewrite `this` using `[h, norm_zero]`.

Conclude with `(norm_nonneg _).not_gt this`. Establish `hTinj : Function.Injective T`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `v hv`. Use function extensionality and compare the values at `j`.

Establish `h1` using `hq j v`. Rewrite `h1` using `[hv, map_zero]`. Establish `h2` using `congrFun h1.symm j`. Rewrite `h2` using `[hT]`. Conclude with `coordsDiag_key _ _ _ (hαβ j) h2`.

Establish `hTsurj : Function.Surjective T` using `LinearMap.injective_iff_surjective.mp hTinj`. Set `L : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)` to `LinearMap.pi (fun j => (α j)⁻¹ • (LinearMap.proj j ∘ₗ q j))`. Establish `hL : ∀ v, L (T v) = fun j ↦ v j + β j / α j * starRingEnd ℂ (v j)`. Introduce `v`. Use function extensionality and compare the values at `j`.

Simplify using `only [L, LinearMap.pi_apply, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.proj_apply, smul_eq_mul]`. Rewrite using `[hq j v, hT]`. Clear denominators, using `[hα j]` for the nonvanishing conditions. Establish `hLinj : Function.Injective L`. Rewrite using `[injective_iff_map_eq_zero]`.

Introduce `w hw`. Take `⟨v, rfl⟩` from `hTsurj w`. Establish `hv : v = 0`. Use function extensionality and compare the values at `j`. Establish `h3` using `congrFun ((hL v).symm.trans hw) j`.

Establish `hz : ‖β j / α j‖ < ‖(1 : ℂ)‖`. Rewrite using `[norm_div, norm_one, div_lt_one (norm_pos_iff.mpr (hα j))]`. Conclude with `hαβ j`. Apply `coordsDiag_key 1 (β j / α j) (v j) hz` to reduce the goal to its premises. Simplify using `using h3`.

Rewrite using `[hv, map_zero]`. Establish `hLsurj` using `LinearMap.injective_iff_surjective.mp hLinj`. Use `⟨LinearEquiv.ofBijective L ⟨hLinj, hLsurj⟩, hL, ?_⟩` and prove the remaining obligations. Introduce `c M hM w`. Take `⟨v, rfl⟩` from `hTsurj w`.

Use `show L (M (T v)) = fun j => (c j : ℂ) * L (T v) j`. Rewrite using `[← hM, hL, hL]`. Use function extensionality and compare the values at `j`. Simplify using `only [map_mul, Complex.conj_ofReal]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem coordsDiag : ∀ (g : ℕ) (T : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ)),
    (∀ j : Fin g, ∃ q : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ v, q (T v) = T (Pi.single j (v j))) →
    ∀ (α β : Fin g → ℂ), (∀ j, ‖β j‖ < ‖α j‖) →
    (∀ j (y : ℂ), T (Pi.single j y) j = α j * y + β j * starRingEnd ℂ y) →
    ∃ D : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ),
      (∀ v, D (T v) = fun j ↦ v j + β j / α j * starRingEnd ℂ (v j)) ∧
      ∀ (c : Fin g → ℝ) (M : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), (∀ v, T (fun m ↦ (c m : ℂ) * v m) = M (T v)) →
        ∀ w, D (M w) = fun j ↦ (c j : ℂ) * D w j := by
  intro g T hq α β hαβ hT
  choose q hq using hq
  have hα : ∀ j, α j ≠ 0 := fun j h => by
    have := hαβ j
    rw [h, norm_zero] at this
    exact (norm_nonneg _).not_gt this
  have hTinj : Function.Injective T := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    funext j
    have h1 := hq j v
    rw [hv, map_zero] at h1
    have h2 := congrFun h1.symm j
    rw [hT] at h2
    exact coordsDiag_key _ _ _ (hαβ j) h2
  have hTsurj : Function.Surjective T := LinearMap.injective_iff_surjective.mp hTinj
  let L : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) :=
    LinearMap.pi (fun j => (α j)⁻¹ • (LinearMap.proj j ∘ₗ q j))
  have hL : ∀ v, L (T v) = fun j ↦ v j + β j / α j * starRingEnd ℂ (v j) := by
    intro v; funext j
    simp only [L, LinearMap.pi_apply, LinearMap.smul_apply, LinearMap.comp_apply,
      LinearMap.proj_apply, smul_eq_mul]
    rw [hq j v, hT]
    field_simp [hα j]
  have hLinj : Function.Injective L := by
    rw [injective_iff_map_eq_zero]
    intro w hw
    obtain ⟨v, rfl⟩ := hTsurj w
    have hv : v = 0 := by
      funext j
      have h3 := congrFun ((hL v).symm.trans hw) j
      have hz : ‖β j / α j‖ < ‖(1 : ℂ)‖ := by
        rw [norm_div, norm_one, div_lt_one (norm_pos_iff.mpr (hα j))]
        exact hαβ j
      apply coordsDiag_key 1 (β j / α j) (v j) hz
      simpa using h3
    rw [hv, map_zero]
  have hLsurj := LinearMap.injective_iff_surjective.mp hLinj
  refine ⟨LinearEquiv.ofBijective L ⟨hLinj, hLsurj⟩, hL, ?_⟩
  intro c M hM w
  obtain ⟨v, rfl⟩ := hTsurj w
  show L (M (T v)) = fun j => (c j : ℂ) * L (T v) j
  rw [← hM, hL, hL]
  funext j
  simp only [map_mul, Complex.conj_ofReal]
  ring

end GlobalTheory
