import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIndexOfGammaLe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.JInvariantEqualSl2OrbitStatement
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

namespace GlobalTheory.EllipticZero

/- English proof (translation)
Establish `hd : 0 < ((h : GL (Fin 2) ℝ)).det.val` using `by simp`. Use `denom_cocycle (g : GL (Fin 2) ℝ) (h : GL (Fin 2) ℝ) z.im_ne_zero` as an intermediate fact. Rewrite `this` using `[← coe_smul_of_det_pos hd, ← ModularGroup.sl_moeb]`. Rewrite using `[← this, map_mul, map_mul]`.
-/
lemma denom_mul_SL (g h : SL(2, ℤ)) (z : ℍ) :
    denom ((g * h : SL(2, ℤ)) : GL (Fin 2) ℝ) z
      = denom (g : GL (Fin 2) ℝ) ((h • z : ℍ) : ℂ) * denom (h : GL (Fin 2) ℝ) z := by
  have hd : 0 < ((h : GL (Fin 2) ℝ)).det.val := by simp
  have := denom_cocycle (g : GL (Fin 2) ℝ) (h : GL (Fin 2) ℝ) z.im_ne_zero
  rw [← coe_smul_of_det_pos hd, ← ModularGroup.sl_moeb] at this
  rw [← this, map_mul, map_mul]

/- English proof (translation)
Use `⟨by rw [mul_smul, mul_smul, inv_smul_smul, hu], ?_⟩` and prove the remaining obligations. Establish `h1` using `denom_mul_SL (γ * u * γ⁻¹) γ σ`. Establish `h2` using `denom_mul_SL γ u σ`. Rewrite `h1` using `[inv_mul_cancel_right, h2, hu, mul_comm]`. Conclude with `(mul_right_cancel₀ (denom_ne_zero _ _) h1).symm`.
-/
lemma conj_fix (γ u : SL(2, ℤ)) (σ : ℍ) (hu : u • σ = σ) :
    (γ * u * γ⁻¹) • (γ • σ) = γ • σ ∧
      denom ((γ * u * γ⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ) ((γ • σ : ℍ) : ℂ)
        = denom (u : GL (Fin 2) ℝ) σ := by
  refine ⟨by rw [mul_smul, mul_smul, inv_smul_smul, hu], ?_⟩
  have h1 := denom_mul_SL (γ * u * γ⁻¹) γ σ
  have h2 := denom_mul_SL γ u σ
  rw [inv_mul_cancel_right, h2, hu, mul_comm] at h1
  exact (mul_right_cancel₀ (denom_ne_zero _ _) h1).symm

/- English proof (translation)
Establish `h : f (u • σ) = denom u σ ^ k * f σ` using `SlashInvariantForm.slash_action_eqn'' f (by simp) σ`. Rewrite `h` using `[hu]`. Establish `: (denom (u : GL (Fin 2) ℝ) σ ^ k - 1) * f σ = 0` using `by linear_combination -h`. Conclude with `(mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hk)`.
-/
lemma eq_zero_of_fix {k : ℤ} (f : ModularForm 𝒮ℒ k) (u : SL(2, ℤ)) (σ : ℍ) (hu : u • σ = σ)
    (hk : denom (u : GL (Fin 2) ℝ) σ ^ k ≠ 1) : f σ = 0 := by
  have h : f (u • σ) = denom u σ ^ k * f σ :=
    SlashInvariantForm.slash_action_eqn'' f (by simp) σ
  rw [hu] at h
  have : (denom (u : GL (Fin 2) ℝ) σ ^ k - 1) * f σ = 0 := by linear_combination -h
  exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hk)

/- English proof (translation)
Use `⟨UpperHalfPlane.I, ModularGroup.S, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[modular_S_smul]`. Use `ext1`. Simplify using the standard rewrite rules. Rewrite using `[ModularGroup.denom_S]`.

Conclude with `Complex.isPrimitiveRoot_I`.
-/
lemma exists_four : ∃ (σ : ℍ) (u : SL(2, ℤ)), u • σ = σ ∧
    IsPrimitiveRoot (denom (u : GL (Fin 2) ℝ) σ) 4 := by
  refine ⟨UpperHalfPlane.I, ModularGroup.S, ?_, ?_⟩
  · rw [modular_S_smul]; ext1; simp
  · rw [ModularGroup.denom_S]; exact Complex.isPrimitiveRoot_I

/- English proof (translation)
Establish `hp` using `Complex.isPrimitiveRoot_exp 6 (by norm_num)`. Use `set μ := Complex.exp (2 * Real.pi * Complex.I / (6 : ℕ)) with hμ`. Establish `him : 0 < μ.im`. Establish `: μ = Complex.exp (((Real.pi / 3 : ℝ) : ℂ) * Complex.I)`. Rewrite using `[hμ]`.

Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, Complex.exp_ofReal_mul_I_im, Real.sin_pi_div_three]`. Check the signs of the components of the expression.

Establish `h6 : μ ^ 6 = 1` using `hp.pow_eq_one`. Establish `h3 : μ ^ 3 - 1 ≠ 0` using `sub_ne_zero.2 (hp.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num))`. Establish `h1 : μ + 1 ≠ 0` using `fun h => by`. Use `congrArg Complex.im h` as an intermediate fact. Simplify using `at this`.

Conclude with `him.ne' this`. Establish `hq : μ ^ 2 - μ + 1 = 0`. Establish `: (μ ^ 3 - 1) * ((μ + 1) * (μ ^ 2 - μ + 1)) = 0` using `by linear_combination h6`. Conclude with `(mul_eq_zero.1 ((mul_eq_zero.1 this).resolve_left h3)).resolve_left h1`. Establish `h0 : μ ≠ 0` using `hp.ne_zero (by norm_num)`.

Use `⟨⟨μ, him⟩, ModularGroup.T * ModularGroup.S, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_smul, modular_S_smul, modular_T_smul] ext1`. Simplify using `only [coe_vadd]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.

Take the linear combination `-hq`. Rewrite using `[denom_mul_SL, ModularGroup.denom_S]`. Establish `: ∀ z : ℍ, denom ((ModularGroup.T : SL(2, ℤ)) : GL (Fin 2) ℝ) z = 1` using `fun z => by`. Rewrite using `[ModularGroup.denom_apply]`. Simplify using `[ModularGroup.T]`.

Rewrite using `[this, one_mul]`. Conclude with `hp`.
-/
lemma exists_six : ∃ (σ : ℍ) (u : SL(2, ℤ)), u • σ = σ ∧
    IsPrimitiveRoot (denom (u : GL (Fin 2) ℝ) σ) 6 := by
  have hp := Complex.isPrimitiveRoot_exp 6 (by norm_num)
  set μ := Complex.exp (2 * Real.pi * Complex.I / (6 : ℕ)) with hμ
  have him : 0 < μ.im := by
    have : μ = Complex.exp (((Real.pi / 3 : ℝ) : ℂ) * Complex.I) := by
      rw [hμ]; congr 1; push_cast; ring
    rw [this, Complex.exp_ofReal_mul_I_im, Real.sin_pi_div_three]
    positivity
  have h6 : μ ^ 6 = 1 := hp.pow_eq_one
  have h3 : μ ^ 3 - 1 ≠ 0 := sub_ne_zero.2 (hp.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num))
  have h1 : μ + 1 ≠ 0 := fun h => by
    have := congrArg Complex.im h
    simp at this
    exact him.ne' this
  have hq : μ ^ 2 - μ + 1 = 0 := by
    have : (μ ^ 3 - 1) * ((μ + 1) * (μ ^ 2 - μ + 1)) = 0 := by linear_combination h6
    exact (mul_eq_zero.1 ((mul_eq_zero.1 this).resolve_left h3)).resolve_left h1
  have h0 : μ ≠ 0 := hp.ne_zero (by norm_num)
  refine ⟨⟨μ, him⟩, ModularGroup.T * ModularGroup.S, ?_, ?_⟩
  · rw [mul_smul, modular_S_smul, modular_T_smul]
    ext1
    simp only [coe_vadd]
    push_cast
    field_simp
    linear_combination -hq
  · rw [denom_mul_SL, ModularGroup.denom_S]
    have : ∀ z : ℍ, denom ((ModularGroup.T : SL(2, ℤ)) : GL (Fin 2) ℝ) z = 1 := fun z => by
      rw [ModularGroup.denom_apply]; simp [ModularGroup.T]
    rw [this, one_mul]
    exact hp

/- English proof (translation)
Introduce `τ₀`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Take `⟨σ, u, hu, hp⟩` from `exists_four`. Establish `h0 : E₆ σ = 0` using `eq_zero_of_fix E₆ u σ hu (by`.

Rewrite using `[Ne, hp.zpow_eq_one_iff_dvd]`. Use the proof step `norm_num)`. Take `⟨γ, rfl⟩` from `GlobalTheory.T.j_invariant_equal_sl2_orbit τ₀ σ (by rw [h, h0]; ring)`. Take `⟨h1, h2⟩` from `conj_fix γ u σ hu`. Conclude with `⟨_, h1, h2 ▸ hp⟩`.

Introduce `h`. Take `⟨σ, u, hu, hp⟩` from `exists_six`. Establish `h0 : E₄ σ = 0` using `eq_zero_of_fix E₄ u σ hu (by`. Rewrite using `[Ne, hp.zpow_eq_one_iff_dvd]`. Use the proof step `norm_num)`.

Take `⟨γ, rfl⟩` from `GlobalTheory.T.j_invariant_equal_sl2_orbit τ₀ σ (by rw [h, h0]; ring)`. Take `⟨h1, h2⟩` from `conj_fix γ u σ hu`. Conclude with `⟨_, h1, h2 ▸ hp⟩`.
-/
theorem elliptic_of_zero : ∀ τ₀ : ℍ,
    (E₆ τ₀ = 0 → ∃ u : SL(2, ℤ), u • τ₀ = τ₀ ∧ IsPrimitiveRoot (denom (u : GL (Fin 2) ℝ) τ₀) 4) ∧
    (E₄ τ₀ = 0 → ∃ u : SL(2, ℤ), u • τ₀ = τ₀ ∧
      IsPrimitiveRoot (denom (u : GL (Fin 2) ℝ) τ₀) 6) := by
  intro τ₀
  constructor
  · intro h
    obtain ⟨σ, u, hu, hp⟩ := exists_four
    have h0 : E₆ σ = 0 := eq_zero_of_fix E₆ u σ hu (by
      rw [Ne, hp.zpow_eq_one_iff_dvd]; norm_num)
    obtain ⟨γ, rfl⟩ := GlobalTheory.T.j_invariant_equal_sl2_orbit τ₀ σ (by rw [h, h0]; ring)
    obtain ⟨h1, h2⟩ := conj_fix γ u σ hu
    exact ⟨_, h1, h2 ▸ hp⟩
  · intro h
    obtain ⟨σ, u, hu, hp⟩ := exists_six
    have h0 : E₄ σ = 0 := eq_zero_of_fix E₄ u σ hu (by
      rw [Ne, hp.zpow_eq_one_iff_dvd]; norm_num)
    obtain ⟨γ, rfl⟩ := GlobalTheory.T.j_invariant_equal_sl2_orbit τ₀ σ (by rw [h, h0]; ring)
    obtain ⟨h1, h2⟩ := conj_fix γ u σ hu
    exact ⟨_, h1, h2 ▸ hp⟩

end GlobalTheory.EllipticZero
