import Mathlib
open Matrix

namespace GlobalTheory.CompanionTheory.UnitFrame

/- English proof (translation)
Take `⟨w, hw, hv⟩ : ∃ w, (fr⁻¹).1 *ᵥ v = w ∧ v = fr.1 *ᵥ w` from `⟨_, rfl, by rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]⟩`. Rewrite using `[hw]`. Substitute `hv` using the available equality. Establish `hc : ((s : ℤ) : ℂ) * ((s : ℤ) : ℂ) = 1`. Rewrite using `[← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]`.

Establish `hB : star ζ • (fr.1ᵀ * J * fr.1.map star).map star = ((s : ℤ) : ℂ) • (1 : Matrix (Fin m) (Fin m) ℂ)`. Use extensionality with `i j`. Establish `h1` using `congrArg star (congrFun (congrFun h i) j)`. Simplify using `only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, star_mul'] at h1 ⊢`. Rewrite using `[h1]`.

Apply the tactic sequence `by_cases hij : i = j <;> simp [Matrix.one_apply, hij]`. Establish `hX : (fr.1ᵀ * J * fr.1.map star).map star = fr.1ᴴ * J.map star * fr.1`. Use extensionality with `i j`. Simplify using `only [Matrix.map_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.transpose_apply, star_sum, star_mul', star_star]`. Rewrite using `[star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, ← hX, mul_assoc, ← smul_eq_mul (star ζ), ← dotProduct_smul, ← smul_mulVec, hB, smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul, ← mul_assoc, hc, one_mul]`.

Simplify using `only [dotProduct, Pi.star_apply, Complex.ofReal_sum, Complex.ofReal_pow]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Complex.star_def, Complex.conj_mul']`.
-/
theorem normSq_eq_scalar_mul_form {m : ℕ} (J : Matrix (Fin m) (Fin m) ℂ) (fr : GL (Fin m) ℂ)
    (ζ : ℂ) (s : ℤˣ)
    (h : ζ • (fr.1ᵀ * J * fr.1.map star) = ((s : ℤ) : ℂ) • 1) (v : Fin m → ℂ) :
    ((∑ a, ‖((fr⁻¹).1 *ᵥ v) a‖ ^ 2 : ℝ) : ℂ) =
      (((s : ℤ) : ℂ) * star ζ) * (star v ⬝ᵥ (J.map star *ᵥ v)) := by
  obtain ⟨w, hw, hv⟩ : ∃ w, (fr⁻¹).1 *ᵥ v = w ∧ v = fr.1 *ᵥ w :=
    ⟨_, rfl, by rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]⟩
  rw [hw]
  subst hv
  have hc : ((s : ℤ) : ℂ) * ((s : ℤ) : ℂ) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  have hB : star ζ • (fr.1ᵀ * J * fr.1.map star).map star =
      ((s : ℤ) : ℂ) • (1 : Matrix (Fin m) (Fin m) ℂ) := by
    ext i j
    have h1 := congrArg star (congrFun (congrFun h i) j)
    simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, star_mul'] at h1 ⊢
    rw [h1]
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  have hX : (fr.1ᵀ * J * fr.1.map star).map star = fr.1ᴴ * J.map star * fr.1 := by
    ext i j
    simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.transpose_apply,
      star_sum, star_mul', star_star]
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, ← hX, mul_assoc,
    ← smul_eq_mul (star ζ), ← dotProduct_smul, ← smul_mulVec, hB, smul_mulVec, one_mulVec, dotProduct_smul,
    smul_eq_mul, ← mul_assoc, hc, one_mul]
  simp only [dotProduct, Pi.star_apply, Complex.ofReal_sum, Complex.ofReal_pow]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Complex.star_def, Complex.conj_mul']

/- English proof (translation)
Establish `hne : (fr⁻¹).1 *ᵥ (Pi.single (⟨0, hm⟩ : Fin m) (1 : ℂ)) ≠ 0`. Introduce `h0`. Establish `h1` using `congrArg (fun u => fr.1 *ᵥ u) h0`. Simplify using `only [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec, mulVec_zero] at h1`. Conclude with `one_ne_zero (Pi.single_eq_zero_iff.mp h1)`.

Take `⟨a, ha⟩` from `Function.ne_iff.mp hne`. Conclude with `Finset.sum_pos' (fun i _ => by positivity) ⟨a, Finset.mem_univ _, pow_pos (norm_pos_iff.mpr ha) 2⟩`.
-/
theorem normSq_pos {m : ℕ} (hm : 1 ≤ m) (fr : GL (Fin m) ℂ) :
    0 < ∑ a, ‖((fr⁻¹).1 *ᵥ (Pi.single (⟨0, hm⟩ : Fin m) (1 : ℂ))) a‖ ^ 2 := by
  have hne : (fr⁻¹).1 *ᵥ (Pi.single (⟨0, hm⟩ : Fin m) (1 : ℂ)) ≠ 0 := by
    intro h0
    have h1 := congrArg (fun u => fr.1 *ᵥ u) h0
    simp only [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec,
      mulVec_zero] at h1
    exact one_ne_zero (Pi.single_eq_zero_iff.mp h1)
  obtain ⟨a, ha⟩ := Function.ne_iff.mp hne
  exact Finset.sum_pos' (fun i _ => by positivity)
    ⟨a, Finset.mem_univ _, pow_pos (norm_pos_iff.mpr ha) 2⟩

/- English proof (translation)
Introduce `m hm J fr fr' ζ ζ' s s' hζ hζ' h h' v`. Establish `key` using `normSq_eq_scalar_mul_form J fr ζ s h`. Establish `key'` using `normSq_eq_scalar_mul_form J fr' ζ' s' h'`. Establish `hα : ((s : ℤ) : ℂ) * star ζ = ((s' : ℤ) : ℂ) * star ζ'`. Establish `k0` using `key (Pi.single (⟨0, hm⟩ : Fin m) (1 : ℂ))`.

Establish `k0'` using `key' (Pi.single (⟨0, hm⟩ : Fin m) (1 : ℂ))`. Establish `hr` using `normSq_pos hm fr`. Establish `hr'` using `normSq_pos hm fr'`. Generalize the expression as in `(∑ a, ‖((fr⁻¹).1 *ᵥ (Pi.single (⟨0, hm⟩ : Fin m) (1 : ℂ))) a‖ ^ 2) = r at k0 hr`. Generalize the expression as in `(∑ a, ‖((fr'⁻¹).1 *ᵥ (Pi.single (⟨0, hm⟩ : Fin m) (1 : ℂ))) a‖ ^ 2) = r' at k0' hr'`.

Generalize the expression as in `(star (Pi.single (⟨0, hm⟩ : Fin m) (1 : ℂ)) ⬝ᵥ (J.map star *ᵥ (Pi.single (⟨0, hm⟩ : Fin m) (1 : ℂ)))) = Q at k0 k0'`. Apply the tactic sequence `rcases hζ with rfl | rfl <;> rcases hζ' with rfl | rfl <;>`. Apply the tactic sequence `rcases Int.units_eq_one_or s with rfl | rfl <;>`. Apply the tactic sequence `rcases Int.units_eq_one_or s' with rfl | rfl <;>`. Apply the tactic sequence `simp [Complex.ext_iff] at k0 k0' ⊢ <;> linarith`.

Apply `Complex.ofReal_injective` to reduce the goal to its premises. Rewrite using `[key v, key' v, hα]`.
-/
theorem normSq_eq_of_unit_frames : ∀ (m : ℕ), 1 ≤ m → ∀ (J : Matrix (Fin m) (Fin m) ℂ) (fr fr' : GL (Fin m) ℂ) (ζ ζ' : ℂ) (s s' : ℤˣ), (ζ = 1 ∨ ζ = Complex.I) → (ζ' = 1 ∨ ζ' = Complex.I) → ζ • (fr.1ᵀ * J * fr.1.map star) = ((s : ℤ) : ℂ) • 1 → ζ' • (fr'.1ᵀ * J * fr'.1.map star) = ((s' : ℤ) : ℂ) • 1 → ∀ v : Fin m → ℂ, ∑ a, ‖((fr⁻¹).1 *ᵥ v) a‖ ^ 2 = ∑ a, ‖((fr'⁻¹).1 *ᵥ v) a‖ ^ 2 := by
  intro m hm J fr fr' ζ ζ' s s' hζ hζ' h h' v
  have key := normSq_eq_scalar_mul_form J fr ζ s h
  have key' := normSq_eq_scalar_mul_form J fr' ζ' s' h'
  have hα : ((s : ℤ) : ℂ) * star ζ = ((s' : ℤ) : ℂ) * star ζ' := by
    have k0 := key (Pi.single (⟨0, hm⟩ : Fin m) (1 : ℂ))
    have k0' := key' (Pi.single (⟨0, hm⟩ : Fin m) (1 : ℂ))
    have hr := normSq_pos hm fr
    have hr' := normSq_pos hm fr'
    generalize (∑ a, ‖((fr⁻¹).1 *ᵥ (Pi.single (⟨0, hm⟩ : Fin m) (1 : ℂ))) a‖ ^ 2) = r at k0 hr
    generalize (∑ a, ‖((fr'⁻¹).1 *ᵥ (Pi.single (⟨0, hm⟩ : Fin m) (1 : ℂ))) a‖ ^ 2) = r' at k0' hr'
    generalize (star (Pi.single (⟨0, hm⟩ : Fin m) (1 : ℂ)) ⬝ᵥ
      (J.map star *ᵥ (Pi.single (⟨0, hm⟩ : Fin m) (1 : ℂ)))) = Q at k0 k0'
    rcases hζ with rfl | rfl <;> rcases hζ' with rfl | rfl <;>
      rcases Int.units_eq_one_or s with rfl | rfl <;>
      rcases Int.units_eq_one_or s' with rfl | rfl <;>
      simp [Complex.ext_iff] at k0 k0' ⊢ <;> linarith
  apply Complex.ofReal_injective
  rw [key v, key' v, hα]

end GlobalTheory.CompanionTheory.UnitFrame
