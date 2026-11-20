import Mathlib
import ReciprocityTheory.EigenFrames.EigenSt

noncomputable section
open scoped BigOperators
open NumberField

namespace ReciprocityTheory.EigenFramesTheory

/- English proof (translation)
Assume the negation of the conclusion as `hy`. Rewrite `hy` using `[not_le]`. Use `set n := f.natDegree`. Establish `hn : n ≠ 0`. Introduce `h0`.

Establish `hf1 : f = 1` using `Polynomial.eq_one_of_monic_natDegree_zero hf h0`. Rewrite `h` using `[hf1, Polynomial.eval₂_one]`. Conclude with `one_ne_zero h`. Rewrite `h` using `[Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hf.coeff_natDegree, map_one, one_mul]`. Use `set S := ∑ i ∈ Finset.range n, Int.castRingHom ℂ_[p] (f.coeff i) * y ^ i`.

Establish `hS : ‖S‖ ≤ ‖y‖ ^ (n - 1)`. Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun i hi => ?_` and prove the remaining obligations. Rewrite using `[norm_mul, norm_pow]`. Establish `hi' : i ≤ n - 1` using `by have := Finset.mem_range.1 hi; omega`. Use `(mul_le_of_le_one_left (by positivity) ?_).trans (pow_le_pow_right₀ hy.le hi')` and prove the remaining obligations.

Rewrite using `[eq_intCast]`. Conclude with `IsUltrametricDist.norm_intCast_le_one _ _`. Establish `hyn : y ^ n = -S` using `by rw [eq_neg_iff_add_eq_zero, add_comm]; exact h`. Establish `h2 : ‖y‖ ^ n ≤ ‖y‖ ^ (n - 1)` using `by rw [← norm_pow, hyn, norm_neg]; exact hS`. Establish `h3 : ‖y‖ ^ (n - 1) < ‖y‖ ^ n` using `pow_lt_pow_right₀ hy (by omega)`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem norm_le_one_of_monic {p : ℕ} [Fact p.Prime] {f : Polynomial ℤ} (hf : f.Monic) {y : ℂ_[p]}
    (h : Polynomial.eval₂ (Int.castRingHom ℂ_[p]) y f = 0) : ‖y‖ ≤ 1 := by
  by_contra hy
  rw [not_le] at hy
  set n := f.natDegree
  have hn : n ≠ 0 := by
    intro h0
    have hf1 : f = 1 := Polynomial.eq_one_of_monic_natDegree_zero hf h0
    rw [hf1, Polynomial.eval₂_one] at h
    exact one_ne_zero h
  rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hf.coeff_natDegree, map_one, one_mul] at h
  set S := ∑ i ∈ Finset.range n, Int.castRingHom ℂ_[p] (f.coeff i) * y ^ i
  have hS : ‖S‖ ≤ ‖y‖ ^ (n - 1) := by
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun i hi => ?_
    rw [norm_mul, norm_pow]
    have hi' : i ≤ n - 1 := by have := Finset.mem_range.1 hi; omega
    refine (mul_le_of_le_one_left (by positivity) ?_).trans (pow_le_pow_right₀ hy.le hi')
    rw [eq_intCast]
    exact IsUltrametricDist.norm_intCast_le_one _ _
  have hyn : y ^ n = -S := by rw [eq_neg_iff_add_eq_zero, add_comm]; exact h
  have h2 : ‖y‖ ^ n ≤ ‖y‖ ^ (n - 1) := by rw [← norm_pow, hyn, norm_neg]; exact hS
  have h3 : ‖y‖ ^ (n - 1) < ‖y‖ ^ n := pow_lt_pow_right₀ hy (by omega)
  linarith

/- English proof (translation)
Rewrite using `[Matrix.det_apply']`. Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[norm_mul, norm_prod]`. Conclude with `mul_le_one₀ (IsUltrametricDist.norm_intCast_le_one _ _) (Finset.prod_nonneg fun _ _ => norm_nonneg _) (Finset.prod_le_one (fun _ _ => norm_nonneg _) fun _ _ => hM _ _)`.
-/
theorem eig_norm_det_le_one {p : ℕ} [Fact p.Prime] {κ : Type*} [Fintype κ] [DecidableEq κ]
    (M : Matrix κ κ ℂ_[p]) (hM : ∀ i j, ‖M i j‖ ≤ 1) : ‖M.det‖ ≤ 1 := by
  rw [Matrix.det_apply']
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun σ _ => ?_
  rw [norm_mul, norm_prod]
  exact mul_le_one₀ (IsUltrametricDist.norm_intCast_le_one _ _)
    (Finset.prod_nonneg fun _ _ => norm_nonneg _) (Finset.prod_le_one (fun _ _ => norm_nonneg _) fun _ _ => hM _ _)

/- English proof (translation)
Rewrite using `[← map_intCast (algebraMap ℚ_[p] ℂ_[p]) z, norm_algebraMap']`. Conclude with `le_antisymm (Padic.norm_int_le_one z) (not_lt.mp fun h' => h (Padic.norm_intCast_lt_one_iff.mp h'))`.
-/
theorem eig_norm_intCast {p : ℕ} [Fact p.Prime] {z : ℤ} (h : ¬ (p : ℤ) ∣ z) : ‖(z : ℂ_[p])‖ = 1 := by
  rw [← map_intCast (algebraMap ℚ_[p] ℂ_[p]) z, norm_algebraMap']
  exact le_antisymm (Padic.norm_int_le_one z) (not_lt.mp fun h' => h (Padic.norm_intCast_lt_one_iff.mp h'))

universe u v

/- English proof (translation)
Introduce `p _ E _ _ κ _ b ι hd τ₀`. Set `bQ : Module.Basis κ ℚ E` to `b.localizationLocalization ℚ (nonZeroDivisors ℤ) E`. Establish `hbQ : ∀ i, bQ i = ((b i : 𝓞 E) : E)` using `fun i => Module.Basis.localizationLocalization_apply ℚ (nonZeroDivisors ℤ) E b i`. Establish `hcard : Fintype.card κ = Fintype.card (E →ₐ[ℚ] ℂ)`. Rewrite using `[AlgHom.card, Module.finrank_eq_card_basis bQ]`.

Set `e : κ ≃ (E →ₐ[ℚ] ℂ)` to `Fintype.equivOfCardEq hcard`. Set `N : Matrix κ κ ℂ` to `Algebra.embeddingsMatrixReindex ℚ ℂ bQ e`. Establish `hN : N.det ^ 2 = ((NumberField.discr E : ℤ) : ℂ)`. Rewrite using `[← Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ ℂ bQ e, Algebra.discr_localizationLocalization ℤ (nonZeroDivisors ℤ) E b, NumberField.discr_eq_discr E b]`. Simplify using the standard rewrite rules.

Set `M : Matrix κ κ ℂ_[p]` to `(ι : ℂ →+* ℂ_[p]).mapMatrix N`. Establish `hMa : ∀ i j, M i j = ι (e j ((b i : 𝓞 E) : E))`. Introduce `i j`. Rewrite using `[← hbQ]`. Both sides reduce to the same expression.

Establish `hM2 : M.det ^ 2 = ((NumberField.discr E : ℤ) : ℂ_[p])`. Rewrite using `[← RingHom.map_det, ← map_pow, hN, map_intCast]`. Establish `hM1 : ‖M.det‖ = 1`. Establish `h` using `congrArg norm hM2`. Rewrite `h` using `[norm_pow, eig_norm_intCast hd]`.

Conclude with `(pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h`. Establish `hM0 : M.det ≠ 0`. Introduce `h0`. Rewrite `hM1` using `[h0, norm_zero]`. Conclude with `zero_ne_one hM1`.

Establish `hint : ∀ i j, ‖M i j‖ ≤ 1`. Introduce `i j`. Take `⟨f, hmon, hf⟩` from `(NumberField.RingOfIntegers.isIntegral_coe (b i) : IsIntegral ℤ ((b i : 𝓞 E) : E))`. Use `norm_le_one_of_monic hmon ?_` and prove the remaining obligations. Set `g : E →+* ℂ_[p]` to `(ι : ℂ →+* ℂ_[p]).comp (e j : E →+* ℂ)`.

Establish `h` using `congrArg g hf`. Rewrite `h` using `[map_zero, Polynomial.hom_eval₂]`. Rewrite `h` using `[RingHom.ext_int (g.comp (algebraMap ℤ E)) (Int.castRingHom ℂ_[p])]`. Rewrite using `[hMa]`. Conclude with `h`.

Set `j₀ : κ` to `e.symm τ₀.toRatAlgHom`. Use `⟨fun i => (M.det)⁻¹ * M.adjugate j₀ i, fun i => ?_, fun φ => ?_⟩` and prove the remaining obligations. Rewrite using `[norm_mul, norm_inv, hM1, inv_one, one_mul, Matrix.adjugate_apply]`. Use `eig_norm_det_le_one _ fun a c => ?_` and prove the remaining obligations. Rewrite using `[Matrix.updateRow_apply]`.

Use `split_ifs`. Apply the tactic sequence `rw [Pi.single_apply] split_ifs <;> simp`. Conclude with `hint a c`. Set `j : κ` to `e.symm φ.toRatAlgHom`. Establish `hφ : ∀ i, ι (φ ((b i : 𝓞 E) : E)) = M i j`.

Introduce `i`. Rewrite using `[hMa, Equiv.apply_symm_apply]`. Both sides reduce to the same expression. Establish `h1 : ∑ i, M.adjugate j₀ i * M i j = M.det * (if j₀ = j then 1 else 0)`. Establish `h` using `congrFun (congrFun (Matrix.adjugate_mul M) j₀) j`.

Rewrite `h` using `[Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]`. Conclude with `h`. Simplify using `only [hφ, mul_assoc]`. Rewrite using `[← Finset.mul_sum, h1, ← mul_assoc, inv_mul_cancel₀ hM0, one_mul]`. Distinguish the cases in `hc : φ = τ₀`.

Substitute `hc` using the available equality. Simplify using `[j, j₀]`. Rewrite using `[if_neg hc, if_neg]`. Introduce `hj`. Apply `hc` to reduce the goal to its premises.

Establish `h2 : τ₀.toRatAlgHom = φ.toRatAlgHom` using `e.symm.injective hj`. Use extensionality with `x`. Conclude with `(DFunLike.congr_fun h2 x).symm`.
-/
theorem eigenFrameDual : EigenFrameDual.{u, v} := by
  intro p _ E _ _ κ _ b ι hd τ₀
  classical
  let bQ : Module.Basis κ ℚ E := b.localizationLocalization ℚ (nonZeroDivisors ℤ) E
  have hbQ : ∀ i, bQ i = ((b i : 𝓞 E) : E) := fun i =>
    Module.Basis.localizationLocalization_apply ℚ (nonZeroDivisors ℤ) E b i
  have hcard : Fintype.card κ = Fintype.card (E →ₐ[ℚ] ℂ) := by
    rw [AlgHom.card, Module.finrank_eq_card_basis bQ]
  let e : κ ≃ (E →ₐ[ℚ] ℂ) := Fintype.equivOfCardEq hcard
  let N : Matrix κ κ ℂ := Algebra.embeddingsMatrixReindex ℚ ℂ bQ e
  have hN : N.det ^ 2 = ((NumberField.discr E : ℤ) : ℂ) := by
    rw [← Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ ℂ bQ e,
      Algebra.discr_localizationLocalization ℤ (nonZeroDivisors ℤ) E b, NumberField.discr_eq_discr E b]
    simp
  let M : Matrix κ κ ℂ_[p] := (ι : ℂ →+* ℂ_[p]).mapMatrix N
  have hMa : ∀ i j, M i j = ι (e j ((b i : 𝓞 E) : E)) := by
    intro i j
    rw [← hbQ]
    rfl
  have hM2 : M.det ^ 2 = ((NumberField.discr E : ℤ) : ℂ_[p]) := by
    rw [← RingHom.map_det, ← map_pow, hN, map_intCast]
  have hM1 : ‖M.det‖ = 1 := by
    have h := congrArg norm hM2
    rw [norm_pow, eig_norm_intCast hd] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h
  have hM0 : M.det ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hM1
    exact zero_ne_one hM1
  have hint : ∀ i j, ‖M i j‖ ≤ 1 := by
    intro i j
    obtain ⟨f, hmon, hf⟩ := (NumberField.RingOfIntegers.isIntegral_coe (b i) : IsIntegral ℤ ((b i : 𝓞 E) : E))
    refine norm_le_one_of_monic hmon ?_
    let g : E →+* ℂ_[p] := (ι : ℂ →+* ℂ_[p]).comp (e j : E →+* ℂ)
    have h := congrArg g hf
    rw [map_zero, Polynomial.hom_eval₂] at h
    rw [RingHom.ext_int (g.comp (algebraMap ℤ E)) (Int.castRingHom ℂ_[p])] at h
    rw [hMa]
    exact h
  let j₀ : κ := e.symm τ₀.toRatAlgHom
  refine ⟨fun i => (M.det)⁻¹ * M.adjugate j₀ i, fun i => ?_, fun φ => ?_⟩
  · rw [norm_mul, norm_inv, hM1, inv_one, one_mul, Matrix.adjugate_apply]
    refine eig_norm_det_le_one _ fun a c => ?_
    rw [Matrix.updateRow_apply]
    split_ifs
    · rw [Pi.single_apply]
      split_ifs <;> simp
    · exact hint a c
  · let j : κ := e.symm φ.toRatAlgHom
    have hφ : ∀ i, ι (φ ((b i : 𝓞 E) : E)) = M i j := by
      intro i
      rw [hMa, Equiv.apply_symm_apply]
      rfl
    have h1 : ∑ i, M.adjugate j₀ i * M i j = M.det * (if j₀ = j then 1 else 0) := by
      have h := congrFun (congrFun (Matrix.adjugate_mul M) j₀) j
      rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] at h
      exact h
    simp only [hφ, mul_assoc]
    rw [← Finset.mul_sum, h1, ← mul_assoc, inv_mul_cancel₀ hM0, one_mul]
    by_cases hc : φ = τ₀
    · subst hc
      simp [j, j₀]
    · rw [if_neg hc, if_neg]
      intro hj
      apply hc
      have h2 : τ₀.toRatAlgHom = φ.toRatAlgHom := e.symm.injective hj
      ext x
      exact (DFunLike.congr_fun h2 x).symm

end ReciprocityTheory.EigenFramesTheory
