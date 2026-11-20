import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsUnitaryMulTriangular
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DualWeylEqEvalAtOneSmulExtremalOfRowWeight

open GlobalTheory.DualWeyl MvPolynomial NumberField MeasureTheory
open scoped Matrix ComplexConjugate InnerProductSpace

namespace GlobalTheory.DualWeyl.Repro

variable {N : ℕ} {la : Fin N → ℕ}

/- English proof (translation)
Establish `: CompleteSpace (Space la)` using `FiniteDimensional.complete ℂ _`. Use `⟨(toSpace la).symm ((InnerProductSpace.toDual ℂ (Space la)).symm (LinearMap.toContinuousLinearMap (evSpace la 1))), fun f => ?_⟩` and prove the remaining obligations. Rewrite using `[← inner_toSpace, LinearEquiv.apply_symm_apply, InnerProductSpace.toDual_symm_apply]`. Both sides reduce to the same expression.
-/
theorem exists_repr (la : Fin N → ℕ) :
    ∃ k : nabla la ℂ, ∀ f : nabla la ℂ, form la f.1 k.1 = evalAt 1 f.1 := by
  have : CompleteSpace (Space la) := FiniteDimensional.complete ℂ _
  refine ⟨(toSpace la).symm ((InnerProductSpace.toDual ℂ (Space la)).symm
    (LinearMap.toContinuousLinearMap (evSpace la 1))), fun f => ?_⟩
  rw [← inner_toSpace, LinearEquiv.apply_symm_apply, InnerProductSpace.toDual_symm_apply]
  rfl

/- English proof (translation)
Rewrite using `[← form_rhoU u, Representation.self_inv_apply, hk, rhoU_apply, evalAt_rho, Matrix.mul_one]`.
-/
theorem form_rhoU_repr {k : nabla la ℂ} (hk : ∀ f : nabla la ℂ, form la f.1 k.1 = evalAt 1 f.1)
    (u : UN N) (f : nabla la ℂ) :
    form la f.1 (rhoU la u⁻¹ k : Pol N ℂ) = evalAt u.1ᵀ f.1 := by
  rw [← form_rhoU u, Representation.self_inv_apply, hk, rhoU_apply, evalAt_rho, Matrix.mul_one]

/- English proof (translation)
Set `e : Idx la → nabla la ℂ` to `fun i => (toSpace la).symm (onBasis la i)`. Establish `he : ∀ i, toSpace la (e i) = onBasis la i` using `fun i => (toSpace la).apply_symm_apply _`. Establish `h1 : ∀ g : UN N, ∑ i, ‖evalAt g.1 (e i).1‖ ^ 2 = normSq la k.1`. Introduce `g`. Set `u : UN N` to `⟨g.1ᵀ, transpose_mem_unitaryGroup g.2⟩`.

Rewrite using `[← normSq_rhoU u⁻¹, ← norm_toSpace_sq, ← (onBasis la).sum_sq_norm_inner_left]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← he, inner_toSpace, form_rhoU_repr hk]`. Both sides reduce to the same expression. Establish `h2 : ∑ i, normSq la (e i).1 = dim la`.

Simplify using `only [← norm_toSpace_sq, he, (onBasis la).orthonormal.1]`. Simplify using `[dim_eq_card]`. Establish `h3 : ∑ i, normSq la (e i).1 = dim la * normSq la k.1` using `by conv_lhs => simp only [normSq]`. Rewrite using `[← Finset.mul_sum, ← integral_finsetSum _ fun i _ => integrable_norm_sq _]`. Simplify using `only [h1]`.

Simplify using the standard rewrite rules. Establish `hd : (dim la : ℝ) ≠ 0` using `by exact_mod_cast (dim_pos hla).ne'`. Conclude with `mul_left_cancel₀ hd (by rw [← h3, h2, mul_one])`.
-/
theorem normSq_repr (hla : Antitone la) {k : nabla la ℂ}
    (hk : ∀ f : nabla la ℂ, form la f.1 k.1 = evalAt 1 f.1) : normSq la k.1 = 1 := by
  let e : Idx la → nabla la ℂ := fun i => (toSpace la).symm (onBasis la i)
  have he : ∀ i, toSpace la (e i) = onBasis la i := fun i => (toSpace la).apply_symm_apply _
  have h1 : ∀ g : UN N, ∑ i, ‖evalAt g.1 (e i).1‖ ^ 2 = normSq la k.1 := by
    intro g
    let u : UN N := ⟨g.1ᵀ, transpose_mem_unitaryGroup g.2⟩
    rw [← normSq_rhoU u⁻¹, ← norm_toSpace_sq, ← (onBasis la).sum_sq_norm_inner_left]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← he, inner_toSpace, form_rhoU_repr hk]
    rfl
  have h2 : ∑ i, normSq la (e i).1 = dim la := by
    simp only [← norm_toSpace_sq, he, (onBasis la).orthonormal.1]
    simp [dim_eq_card]
  have h3 : ∑ i, normSq la (e i).1 = dim la * normSq la k.1 := by
    conv_lhs => simp only [normSq]
    rw [← Finset.mul_sum, ← integral_finsetSum _ fun i _ => integrable_norm_sq _]
    simp only [h1]
    simp
  have hd : (dim la : ℝ) ≠ 0 := by exact_mod_cast (dim_pos hla).ne'
  exact mul_left_cancel₀ hd (by rw [← h3, h2, mul_one])

/- English proof (translation)
Establish `hu : Matrix.diagonal t ∈ Matrix.unitaryGroup (Fin N) ℂ`. Rewrite using `[Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `a`. Simplify using `[Complex.mul_conj', ht]`.

Set `u : UN N` to `⟨_, hu⟩`. Establish `hinv : (u⁻¹).1ᵀ = Matrix.diagonal (star t)`. Express the relevant statement in the definitionally equal form `(star (Matrix.diagonal t))ᵀ = _`. Rewrite using `[Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.diagonal_transpose]`. Establish `h : rhoU la u k = (∏ a, t a ^ la a) • k`.

Apply `(toSpace la).injective` to reduce the goal to its premises. Use `ext_inner_right ℂ fun v => ?_` and prove the remaining obligations. Take `⟨f, rfl⟩` from `(toSpace la).surjective v`. Rewrite using `[inner_toSpace, inner_toSpace, ← inv_inv u, form_rhoU_repr hk, hinv, Submodule.coe_smul, form_smul_right, hk, ← Matrix.one_mul (Matrix.diagonal (star t)), ← evalAt_colAct, colAct_of_mem f.2 _ (Matrix.blockTriangular_diagonal _), map_smul]`. Simplify using `[diagChar]`.

Establish `h'` using `congrArg Subtype.val h`. Rewrite `h'` using `[rhoU_apply, coe_rho, Matrix.diagonal_transpose]`. Then use the resulting hypothesis.
-/
theorem rowAct_diagonal_repr {k : nabla la ℂ}
    (hk : ∀ f : nabla la ℂ, form la f.1 k.1 = evalAt 1 f.1) (t : Fin N → ℂ) (ht : ∀ a, ‖t a‖ = 1) :
    Formalism.GradedWeylDivisibility.rowAct ℂ (Matrix.diagonal t) k.1 = (∏ a, t a ^ la a) • k.1 := by
  have hu : Matrix.diagonal t ∈ Matrix.unitaryGroup (Fin N) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    simp [Complex.mul_conj', ht]
  let u : UN N := ⟨_, hu⟩
  have hinv : (u⁻¹).1ᵀ = Matrix.diagonal (star t) := by
    change (star (Matrix.diagonal t))ᵀ = _
    rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.diagonal_transpose]
  have h : rhoU la u k = (∏ a, t a ^ la a) • k := by
    apply (toSpace la).injective
    refine ext_inner_right ℂ fun v => ?_
    obtain ⟨f, rfl⟩ := (toSpace la).surjective v
    rw [inner_toSpace, inner_toSpace, ← inv_inv u, form_rhoU_repr hk, hinv, Submodule.coe_smul, form_smul_right,
      hk, ← Matrix.one_mul (Matrix.diagonal (star t)), ← evalAt_colAct,
      colAct_of_mem f.2 _ (Matrix.blockTriangular_diagonal _), map_smul]
    simp [diagChar]
  have h' := congrArg Subtype.val h
  rwa [rhoU_apply, coe_rho, Matrix.diagonal_transpose] at h'

/- English proof (translation)
Introduce `m hm`. Use function extensionality and compare the values at `a`. Rewrite using `[Formalism.GradedWeylDivisibility.ldrow_weight_rowW]`. Establish `hn : Formalism.GradedWeylDivisibility.rowDeg m a + la a + 1 ≠ 0` using `by omega`. Establish `hz` using `Complex.isPrimitiveRoot_exp _ hn`.

Establish `hz1` using `hz.norm'_eq_one hn`. Generalize the expression as in `Complex.exp _ = z at hz hz1`. Establish `h1` using `congrArg (coeff m) (h (Function.update 1 a z) fun b => by`. Distinguish the cases in `hb : b = a`. Substitute `hb` using the available equality.

Simplify using `using hz1`. Simplify using `[Function.update_of_ne hb])`. Rewrite `h1` using `[Formalism.GradedWeylDivisibility.ldrow_coeff_rowAct_diag, coeff_smul, smul_eq_mul, mul_comm]`. Establish `h2` using `mul_right_cancel₀ hm h1`. Establish `h3 : ∀ d : Fin N → ℕ, ∏ b, Function.update (1 : Fin N → ℂ) a z b ^ d b = z ^ d a`.

Introduce `d`. Rewrite using `[Finset.prod_eq_single a]`. Simplify using the standard rewrite rules. Introduce `b _ hb`. Simplify using `[Function.update_of_ne hb]`.

Simplify using the standard rewrite rules. Rewrite `h2` using `[h3, h3]`. Conclude with `hz.pow_inj (by omega) (by omega) h2`.
-/
theorem isWeightedHomogeneous_of_torus {f : Pol N ℂ}
    (h : ∀ t : Fin N → ℂ, (∀ a, ‖t a‖ = 1) →
      Formalism.GradedWeylDivisibility.rowAct ℂ (Matrix.diagonal t) f = (∏ a, t a ^ la a) • f) :
    IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.rowW N N) f la := by
  classical
  intro m hm
  funext a
  rw [Formalism.GradedWeylDivisibility.ldrow_weight_rowW]
  have hn : Formalism.GradedWeylDivisibility.rowDeg m a + la a + 1 ≠ 0 := by omega
  have hz := Complex.isPrimitiveRoot_exp _ hn
  have hz1 := hz.norm'_eq_one hn
  generalize Complex.exp _ = z at hz hz1
  have h1 := congrArg (coeff m) (h (Function.update 1 a z) fun b => by
    by_cases hb : b = a
    · subst hb; simpa using hz1
    · simp [Function.update_of_ne hb])
  rw [Formalism.GradedWeylDivisibility.ldrow_coeff_rowAct_diag, coeff_smul, smul_eq_mul, mul_comm] at h1
  have h2 := mul_right_cancel₀ hm h1
  have h3 : ∀ d : Fin N → ℕ, ∏ b, Function.update (1 : Fin N → ℂ) a z b ^ d b = z ^ d a := by
    intro d
    rw [Finset.prod_eq_single a]
    · simp
    · intro b _ hb
      simp [Function.update_of_ne hb]
    · simp
  rw [h3, h3] at h2
  exact hz.pow_inj (by omega) (by omega) h2

/- English proof (translation)
Introduce `N la hla`. Take `⟨k, hk⟩` from `exists_repr la`. Establish `h1` using `normSq_repr hla hk`. Establish `h2 : evalAt 1 k.1 = 1` using `by rw [← hk, form_self, h1, Complex.ofReal_one]`. Establish `h3` using `GlobalTheory.DualWeyl.eq_evalAt_one_smul_extremal_of_rowWeight ℂ N la hla k.1 k.2 (isWeightedHomogeneous_of_torus (rowAct_diagonal_repr hk))`.

Rewrite `h3` using `[h2, one_smul]`. Rewrite using `[← h3]`. Conclude with `⟨fun f hf => hk ⟨f, hf⟩, h1⟩`.
-/
theorem extremal_reproducing : ∀ (N : ℕ) (la : Fin N → ℕ), Antitone la →
    (∀ f ∈ nabla la ℂ, form la f (extremal la ℂ) = evalAt 1 f) ∧ normSq la (extremal la ℂ) = 1 := by
  intro N la hla
  obtain ⟨k, hk⟩ := exists_repr la
  have h1 := normSq_repr hla hk
  have h2 : evalAt 1 k.1 = 1 := by rw [← hk, form_self, h1, Complex.ofReal_one]
  have h3 := GlobalTheory.DualWeyl.eq_evalAt_one_smul_extremal_of_rowWeight ℂ N la hla k.1 k.2 (isWeightedHomogeneous_of_torus (rowAct_diagonal_repr hk))
  rw [h2, one_smul] at h3
  rw [← h3]
  exact ⟨fun f hf => hk ⟨f, hf⟩, h1⟩

end GlobalTheory.DualWeyl.Repro
