import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealGaussianTraces.TraceAdd

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.GReal

open HeckeCharacterZeroLocus.SiegelWeilU NumberField MeasureTheory PositivityTheory.PfSWUS.Loc PositivityTheory.Rg.Sw PositivityTheory.SiegelWeilFormula.Gen
open scoped TensorProduct Matrix NNReal

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Rewrite using `[← IsScalarTower.algebraMap_apply]`. Establish `: (θ.comp (algebraMap F (Ainf F ⊗[F] E))) (1 / 2) = 1 / 2`. Rewrite using `[map_div₀, map_one, map_ofNat]`. Conclude with `this`.
-/
theorem th_half (θ : Ainf F ⊗[F] E →+* ℂ) :
    θ (algebraMap (Ainf F) (Ainf F ⊗[F] E) (algebraMap F (Ainf F) (1 / 2))) = 1 / 2 := by
  rw [← IsScalarTower.algebraMap_apply]
  have : (θ.comp (algebraMap F (Ainf F ⊗[F] E))) (1 / 2) = 1 / 2 := by
    rw [map_div₀, map_one, map_ofNat]
  exact this

/- English proof (translation)
Rewrite using `[trPair, map_mul, map_mul, th_half, trace_add σ hCM, map_add, hc]`. Establish `e : θ (∑ a, ∑ c, S a c * G c a) = (S.map θ * G.map θ).trace`. Simplify using `[Matrix.trace, Matrix.mul_apply, map_sum, map_mul]`. Rewrite using `[e, Complex.star_def, Complex.add_conj]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem th_trPair (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (θ : Ainf F ⊗[F] E →+* ℂ)
    (hc : ∀ z, θ (sigR (Ainf F) σ z) = star (θ z)) {n : ℕ} (S G : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) :
    θ (algebraMap (Ainf F) (Ainf F ⊗[F] E) (trPair (Ainf F) S G)) = (((S.map θ * G.map θ).trace.re : ℝ) : ℂ) := by
  rw [trPair, map_mul, map_mul, th_half, trace_add σ hCM, map_add, hc]
  have e : θ (∑ a, ∑ c, S a c * G c a) = (S.map θ * G.map θ).trace := by
    simp [Matrix.trace, Matrix.mul_apply, map_sum, map_mul]
  rw [e, Complex.star_def, Complex.add_conj]
  push_cast
  ring

/- English proof (translation)
Rewrite using `[Algebra.TensorProduct.algebraMap_apply]`. Both sides reduce to the same expression.
-/
theorem tmul_one_eq (x : Ainf F) : (x ⊗ₜ[F] (1 : E)) = algebraMap (Ainf F) (Ainf F ⊗[F] E) x := by
  rw [Algebra.TensorProduct.algebraMap_apply]
  rfl

/- English proof (translation)
Rewrite using `[hP.psi]`. Use `congr 2`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[tmul_one_eq, th_trPair σ hCM (θ i) (hP.conj i)]`.
-/
theorem psi_trPair_gen (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (ψ : AddChar (AF F) ℂ) {ι : Type} [Fintype ι]
    (θ : ι → (Ainf F ⊗[F] E →+* ℂ)) (l : ι → ℝ) (hP : IsPlaces σ ψ θ l) {n : ℕ}
    (S G : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) :
    psiInf F ψ (trPair (Ainf F) S G) =
      Complex.exp (2 * Real.pi * Complex.I * ∑ i, (l i : ℂ) * (((S.map (θ i) * G.map (θ i)).trace.re : ℝ) : ℂ)) := by
  rw [hP.psi]
  congr 2
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [tmul_one_eq, th_trPair σ hCM (θ i) (hP.conj i)]

/- English proof (translation)
Rewrite using `[hP.psi]`. Use `congr 2`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[tmul_one_eq, map_neg, map_neg, th_trPair σ hCM (θ i) (hP.conj i)]`.
-/
theorem psi_neg_trPair_gen (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (ψ : AddChar (AF F) ℂ) {ι : Type} [Fintype ι]
    (θ : ι → (Ainf F ⊗[F] E →+* ℂ)) (l : ι → ℝ) (hP : IsPlaces σ ψ θ l) {n : ℕ}
    (S G : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) :
    psiInf F ψ (-trPair (Ainf F) S G) =
      Complex.exp (2 * Real.pi * Complex.I * ∑ i, (l i : ℂ) * (-(((S.map (θ i) * G.map (θ i)).trace.re : ℝ) : ℂ))) := by
  rw [hP.psi]
  congr 2
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [tmul_one_eq, map_neg, map_neg, th_trPair σ hCM (θ i) (hP.conj i)]

/- English proof (translation)
Use extensionality with `a c`. Simplify using `only [Matrix.conjTranspose_apply, Matrix.map_apply]`. Rewrite using `[← hc]`. Conclude with `congrArg θ (b.2 a c)`.
-/
theorem map_isHerm (σ : E →ₐ[F] E) (θ : Ainf F ⊗[F] E →+* ℂ)
    (hc : ∀ z, θ (sigR (Ainf F) σ z) = star (θ z)) {n : ℕ} (b : HermR (Ainf F) σ n) :
    ((b : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).map θ).IsHermitian := by
  ext a c
  simp only [Matrix.conjTranspose_apply, Matrix.map_apply]
  rw [← hc]
  exact congrArg θ (b.2 a c)

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [gramX, Qp, Qb, evX, map_sub, map_sum, map_mul, MvPolynomial.eval_X, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, sgn]`. Simplify using `only [Finset.sum_filter, if_true, Bool.false_eq_true, if_false]`. Rewrite using `[← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations.

Apply the tactic sequence `cases ε a <;> simp`.
-/
theorem gramX_eq {m n : ℕ} (ε : Fin m → Bool) (x : Matrix (Fin m) (Fin n) ℂ) :
    gramX ε x = xᴴ * Matrix.diagonal (sgn ε) * x := by
  ext i j
  simp only [gramX, Qp, Qb, evX, map_sub, map_sum, map_mul, MvPolynomial.eval_X, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true, sgn]
  simp only [Finset.sum_filter, if_true, Bool.false_eq_true, if_false]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  cases ε a <;> simp

/- English proof (translation)
Rewrite using `[gramX_eq, Matrix.IsHermitian, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.mul_assoc]`. Establish `hs : star (sgn ε) = sgn ε`. Use function extensionality and compare the values at `a`. Simplify using `only [Pi.star_apply, sgn]`. Apply the tactic sequence `split_ifs <;> simp`.

Rewrite using `[hs]`.
-/
theorem gramX_isHerm {m n : ℕ} (ε : Fin m → Bool) (x : Matrix (Fin m) (Fin n) ℂ) : (gramX ε x).IsHermitian := by
  rw [gramX_eq, Matrix.IsHermitian, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.diagonal_conjTranspose, Matrix.mul_assoc]
  have hs : star (sgn ε) = sgn ε := by
    funext a
    simp only [Pi.star_apply, sgn]
    split_ifs <;> simp
  rw [hs]

end PositivityTheory.SiegelWeilFormula.GReal
