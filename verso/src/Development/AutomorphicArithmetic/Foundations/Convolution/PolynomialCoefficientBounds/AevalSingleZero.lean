import Mathlib
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.AffineCharacterGenerators.Generators
import Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.PieceAdd

open MvPolynomial Filter Topology PositivityTheory.Rg.Fx

/- English proof (translation)
Proceed by induction on `p using MvPolynomial.induction_on with`. Consider the case `C a`. Rewrite using `[aeval_C, aeval_C]`. Both sides reduce to the same expression. Consider the case `add p r hp hr => rw [map_add, map_add, hp, hr, AddMonoidAlgebra.single_add]`.

Consider the case `mul_X p i hp`. Rewrite using `[map_mul, map_mul, hp, aeval_X, aeval_X, AddMonoidAlgebra.single_mul_single, add_zero]`.
-/
private theorem UpperTheory.ConvolutionTheory.FX.aeval_single_zero {ι ι' : Type} (q : ι → MvPolynomial ι' ℂ)
    (p : MvPolynomial ι ℂ) :
    aeval (fun i => (AddMonoidAlgebra.single 0 (q i) : EP ι')) p
      = (AddMonoidAlgebra.single 0 (aeval q p) : EP ι') := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    rw [aeval_C, aeval_C]
    rfl
  | add p r hp hr => rw [map_add, map_add, hp, hr, AddMonoidAlgebra.single_add]
  | mul_X p i hp =>
    rw [map_mul, map_mul, hp, aeval_X, aeval_X, AddMonoidAlgebra.single_mul_single, add_zero]

/- English proof (translation)
Unfold `lin`. Rewrite using `[Finset.sum_eq_single (δ i)]`. Simplify using the standard rewrite rules. Introduce `j _ hj`. Simplify using `[Ne.symm hj]`.

Simplify using the standard rewrite rules.
-/
private theorem UpperTheory.ConvolutionTheory.FX.lin_delta {ι ι' : Type} [Fintype ι'] [DecidableEq ι'] (δ : ι → ι') (i : ι) :
    lin (fun j => if δ i = j then (1 : ℝ) else 0) = (X (δ i) : MvPolynomial ι' ℂ) := by
  unfold lin
  rw [Finset.sum_eq_single (δ i)]
  · simp
  · intro j _ hj
    simp [Ne.symm hj]
  · simp

/- English proof (translation)
Unfold `lin`. Simplify using `only [Matrix.vecMul, dotProduct, Matrix.of_apply, map_sum, map_mul, rename_C, rename_X, Complex.ofReal_sum, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_eq_single (δ i)]`.

Simplify using the standard rewrite rules. Introduce `j _ hj`. Simplify using `[Ne.symm hj]`. Simplify using the standard rewrite rules.
-/
private theorem UpperTheory.ConvolutionTheory.FX.lin_push {ι ι' : Type} [Fintype ι] [Fintype ι'] [DecidableEq ι'] (δ : ι → ι')
    (v : ι → ℝ) :
    lin (Matrix.vecMul v (Matrix.of fun i j => if δ i = j then (1 : ℝ) else 0)) = rename δ (lin v) := by
  unfold lin
  simp only [Matrix.vecMul, dotProduct, Matrix.of_apply, map_sum, map_mul, rename_C, rename_X,
    Complex.ofReal_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single (δ i)]
  · simp
  · intro j _ hj
    simp [Ne.symm hj]
  · simp

/- English proof (translation)
Establish `h1 : (fun i => (C ((0 : ι → ℂ) i) + lin ((Matrix.of fun i j => if δ i = j then (1 : ℝ) else 0) i) : MvPolynomial ι' ℂ)) = X ∘ δ`. Use function extensionality and compare the values at `i`. Use `UpperTheory.ConvolutionTheory.FX.lin_delta δ i` as an intermediate fact. Simplify using `only [Pi.zero_apply, map_zero, zero_add, Function.comp]`. Conclude with `this`.

Unfold `ren aff lift`. Rewrite using `[AddMonoidAlgebra.liftNCRingHom_single]`. Express the relevant statement in the definitionally equal form `aeval (fun i => (AddMonoidAlgebra.single 0 (C ((0 : ι → ℂ) i) + lin ((Matrix.of fun i j => if δ i = j then (1 : ℝ) else 0) i)) : EP ι')) p * (AddMonoidAlgebra.single (Matrix.vecMul v _) (C (expChar 0 (Multiplicative.ofAdd v))) : EP ι') = _`. Rewrite using `[UpperTheory.ConvolutionTheory.FX.aeval_single_zero, h1, AddMonoidAlgebra.single_mul_single, zero_add]`. Establish `h2 : expChar (0 : ι → ℂ) (Multiplicative.ofAdd v) = 1` using `by simp [expChar]`.

Rewrite using `[h2, map_one, mul_one, rename_eq_aeval]`.
-/
private theorem UpperTheory.ConvolutionTheory.FX.ren_single {ι ι' : Type} [Fintype ι] [Fintype ι'] [DecidableEq ι'] (δ : ι → ι')
    (v : ι → ℝ) (p : MvPolynomial ι ℂ) :
    ren δ (AddMonoidAlgebra.single v p : EP ι) =
      (AddMonoidAlgebra.single (Matrix.vecMul v (Matrix.of fun i j => if δ i = j then (1 : ℝ) else 0))
        (rename δ p) : EP ι') := by
  have h1 : (fun i => (C ((0 : ι → ℂ) i) + lin ((Matrix.of fun i j => if δ i = j then (1 : ℝ) else 0) i) :
      MvPolynomial ι' ℂ)) = X ∘ δ := by
    funext i
    have := UpperTheory.ConvolutionTheory.FX.lin_delta δ i
    simp only [Pi.zero_apply, map_zero, zero_add, Function.comp]
    exact this
  unfold ren aff lift
  rw [AddMonoidAlgebra.liftNCRingHom_single]
  change aeval (fun i => (AddMonoidAlgebra.single 0 (C ((0 : ι → ℂ) i) +
      lin ((Matrix.of fun i j => if δ i = j then (1 : ℝ) else 0) i)) : EP ι')) p *
    (AddMonoidAlgebra.single (Matrix.vecMul v _) (C (expChar 0 (Multiplicative.ofAdd v))) : EP ι') = _
  rw [UpperTheory.ConvolutionTheory.FX.aeval_single_zero, h1, AddMonoidAlgebra.single_mul_single, zero_add]
  have h2 : expChar (0 : ι → ℂ) (Multiplicative.ofAdd v) = 1 := by simp [expChar]
  rw [h2, map_one, mul_one, rename_eq_aeval]

/- English proof (translation)
Introduce `ι _ f ι' _ _ δ k`. Take `⟨ha, h0, hs⟩` from `UpperTheory.ConvolutionTheory.FX.piece_add ι k`. Take `⟨ha', h0', hs'⟩` from `UpperTheory.ConvolutionTheory.FX.piece_add ι' k`. Proceed by induction on `f using AddMonoidAlgebra.induction_linear with`. Consider the case `zero => rw [map_zero, h0, h0', map_zero]`.

Consider the case `add f g hf hg => rw [map_add, ha, ha', map_add, hf, hg]`. Consider the case `single v p`. Rewrite using `[UpperTheory.ConvolutionTheory.FX.ren_single, hs, hs', map_sum]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_mul, map_pow, rename_C, UpperTheory.ConvolutionTheory.FX.lin_push, rename_homogeneousComponent]`.
-/
theorem UpperTheory.ConvolutionTheory.FX.piece_ren :
    ∀ (ι : Type) [Fintype ι] (f : EP ι) (ι' : Type) [Fintype ι'] [DecidableEq ι'] (δ : ι → ι') (k : ℕ), piece k (ren δ f) = rename δ (piece k f) := by
  intro ι _ f ι' _ _ δ k
  obtain ⟨ha, h0, hs⟩ := UpperTheory.ConvolutionTheory.FX.piece_add ι k
  obtain ⟨ha', h0', hs'⟩ := UpperTheory.ConvolutionTheory.FX.piece_add ι' k
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => rw [map_zero, h0, h0', map_zero]
  | add f g hf hg => rw [map_add, ha, ha', map_add, hf, hg]
  | single v p =>
    rw [UpperTheory.ConvolutionTheory.FX.ren_single, hs, hs', map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_mul, map_mul, map_pow, rename_C, UpperTheory.ConvolutionTheory.FX.lin_push, rename_homogeneousComponent]
