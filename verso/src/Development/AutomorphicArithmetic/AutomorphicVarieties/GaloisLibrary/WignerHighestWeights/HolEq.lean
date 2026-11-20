import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.IsAlgIsoRefl
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualInfinitesimalCharacterRegular
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

/- English proof (translation)
Introduce `E _ _ _ a N _ _ _ _ τ L x`. Set `L' : Matrix (Fin a) (Fin a) (Cinf E) →ₗ[ℝ] N` to `L`. Establish `hsum : ∀ y : Matrix (Fin a) (Fin a) ℂ, L' (y.map (atEmb τ)) = ∑ i, ∑ j, L' (Matrix.single i j (atEmb τ (y i j)))` using `fun y => by conv_lhs => rw [Matrix.matrix_eq_sum_single (y.map (atEmb τ))]`. Simplify using `only [map_sum, Matrix.map_apply]`. Establish `hL : ∀ (i j : Fin a) (w : ℂ), L' (Matrix.single i j (atEmb τ w)) = (w.re : ℂ) • L' (Matrix.single i j (atEmb τ 1)) + (w.im : ℂ) • L' (Matrix.single i j (atEmb τ Complex.I))` using `fun i j w => by`.

Rewrite using `[atEmb_eq τ w, Matrix.single_add, ← Matrix.smul_single, ← Matrix.smul_single, map_add, map_smul, map_smul, ← algebraMap_smul ℂ w.re, ← algebraMap_smul ℂ w.im]`. Both sides reduce to the same expression. Express the relevant statement in the definitionally equal form `∑ i, ∑ j, x i j • ((1 / 2 : ℂ) • (L' (Matrix.single i j (atEmb τ 1)) - Complex.I • L' (Matrix.single i j (atEmb τ Complex.I)))) = (1 / 2 : ℂ) • (L' (x.map (atEmb τ)) - Complex.I • L' ((Complex.I • x).map (atEmb τ)))`. Rewrite using `[hsum, hsum]`. Simplify using `only [Finset.smul_sum, ← Finset.sum_sub_distrib]`.

Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.smul_apply, smul_eq_mul, hL i j (x i j), hL i j (Complex.I * x i j)]`. Generalize the expression as in `x i j = c`. Use `conv_lhs => rw [← Complex.re_add_im c]`. Simplify using `only [Complex.I_mul_re, Complex.I_mul_im, Complex.ofReal_neg]`.

Use `match_scalars`. Expand and normalize the polynomial expressions, which then agree. Take the linear combination `(-(c.im : ℂ) / 2) * Complex.I_mul_I`.
-/
theorem UpperTheory.V.AlgRepEndIrreducible.holEq :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (N : Type) [AddCommGroup N] [Module ℂ N] [Module ℝ N] [IsScalarTower ℝ ℂ N] (τ : E →+* ℂ) (L : Lie E a →ₗ[ℝ] N) (x : Matrix (Fin a) (Fin a) ℂ),
      hol τ L x = (1 / 2 : ℂ) • (L (toL (x.map (atEmb τ))) - Complex.I • L (toL ((Complex.I • x).map (atEmb τ)))) := by
  intro E _ _ _ a N _ _ _ _ τ L x
  let L' : Matrix (Fin a) (Fin a) (Cinf E) →ₗ[ℝ] N := L
  have hsum : ∀ y : Matrix (Fin a) (Fin a) ℂ,
      L' (y.map (atEmb τ)) = ∑ i, ∑ j, L' (Matrix.single i j (atEmb τ (y i j))) := fun y => by
    conv_lhs => rw [Matrix.matrix_eq_sum_single (y.map (atEmb τ))]
    simp only [map_sum, Matrix.map_apply]
  have hL : ∀ (i j : Fin a) (w : ℂ), L' (Matrix.single i j (atEmb τ w)) =
      (w.re : ℂ) • L' (Matrix.single i j (atEmb τ 1)) +
        (w.im : ℂ) • L' (Matrix.single i j (atEmb τ Complex.I)) := fun i j w => by
    rw [atEmb_eq τ w, Matrix.single_add, ← Matrix.smul_single, ← Matrix.smul_single, map_add, map_smul, map_smul,
      ← algebraMap_smul ℂ w.re, ← algebraMap_smul ℂ w.im]
    rfl
  change ∑ i, ∑ j, x i j • ((1 / 2 : ℂ) • (L' (Matrix.single i j (atEmb τ 1)) -
      Complex.I • L' (Matrix.single i j (atEmb τ Complex.I)))) =
    (1 / 2 : ℂ) • (L' (x.map (atEmb τ)) - Complex.I • L' ((Complex.I • x).map (atEmb τ)))
  rw [hsum, hsum]
  simp only [Finset.smul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.smul_apply, smul_eq_mul, hL i j (x i j), hL i j (Complex.I * x i j)]
  generalize x i j = c
  conv_lhs => rw [← Complex.re_add_im c]
  simp only [Complex.I_mul_re, Complex.I_mul_im, Complex.ofReal_neg]
  match_scalars
  · ring
  · linear_combination (-(c.im : ℂ) / 2) * Complex.I_mul_I
