import Mathlib
import Development.AbelianVarietyTheory.Statements.ShortVectorBound.ScaledLatticesInSupLattices

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PlaceScalar
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.L2.Pj GlobalTheory.PtTie GlobalTheory.PlaceTop

/- English proof (translation)
Rewrite using `[Nat.ceil_le]`. Use `push_cast`. Establish `h1` using `Nat.le_ceil x`. Establish `h2` using `Nat.le_ceil y`. Establish `h3 : (k : ℝ) * x ≤ k * (⌈x⌉₊ : ℝ)` using `mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg k)`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem ceil_mul_add_le (x y : ℝ) (k : ℕ) : ⌈(k : ℝ) * x + y⌉₊ ≤ k * ⌈x⌉₊ + ⌈y⌉₊ := by
  rw [Nat.ceil_le]
  push_cast
  have h1 := Nat.le_ceil x
  have h2 := Nat.le_ceil y
  have h3 : (k : ℝ) * x ≤ k * (⌈x⌉₊ : ℝ) := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg k)
  linarith

/- English proof (translation)
Introduce `D B hinj EX j wL wF w k hP hM`. Establish `hp : Formalism.MainNotions.DIV.Cons.Dplus w = k * Formalism.MainNotions.DIV.Cons.Dplus wL + Formalism.MainNotions.DIV.Cons.Dplus wF`. Simplify using `only [Formalism.MainNotions.DIV.Cons.Dplus, hP, Finset.sum_add_distrib, Finset.mul_sum]`. Expand and normalize the polynomial expressions, which then agree. Establish `hm : Formalism.MainNotions.DIV.Cons.Dminus w = k * Formalism.MainNotions.DIV.Cons.Dminus wL + Formalism.MainNotions.DIV.Cons.Dminus wF`.

Simplify using `only [Formalism.MainNotions.DIV.Cons.Dminus, hM, Finset.sum_add_distrib, Finset.mul_sum]`. Expand and normalize the polynomial expressions, which then agree. Establish `hs : ∀ u : WeightFamilies.Wt D j, WeightAlgebra.DF u = Formalism.MainNotions.DIV.Cons.Dplus u + Formalism.MainNotions.DIV.Cons.Dminus u`. Introduce `u`. Simplify using `only [WeightAlgebra.DF, WeightAlgebra.degP, Formalism.MainNotions.DIV.Cons.Dplus, Formalism.MainNotions.DIV.Cons.Dminus, Finset.sum_add_distrib]`.

Establish `hf : (WeightAlgebra.DF w : ℝ) = k * (WeightAlgebra.DF wL : ℝ) + (WeightAlgebra.DF wF : ℝ)`. Rewrite using `[hs, hs, hs, hp, hm]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations.

Simplify using `only [nnW, hp, hm]`. Rewrite using `[← Finset.prod_pow, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Unfold `c2`.

Conclude with `le_of_eq (by exact_mod_cast hf)`. Unfold `Formalism.MainNotions.DIV.Cons.cHalf`. Establish `: (WeightAlgebra.DF w : ℝ) / 2 = k * ((WeightAlgebra.DF wL : ℝ) / 2) + (WeightAlgebra.DF wF : ℝ) / 2`. Rewrite using `[hf]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[this]`. Conclude with `ceil_mul_add_le _ _ _`.
-/
theorem weight_normalizer_and_exponents_of_weight_sum :
    ∀ (D : D7) (B : WeightFamilies.Prov D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (j : ℕ) (wL wF w : WeightFamilies.Wt D j) (k : ℕ), (∀ τ i, w.aP τ i = wF.aP τ i + k * wL.aP τ i) → (∀ τ i, w.aM τ i = wF.aM τ i + k * wL.aM τ i) → nnW B hinj EX w = nnW B hinj EX wL ^ k * nnW B hinj EX wF ∧ c2 D w ≤ k * c2 D wL + c2 D wF ∧ Formalism.MainNotions.DIV.Cons.cHalf w ≤ k * Formalism.MainNotions.DIV.Cons.cHalf wL + Formalism.MainNotions.DIV.Cons.cHalf wF := by
  intro D B hinj EX j wL wF w k hP hM
  have hp : Formalism.MainNotions.DIV.Cons.Dplus w = k * Formalism.MainNotions.DIV.Cons.Dplus wL + Formalism.MainNotions.DIV.Cons.Dplus wF := by
    simp only [Formalism.MainNotions.DIV.Cons.Dplus, hP, Finset.sum_add_distrib, Finset.mul_sum]
    ring
  have hm : Formalism.MainNotions.DIV.Cons.Dminus w = k * Formalism.MainNotions.DIV.Cons.Dminus wL + Formalism.MainNotions.DIV.Cons.Dminus wF := by
    simp only [Formalism.MainNotions.DIV.Cons.Dminus, hM, Finset.sum_add_distrib, Finset.mul_sum]
    ring
  have hs : ∀ u : WeightFamilies.Wt D j, WeightAlgebra.DF u = Formalism.MainNotions.DIV.Cons.Dplus u + Formalism.MainNotions.DIV.Cons.Dminus u := by
    intro u
    simp only [WeightAlgebra.DF, WeightAlgebra.degP, Formalism.MainNotions.DIV.Cons.Dplus, Formalism.MainNotions.DIV.Cons.Dminus, Finset.sum_add_distrib]
  have hf : (WeightAlgebra.DF w : ℝ) = k * (WeightAlgebra.DF wL : ℝ) + (WeightAlgebra.DF wF : ℝ) := by
    rw [hs, hs, hs, hp, hm]
    push_cast
    ring
  refine ⟨?_, ?_, ?_⟩
  · simp only [nnW, hp, hm]
    rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    ring
  · unfold c2
    exact le_of_eq (by exact_mod_cast hf)
  · unfold Formalism.MainNotions.DIV.Cons.cHalf
    have : (WeightAlgebra.DF w : ℝ) / 2 = k * ((WeightAlgebra.DF wL : ℝ) / 2) + (WeightAlgebra.DF wF : ℝ) / 2 := by
      rw [hf]; ring
    rw [this]
    exact ceil_mul_add_le _ _ _

end GlobalTheory.PlaceScalar
