import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.LowBlock

namespace ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds

open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder

noncomputable section

/- English proof (translation)
Simplify using `only [nsq, dotProduct, Pi.star_apply]`. Use `push_cast`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Conclude with `Complex.conj_mul' (y i)`.
-/
lemma dot_self {n : ℕ} (y : Fin n → ℂ) : star y ⬝ᵥ y = ((nsq y : ℝ) : ℂ) := by
  simp only [nsq, dotProduct, Pi.star_apply]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  exact Complex.conj_mul' (y i)

/- English proof (translation)
Establish `h : A *ᵥ star y = star (A.map (starRingEnd ℂ) *ᵥ y)`. Use function extensionality and compare the values at `i`. Simplify using `[Matrix.mulVec, dotProduct, star_sum, mul_comm]`. Rewrite using `[← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, h, dot_self]`.
-/
lemma quad_AtA {n q : ℕ} (A : Matrix (Fin q) (Fin n) ℂ) (y : Fin n → ℂ) :
    star y ⬝ᵥ ((Aᵀ * A.map (starRingEnd ℂ)) *ᵥ y) = ((nsq (A.map (starRingEnd ℂ) *ᵥ y) : ℝ) : ℂ) := by
  have h : A *ᵥ star y = star (A.map (starRingEnd ℂ) *ᵥ y) := by
    funext i
    simp [Matrix.mulVec, dotProduct, star_sum, mul_comm]
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, h, dot_self]

/- English proof (translation)
Establish `hH : (1 - Aᵀ * A.map (starRingEnd ℂ) + Bᵀ * B.map (starRingEnd ℂ)).IsHermitian`. Establish `h1 : ∀ {m : ℕ} (C : Matrix (Fin m) (Fin n) ℂ), (Cᵀ * C.map (starRingEnd ℂ)).IsHermitian`. Introduce `m C`. Use extensionality with `i j`. Simplify using `[Matrix.conjTranspose_apply, Matrix.mul_apply, star_sum, mul_comm]`.

Conclude with `((Matrix.isHermitian_one.sub (h1 A)).add (h1 B))`. Use `Matrix.PosDef.of_dotProduct_mulVec_pos hH fun x hx => ?_` and prove the remaining obligations. Rewrite using `[Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_add, dotProduct_sub, dot_self, quad_AtA, quad_AtA]`. Establish `hpos : 0 < nsq x`. Take `⟨i, hi⟩` from `Function.ne_iff.mp hx`.

Establish `: 0 < ‖x i‖ ^ 2` using `by positivity`. Conclude with `lt_of_lt_of_le this (Finset.single_le_sum (f := fun j => ‖x j‖ ^ 2) (fun j _ => by positivity) (Finset.mem_univ i))`. Establish `hB` using `nsq_nonneg (B.map (starRingEnd ℂ) *ᵥ x)`. Establish `hA'` using `hA x`. Establish `hs2 : s ^ 2 < 1` using `by nlinarith`.

Establish `key : 0 < nsq x - nsq (A.map (starRingEnd ℂ) *ᵥ x) + nsq (B.map (starRingEnd ℂ) *ᵥ x)`. Use the polynomial consequences of the given equalities and inequalities. Establish `: ((nsq x - nsq (A.map (starRingEnd ℂ) *ᵥ x) + nsq (B.map (starRingEnd ℂ) *ᵥ x) : ℝ) : ℂ) = ((nsq x : ℝ) : ℂ) - ((nsq (A.map (starRingEnd ℂ) *ᵥ x) : ℝ) : ℂ) + ((nsq (B.map (starRingEnd ℂ) *ᵥ x) : ℝ) : ℂ)` using `by push_cast; ring`. Rewrite using `[← this]`. Conclude with `key` after adjusting the coercions.
-/
lemma posDef_of_bound {n q k : ℕ} (A : Matrix (Fin q) (Fin n) ℂ) (B : Matrix (Fin k) (Fin n) ℂ) {s : ℝ}
    (hs : s < 1) (hA : ∀ y, nsq (A.map (starRingEnd ℂ) *ᵥ y) ≤ s ^ 2 * nsq y) (hs0 : 0 ≤ s) :
    (1 - Aᵀ * A.map (starRingEnd ℂ) + Bᵀ * B.map (starRingEnd ℂ)).PosDef := by
  have hH : (1 - Aᵀ * A.map (starRingEnd ℂ) + Bᵀ * B.map (starRingEnd ℂ)).IsHermitian := by
    have h1 : ∀ {m : ℕ} (C : Matrix (Fin m) (Fin n) ℂ), (Cᵀ * C.map (starRingEnd ℂ)).IsHermitian := by
      intro m C
      ext i j
      simp [Matrix.conjTranspose_apply, Matrix.mul_apply, star_sum, mul_comm]
    exact ((Matrix.isHermitian_one.sub (h1 A)).add (h1 B))
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hH fun x hx => ?_
  rw [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_add, dotProduct_sub,
    dot_self, quad_AtA, quad_AtA]
  have hpos : 0 < nsq x := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
    have : 0 < ‖x i‖ ^ 2 := by positivity
    exact lt_of_lt_of_le this (Finset.single_le_sum (f := fun j => ‖x j‖ ^ 2)
      (fun j _ => by positivity) (Finset.mem_univ i))
  have hB := nsq_nonneg (B.map (starRingEnd ℂ) *ᵥ x)
  have hA' := hA x
  have hs2 : s ^ 2 < 1 := by nlinarith
  have key : 0 < nsq x - nsq (A.map (starRingEnd ℂ) *ᵥ x) + nsq (B.map (starRingEnd ℂ) *ᵥ x) := by
    nlinarith
  have : ((nsq x - nsq (A.map (starRingEnd ℂ) *ᵥ x) + nsq (B.map (starRingEnd ℂ) *ᵥ x) : ℝ) : ℂ) =
      ((nsq x : ℝ) : ℂ) - ((nsq (A.map (starRingEnd ℂ) *ᵥ x) : ℝ) : ℂ) +
        ((nsq (B.map (starRingEnd ℂ) *ᵥ x) : ℝ) : ℂ) := by push_cast; ring
  rw [← this]
  exact_mod_cast key

end

end ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds
