import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.EisCellsDefs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsBlockMatrixTwoByTwoFinEq

noncomputable section
open scoped Matrix
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions.EC

namespace GlobalTheory.CompanionTheory.BruhatCell

variable {K : Type} [Field K]

/- English proof (translation)
Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Establish `h : (q * M) i = ∑ k, q i k • M k`. Use function extensionality and compare the values at `j`. Simplify using `[Matrix.mul_apply, Finset.sum_apply]`.

Rewrite using `[h]`. Conclude with `Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)`.
-/
theorem span_range_mul_le {n : ℕ} (q M : Matrix (Fin n) (Fin n) K) :
    Submodule.span K (Set.range (q * M)) ≤ Submodule.span K (Set.range M) := by
  rw [Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  have h : (q * M) i = ∑ k, q i k • M k := by
    funext j
    simp [Matrix.mul_apply, Finset.sum_apply]
  rw [h]
  exact Submodule.sum_mem _ fun k _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

/- English proof (translation)
Use `le_antisymm (span_range_mul_le p M) ?_` and prove the remaining obligations. Establish `h` using `span_range_mul_le p⁻¹ (p * M)`. Rewrite `h` using `[← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hp, Matrix.one_mul]`. Then use the resulting hypothesis.
-/
theorem span_range_mul_of_isUnit {n : ℕ} {p : Matrix (Fin n) (Fin n) K} (hp : IsUnit p.det)
    (M : Matrix (Fin n) (Fin n) K) :
    Submodule.span K (Set.range (p * M)) = Submodule.span K (Set.range M) := by
  refine le_antisymm (span_range_mul_le p M) ?_
  have h := span_range_mul_le p⁻¹ (p * M)
  rwa [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hp, Matrix.one_mul] at h

/- English proof (translation)
Establish `row : ∀ i : Fin n, (eId K n r * a) i = if (i : ℕ) < r then a i else 0`. Introduce `i`. Use function extensionality and compare the values at `j`. Apply the tactic sequence `by_cases hi : (i : ℕ) < r <;> simp [eId, Matrix.diagonal_mul, hi]`. Use `le_antisymm ?_ ?_` and prove the remaining obligations.

Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Express the relevant statement in the definitionally equal form `(eId K n r * a) i ∈ _`. Rewrite using `[row i]`. Distinguish the cases in `hi : (i : ℕ) < r`.

Rewrite using `[if_pos hi, h.2 i hi]`. Conclude with `Submodule.subset_span ⟨_, rfl⟩`. Rewrite using `[if_neg hi]`. Conclude with `Submodule.zero_mem _`. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `_ ⟨j, rfl⟩`. Use `Submodule.subset_span ⟨⟨j, j.2.trans_le hr⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(eId K n r * a) ⟨j, j.2.trans_le hr⟩ = c j`. Rewrite using `[row, if_pos j.2, h.2 ⟨j, j.2.trans_le hr⟩ j.2]`.
-/
theorem span_range_eId_mul {n r : ℕ} (hr : r ≤ n) {c : Matrix (Fin r) (Fin n) K}
    {a : Matrix (Fin n) (Fin n) K} (h : IsCompl c a) :
    Submodule.span K (Set.range (eId K n r * a)) = Submodule.span K (Set.range c) := by
  have row : ∀ i : Fin n, (eId K n r * a) i = if (i : ℕ) < r then a i else 0 := by
    intro i
    funext j
    by_cases hi : (i : ℕ) < r <;> simp [eId, Matrix.diagonal_mul, hi]
  refine le_antisymm ?_ ?_
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    change (eId K n r * a) i ∈ _
    rw [row i]
    by_cases hi : (i : ℕ) < r
    · rw [if_pos hi, h.2 i hi]
      exact Submodule.subset_span ⟨_, rfl⟩
    · rw [if_neg hi]
      exact Submodule.zero_mem _
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    refine Submodule.subset_span ⟨⟨j, j.2.trans_le hr⟩, ?_⟩
    change (eId K n r * a) ⟨j, j.2.trans_le hr⟩ = c j
    rw [row, if_pos j.2, h.2 ⟨j, j.2.trans_le hr⟩ j.2]

/- English proof (translation)
Introduce `K _ n r hr c a p h hp`. Establish `hneg : p * -(eId K n r * a) = (-p) * (eId K n r * a)`. Rewrite using `[Matrix.mul_neg, Matrix.neg_mul]`. Establish `hdet : IsUnit (-p).det`. Rewrite using `[Matrix.det_neg]`.

Conclude with `((IsUnit.neg isUnit_one).pow _).mul hp`. Rewrite using `[hneg, span_range_mul_of_isUnit hdet, span_range_eId_mul hr h]`.
-/
theorem span_range_lowerLeft : ∀ {K : Type} [Field K] {n r : ℕ}, r ≤ n →
    ∀ (c : Matrix (Fin r) (Fin n) K) (a p : Matrix (Fin n) (Fin n) K), IsCompl c a → IsUnit p.det →
      Submodule.span K (Set.range (p * -(eId K n r * a))) = Submodule.span K (Set.range c) := by
  intro K _ n r hr c a p h hp
  have hneg : p * -(eId K n r * a) = (-p) * (eId K n r * a) := by
    rw [Matrix.mul_neg, Matrix.neg_mul]
  have hdet : IsUnit (-p).det := by
    rw [Matrix.det_neg]
    exact ((IsUnit.neg isUnit_one).pow _).mul hp
  rw [hneg, span_range_mul_of_isUnit hdet, span_range_eId_mul hr h]

end GlobalTheory.CompanionTheory.BruhatCell
