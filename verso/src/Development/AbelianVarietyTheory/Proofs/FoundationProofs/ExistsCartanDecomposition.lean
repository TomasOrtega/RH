import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.SingularValueFrame
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.PolarJmConjTranspose
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ExpInPPosDef

noncomputable section

open scoped Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership

namespace GlobalTheory.CartanExists

variable {n : ℕ} (ε : Fin n → Bool)

/- English proof (translation)
Apply the tactic sequence `cases hi : ε i <;> cases hj : ε j <;> simp_all <;> norm_num`.
-/
lemma sign_ne {i j : Fin n} (h : ε i ≠ ε j) :
    (if ε i then (1 : ℂ) else -1) ≠ (if ε j then (1 : ℂ) else -1) := by
  cases hi : ε i <;> cases hj : ε j <;> simp_all <;> norm_num

/- English proof (translation)
Apply the tactic sequence `cases ε i <;> simp`.
-/
lemma sign_ne_zero (i : Fin n) : (if ε i then (1 : ℂ) else -1) ≠ 0 := by
  cases ε i <;> simp

/- English proof (translation)
Use `⟨hk.1, fun i j hij => ?_⟩` and prove the remaining obligations. Establish `h` using `congrFun (congrFun hk.2 i) j`. Simplify using `only [ReciprocityTheory.ChartRestriction.DS.Jm, Matrix.mul_diagonal, Matrix.diagonal_mul] at h`. Establish `h2 : k i j * ((if ε j then (1 : ℂ) else -1) - (if ε i then (1 : ℂ) else -1)) = 0`. Rewrite using `[mul_sub, h]`.

Expand and normalize the polynomial expressions, which then agree. Break down `mul_eq_zero.mp h2 with h3 | h3` into its components or cases. Conclude with `h3`. Conclude with `absurd (sub_eq_zero.mp h3).symm (sign_ne ε hij)`.
-/
lemma isInK_of_mem {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ ReciprocityTheory.ChartRestriction.DS.Kset ε) : IsInK ε k := by
  refine ⟨hk.1, fun i j hij => ?_⟩
  have h := congrFun (congrFun hk.2 i) j
  simp only [ReciprocityTheory.ChartRestriction.DS.Jm, Matrix.mul_diagonal, Matrix.diagonal_mul] at h
  have h2 : k i j * ((if ε j then (1 : ℂ) else -1) - (if ε i then (1 : ℂ) else -1)) = 0 := by
    rw [mul_sub, h]; ring
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact h3
  · exact absurd (sub_eq_zero.mp h3).symm (sign_ne ε hij)

/- English proof (translation)
Use `⟨ReciprocityTheory.ChartRestriction.DS.S7.isHermitian_of_mem_noncompactPart' hX, fun i j hij => ?_⟩` and prove the remaining obligations. Establish `h` using `congrFun (congrFun hX.2 i) j`. Simplify using `only [ReciprocityTheory.ChartRestriction.DS.Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.neg_apply] at h`. Rewrite `h` using `[← hij]`. Establish `h2 : (2 * (if ε i then (1 : ℂ) else -1)) * X i j = 0`.

Take the linear combination `h`. Break down `mul_eq_zero.mp h2 with h3 | h3` into its components or cases. Conclude with `absurd h3 (mul_ne_zero two_ne_zero (sign_ne_zero ε i))`. Conclude with `h3`.
-/
lemma isInP_of_inP {X : Matrix (Fin n) (Fin n) ℂ} (hX : ReciprocityTheory.ChartRestriction.DS.inP ε X) : IsInP ε X := by
  refine ⟨ReciprocityTheory.ChartRestriction.DS.S7.isHermitian_of_mem_noncompactPart' hX, fun i j hij => ?_⟩
  have h := congrFun (congrFun hX.2 i) j
  simp only [ReciprocityTheory.ChartRestriction.DS.Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.neg_apply] at h
  rw [← hij] at h
  have h2 : (2 * (if ε i then (1 : ℂ) else -1)) * X i j = 0 := by
    linear_combination h
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd h3 (mul_ne_zero two_ne_zero (sign_ne_zero ε i))
  · exact h3

/- English proof (translation)
Introduce `n ε g hg`. Take `⟨k, hk, Y, hY, rfl⟩` from `ReciprocityTheory.ChartRestriction.DS.polar_UJ (ε := ε) (g := g) hg`. Use `⟨Y, isInP_of_inP ε hY, k, 1, isInK_of_mem ε hk, ⟨one_mem _, fun _ _ h => Matrix.one_apply_ne fun e => h (congrArg ε e)⟩, by rw [Matrix.mul_one]⟩` and prove the remaining obligations.
-/
theorem exists_isCartan : ∀ (n : ℕ) (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) ℂ), IsInU ε g →
    ∃ X, IsCartan ε g X := by
  intro n ε g hg
  obtain ⟨k, hk, Y, hY, rfl⟩ := ReciprocityTheory.ChartRestriction.DS.polar_UJ (ε := ε) (g := g) hg
  refine ⟨Y, isInP_of_inP ε hY, k, 1, isInK_of_mem ε hk,
    ⟨one_mem _, fun _ _ h => Matrix.one_apply_ne fun e => h (congrArg ε e)⟩, by rw [Matrix.mul_one]⟩

end GlobalTheory.CartanExists
