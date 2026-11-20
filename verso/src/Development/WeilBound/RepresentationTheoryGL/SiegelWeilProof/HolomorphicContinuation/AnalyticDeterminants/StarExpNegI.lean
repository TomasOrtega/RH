import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.TCMatC

noncomputable section

open Matrix ComplexConjugate

namespace PositivityTheory.Rg.Sw.LVs.TC

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

variable {n : ℕ}

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem exp_neg_I (t : ℂ) : Complex.exp (-t * Complex.I) = (Complex.exp (t * Complex.I))⁻¹ := by
  rw [neg_mul, Complex.exp_neg]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem star_exp_I (θ : ℝ) : star (Complex.exp (θ * Complex.I)) * Complex.exp (θ * Complex.I) = 1 := by
  rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
  simp

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem star_exp_negI (θ : ℝ) : star (Complex.exp (-θ * Complex.I)) * Complex.exp (-θ * Complex.I) = 1 := by
  rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
  simp

def dA (j : ℕ) (θ : ℝ) : Fin n → ℂ := fun a => if a ∈ blkA j then Complex.exp (θ * Complex.I) else Complex.exp (-θ * Complex.I)

def dB (j : ℕ) (θ : ℝ) : Fin n → ℂ := fun a => if a ∈ blkA j then Complex.exp (-θ * Complex.I) else Complex.exp (θ * Complex.I)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem rot_eq (j : ℕ) (θ : ℝ) : rot (n := n) j θ = Cm n * fromBlocks (diagonal (dA j θ)) 0 0 (diagonal (dB j θ)) * CmI n := rfl

/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem dA_ne (j : ℕ) (θ : ℝ) (a : Fin n) : dA j θ a ≠ 0 := by unfold dA; split_ifs <;> exact Complex.exp_ne_zero _

/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem dB_ne (j : ℕ) (θ : ℝ) (a : Fin n) : dB j θ a ≠ 0 := by unfold dB; split_ifs <;> exact Complex.exp_ne_zero _

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Replace the relevant objects with their definitions. Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
theorem rot_inG (j : ℕ) (θ : ℝ) : InG (rot (n := n) j θ) := by
  rw [rot_eq]
  refine inG_conjDiag _ _ (fun a => ?_) (fun a => ?_)
  · unfold dA; split_ifs
    · exact star_exp_I θ
    · exact star_exp_negI θ
  · unfold dB; split_ifs
    · exact star_exp_negI θ
    · exact star_exp_I θ

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem smul_conjCm (c : ℂ) (X : M2 n) : c • (Cm n * X * CmI n) = Cm n * (c • X) * CmI n := by
  rw [Matrix.mul_smul, Matrix.smul_mul]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Apply the first step, then apply the next step to every resulting obligation. Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem rot_conj (j : ℕ) (θ : ℝ) (r s : Fin n) :
    Complex.exp (2 * θ * Complex.I) • (rot j θ * nU (single r s 1) * (rot j θ)⁻¹ - 1) =
      Cm n * (zLow j r s + Complex.exp (2 * θ * Complex.I) • zMid j r s +
        Complex.exp (2 * θ * Complex.I) ^ 2 • zTop j r s) * CmI n := by
  rw [rot_eq, conj_nU _ _ (dA_ne j θ) (dB_ne j θ), smul_conjCm]
  congr 2
  have he : Complex.exp (2 * θ * Complex.I) = Complex.exp (θ * Complex.I) ^ 2 := by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hu0 : Complex.exp (θ * Complex.I) ≠ 0 := Complex.exp_ne_zero _
  rw [he]
  simp only [dA, dB, zLow, zMid, zTop, blkB, Finset.mem_compl, exp_neg_I]
  by_cases hr : r ∈ blkA j <;> by_cases hs : s ∈ blkA j <;>
    simp [hr, hs, fromBlocks_smul, fromBlocks_add, fromBlocks_neg, smul_single, fromBlocks_inj]
  all_goals constructor <;> congr 1 <;> field_simp <;> ring

end PositivityTheory.Rg.Sw.LVs.TC
