import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.IsStarRep
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GelfandInvariantsCentralCharacter
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GelfValTwoEqCvalR

open Finset Formalism.REAL

namespace PositivityTheory.Rg.Cz.J

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Move the embeddings inside the algebraic operations. Take a linear combination of the given relations to obtain the conclusion.
-/
theorem natSub_cast {n : ℕ} (k : Fin n) : ((n - 1 - (k : ℕ) : ℕ) : ℂ) = (n : ℂ) - 1 - ((k : ℕ) : ℂ) := by
  have h' : (n - 1 - (k : ℕ) : ℕ) + (k : ℕ) + 1 = n := by omega
  have := congrArg (Nat.cast (R := ℂ)) h'
  push_cast at this
  linear_combination this

/- English proof (translation)
Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules. Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem gelfVal_one_eq {n : ℕ} (χ : Fin n → ℂ) :
    GlobalTheory.Dec.gelfVal χ 1 = ∑ a : Fin n, (χ a + ((n : ℂ) - 1) / 2 - ((n - 1 - (a : ℕ) : ℕ) : ℂ)) := by
  simp only [GlobalTheory.Dec.gelfVal, pow_one]
  refine Finset.sum_congr rfl fun a _ => ?_
  have e : ∀ b : Fin n, (Amat (fun c => χ c + ((n : ℂ) - 1) / 2)) a b =
      (if a = b then χ a + ((n : ℂ) - 1) / 2 else 0) - (if b ∈ Finset.Ioi a then 1 else 0) := by
    intro b
    simp only [Amat, Matrix.of_apply, Finset.mem_Ioi]
    by_cases h1 : a = b
    · subst h1; simp
    · by_cases h2 : a < b
      · simp [h1, h2]
      · simp [h1, h2]
  simp only [e, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_ite_mem,
    Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, Fin.card_Ioi, mul_one]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.

Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem casVal_holds : CasVal := by
  intro n M _ _ F l hF hC
  set χ : Fin n → ℂ := fun k => l k + ((n : ℂ) - 1) / 2 with hχ
  have hq : ∀ u : ℂ, qdet F (u + ((n : ℂ) - 1) / 2) =
      algebraMap ℂ (Module.End ℂ M) (∏ s, (u + χ s)) := by
    intro u
    rw [hC]
    congr 1
    refine Finset.prod_congr rfl fun s _ => ?_
    simp only [hχ]
    ring
  have h1 := GlobalTheory.GelfandOfCapelli.gelfand_of_capelli (Module.End ℂ M) n F χ hF hq 0
  have h2 := GlobalTheory.GelfandOfCapelli.gelfand_of_capelli (Module.End ℂ M) n F χ hF hq 1
  refine ⟨?_, ?_⟩
  · have e : etr F (0 + 1) = ∑ i, F i i := by
      simp [etr, epow]
    rw [← e, h1]
    congr 1
    rw [zero_add, gelfVal_one_eq]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [natSub_cast k]
    simp only [hχ]
    ring
  · have e : etr F (1 + 1) = ∑ i, ∑ j, F i j * F j i := by
      simp [etr, epow, ite_mul, Finset.sum_ite_eq]
    rw [← e, h2]
    congr 1
    rw [show (1 + 1 : ℕ) = 2 from rfl, GlobalTheory.CasimirEigen.gelfVal_two_eq, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hχ, Formalism.QuantumDeterminants.rhoStd]
    push_cast
    ring

end PositivityTheory.Rg.Cz.J
