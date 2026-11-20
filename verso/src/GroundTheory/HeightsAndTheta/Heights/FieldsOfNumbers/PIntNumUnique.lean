import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsDivSupport
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Substitute using the available equality. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Simplify using the standard rewrite rules. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument.

Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Replace the relevant objects with their definitions. Consider separately whether the proposition holds or fails.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem IntNumUnique.proof (h1 : CutRational.Statement.{u}) (h2 : IntNumBase.Statement.{u})
    (h3 : ExistsForm.Statement.{u}) (h4 : DivCycleSupport.Statement.{u}) :
    IntNumUnique.Statement.{u} := by
  intro F _ K _ _ ι _ N hN P hP n
  induction n generalizing P with
  | zero =>
    intro hdim bs
    have hbs : bs = ![] := Subsingleton.elim _ _
    subst hbs
    rw [hN.base P hP hdim]
    obtain ⟨-, h⟩ := h2 F K ι P hP hdim
    rw [h]
    have := hP.isPrime
    simp [resDeg, hP.isPrime]
  | succ n ih =>
    intro hdim bs
    obtain ⟨bf, bg, f, g, hf, hg, hfP, hgP, hb⟩ := h3 F K ι P hP (bs (Fin.last n))
    have hbs : bs = Fin.snoc (α := fun _ => K → ℤ) (Fin.init bs) (fun k => (bf k : ℤ) - bg k) := by
      rw [hb, Fin.snoc_init_self]
    rw [hbs, hN.cut P n hP hdim bf bg f g hf hg hfP hgP,
      h1 F K ι P hP n hdim bf bg f g hf hg hfP hgP]
    unfold cycEval
    congr 1
    funext W
    by_cases hW : ratDiv P f g W = 0
    · rw [hW, zero_mul, zero_mul]
    · have hsupp : IsMultiProjPrime W ∧ relDim W = (n : ℕ) := by
        unfold ratDiv at hW
        by_cases hfW : divCycle P f W = 0
        · have hgW : divCycle P g W ≠ 0 := by
            intro h
            apply hW
            rw [hfW, h, sub_zero]
          exact h4 F K ι P hP n hdim bg g hg hgP W hgW
        · exact h4 F K ι P hP n hdim bf f hf hfP W hfW
      simp only [ih W hsupp.1 hsupp.2]

end

end GroundTheory.Heights₂.Heights.FieldNumbers
