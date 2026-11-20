import Mathlib
import Formalism.GradedWeylDivisibility.StatementE

open MvPolynomial Formalism.GradedWeylDivisibility

namespace GlobalTheory.FockAdj

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Both sides reduce to the same expression. Treat this case separately.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem fockQ_applyWord : Formalism.GradedWeylDivisibility.FockQWordAdj := by
  intro r n w
  induction w with
  | nil => intro F G; rfl
  | cons x w ih =>
    intro F G
    have h1 : applyWord ℚ (x :: w) F = rowDiv ℚ x.1 x.2.1 x.2.2 (applyWord ℚ w F) := rfl
    have h2 : applyWord ℚ (transposeWord (x :: w)) G =
        applyWord ℚ (transposeWord w) (rowDiv ℚ x.2.1 x.1 x.2.2 G) := by
      simp [applyWord, transposeWord, List.foldr_append]
    rw [h1, h2, fockQRowDivAdj, ih]

/- English proof (translation)
Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem map_rowAct {r n : ℕ} (g : Matrix (Fin r) (Fin r) ℚ) (f : MvPolynomial (Fin r × Fin n) ℚ) :
    map (Rat.castHom ℂ) (rowAct ℚ g f) =
      rowAct ℂ (g.map (Rat.castHom ℂ)) (map (Rat.castHom ℂ) f) := by
  have : (map (Rat.castHom ℂ)).comp (rowAct ℚ (n := n) g).toRingHom =
      (rowAct ℂ (n := n) (g.map (Rat.castHom ℂ))).toRingHom.comp (map (Rat.castHom ℂ)) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [rowAct]
    · intro v
      simp [rowAct]
  exact congrArg (fun φ => φ f) this

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem fockQ_rowAct : Formalism.GradedWeylDivisibility.FockQRowAct := by
  intro r n g P Q
  have ht : (g.map (Rat.castHom ℂ)).conjTranspose = g.transpose.map (Rat.castHom ℂ) := by
    ext i j
    simp [Matrix.conjTranspose_apply]
  have h : ((fockQ (rowAct ℚ g P) Q : ℚ) : ℂ) = ((fockQ P (rowAct ℚ g.transpose Q) : ℚ) : ℂ) := by
    rw [lfockq_cast, lfockq_cast, map_rowAct, map_rowAct, fockRowAdj, ht]
  exact_mod_cast h

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem fockQ_word_rowAct_adj : Formalism.GradedWeylDivisibility.FockQWordAdj ∧ Formalism.GradedWeylDivisibility.FockQRowAct :=
  ⟨fockQ_applyWord, fockQ_rowAct⟩

end GlobalTheory.FockAdj
