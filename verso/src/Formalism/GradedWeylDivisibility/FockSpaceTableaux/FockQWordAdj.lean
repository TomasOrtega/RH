import Formalism.GradedWeylDivisibility.StatementE

open MvPolynomial

namespace Formalism.GradedWeylDivisibility

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma leadj_applyWord_cons {r n : ℕ} (x : Fin r × Fin r × ℕ) (w : List (Fin r × Fin r × ℕ))
    (F : MvPolynomial (Fin r × Fin n) ℚ) :
    applyWord ℚ (x :: w) F = rowDiv ℚ x.1 x.2.1 x.2.2 (applyWord ℚ w F) := by
  rfl

/- English proof (translation)
Unfold `applyWord`. Rewrite using `[List.foldr_append]`.
-/
lemma leadj_applyWord_append {r n : ℕ} (l1 l2 : List (Fin r × Fin r × ℕ))
    (F : MvPolynomial (Fin r × Fin n) ℚ) :
    applyWord ℚ (l1 ++ l2) F = applyWord ℚ l1 (applyWord ℚ l2 F) := by
  unfold applyWord
  rw [List.foldr_append]

/- English proof (translation)
Simplify using `[transposeWord]`.
-/
lemma leadj_transposeWord_cons {r : ℕ} (x : Fin r × Fin r × ℕ) (w : List (Fin r × Fin r × ℕ)) :
    transposeWord (x :: w) = transposeWord w ++ [(x.2.1, x.1, x.2.2)] := by
  simp [transposeWord]

/- English proof (translation)
Introduce `r n w`. Proceed by induction on `w with`. Consider the case `nil => intro F G`. Simplify using `[applyWord, transposeWord]`. Consider the case `cons x w ih`.

Introduce `F G`. Rewrite using `[leadj_applyWord_cons, fockQRowDivAdj, ih, leadj_transposeWord_cons, leadj_applyWord_append]`. Simplify using `[applyWord]`.
-/
theorem fock_space_word_adjoint : FockQWordAdj := by
  intro r n w
  induction w with
  | nil => intro F G; simp [applyWord, transposeWord]
  | cons x w ih =>
    intro F G
    rw [leadj_applyWord_cons, fockQRowDivAdj, ih, leadj_transposeWord_cons, leadj_applyWord_append]
    simp [applyWord]

end Formalism.GradedWeylDivisibility
