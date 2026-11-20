import Mathlib

namespace GlobalTheory.CompanionTheory.NumberFieldMatrix

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem countable_of_numberField (E : Type) [Field E] [NumberField E] : Countable E :=
  (Module.finBasis ℚ E).equivFun.injective.countable

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem countable_matrix (E : Type) [Field E] [NumberField E] (m n : ℕ) :
    Countable (Matrix (Fin m) (Fin n) E) := by
  haveI := GlobalTheory.CompanionTheory.NumberFieldMatrix.countable_of_numberField E
  exact inferInstanceAs (Countable (Fin m → Fin n → E))

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem matrix_countable :
    ∀ (E : Type) [Field E] [NumberField E] (m n : ℕ),
      Countable (Matrix (Fin m) (Fin n) E) :=
  fun E _ _ m n => countable_matrix E m n

end GlobalTheory.CompanionTheory.NumberFieldMatrix
