import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.RingKrullDimLocalizationQuotientEqHeight

namespace ReciprocityTheory.CA

open IsLocalRing

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Reduce the argument to an intermediate assertion.

Proceed by induction. Treat this case separately. Treat this case separately. Proceed by induction. Treat this case separately.

Treat this case separately. Proceed by induction. Treat this case separately. Treat this case separately. Proceed by induction.

Treat this case separately. Treat this case separately. Put the expressions in a common number system so they can be compared. Use linear arithmetic over natural numbers and integers.
-/
theorem dimFormula_arith (a b : ℕ∞) (c d : WithBot ℕ∞) (n : ℕ) (hc : c ≠ ⊥) (hd : d ≠ ⊥)
    (h1 : ((a + b : ℕ∞) : WithBot ℕ∞) + c = n) (h2 : (a : WithBot ℕ∞) + d = n) :
    (b : WithBot ℕ∞) + c = d := by
  obtain ⟨c, rfl⟩ := WithBot.ne_bot_iff_exists.mp hc
  obtain ⟨d, rfl⟩ := WithBot.ne_bot_iff_exists.mp hd
  have e1 : a + b + c = (n : ℕ∞) := by exact_mod_cast h1
  have e2 : a + d = (n : ℕ∞) := by exact_mod_cast h2
  suffices e3 : b + c = d by exact_mod_cast e3
  induction a using ENat.recTopCoe with
  | top => simp at e2
  | coe a =>
    induction d using ENat.recTopCoe with
    | top => simp at e2
    | coe d =>
      induction b using ENat.recTopCoe with
      | top => simp at e1
      | coe b =>
        induction c using ENat.recTopCoe with
        | top => simp at e1
        | coe c =>
          norm_cast at e1 e2 ⊢
          omega

end ReciprocityTheory.CA
