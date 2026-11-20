import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.RingKrullDimLocalizationQuotientEqHeight

namespace ReciprocityTheory.CA

open IsLocalRing

/- English proof (translation)
Take `⟨c, rfl⟩` from `WithBot.ne_bot_iff_exists.mp hc`. Take `⟨d, rfl⟩` from `WithBot.ne_bot_iff_exists.mp hd`. Establish `e1 : a + b + c = (n : ℕ∞)` using `by exact_mod_cast h1`. Establish `e2 : a + d = (n : ℕ∞)` using `by exact_mod_cast h2`. It suffices to establish `e3 : b + c = d by exact_mod_cast e3`.

Proceed by induction on `a using ENat.recTopCoe with`. Consider the case `top => simp at e2`. Consider the case `coe a`. Proceed by induction on `d using ENat.recTopCoe with`. Consider the case `top => simp at e2`.

Consider the case `coe d`. Proceed by induction on `b using ENat.recTopCoe with`. Consider the case `top => simp at e1`. Consider the case `coe b`. Proceed by induction on `c using ENat.recTopCoe with`.

Consider the case `top => simp at e1`. Consider the case `coe c`. Normalize the coercions in `at e1 e2 ⊢`. Use linear arithmetic over natural numbers and integers.
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
