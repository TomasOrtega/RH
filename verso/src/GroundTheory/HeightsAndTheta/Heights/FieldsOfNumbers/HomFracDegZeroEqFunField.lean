import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PfContractedHypothesesExample
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

section

variable {F : Type*} [Field F] {K : Type*} {ι : K → Type*}

/- English proof (translation)
Unfold `relDim IndefiniteRowSideFullHecke.FieldNumbers.HasRelDim`. Generalize the expression as in `ringKrullDim (MRing ι F ⧸ I) = x`. Establish `e1 : ((n : ℕ) : WithBot (WithTop ℤ)) = some (some (n : ℤ))` using `rfl`. Establish `e2 : ((n + Fintype.card K : ℕ) : WithBot ℕ∞) = some (some (n + Fintype.card K))` using `rfl`. Rewrite using `[e1, e2]`.

Break down `x with _ | _ | e` into its components or cases. Simplify using `[WithBot.map]`. Simplify using `only [WithBot.map, WithTop.map, Option.map]`. Conclude with `⟨fun h => (nomatch h), fun h => (nomatch h)⟩`. Simplify using `only [WithBot.map, WithTop.map, Option.map]`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h1 : (e : ℤ) - Fintype.card K = n` using `Option.some.inj (Option.some.inj h)`. Establish `h2 : e = n + Fintype.card K` using `by omega`. Rewrite using `[h2]`.

Conclude with `rfl`. Introduce `h`. Establish `h1 : e = n + Fintype.card K` using `Option.some.inj (Option.some.inj h)`. Substitute `h1` using the available equality. Use `congr 2`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem relDim_eq_iff_hasRelDim [Fintype K] (I : Ideal (MRing ι F)) (n : ℕ) :
    relDim I = (n : WithBot (WithTop ℤ)) ↔ IndefiniteRowSideFullHecke.FieldNumbers.HasRelDim I n := by
  unfold relDim IndefiniteRowSideFullHecke.FieldNumbers.HasRelDim
  generalize ringKrullDim (MRing ι F ⧸ I) = x
  have e1 : ((n : ℕ) : WithBot (WithTop ℤ)) = some (some (n : ℤ)) := rfl
  have e2 : ((n + Fintype.card K : ℕ) : WithBot ℕ∞) = some (some (n + Fintype.card K)) := rfl
  rw [e1, e2]
  rcases x with _ | _ | e
  · simp [WithBot.map]
  · simp only [WithBot.map, WithTop.map, Option.map]
    exact ⟨fun h => (nomatch h), fun h => (nomatch h)⟩
  · simp only [WithBot.map, WithTop.map, Option.map]
    constructor
    · intro h
      have h1 : (e : ℤ) - Fintype.card K = n := Option.some.inj (Option.some.inj h)
      have h2 : e = n + Fintype.card K := by omega
      rw [h2]
      exact rfl
    · intro h
      have h1 : e = n + Fintype.card K := Option.some.inj (Option.some.inj h)
      subst h1
      congr 2
      push_cast
      ring

variable [DecidableEq K]

end

end GroundTheory.Heights₂.Heights.FieldNumbers
