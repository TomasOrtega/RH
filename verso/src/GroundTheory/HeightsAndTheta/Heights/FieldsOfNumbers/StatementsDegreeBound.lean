import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsExamples
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

def EventuallyPolyUnique.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (h : (K → ℤ) → ℤ) (p q : MvPolynomial K ℚ),
    EventuallyPoly h p → EventuallyPoly h q → p = q

def EventuallyPolyShift.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (h : (K → ℤ) → ℤ) (p : MvPolynomial K ℚ) (c : K → ℤ),
    EventuallyPoly h p → ∃ q : MvPolynomial K ℚ,
      EventuallyPoly (fun m => h (m - c)) q ∧ q.totalDegree ≤ p.totalDegree ∧ (p = 0 → q = 0)

def HilbIrrelevantZero.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (I : Ideal (MRing ι F)), ¬ IsRelevant I →
    ∀ᶠ m in Filter.atTop, hilbFn I m = 0

def RelevantPrimeDimGe.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι F)), IsMultiProjPrime P →
    ((Fintype.card K : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (MRing ι F ⧸ P)

/- English proof (translation)
Assemble the required witnesses or components as `⟨eventuallyPoly_projectiveLine, eventuallyPoly_projectiveLine⟩`.
-/
theorem EventuallyPolyUnique.hypotheses_example :
    EventuallyPoly (hilbFn (⊥ : Ideal (MRing (ProjIdx 1) ℚ))) (X () + 1) ∧
      EventuallyPoly (hilbFn (⊥ : Ideal (MRing (ProjIdx 1) ℚ))) (X () + 1) :=
  ⟨eventuallyPoly_projectiveLine, eventuallyPoly_projectiveLine⟩

/- English proof (translation)
The claim follows from `eventuallyPoly_projectiveLine`.
-/
theorem EventuallyPolyShift.hypotheses_example :
    EventuallyPoly (hilbFn (⊥ : Ideal (MRing (ProjIdx 1) ℚ))) (X () + 1) :=
  eventuallyPoly_projectiveLine

/- English proof (translation)
Introduce `h`. Take `⟨i, hi⟩` from `h ()`. Conclude with `hi (Ideal.subset_span ⟨_, rfl⟩)`.
-/
theorem HilbIrrelevantZero.hypotheses_example :
    ¬ IsRelevant (Ideal.span (Set.range X) : Ideal (MRing (ProjIdx 1) ℚ)) := by
  intro h
  obtain ⟨i, hi⟩ := h ()
  exact hi (Ideal.subset_span ⟨_, rfl⟩)

/- English proof (translation)
The claim follows from `isMultiProjPrime_bot`.
-/
theorem RelevantPrimeDimGe.hypotheses_example :
    IsMultiProjPrime (⊥ : Ideal (MRing (ProjIdx 1) ℚ)) :=
  isMultiProjPrime_bot

end

end GroundTheory.Heights₂.Heights.FieldNumbers
