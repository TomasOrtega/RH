import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonemptyGrpData
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonemptyFockModelOfUnitaryPairCoversStatement
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

namespace GlobalTheory

def realPlaceStdParam (p q : ℕ) : Ix p q → ℚ :=
  Sum.elim (fun i => -((i : ℕ) : ℚ)) (fun j => -(((p + j : ℕ)) : ℚ))

/- English proof (translation)
Separate the alternatives or extract the components of the hypothesis. Supply the required witnesses or components. Supply the required witnesses or components.
-/
theorem realPlaceStdParam_int (p q : ℕ) (a : Ix p q) :
    ∃ k : ℤ, realPlaceStdParam p q a = k := by
  rcases a with i | j
  · exact ⟨-((i : ℕ) : ℤ), by simp [realPlaceStdParam]⟩
  · exact ⟨-((p + j : ℕ) : ℤ), by simp [realPlaceStdParam]⟩

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Establish an intermediate fact.

Use linear arithmetic over natural numbers and integers. Simplify using the standard rewrite rules. Establish an intermediate fact. Use linear arithmetic over natural numbers and integers. Simplify using the standard rewrite rules.

Assume the hypotheses and unpack their components. Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact. Simplify using the standard rewrite rules.

Use linear arithmetic over natural numbers and integers. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Supply the required witnesses or components. Fix the arbitrary inputs or assume the hypotheses.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem realPlaceStdParam_isParam (p q : ℕ) : IsParam (realPlaceStdParam p q) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro (i | j) (i' | j') h
    · simp only [realPlaceStdParam, Sum.elim_inl, neg_inj, Nat.cast_inj] at h
      exact congrArg Sum.inl (Fin.ext h)
    · simp only [realPlaceStdParam, Sum.elim_inl, Sum.elim_inr, neg_inj, Nat.cast_inj] at h
      have := i.2
      omega
    · simp only [realPlaceStdParam, Sum.elim_inl, Sum.elim_inr, neg_inj, Nat.cast_inj] at h
      have := i'.2
      omega
    · simp only [realPlaceStdParam, Sum.elim_inr, neg_inj, Nat.cast_inj] at h
      exact congrArg Sum.inr (Fin.ext (by omega))
  · rintro (i | j) (i' | j') h
    · have h' : (i : ℕ) < i' := h
      simp only [realPlaceStdParam, Sum.elim_inl, neg_lt_neg_iff, Nat.cast_lt]
      exact h'
    · exact absurd h (by simp [posC])
    · exact absurd h (by simp [posC])
    · have h' : (j : ℕ) < j' := h
      simp only [realPlaceStdParam, Sum.elim_inr, neg_lt_neg_iff, Nat.cast_lt]
      omega
  · intro a
    obtain ⟨k, hk⟩ := realPlaceStdParam_int p q a
    exact ⟨2 * k, by rw [hk]; push_cast; ring⟩
  · intro a b
    obtain ⟨k, hk⟩ := realPlaceStdParam_int p q a
    obtain ⟨l, hl⟩ := realPlaceStdParam_int p q b
    exact ⟨k - l, by rw [hk, hl]; push_cast; ring⟩

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails.

Extract witnesses or component facts from the available result. Supply the required witnesses or components. Extract witnesses or component facts from the available result. Supply the required witnesses or components. Supply the required witnesses or components.

A detailed English derivation is pending.
-/
theorem exists_provA_of_forall_exists_hasParam :
    (∀ (p q : ℕ) (T : GrpData p q) (lam : Ix p q → ℚ), IsParam lam →
      ∃ R : DSRep T, Formalism.L2.Theta.HasParam R lam) →
    ∃ X : ProvA, ∀ (p q : ℕ) (lam : Ix p q → ℚ), IsParam lam →
      Formalism.L2.Theta.HasParam (X.ds p q lam) lam := by
  intro H
  classical
  let grp : ∀ p q : ℕ, GrpData p q := fun p q => Classical.choice (GlobalTheory.DetSqrtCover.nonempty_grpData p q)
  have key : ∀ (p q : ℕ) (lam : Ix p q → ℚ), ∃ R : DSRep (grp p q),
      IsParam lam → Formalism.L2.Theta.HasParam R lam := by
    intro p q lam
    by_cases h : IsParam lam
    · obtain ⟨R, hR⟩ := H p q (grp p q) lam h
      exact ⟨R, fun _ => hR⟩
    · obtain ⟨R, -⟩ := H p q (grp p q) _ (realPlaceStdParam_isParam p q)
      exact ⟨R, fun h' => absurd h' h⟩
  choose ds hds using key
  exact ⟨⟨grp, fun p q r s => Classical.choice (GlobalTheory.T.nonempty_fockModel_of_unitary_pair_covers p q r s _ _ _), ds⟩, hds⟩

end GlobalTheory
