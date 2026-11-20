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
Break down `a with i | j` into its components or cases. Conclude with `⟨-((i : ℕ) : ℤ), by simp [realPlaceStdParam]⟩`. Conclude with `⟨-((p + j : ℕ) : ℤ), by simp [realPlaceStdParam]⟩`.
-/
theorem realPlaceStdParam_int (p q : ℕ) (a : Ix p q) :
    ∃ k : ℤ, realPlaceStdParam p q a = k := by
  rcases a with i | j
  · exact ⟨-((i : ℕ) : ℤ), by simp [realPlaceStdParam]⟩
  · exact ⟨-((p + j : ℕ) : ℤ), by simp [realPlaceStdParam]⟩

/- English proof (translation)
Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `(i | j) (i' | j') h`. Simplify using `only [realPlaceStdParam, Sum.elim_inl, neg_inj, Nat.cast_inj] at h`. Conclude with `congrArg Sum.inl (Fin.ext h)`. Simplify using `only [realPlaceStdParam, Sum.elim_inl, Sum.elim_inr, neg_inj, Nat.cast_inj] at h`.

Use `i.2` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Simplify using `only [realPlaceStdParam, Sum.elim_inl, Sum.elim_inr, neg_inj, Nat.cast_inj] at h`. Use `i'.2` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Simplify using `only [realPlaceStdParam, Sum.elim_inr, neg_inj, Nat.cast_inj] at h`. Conclude with `congrArg Sum.inr (Fin.ext (by omega))`. Introduce and unpack `(i | j) (i' | j') h`. Establish `h' : (i : ℕ) < i'` using `h`. Simplify using `only [realPlaceStdParam, Sum.elim_inl, neg_lt_neg_iff, Nat.cast_lt]`.

Conclude with `h'`. Conclude with `absurd h (by simp [posC])`. Conclude with `absurd h (by simp [posC])`. Establish `h' : (j : ℕ) < j'` using `h`. Simplify using `only [realPlaceStdParam, Sum.elim_inr, neg_lt_neg_iff, Nat.cast_lt]`.

Use linear arithmetic over natural numbers and integers. Introduce `a`. Take `⟨k, hk⟩` from `realPlaceStdParam_int p q a`. Conclude with `⟨2 * k, by rw [hk]; push_cast; ring⟩`. Introduce `a b`.

Take `⟨k, hk⟩` from `realPlaceStdParam_int p q a`. Take `⟨l, hl⟩` from `realPlaceStdParam_int p q b`. Conclude with `⟨k - l, by rw [hk, hl]; push_cast; ring⟩`.
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
Introduce `H`. Set `grp : ∀ p q : ℕ, GrpData p q` to `fun p q => Classical.choice (GlobalTheory.DetSqrtCover.nonempty_grpData p q)`. Establish `key : ∀ (p q : ℕ) (lam : Ix p q → ℚ), ∃ R : DSRep (grp p q), IsParam lam → Formalism.L2.Theta.HasParam R lam`. Introduce `p q lam`. Distinguish the cases in `h : IsParam lam`.

Take `⟨R, hR⟩` from `H p q (grp p q) lam h`. Conclude with `⟨R, fun _ => hR⟩`. Take `⟨R, -⟩` from `H p q (grp p q) _ (realPlaceStdParam_isParam p q)`. Conclude with `⟨R, fun h' => absurd h' h⟩`. Use `choose ds hds using key`.

Conclude with `⟨⟨grp, fun p q r s => Classical.choice (GlobalTheory.T.nonempty_fockModel_of_unitary_pair_covers p q r s _ _ _), ds⟩, hds⟩`.
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
