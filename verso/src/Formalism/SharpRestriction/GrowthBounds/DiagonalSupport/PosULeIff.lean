import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.FrMemLetters

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Proposition5Numerics

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords
open Formalism.MainNotions.G.WittFrameLocaliserOrders Formalism.MainNotions.G.symbolGeneratorData

section Ord2

variable {n' r : ℕ} [NeZero n'] {Fr : Frames n' r} {L₁ N₁ : ℕ}

/- English proof (translation)
Substitute using the available equality. A detailed English derivation is pending.
-/
theorem posU_lt_iff' (hV : Fr.Valid L₁ N₁) (j : ℤ) (N : ℕ) (hN : N = (Fr.LLset j).card) (a b : ℕ) (ha : a < N + r)
    (hb : b < N + r) : posU Fr N j a < posU Fr N j b ↔ a < b := by
  subst hN; exact posU_lt_iff hV j a b ha hb

/- English proof (translation)
Substitute using the available equality. A detailed English derivation is pending.
-/
theorem posU_le_iff' (hV : Fr.Valid L₁ N₁) (j : ℤ) (N : ℕ) (hN : N = (Fr.LLset j).card) (a b : ℕ) (ha : a < N + r)
    (hb : b < N + r) : posU Fr N j a ≤ posU Fr N j b ↔ a ≤ b := by
  subst hN; exact posU_le_iff hV j a b ha hb

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
theorem posU_ll' (j : ℤ) (N : ℕ) (l : ℕ) (hl : l < N) : posU Fr N j l = llPos Fr j l := by
  unfold posU
  rw [if_pos hl]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
theorem posU_fr' (j : ℤ) (N : ℕ) (i : ℕ) : posU Fr N j (N + i) = Fr.fr j i := by
  unfold posU
  rw [if_neg (by omega), Nat.add_sub_cancel_left]

/- English proof (translation)
Substitute using the available equality. A detailed English derivation is pending.
-/
theorem w_lt_posU' (hV : Fr.Valid L₁ N₁) (hr : 1 ≤ r) (j : ℤ) (N : ℕ) (hN : N = (Fr.LLset j).card) (i u : ℕ) (hi : i < r)
    (hu : u < N + r) : Fr.fr (j - 1) i < posU Fr N j u := by
  subst hN; exact w_lt_posU hV hr j i u hi hu

end Ord2

section Pre

variable {n' r : ℕ} [NeZero n'] {Fr : Frames n' r} {L₁ N₁ : ℕ} {J : ℕ} {nL : ZMod J → ℕ}

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Rewrite the indicated hypotheses using the stated equalities. Assume the hypotheses and unpack their components.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem ml_ll_lt (hV : Fr.Valid L₁ N₁) (hnL : ∀ j, nL j = (Fr.LLset (segZ j)).card) (j : ZMod J) (u : ℕ)
    (hu : u < nL j + r) (j' : ZMod J) (l : Fin (nL j')) :
    mlPos Fr nL (ML.ll j' l) ∈ SLt j (posU Fr (nL j) (segZ j) u) ↔ j' = j ∧ l.val < u := by
  show (j' = j ∧ llPos Fr (segZ j') l.val < _) ↔ _
  constructor
  · rintro ⟨rfl, h⟩
    refine ⟨rfl, ?_⟩
    rw [← posU_ll' (Fr := Fr) (segZ j') (nL j') l.val l.isLt] at h
    exact (posU_lt_iff' hV (segZ j') (nL j') (hnL j') l.val u (by omega) hu).mp h
  · rintro ⟨rfl, h⟩
    refine ⟨rfl, ?_⟩
    rw [← posU_ll' (Fr := Fr) (segZ j') (nL j') l.val l.isLt]
    exact (posU_lt_iff' hV (segZ j') (nL j') (hnL j') l.val u (by omega) hu).mpr h

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Rewrite the indicated hypotheses using the stated equalities. Assume the hypotheses and unpack their components.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem ml_ll_le (hV : Fr.Valid L₁ N₁) (hnL : ∀ j, nL j = (Fr.LLset (segZ j)).card) (j : ZMod J) (u : ℕ)
    (hu : u < nL j + r) (j' : ZMod J) (l : Fin (nL j')) :
    mlPos Fr nL (ML.ll j' l) ∈ SLe j (posU Fr (nL j) (segZ j) u) ↔ j' = j ∧ l.val ≤ u := by
  show (j' = j ∧ llPos Fr (segZ j') l.val ≤ _) ↔ _
  constructor
  · rintro ⟨rfl, h⟩
    refine ⟨rfl, ?_⟩
    rw [← posU_ll' (Fr := Fr) (segZ j') (nL j') l.val l.isLt] at h
    exact (posU_le_iff' hV (segZ j') (nL j') (hnL j') l.val u (by omega) hu).mp h
  · rintro ⟨rfl, h⟩
    refine ⟨rfl, ?_⟩
    rw [← posU_ll' (Fr := Fr) (segZ j') (nL j') l.val l.isLt]
    exact (posU_le_iff' hV (segZ j') (nL j') (hnL j') l.val u (by omega) hu).mpr h

/- English proof (translation)
Establish an intermediate fact. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Rewrite the indicated hypotheses using the stated equalities.

Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem fr_lt (hV : Fr.Valid L₁ N₁) (hnL : ∀ j, nL j = (Fr.LLset (segZ j)).card) (j : ZMod J) (u : ℕ)
    (hu : u < nL j + r) (j' : ZMod J) (m : Fin r) :
    (j' = j ∧ Fr.fr (segZ j') (r - 1 - m.val) < posU Fr (nL j) (segZ j) u) ↔ j' = j ∧ nL j + (r - 1 - m.val) < u := by
  have hm := m.isLt
  constructor
  · rintro ⟨rfl, h⟩
    refine ⟨rfl, ?_⟩
    rw [← posU_fr' (Fr := Fr) (segZ j') (nL j')] at h
    exact (posU_lt_iff' hV _ _ (hnL j') _ u (by omega) hu).mp h
  · rintro ⟨rfl, h⟩
    refine ⟨rfl, ?_⟩
    rw [← posU_fr' (Fr := Fr) (segZ j') (nL j')]
    exact (posU_lt_iff' hV _ _ (hnL j') _ u (by omega) hu).mpr h

/- English proof (translation)
Establish an intermediate fact. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Rewrite the indicated hypotheses using the stated equalities.

Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem fr_le (hV : Fr.Valid L₁ N₁) (hnL : ∀ j, nL j = (Fr.LLset (segZ j)).card) (j : ZMod J) (u : ℕ)
    (hu : u < nL j + r) (j' : ZMod J) (m : Fin r) :
    (j' = j ∧ Fr.fr (segZ j') (r - 1 - m.val) ≤ posU Fr (nL j) (segZ j) u) ↔ j' = j ∧ nL j + (r - 1 - m.val) ≤ u := by
  have hm := m.isLt
  constructor
  · rintro ⟨rfl, h⟩
    refine ⟨rfl, ?_⟩
    rw [← posU_fr' (Fr := Fr) (segZ j') (nL j')] at h
    exact (posU_le_iff' hV _ _ (hnL j') _ u (by omega) hu).mp h
  · rintro ⟨rfl, h⟩
    refine ⟨rfl, ?_⟩
    rw [← posU_fr' (Fr := Fr) (segZ j') (nL j')]
    exact (posU_le_iff' hV _ _ (hnL j') _ u (by omega) hu).mpr h

/- English proof (translation)
By extensionality, compare the relevant components. Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Prove the components needed by the constructor for the conclusion.

Assume the hypotheses and unpack their components. Prove the first alternative. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Split into cases according to the possible forms of the given data.

Supply the required witnesses or components. Extract witnesses or component facts from the available result. Split into cases according to the possible forms of the given data. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Prove the second alternative. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result.

Split into cases according to the possible forms of the given data. Extract witnesses or component facts from the available result. Split into cases according to the possible forms of the given data. Supply the required witnesses or components.
-/
theorem tl_pre_lt (hV : Fr.Valid L₁ N₁) (hnL : ∀ j, nL j = (Fr.LLset (segZ j)).card) (j : ZMod J) (u : ℕ)
    (hu : u < nL j + r) : tlPos Fr nL ⁻¹' SLt j (posU Fr (nL j) (segZ j) u) = NSet nL j u := by
  ext ⟨j', x⟩
  rcases x with l | m
  · rw [Set.mem_preimage]
    refine (ml_ll_lt hV hnL j u hu j' l).trans ?_
    constructor
    · rintro ⟨rfl, h⟩
      exact Or.inl ⟨l, rfl, h⟩
    · rintro (⟨l', he, h⟩ | ⟨m', he, _⟩)
      · obtain ⟨rfl, he2⟩ := Sigma.mk.inj_iff.mp he
        cases he2
        exact ⟨rfl, h⟩
      · obtain ⟨rfl, he2⟩ := Sigma.mk.inj_iff.mp he
        cases he2
  · rw [Set.mem_preimage]
    refine (fr_lt hV hnL j u hu j' m).trans ?_
    constructor
    · rintro ⟨rfl, h⟩
      exact Or.inr ⟨m, rfl, h⟩
    · rintro (⟨l', he, _⟩ | ⟨m', he, h⟩)
      · obtain ⟨rfl, he2⟩ := Sigma.mk.inj_iff.mp he
        cases he2
      · obtain ⟨rfl, he2⟩ := Sigma.mk.inj_iff.mp he
        cases he2
        exact ⟨rfl, h⟩

/- English proof (translation)
By extensionality, compare the relevant components. Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Prove the components needed by the constructor for the conclusion.

Assume the hypotheses and unpack their components. Prove the first alternative. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Split into cases according to the possible forms of the given data.

Supply the required witnesses or components. Extract witnesses or component facts from the available result. Split into cases according to the possible forms of the given data. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Prove the second alternative. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result.

Split into cases according to the possible forms of the given data. Extract witnesses or component facts from the available result. Split into cases according to the possible forms of the given data. Supply the required witnesses or components.
-/
theorem tl_pre_le (hV : Fr.Valid L₁ N₁) (hnL : ∀ j, nL j = (Fr.LLset (segZ j)).card) (j : ZMod J) (u : ℕ)
    (hu : u < nL j + r) : tlPos Fr nL ⁻¹' SLe j (posU Fr (nL j) (segZ j) u) = NSet nL j (u + 1) := by
  ext ⟨j', x⟩
  rcases x with l | m
  · rw [Set.mem_preimage]
    refine (ml_ll_le hV hnL j u hu j' l).trans ?_
    constructor
    · rintro ⟨rfl, h⟩
      exact Or.inl ⟨l, rfl, by omega⟩
    · rintro (⟨l', he, h⟩ | ⟨m', he, _⟩)
      · obtain ⟨rfl, he2⟩ := Sigma.mk.inj_iff.mp he
        cases he2
        exact ⟨rfl, by omega⟩
      · obtain ⟨rfl, he2⟩ := Sigma.mk.inj_iff.mp he
        cases he2
  · rw [Set.mem_preimage]
    refine (fr_le hV hnL j u hu j' m).trans ?_
    constructor
    · rintro ⟨rfl, h⟩
      exact Or.inr ⟨m, rfl, by omega⟩
    · rintro (⟨l', he, _⟩ | ⟨m', he, h⟩)
      · obtain ⟨rfl, he2⟩ := Sigma.mk.inj_iff.mp he
        cases he2
      · obtain ⟨rfl, he2⟩ := Sigma.mk.inj_iff.mp he
        cases he2
        exact ⟨rfl, by omega⟩

end Pre

end Formalism.MainNotions.Proposition5Numerics
