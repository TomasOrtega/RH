import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.IsCoreMod

open Finset

namespace GlobalTheory.CompanionTheory.LevelCompress

open PositivityTheory.RgBcC.RealD

variable {n : ℕ}

def lowCount (lev : Fin n → ℕ) (a : Fin n) : ℕ := (univ.filter fun b => lev b < lev a).card

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem lowCount_lt (lev : Fin n → ℕ) (a : Fin n) : lowCount lev a < n := by
  have h : (univ.filter fun b => lev b < lev a).card < (univ : Finset (Fin n)).card :=
    Finset.card_lt_card (Finset.filter_ssubset.2 ⟨a, Finset.mem_univ a, lt_irrefl (lev a)⟩)
  rw [Finset.card_univ, Fintype.card_fin] at h
  exact h

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Supply the required witnesses or components.
-/
theorem lowCount_le_of_le {lev : Fin n → ℕ} {a b : Fin n} (h : lev a ≤ lev b) :
    lowCount lev a ≤ lowCount lev b := by
  unfold lowCount
  apply Finset.card_le_card
  intro c hc
  simp only [Finset.mem_filter] at hc ⊢
  exact ⟨hc.1, lt_of_lt_of_le hc.2 h⟩

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.

Supply the required witnesses or components. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Supply the required witnesses or components.
-/
theorem lowCount_lt_of_lt {lev : Fin n → ℕ} {a b : Fin n} (h : lev a < lev b) :
    lowCount lev a < lowCount lev b := by
  unfold lowCount
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨a, ?_, ?_⟩
    · simp only [Finset.mem_filter]
      exact ⟨Finset.mem_univ a, h⟩
    · simp only [Finset.mem_filter, lt_irrefl, and_false, not_false_eq_true]
  · intro c hc
    simp only [Finset.mem_filter] at hc ⊢
    exact ⟨hc.1, hc.2.trans h⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction. A detailed English derivation is pending.
-/
theorem lowCount_lt_iff {lev : Fin n → ℕ} {a b : Fin n} :
    lowCount lev a < lowCount lev b ↔ lev a < lev b := by
  constructor
  · intro h
    by_contra h'
    exact absurd h (not_lt.2 (lowCount_le_of_le (not_lt.1 h')))
  · exact lowCount_lt_of_lt

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.
-/
theorem rhoU_lowCount (lev : Fin n → ℕ) : rhoU (lowCount lev) = rhoU lev := by
  funext a
  simp only [rhoU, lowCount_lt_iff]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
theorem muQ_lowCount (lam : Fin n → ℤ) (lev : Fin n → ℕ) : muQ lam (lowCount lev) = muQ lam lev := by
  unfold muQ
  rw [rhoU_lowCount]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Separate the alternatives or extract the components of the hypothesis. A detailed English derivation is pending.
-/
theorem isLev_lowCount {lam : Fin n → ℤ} {lev : Fin n → ℕ} (h : IsLev lam lev) :
    IsLev lam (lowCount lev) := by
  refine ⟨fun a b hab => lowCount_le_of_le (h.1 hab), fun a b hab => h.2 a b ?_⟩
  rcases lt_trichotomy (lev a) (lev b) with h1 | h1 | h1
  · exact absurd hab (ne_of_lt (lowCount_lt_of_lt h1))
  · exact h1
  · exact absurd hab (ne_of_gt (lowCount_lt_of_lt h1))

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem exists_compress (lam : Fin n → ℤ) (lev : Fin n → ℕ) (h : IsLev lam lev) :
    ∃ l : Fin n → Fin n, (IsLev lam fun a => (l a : ℕ)) ∧ (muQ lam fun a => (l a : ℕ)) = muQ lam lev := by
  exact ⟨fun a => ⟨lowCount lev a, lowCount_lt lev a⟩, isLev_lowCount h, muQ_lowCount lam lev⟩

/- English proof (translation)
Extract witnesses or component facts from the available result. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem muQ_mem_harmSet {lam : Fin n → ℤ} {lev : Fin n → ℕ} (h : IsLev lam lev) :
    muQ lam lev ∈ harmSet lam := by
  obtain ⟨l, hl, he⟩ := exists_compress lam lev h
  unfold harmSet
  rw [Finset.mem_image]
  refine ⟨l, ?_, he⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact hl

end GlobalTheory.CompanionTheory.LevelCompress
