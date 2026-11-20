import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.IsCoreMod

open Finset

namespace GlobalTheory.CompanionTheory.LevelCompress

open PositivityTheory.RgBcC.RealD

variable {n : ℕ}

def lowCount (lev : Fin n → ℕ) (a : Fin n) : ℕ := (univ.filter fun b => lev b < lev a).card

/- English proof (translation)
Establish `h : (univ.filter fun b => lev b < lev a).card < (univ : Finset (Fin n)).card` using `Finset.card_lt_card (Finset.filter_ssubset.2 ⟨a, Finset.mem_univ a, lt_irrefl (lev a)⟩)`. Rewrite `h` using `[Finset.card_univ, Fintype.card_fin]`. Conclude with `h`.
-/
theorem lowCount_lt (lev : Fin n → ℕ) (a : Fin n) : lowCount lev a < n := by
  have h : (univ.filter fun b => lev b < lev a).card < (univ : Finset (Fin n)).card :=
    Finset.card_lt_card (Finset.filter_ssubset.2 ⟨a, Finset.mem_univ a, lt_irrefl (lev a)⟩)
  rw [Finset.card_univ, Fintype.card_fin] at h
  exact h

/- English proof (translation)
Unfold `lowCount`. Apply `Finset.card_le_card` to reduce the goal to its premises. Introduce `c hc`. Simplify using `only [Finset.mem_filter] at hc ⊢`. Conclude with `⟨hc.1, lt_of_lt_of_le hc.2 h⟩`.
-/
theorem lowCount_le_of_le {lev : Fin n → ℕ} {a b : Fin n} (h : lev a ≤ lev b) :
    lowCount lev a ≤ lowCount lev b := by
  unfold lowCount
  apply Finset.card_le_card
  intro c hc
  simp only [Finset.mem_filter] at hc ⊢
  exact ⟨hc.1, lt_of_lt_of_le hc.2 h⟩

/- English proof (translation)
Unfold `lowCount`. Apply `Finset.card_lt_card` to reduce the goal to its premises. Rewrite using `[Finset.ssubset_iff_of_subset]`. Use `⟨a, ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [Finset.mem_filter]`.

Conclude with `⟨Finset.mem_univ a, h⟩`. Simplify using `only [Finset.mem_filter, lt_irrefl, and_false, not_false_eq_true]`. Introduce `c hc`. Simplify using `only [Finset.mem_filter] at hc ⊢`. Conclude with `⟨hc.1, hc.2.trans h⟩`.
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
Prove the components needed by the constructor for the conclusion. Introduce `h`. Assume the negation of the conclusion as `h'`. Conclude with `absurd h (not_lt.2 (lowCount_le_of_le (not_lt.1 h')))`. Conclude with `lowCount_lt_of_lt`.
-/
theorem lowCount_lt_iff {lev : Fin n → ℕ} {a b : Fin n} :
    lowCount lev a < lowCount lev b ↔ lev a < lev b := by
  constructor
  · intro h
    by_contra h'
    exact absurd h (not_lt.2 (lowCount_le_of_le (not_lt.1 h')))
  · exact lowCount_lt_of_lt

/- English proof (translation)
Use function extensionality and compare the values at `a`. Simplify using `only [rhoU, lowCount_lt_iff]`.
-/
theorem rhoU_lowCount (lev : Fin n → ℕ) : rhoU (lowCount lev) = rhoU lev := by
  funext a
  simp only [rhoU, lowCount_lt_iff]

/- English proof (translation)
Unfold `muQ`. Rewrite using `[rhoU_lowCount]`.
-/
theorem muQ_lowCount (lam : Fin n → ℤ) (lev : Fin n → ℕ) : muQ lam (lowCount lev) = muQ lam lev := by
  unfold muQ
  rw [rhoU_lowCount]

/- English proof (translation)
Use `⟨fun a b hab => lowCount_le_of_le (h.1 hab), fun a b hab => h.2 a b ?_⟩` and prove the remaining obligations. Break down `lt_trichotomy (lev a) (lev b) with h1 | h1 | h1` into its components or cases. Conclude with `absurd hab (ne_of_lt (lowCount_lt_of_lt h1))`. Conclude with `h1`. Conclude with `absurd hab (ne_of_gt (lowCount_lt_of_lt h1))`.
-/
theorem isLev_lowCount {lam : Fin n → ℤ} {lev : Fin n → ℕ} (h : IsLev lam lev) :
    IsLev lam (lowCount lev) := by
  refine ⟨fun a b hab => lowCount_le_of_le (h.1 hab), fun a b hab => h.2 a b ?_⟩
  rcases lt_trichotomy (lev a) (lev b) with h1 | h1 | h1
  · exact absurd hab (ne_of_lt (lowCount_lt_of_lt h1))
  · exact h1
  · exact absurd hab (ne_of_gt (lowCount_lt_of_lt h1))

/- English proof (translation)
Conclude with `⟨fun a => ⟨lowCount lev a, lowCount_lt lev a⟩, isLev_lowCount h, muQ_lowCount lam lev⟩`.
-/
theorem exists_compress (lam : Fin n → ℤ) (lev : Fin n → ℕ) (h : IsLev lam lev) :
    ∃ l : Fin n → Fin n, (IsLev lam fun a => (l a : ℕ)) ∧ (muQ lam fun a => (l a : ℕ)) = muQ lam lev := by
  exact ⟨fun a => ⟨lowCount lev a, lowCount_lt lev a⟩, isLev_lowCount h, muQ_lowCount lam lev⟩

/- English proof (translation)
Take `⟨l, hl, he⟩` from `exists_compress lam lev h`. Unfold `harmSet`. Rewrite using `[Finset.mem_image]`. Use `⟨l, ?_, he⟩` and prove the remaining obligations. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and]`.

Conclude with `hl`.
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
