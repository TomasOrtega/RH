import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsMirClass
open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

namespace GlobalTheory

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero`. Introduce `j hj`. Establish `: σ j = σ i` using `Fin.ext (by simpa using hj)`. Rewrite using `[σ.injective this]`.

Conclude with `hi`. Consider the case `succ k ih`. Introduce `j hj`. Establish `hlt : (σ i : ℕ) + k < n` using `by have := (σ j).isLt; omega`. Establish `h1 : ((σ (σ.symm ⟨σ i + k, hlt⟩) : Fin n) : ℕ) = σ i + k` using `by simp`.

Establish `h2` using `ih _ h1`. Assume the negation of the conclusion as `hc`. Conclude with `h _ j h2 (not_lt.mp hc) (by omega)`.
-/
theorem shuffle_first_block_upper (a n : ℕ) (σ : Equiv.Perm (Fin n))
    (h : ∀ i j : Fin n, (i : ℕ) < a → a ≤ (j : ℕ) → (σ j : ℕ) ≠ σ i + 1)
    (i : Fin n) (hi : (i : ℕ) < a) (k : ℕ) :
    ∀ j : Fin n, (σ j : ℕ) = σ i + k → (j : ℕ) < a := by
  induction k with
  | zero =>
    intro j hj
    have : σ j = σ i := Fin.ext (by simpa using hj)
    rw [σ.injective this]; exact hi
  | succ k ih =>
    intro j hj
    have hlt : (σ i : ℕ) + k < n := by have := (σ j).isLt; omega
    have h1 : ((σ (σ.symm ⟨σ i + k, hlt⟩) : Fin n) : ℕ) = σ i + k := by simp
    have h2 := ih _ h1
    by_contra hc
    exact h _ j h2 (not_lt.mp hc) (by omega)

/- English proof (translation)
Introduce `a b n σ hn hmono`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `hup : ∀ i j : Fin n, (i : ℕ) < a → a ≤ (j : ℕ) → σ j < σ i`. Introduce `i j hi hj`.

Assume the negation of the conclusion as `hc`. Establish `hc' : (σ i : ℕ) ≤ σ j` using `not_lt.mp hc`. Use `shuffle_first_block_upper a n σ h i hi (σ j - σ i) j (by omega)` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Apply the tactic sequence `let ρ : Fin n → Fin n := fun k => ⟨if (k : ℕ) < b then a + k else k - b, by have := k.isLt; split_ifs <;> omega⟩`.

Establish `hρ : ∀ k, (ρ k : ℕ) = if (k : ℕ) < b then a + k else k - b` using `fun _ => rfl`. Establish `hs : StrictMono (fun k => σ (ρ k))`. Introduce `k l hkl`. Establish `hkl' : (k : ℕ) < l` using `hkl`. Establish `hk` using `hρ k`.

Establish `hl` using `hρ l`. Establish `hl2` using `l.isLt`. Use `show σ (ρ k) < σ (ρ l)`. Distinguish the cases in `h1 : (k : ℕ) < b`. Distinguish the cases in `h2 : (l : ℕ) < b`.

Rewrite `hk` using `[if_pos h1]`. Rewrite `hl` using `[if_pos h2]`. Conclude with `hmono _ _ (Fin.lt_def.mpr (by omega)) (Or.inr (by omega))`. Rewrite `hk` using `[if_pos h1]`. Rewrite `hl` using `[if_neg h2]`.

Conclude with `hup _ _ (by omega) (by omega)`. Establish `h2 : ¬ (l : ℕ) < b` using `by omega`. Rewrite `hk` using `[if_neg h1]`. Rewrite `hl` using `[if_neg h2]`. Conclude with `hmono _ _ (Fin.lt_def.mpr (by omega)) (Or.inl (by omega))`.

Establish `hid : ∀ k, σ (ρ k) = k` using `fun k => le_antisymm (hs.dual.le_apply (x := OrderDual.toDual k)) hs.le_apply`. Introduce `j`. Establish `hj` using `j.isLt`. Apply the tactic sequence `let k : Fin n := ⟨if (j : ℕ) < a then b + j else j - a, by split_ifs <;> omega⟩`. Establish `hk : (k : ℕ) = if (j : ℕ) < a then b + j else j - a` using `rfl`.

Establish `hjk : ρ k = j`. Apply `Fin.ext` to reduce the goal to its premises. Rewrite using `[hρ, hk]`. Apply the tactic sequence `split_ifs <;> omega`. Rewrite using `[← hk, ← hid k, hjk]`.

Introduce `h i j hi hj`. Establish `h1` using `h i`. Establish `h2` using `h j`. Use `j.isLt` as an intermediate fact. Rewrite `h1` using `[if_pos hi]`.

Rewrite `h2` using `[if_neg (by omega)]`. Use linear arithmetic over natural numbers and integers.
-/
theorem shuffle_noDescent_iff_open :
    ∀ (a b n : ℕ) (σ : Equiv.Perm (Fin n)), n = a + b → (∀ i j : Fin n, i < j → ((j : ℕ) < a ∨ a ≤ (i : ℕ)) → σ i < σ j) → ((∀ i j : Fin n, (i : ℕ) < a → a ≤ (j : ℕ) → (σ j : ℕ) ≠ σ i + 1) ↔ ∀ j : Fin n, (σ j : ℕ) = if (j : ℕ) < a then b + j else j - a) := by
  intro a b n σ hn hmono
  constructor
  · intro h
    have hup : ∀ i j : Fin n, (i : ℕ) < a → a ≤ (j : ℕ) → σ j < σ i := by
      intro i j hi hj
      by_contra hc
      have hc' : (σ i : ℕ) ≤ σ j := not_lt.mp hc
      have := shuffle_first_block_upper a n σ h i hi (σ j - σ i) j (by omega)
      omega
    let ρ : Fin n → Fin n := fun k =>
      ⟨if (k : ℕ) < b then a + k else k - b, by have := k.isLt; split_ifs <;> omega⟩
    have hρ : ∀ k, (ρ k : ℕ) = if (k : ℕ) < b then a + k else k - b := fun _ => rfl
    have hs : StrictMono (fun k => σ (ρ k)) := by
      intro k l hkl
      have hkl' : (k : ℕ) < l := hkl
      have hk := hρ k
      have hl := hρ l
      have hl2 := l.isLt
      show σ (ρ k) < σ (ρ l)
      by_cases h1 : (k : ℕ) < b
      · by_cases h2 : (l : ℕ) < b
        · rw [if_pos h1] at hk; rw [if_pos h2] at hl
          exact hmono _ _ (Fin.lt_def.mpr (by omega)) (Or.inr (by omega))
        · rw [if_pos h1] at hk; rw [if_neg h2] at hl
          exact hup _ _ (by omega) (by omega)
      · have h2 : ¬ (l : ℕ) < b := by omega
        rw [if_neg h1] at hk; rw [if_neg h2] at hl
        exact hmono _ _ (Fin.lt_def.mpr (by omega)) (Or.inl (by omega))
    have hid : ∀ k, σ (ρ k) = k := fun k =>
      le_antisymm (hs.dual.le_apply (x := OrderDual.toDual k)) hs.le_apply
    intro j
    have hj := j.isLt
    let k : Fin n := ⟨if (j : ℕ) < a then b + j else j - a, by split_ifs <;> omega⟩
    have hk : (k : ℕ) = if (j : ℕ) < a then b + j else j - a := rfl
    have hjk : ρ k = j := by
      apply Fin.ext
      rw [hρ, hk]
      split_ifs <;> omega
    rw [← hk, ← hid k, hjk]
  · intro h i j hi hj
    have h1 := h i
    have h2 := h j
    have := j.isLt
    rw [if_pos hi] at h1
    rw [if_neg (by omega)] at h2
    omega

end GlobalTheory
