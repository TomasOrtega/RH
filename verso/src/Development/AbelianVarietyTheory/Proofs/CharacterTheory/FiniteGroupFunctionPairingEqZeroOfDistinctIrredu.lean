import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
namespace GlobalTheory.BI

/- English proof (translation)
Introduce `G _ _ a b ha hb hab`. Take `⟨n, ρ, hρ, ha⟩` from `ha`. Take `⟨m, σ, hσ, hb⟩` from `hb`. Use `hρ` as an intermediate fact. Use `hσ` as an intermediate fact.

Use `Fintype.ofFinite G` as an intermediate fact. Establish `: Invertible (Nat.card G : ℂ)` using `invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')`. Establish `ha' : a = ρ.character` using `funext fun g => by simp [ha]`. Establish `hb' : b = σ.character` using `funext fun g => by simp [hb]`. Establish `hne : ¬ Nonempty (Representation.Equiv σ ρ)`.

Introduce and unpack `⟨φ⟩`. Conclude with `hab (by rw [ha', hb', Representation.char_iso φ])`. Establish `h` using `Representation.char_orthonormal ρ σ`. Rewrite `h` using `[if_neg hne]`. Unfold `pair`.

Rewrite using `[finsum_eq_sum_of_fintype, ha', hb']`. Simplify using `using h`.
-/
theorem pair_eq_zero_of_isIrrChar_ne : ∀ (G : Type) [Group G] [Finite G] (a b : G → ℂ),
    IsIrrChar ℂ ℂ a → IsIrrChar ℂ ℂ b → a ≠ b → pair a b = 0 := by
  intro G _ _ a b ha hb hab
  obtain ⟨n, ρ, hρ, ha⟩ := ha
  obtain ⟨m, σ, hσ, hb⟩ := hb
  have := hρ
  have := hσ
  have := Fintype.ofFinite G
  have : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have ha' : a = ρ.character := funext fun g => by simp [ha]
  have hb' : b = σ.character := funext fun g => by simp [hb]
  have hne : ¬ Nonempty (Representation.Equiv σ ρ) := by
    rintro ⟨φ⟩
    exact hab (by rw [ha', hb', Representation.char_iso φ])
  have h := Representation.char_orthonormal ρ σ
  rw [if_neg hne] at h
  unfold pair
  rw [finsum_eq_sum_of_fintype, ha', hb']
  simpa using h
end GlobalTheory.BI
