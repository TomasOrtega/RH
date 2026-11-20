import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory

/- English proof (translation)
Introduce `i u hu`. Establish `h0` using `hsz i`. Establish `ht` using `Int.self_le_toNat (W.sz i + W.S)`. Establish `hT'` using `hT i u hu`. Establish `hm1 : (W.η : ℤ) ≤ max (W.η : ℤ) ((W.sz i + W.S).toNat : ℤ)` using `le_max_left _ _`.

Establish `hm2 : (((W.sz i + W.S).toNat : ℕ) : ℤ) ≤ max (W.η : ℤ) ((W.sz i + W.S).toNat : ℤ)` using `le_max_right _ _`. Break down `hT' with h | h` into its components or cases. Distinguish the cases in `hup : W.up i`. Rewrite `h` using `[if_pos hup]`. Simplify using `only [WordData.Mi, WordData.hi, if_pos hup, Nat.cast_max]`.

Use linear arithmetic over natural numbers and integers. Rewrite `h` using `[if_neg hup]`. Simplify using `only [WordData.Mi, WordData.hi, if_neg hup, Nat.cast_max]`. Use linear arithmetic over natural numbers and integers. Establish `h'` using `abs_le.mp h`.

Distinguish the cases in `hup : W.up i`. Simplify using `only [WordData.Mi, WordData.hi, if_pos hup, Nat.cast_max]`. Use linear arithmetic over natural numbers and integers. Simplify using `only [WordData.Mi, WordData.hi, if_neg hup, Nat.cast_max]`. Use linear arithmetic over natural numbers and integers.
-/
theorem HTW.WordData.jumps_mem_box {n : ℕ} (W : WordData n) (hsz : ∀ i, 0 ≤ W.sz i) (hT : W.T1) :
    ∀ i, ∀ u ∈ W.J1 i, -(W.Mi i : ℤ) ≤ u ∧ u ≤ W.hi i := by
  intro i u hu
  have h0 := hsz i
  have ht := Int.self_le_toNat (W.sz i + W.S)
  have hT' := hT i u hu
  have hm1 : (W.η : ℤ) ≤ max (W.η : ℤ) ((W.sz i + W.S).toNat : ℤ) := le_max_left _ _
  have hm2 : (((W.sz i + W.S).toNat : ℕ) : ℤ) ≤ max (W.η : ℤ) ((W.sz i + W.S).toNat : ℤ) :=
    le_max_right _ _
  rcases hT' with h | h
  · by_cases hup : W.up i
    · rw [if_pos hup] at h
      simp only [WordData.Mi, WordData.hi, if_pos hup, Nat.cast_max]
      omega
    · rw [if_neg hup] at h
      simp only [WordData.Mi, WordData.hi, if_neg hup, Nat.cast_max]
      omega
  · have h' := abs_le.mp h
    by_cases hup : W.up i
    · simp only [WordData.Mi, WordData.hi, if_pos hup, Nat.cast_max]
      omega
    · simp only [WordData.Mi, WordData.hi, if_neg hup, Nat.cast_max]
      omega

end GlobalTheory
