import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ComplexConjugationOrbitOneRealPlaceStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AlternatingWordLargeSizeNumericalBoundsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EmbeddingSignAlternateOfSignNegStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualOrbitPageWordThickIffThickEmbeddingStatement

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

/- English proof (translation)
Take `⟨hC, hw, hr, hwb, -, hb⟩` from `h`. Establish `he` using `L.etaSz_pos`. Establish `hS` using `L.Sc_pos`. Establish `ht : (0 : ℝ) ≤ D.R.t` using `Nat.cast_nonneg _`. Establish `hL : (0 : ℝ) ≤ D.host.Lw` using `Nat.cast_nonneg _`.

Establish `hb' : (0 : ℝ) ≤ L.sc.b'` using `by linarith`. Establish `hCL : (100 : ℝ) ≤ C * ((D.host.Lw : ℝ) + 1)` using `by nlinarith`. Establish `hbb : 100 * L.sc.b' ≤ L.sc.b` using `le_trans (mul_le_mul_of_nonneg_right hCL hb') hb`. Establish `h1 : (etaHat L : ℝ) ≤ L.etaSz + D.R.t + 2`. Use `Nat.floor_le he.le` as an intermediate fact.

Unfold `etaHat`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h2 : (sHat L : ℝ) ≤ L.Sc` using `Nat.floor_le hS.le`. Establish `h3 : ⌈L.sc.b⌉₊ ≤ bHat L + D.R.t`.

Unfold `bHat`. Use linear arithmetic over natural numbers and integers. Establish `h4 : L.sc.b ≤ (bHat L : ℝ) + D.R.t`. Establish `h5 : ((⌈L.sc.b⌉₊ : ℕ) : ℝ) ≤ (bHat L : ℝ) + D.R.t` using `by exact_mod_cast h3`. Conclude with `le_trans (Nat.le_ceil _) h5`.

Apply the tactic sequence `constructor <;> linarith`.
-/
theorem bHat_large_of_roomy {D : D7} (L : SizeData₂ D) (C : ℝ) (h : Roomy L C) :
    (100 : ℝ) ≤ bHat L ∧ 2 * (etaHat L : ℝ) + sHat L ≤ (bHat L : ℝ) / 10 := by
  obtain ⟨hC, hw, hr, hwb, -, hb⟩ := h
  have he := L.etaSz_pos
  have hS := L.Sc_pos
  have ht : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  have hL : (0 : ℝ) ≤ D.host.Lw := Nat.cast_nonneg _
  have hb' : (0 : ℝ) ≤ L.sc.b' := by linarith
  have hCL : (100 : ℝ) ≤ C * ((D.host.Lw : ℝ) + 1) := by nlinarith
  have hbb : 100 * L.sc.b' ≤ L.sc.b := le_trans (mul_le_mul_of_nonneg_right hCL hb') hb
  have h1 : (etaHat L : ℝ) ≤ L.etaSz + D.R.t + 2 := by
    have := Nat.floor_le he.le
    unfold etaHat
    push_cast
    linarith
  have h2 : (sHat L : ℝ) ≤ L.Sc := Nat.floor_le hS.le
  have h3 : ⌈L.sc.b⌉₊ ≤ bHat L + D.R.t := by
    unfold bHat
    omega
  have h4 : L.sc.b ≤ (bHat L : ℝ) + D.R.t := by
    have h5 : ((⌈L.sc.b⌉₊ : ℕ) : ℝ) ≤ (bHat L : ℝ) + D.R.t := by exact_mod_cast h3
    exact le_trans (Nat.le_ceil _) h5
  constructor <;> linarith

/- English proof (translation)
Take `⟨hord, hplc⟩` from `GlobalTheory.T.complexConjugation_orbit_one_realPlace τ`. Establish `hth : ∀ i, (pageWord L j ε τ (D.R.cc)).thick i`. Introduce `i`. Rewrite using `[GlobalTheory.T.twistedDualOrbitPageWord_thick_iff_thickEmbedding L C j ε τ (D.R.cc) hR i]`. Unfold `Thick at hτ ⊢`.

Rewrite using `[hplc i]`. Conclude with `hτ`. Use `⟨⟨?_, ?_, ?_⟩, hth⟩` and prove the remaining obligations. Rewrite using `[hord]`. Conclude with `even_two`.

Conclude with `(GlobalTheory.T.embeddingSign_alternate_of_sign_neg ε τ (D.R.cc) rfl).2`. Introduce `M hM i`. Take `⟨hB, hroom⟩` from `bHat_large_of_roomy L C hR`. Establish `hη : (0 : ℝ) ≤ etaHat L` using `Nat.cast_nonneg _`. Establish `hS : (0 : ℝ) ≤ sHat L` using `Nat.cast_nonneg _`.

Establish `key : ∀ k, (bHat L : ℝ) ≤ ((pageWord L j ε τ (D.R.cc)).sz k : ℝ) ∧ ((pageWord L j ε τ (D.R.cc)).sz k : ℝ) ≤ (bHat L : ℝ) + etaHat L`. Introduce `k`. Take `⟨h1, h2⟩` from `hth k`. Establish `h1' : ((bHat L : ℕ) : ℤ) ≤ (pageWord L j ε τ (D.R.cc)).sz k` using `h1`. Establish `h2' : (pageWord L j ε τ (D.R.cc)).sz k ≤ ((bHat L : ℕ) : ℤ) + ((etaHat L : ℕ) : ℤ)` using `h2`.

Conclude with `⟨by exact_mod_cast h1', by exact_mod_cast h2'⟩`. Take `⟨k, hk⟩` from `hM.1`. Establish `hMk` using `key k`. Rewrite `hMk` using `[hk]`. Establish `hi` using `key i`.

Take `⟨h1, h2⟩` from `GlobalTheory.T.alternatingWord_large_size_numerical_bounds l (bHat L) (etaHat L) (sHat L) (M : ℝ) ((pageWord L j ε τ (D.R.cc)).sz i : ℝ) hl hB hη hS hroom (abs_le.2 ⟨by linarith [hMk.1], by linarith [hMk.2]⟩) (abs_le.2 ⟨by linarith [hi.1], by linarith [hi.2]⟩)`. Use `⟨?_, h1, h2⟩` and prove the remaining obligations. Establish `: (1 : ℝ) ≤ ((pageWord L j ε τ (D.R.cc)).sz i : ℝ)` using `by linarith [hi.1]`. Conclude with `this` after adjusting the coercions.
-/
theorem conjWord_hypAT {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) (τ : D.R.GG) (l : ℕ)
    (hR : Roomy L C) (hl : 11 ≤ l) (hτ : Thick D.host τ) :
    (pageWord L j ε τ (D.R.cc)).HypAT l ∧ ∀ i, (pageWord L j ε τ (D.R.cc)).thick i := by
  obtain ⟨hord, hplc⟩ := GlobalTheory.T.complexConjugation_orbit_one_realPlace τ
  have hth : ∀ i, (pageWord L j ε τ (D.R.cc)).thick i := by
    intro i
    rw [GlobalTheory.T.twistedDualOrbitPageWord_thick_iff_thickEmbedding L C j ε τ (D.R.cc) hR i]
    unfold Thick at hτ ⊢
    rw [hplc i]
    exact hτ
  refine ⟨⟨?_, ?_, ?_⟩, hth⟩
  · rw [hord]; exact even_two
  · exact (GlobalTheory.T.embeddingSign_alternate_of_sign_neg ε τ (D.R.cc) rfl).2
  · intro M hM i
    obtain ⟨hB, hroom⟩ := bHat_large_of_roomy L C hR
    have hη : (0 : ℝ) ≤ etaHat L := Nat.cast_nonneg _
    have hS : (0 : ℝ) ≤ sHat L := Nat.cast_nonneg _
    have key : ∀ k, (bHat L : ℝ) ≤ ((pageWord L j ε τ (D.R.cc)).sz k : ℝ) ∧
        ((pageWord L j ε τ (D.R.cc)).sz k : ℝ) ≤ (bHat L : ℝ) + etaHat L := by
      intro k
      obtain ⟨h1, h2⟩ := hth k
      have h1' : ((bHat L : ℕ) : ℤ) ≤ (pageWord L j ε τ (D.R.cc)).sz k := h1
      have h2' : (pageWord L j ε τ (D.R.cc)).sz k ≤ ((bHat L : ℕ) : ℤ) + ((etaHat L : ℕ) : ℤ) := h2
      exact ⟨by exact_mod_cast h1', by exact_mod_cast h2'⟩
    obtain ⟨k, hk⟩ := hM.1
    have hMk := key k
    rw [hk] at hMk
    have hi := key i
    obtain ⟨h1, h2⟩ := GlobalTheory.T.alternatingWord_large_size_numerical_bounds l (bHat L) (etaHat L) (sHat L) (M : ℝ)
      ((pageWord L j ε τ (D.R.cc)).sz i : ℝ) hl hB hη hS hroom
      (abs_le.2 ⟨by linarith [hMk.1], by linarith [hMk.2]⟩)
      (abs_le.2 ⟨by linarith [hi.1], by linarith [hi.2]⟩)
    refine ⟨?_, h1, h2⟩
    have : (1 : ℝ) ≤ ((pageWord L j ε τ (D.R.cc)).sz i : ℝ) := by linarith [hi.1]
    exact_mod_cast this

end GlobalTheory.HTW
