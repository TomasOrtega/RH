import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LatticeDeterminedByInvariants

open GlobalTheory.Published Formalism.L2.Th1.F
open scoped IntermediateField

namespace GlobalTheory.CMModel

/- English proof (translation)
The claim follows from `IsIntegral.of_pow two_pos (by rw [sqrtNegNat_sq]; exact (isIntegral_natCast p).neg)`.
-/
theorem isIntegral_sqrtNegNat (p : ℕ) : IsIntegral ℤ (sqrtNegNat p) :=
  IsIntegral.of_pow two_pos (by rw [sqrtNegNat_sq]; exact (isIntegral_natCast p).neg)

/- English proof (translation)
Establish `hint : IsIntegral ℚ (sqrtNegNat p)` using `(isIntegral_sqrtNegNat p).tower_top`. Establish `hz' : z ∈ Algebra.adjoin ℚ {sqrtNegNat p}`. Rewrite using `[← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic]`. Conclude with `hz`. Use `clear hz`.

Proceed by induction on `hz' using Algebra.adjoin_induction with`. Consider the case `mem x hx => exact ⟨0, 1, by simpa using hx⟩`. Consider the case `algebraMap r => exact ⟨r, 0, by simp⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨a, b, rfl⟩` from `hx`.

Take `⟨c, d, rfl⟩` from `hy`. Conclude with `⟨a + c, b + d, by push_cast; ring⟩`. Consider the case `mul x y _ _ hx hy`. Take `⟨a, b, rfl⟩` from `hx`. Take `⟨c, d, rfl⟩` from `hy`.

Conclude with `⟨a * c - p * (b * d), a * d + b * c, by push_cast; linear_combination (b * d : ℂ) * sqrtNegNat_sq p⟩`.
-/
theorem exists_rat_of_mem_adjoin_sqrtNegNat {p : ℕ} {z : ℂ} (hz : z ∈ ℚ⟮sqrtNegNat p⟯) :
    ∃ a b : ℚ, z = a + b * sqrtNegNat p := by
  have hint : IsIntegral ℚ (sqrtNegNat p) := (isIntegral_sqrtNegNat p).tower_top
  have hz' : z ∈ Algebra.adjoin ℚ {sqrtNegNat p} := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic]
    exact hz
  clear hz
  induction hz' using Algebra.adjoin_induction with
  | mem x hx => exact ⟨0, 1, by simpa using hx⟩
  | algebraMap r => exact ⟨r, 0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, b, rfl⟩ := hx
    obtain ⟨c, d, rfl⟩ := hy
    exact ⟨a + c, b + d, by push_cast; ring⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, b, rfl⟩ := hx
    obtain ⟨c, d, rfl⟩ := hy
    exact ⟨a * c - p * (b * d), a * d + b * c, by
      push_cast; linear_combination (b * d : ℂ) * sqrtNegNat_sq p⟩

/- English proof (translation)
Take `⟨a, b, e⟩` from `exists_rat_of_mem_adjoin_sqrtNegNat h`. Establish `ha : a = 0`. Use `congrArg Complex.re e` as an intermediate fact. Simplify `this.symm` using `[sqrtNegNat]`. Establish `e2 : (q : ℂ) = b ^ 2 * p`.

Use `sqrtNegNat_sq q` as an intermediate fact. Rewrite `this` using `[e, ha]`. Move the coercions through the operations in `at this`. Take the linear combination `this - (b : ℂ) ^ 2 * sqrtNegNat_sq p`. Establish `e3 : (q : ℚ) = b ^ 2 * p` using `by exact_mod_cast e2`.

Establish `hs : IsSquare ((q * p : ℕ) : ℚ)` using `⟨b * p, by push_cast; rw [e3]; ring⟩`. Take `⟨n, hn⟩` from `Rat.isSquare_natCast_iff.1 hs`. Establish `hpn : p ∣ n`. Establish `: p ∣ n * n` using `hn ▸ dvd_mul_left p q`. Conclude with `(hp.dvd_mul.1 this).elim id id`.

Establish `: p * p ∣ q * p` using `hn ▸ mul_dvd_mul hpn hpn`. Conclude with `Nat.dvd_of_mul_dvd_mul_right hp.pos this`.
-/
theorem dvd_of_sqrtNegNat_mem {p q : ℕ} (hp : p.Prime) (h : sqrtNegNat q ∈ ℚ⟮sqrtNegNat p⟯) :
    p ∣ q := by
  obtain ⟨a, b, e⟩ := exists_rat_of_mem_adjoin_sqrtNegNat h
  have ha : a = 0 := by
    have := congrArg Complex.re e
    simpa [sqrtNegNat] using this.symm
  have e2 : (q : ℂ) = b ^ 2 * p := by
    have := sqrtNegNat_sq q
    rw [e, ha] at this
    push_cast at this
    linear_combination this - (b : ℂ) ^ 2 * sqrtNegNat_sq p
  have e3 : (q : ℚ) = b ^ 2 * p := by exact_mod_cast e2
  have hs : IsSquare ((q * p : ℕ) : ℚ) := ⟨b * p, by push_cast; rw [e3]; ring⟩
  obtain ⟨n, hn⟩ := Rat.isSquare_natCast_iff.1 hs
  have hpn : p ∣ n := by
    have : p ∣ n * n := hn ▸ dvd_mul_left p q
    exact (hp.dvd_mul.1 this).elim id id
  have : p * p ∣ q * p := hn ▸ mul_dvd_mul hpn hpn
  exact Nat.dvd_of_mul_dvd_mul_right hp.pos this

/- English proof (translation)
Establish `H₀` using `isHomothetic_scalePeriods L m hm0`. Establish `e` using `lattice_eq_of_g₂_eq_of_g₃_eq (H₀.g₂_eq.trans e2) (H₀.g₃_eq.trans e3)`. Use `(H₀ 1).2 ((hL 1).2 ⟨one_mem _, isIntegral_one⟩)` as an intermediate fact. Rewrite `this` using `[e, mul_one]`. Conclude with `((hL m).1 this).1`.
-/
theorem mem_adjoin_of_invariant {p : ℕ} {L : PeriodPair} (hL : IsIntegersLattice p L) (m : ℂ) (hm0 : m ≠ 0)
    (e2 : (m ^ 4)⁻¹ * L.g₂ = L.g₂) (e3 : (m ^ 6)⁻¹ * L.g₃ = L.g₃) : m ∈ ℚ⟮sqrtNegNat p⟯ := by
  have H₀ := isHomothetic_scalePeriods L m hm0
  have e := lattice_eq_of_g₂_eq_of_g₃_eq (H₀.g₂_eq.trans e2) (H₀.g₃_eq.trans e3)
  have := (H₀ 1).2 ((hL 1).2 ⟨one_mem _, isIntegral_one⟩)
  rw [e, mul_one] at this
  exact ((hL m).1 this).1

/- English proof (translation)
Introduce `p L hp h3 hL`. Use `⟨fun h => ?_, fun h => ?_, fun ω hω => ?_⟩` and prove the remaining obligations. Establish `hs` using `sqrtNegNat_sq 3`. Move the coercions through the operations in `at hs`. Establish `h6 : ((1 + sqrtNegNat 3) / 2) ^ 3 = -1`.

Take the linear combination `(3 / 8 + sqrtNegNat 3 / 8) * hs`. Establish `hm` using `mem_adjoin_of_invariant hL ((1 + sqrtNegNat 3) / 2) (fun e => by rw [e] at h6; norm_num at h6) (by simp [h]) (by rw [show 6 = 3 * 2 by norm_num, pow_mul, h6]; simp)`. Establish `hm' : sqrtNegNat 3 ∈ ℚ⟮sqrtNegNat p⟯`. Use `sub_mem (add_mem hm hm) (one_mem _)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Expand and normalize the polynomial expressions, which then agree. Conclude with `absurd (Nat.le_of_dvd three_pos (dvd_of_sqrtNegNat_mem hp hm')) (not_le.2 h3)`. Establish `hm` using `mem_adjoin_of_invariant hL Complex.I Complex.I_ne_zero (by simp) (by simp [h])`. Establish `hm' : sqrtNegNat 1 ∈ ℚ⟮sqrtNegNat p⟯` using `by simpa [sqrtNegNat] using hm`. Use `Nat.le_of_dvd one_pos (dvd_of_sqrtNegNat_mem hp hm')` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Conclude with `(hL _).2 ⟨mul_mem (IntermediateField.mem_adjoin_simple_self ℚ _) ((hL ω).1 hω).1, (isIntegral_sqrtNegNat p).mul ((hL ω).1 hω).2⟩`.
-/
theorem integersLattice_invariants_ne_zero :
    ∀ (p : ℕ) (L : PeriodPair), p.Prime → 3 < p → IsIntegersLattice p L →
      L.g₂ ≠ 0 ∧ L.g₃ ≠ 0 ∧ MulStable L (sqrtNegNat p) := by
  intro p L hp h3 hL
  refine ⟨fun h => ?_, fun h => ?_, fun ω hω => ?_⟩
  · have hs := sqrtNegNat_sq 3
    push_cast at hs
    have h6 : ((1 + sqrtNegNat 3) / 2) ^ 3 = -1 := by
      linear_combination (3 / 8 + sqrtNegNat 3 / 8) * hs
    have hm := mem_adjoin_of_invariant hL ((1 + sqrtNegNat 3) / 2)
      (fun e => by rw [e] at h6; norm_num at h6) (by simp [h])
      (by rw [show 6 = 3 * 2 by norm_num, pow_mul, h6]; simp)
    have hm' : sqrtNegNat 3 ∈ ℚ⟮sqrtNegNat p⟯ := by
      have := sub_mem (add_mem hm hm) (one_mem _)
      convert this using 1
      ring
    exact absurd (Nat.le_of_dvd three_pos (dvd_of_sqrtNegNat_mem hp hm')) (not_le.2 h3)
  · have hm := mem_adjoin_of_invariant hL Complex.I Complex.I_ne_zero (by simp) (by simp [h])
    have hm' : sqrtNegNat 1 ∈ ℚ⟮sqrtNegNat p⟯ := by simpa [sqrtNegNat] using hm
    have := Nat.le_of_dvd one_pos (dvd_of_sqrtNegNat_mem hp hm')
    omega
  · exact (hL _).2 ⟨mul_mem (IntermediateField.mem_adjoin_simple_self ℚ _) ((hL ω).1 hω).1,
      (isIntegral_sqrtNegNat p).mul ((hL ω).1 hω).2⟩

end GlobalTheory.CMModel
