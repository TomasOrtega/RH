import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusPowRootOfUnity
open ReciprocityTheory.DiscreteGroups.LocalClassField GlobalTheory.LKRes GlobalTheory.LKRes.ResSplit

namespace GlobalTheory.LKRes.ResSplit

/- English proof (translation)
Establish `hper : ζ ^ p ^ r = ζ`. Establish `h1 : 1 ≤ p ^ r` using `Nat.one_le_pow _ _ hp`. Rewrite using `[show p ^ r = (p ^ r - 1) + 1 by omega, pow_succ, hζ, one_mul]`. Establish `hmod : ∀ m, ζ ^ p ^ m = ζ ^ p ^ (m % r)`. Introduce `m`.

Use `conv_lhs => rw [← Nat.mod_add_div m r]`. Generalize the expression as in `m / r = n`. Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`.

Rewrite using `[Nat.mul_succ, ← add_assoc, pow_add, mul_comm, pow_mul, hper, ih]`. Rewrite using `[hmod m₁, hmod m₂, (ZMod.natCast_eq_natCast_iff' m₁ m₂ r).1 h]`.
-/
theorem pow_pow_eq_of_zmod {p : ℕ} {F : Type} [CommMonoid F] {r : ℕ} {ζ : F} (hζ : ζ ^ (p ^ r - 1) = 1)
    (hp : 0 < p) {m₁ m₂ : ℕ} (h : (m₁ : ZMod r) = m₂) : ζ ^ p ^ m₁ = ζ ^ p ^ m₂ := by
  have hper : ζ ^ p ^ r = ζ := by
    have h1 : 1 ≤ p ^ r := Nat.one_le_pow _ _ hp
    rw [show p ^ r = (p ^ r - 1) + 1 by omega, pow_succ, hζ, one_mul]
  have hmod : ∀ m, ζ ^ p ^ m = ζ ^ p ^ (m % r) := by
    intro m
    conv_lhs => rw [← Nat.mod_add_div m r]
    generalize m / r = n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.mul_succ, ← add_assoc, pow_add, mul_comm, pow_mul, hper, ih]
  rw [hmod m₁, hmod m₂, (ZMod.natCast_eq_natCast_iff' m₁ m₂ r).1 h]

/- English proof (translation)
Establish `hp : 1 < p` using `(Fact.out : p.Prime).one_lt`. Use `set d := Nat.gcd f r with hd`. Establish `hd0 : 0 < d` using `Nat.gcd_pos_of_pos_right f hr`. Use `⟨s % d, Nat.mod_lt _ hd0, ?_⟩` and prove the remaining obligations. Use `haveI : NeZero r := ⟨hr.ne'⟩`.

Use `set a : ℕ := ((f.gcdA r : ℤ) : ZMod r).val with ha`. Establish `hfa : ((f : ZMod r) * (a : ZMod r)) = (d : ZMod r)`. Rewrite using `[ha, ZMod.natCast_zmod_val]`. Establish `h` using `Nat.gcd_eq_gcd_ab f r`. Establish `h2 : ((d : ℤ) : ZMod r) = (((f : ℤ) * f.gcdA r + (r : ℤ) * f.gcdB r : ℤ) : ZMod r)`.

Rewrite using `[hd, h]`. Move the coercions through the operations in `at h2`. Rewrite `h2` using `[ZMod.natCast_self, zero_mul, add_zero]`. Conclude with `h2.symm`. Use `set k := a * (s / d) with hk`.

Establish `hcong : ((s % d + f * k : ℕ) : ZMod r) = (s : ZMod r)`. Rewrite using `[hk]`. Use `push_cast`. Rewrite using `[← mul_assoc, hfa]`. Use `conv_rhs => rw [← Nat.mod_add_div s d]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hpN : ¬ p ∣ p ^ r - 1`. Introduce `hdvd`. Establish `h1 : p ∣ p ^ r` using `dvd_pow_self p hr.ne'`.

Establish `h2 : 1 ≤ p ^ r` using `Nat.one_le_pow _ _ (by omega)`. Establish `h3 : p ∣ p ^ r - (p ^ r - 1)` using `Nat.dvd_sub h1 hdvd`. Rewrite `h3` using `[show p ^ r - (p ^ r - 1) = 1 by omega]`. Conclude with `(Fact.out : p.Prime).one_lt.ne' (Nat.dvd_one.1 h3)`. Use `set i := s % d`.

Establish `hζi : (ζ ^ p ^ i) ^ (p ^ r - 1) = 1`. Rewrite using `[← pow_mul, mul_comm, pow_mul, hζ, one_pow]`. Establish `hφ : (frobK p K ^ k) (ζ ^ p ^ i) = ζ ^ p ^ s`. Rewrite using `[IsFrob.pow_apply hK (isFrob_frobK hK) hpN k hζi, hq, ← pow_mul, ← pow_mul, ← pow_add]`. Conclude with `pow_pow_eq_of_zmod hζ (by omega) hcong`.

Use `set φ := frobK p K ^ k`. Establish `hsum : φ (∑ j : Fin r, (c j : PadicAlgCl p) * (ζ ^ p ^ i) ^ (j : ℕ)) = ∑ j : Fin r, (c j : PadicAlgCl p) * (ζ ^ p ^ s) ^ (j : ℕ)`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_pow, hφ]`.

Use `congr 1`. Conclude with `φ.commutes (c j)`. Rewrite using `[← hsum, norm_GK]`.
-/
theorem spread_main (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    (hK : FiniteDimensional ℚ_[p] K) (f r : ℕ) (hq : qK p K = p ^ f) (hr : 0 < r)
    (ζ : PadicAlgCl p) (hζ : ζ ^ (p ^ r - 1) = 1) (c : Fin r → K) (s : ℕ) :
    ∃ i < Nat.gcd f r, ‖∑ j : Fin r, (c j : PadicAlgCl p) * (ζ ^ p ^ s) ^ (j : ℕ)‖ =
      ‖∑ j : Fin r, (c j : PadicAlgCl p) * (ζ ^ p ^ i) ^ (j : ℕ)‖ := by
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  set d := Nat.gcd f r with hd
  have hd0 : 0 < d := Nat.gcd_pos_of_pos_right f hr
  refine ⟨s % d, Nat.mod_lt _ hd0, ?_⟩
  haveI : NeZero r := ⟨hr.ne'⟩

  set a : ℕ := ((f.gcdA r : ℤ) : ZMod r).val with ha
  have hfa : ((f : ZMod r) * (a : ZMod r)) = (d : ZMod r) := by
    rw [ha, ZMod.natCast_zmod_val]
    have h := Nat.gcd_eq_gcd_ab f r
    have h2 : ((d : ℤ) : ZMod r) = (((f : ℤ) * f.gcdA r + (r : ℤ) * f.gcdB r : ℤ) : ZMod r) := by
      rw [hd, h]
    push_cast at h2
    rw [ZMod.natCast_self, zero_mul, add_zero] at h2
    exact h2.symm
  set k := a * (s / d) with hk
  have hcong : ((s % d + f * k : ℕ) : ZMod r) = (s : ZMod r) := by
    rw [hk]
    push_cast
    rw [← mul_assoc, hfa]
    conv_rhs => rw [← Nat.mod_add_div s d]
    push_cast
    ring

  have hpN : ¬ p ∣ p ^ r - 1 := by
    intro hdvd
    have h1 : p ∣ p ^ r := dvd_pow_self p hr.ne'
    have h2 : 1 ≤ p ^ r := Nat.one_le_pow _ _ (by omega)
    have h3 : p ∣ p ^ r - (p ^ r - 1) := Nat.dvd_sub h1 hdvd
    rw [show p ^ r - (p ^ r - 1) = 1 by omega] at h3
    exact (Fact.out : p.Prime).one_lt.ne' (Nat.dvd_one.1 h3)
  set i := s % d
  have hζi : (ζ ^ p ^ i) ^ (p ^ r - 1) = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]
  have hφ : (frobK p K ^ k) (ζ ^ p ^ i) = ζ ^ p ^ s := by
    rw [IsFrob.pow_apply hK (isFrob_frobK hK) hpN k hζi, hq, ← pow_mul, ← pow_mul, ← pow_add]
    exact pow_pow_eq_of_zmod hζ (by omega) hcong
  set φ := frobK p K ^ k
  have hsum : φ (∑ j : Fin r, (c j : PadicAlgCl p) * (ζ ^ p ^ i) ^ (j : ℕ)) =
      ∑ j : Fin r, (c j : PadicAlgCl p) * (ζ ^ p ^ s) ^ (j : ℕ) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, map_pow, hφ]
    congr 1
    exact φ.commutes (c j)
  rw [← hsum, norm_GK]

end GlobalTheory.LKRes.ResSplit

/- English proof (translation)
Introduce `p _ K hK f r hq hr ζ hζ c s` and use `GlobalTheory.LKRes.ResSplit.spread_main p K hK f r hq hr ζ hζ c s`.
-/
theorem GlobalTheory.LKRes.ResSplit.spread : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)), FiniteDimensional ℚ_[p] K → ∀ (f r : ℕ), qK p K = p ^ f → 0 < r → ∀ (ζ : PadicAlgCl p), ζ ^ (p ^ r - 1) = 1 → ∀ (c : Fin r → K) (s : ℕ), ∃ i < Nat.gcd f r, ‖∑ j : Fin r, (c j : PadicAlgCl p) * (ζ ^ p ^ s) ^ (j : ℕ)‖ = ‖∑ j : Fin r, (c j : PadicAlgCl p) * (ζ ^ p ^ i) ^ (j : ℕ)‖ :=
  fun p _ K hK f r hq hr ζ hζ c s => GlobalTheory.LKRes.ResSplit.spread_main p K hK f r hq hr ζ hζ c s
