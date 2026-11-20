import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoTowerQ
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

open IsDiscreteValuationRing in

/- English proof (translation)
Introduce `F _ _ _ _ p e c hp he hord hc w hw heq`. Establish `hw' : w = (p : 𝒪[F]) ^ 2 * (c : 𝒪[F])`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `using heq`. Establish `hcop : IsCoprime (p : ℤ) c` using `(Irreducible.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp hp).irreducible).mpr hc`.

Take `⟨a, b, hab⟩` from `hcop.map (Int.castRingHom 𝒪[F])`. Establish `h1 : IsUnit (a * (Int.castRingHom 𝒪[F]) p + b * (Int.castRingHom 𝒪[F]) c)`. Rewrite using `[hab]`. Conclude with `isUnit_one`. Establish `hpnu : ¬ IsUnit (p : 𝒪[F])`.

Introduce and unpack `⟨u, hu⟩`. Establish `h0` using `addVal_eq_zero_of_unit u`. Rewrite `h0` using `[hu]`. Unfold `OrdIs at hord`. Rewrite `h0` using `[hord]`.

Conclude with `(Nat.pos_iff_ne_zero.mp he) (by exact_mod_cast h0)`. Establish `hcu : IsUnit (c : 𝒪[F])`. Break down `IsLocalRing.isUnit_or_isUnit_of_isUnit_add h1 with h | h` into its components or cases. It suffices to derive a contradiction. Apply `hpnu` to reduce the goal to its premises.

Use `isUnit_of_mul_isUnit_right h` as an intermediate fact. Simplify using `using this`. Use `isUnit_of_mul_isUnit_right h` as an intermediate fact. Simplify using `using this`. Establish `hval : addVal 𝒪[F] w = ((2 * e : ℕ) : ℕ∞)`.

Take `⟨u, hu⟩` from `hcu`. Rewrite using `[hw', addVal_mul, addVal_pow, ← hu, addVal_eq_zero_of_unit, add_zero]`. Unfold `OrdIs at hord`. Rewrite using `[hord]`. Use `push_cast`.

Both sides reduce to the same expression. Take `⟨ϖ, hϖ⟩` from `exists_irreducible 𝒪[F]`. Rewrite `hw` using `[(irreducible_iff_uniformizer ϖ).mp hϖ, Ideal.span_singleton_pow, Ideal.mem_span_singleton]`. Establish `hle` using `(addVal_le_iff_dvd).mpr hw`. Rewrite `hle` using `[addVal_pow, addVal_uniformizer hϖ, hval]`.

Establish `: ((3 * e : ℕ) : ℕ∞) ≤ ((2 * e : ℕ) : ℕ∞)` using `by simpa using hle`. Use `ENat.coe_le_coe.mp this` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem sq_mul_not_mem_maxIdeal_pow :
    ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (p e : ℕ) (c : ℤ),
      p.Prime → 0 < e → OrdIs F p e → ¬ (p : ℤ) ∣ c →
      ∀ w ∈ 𝓂[F] ^ (3 * e), ((w : 𝒪[F]) : F) ≠ (p : F) ^ 2 * (c : F) := by
  intro F _ _ _ _ p e c hp he hord hc w hw heq
  have hw' : w = (p : 𝒪[F]) ^ 2 * (c : 𝒪[F]) := by
    apply Subtype.ext
    simpa using heq

  have hcop : IsCoprime (p : ℤ) c :=
    (Irreducible.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp hp).irreducible).mpr hc
  obtain ⟨a, b, hab⟩ := hcop.map (Int.castRingHom 𝒪[F])
  have h1 : IsUnit (a * (Int.castRingHom 𝒪[F]) p + b * (Int.castRingHom 𝒪[F]) c) := by
    rw [hab]; exact isUnit_one
  have hpnu : ¬ IsUnit (p : 𝒪[F]) := by
    rintro ⟨u, hu⟩
    have h0 := addVal_eq_zero_of_unit u
    rw [hu] at h0
    unfold OrdIs at hord
    rw [hord] at h0
    exact (Nat.pos_iff_ne_zero.mp he) (by exact_mod_cast h0)
  have hcu : IsUnit (c : 𝒪[F]) := by
    rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add h1 with h | h
    · exfalso; apply hpnu
      have := isUnit_of_mul_isUnit_right h
      simpa using this
    · have := isUnit_of_mul_isUnit_right h
      simpa using this

  have hval : addVal 𝒪[F] w = ((2 * e : ℕ) : ℕ∞) := by
    obtain ⟨u, hu⟩ := hcu
    rw [hw', addVal_mul, addVal_pow, ← hu, addVal_eq_zero_of_unit, add_zero]
    unfold OrdIs at hord
    rw [hord]
    push_cast
    rfl
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible 𝒪[F]
  rw [(irreducible_iff_uniformizer ϖ).mp hϖ, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hw
  have hle := (addVal_le_iff_dvd).mpr hw
  rw [addVal_pow, addVal_uniformizer hϖ, hval] at hle
  have : ((3 * e : ℕ) : ℕ∞) ≤ ((2 * e : ℕ) : ℕ∞) := by simpa using hle
  have := ENat.coe_le_coe.mp this
  omega

end GlobalTheory.PMon.Ram
