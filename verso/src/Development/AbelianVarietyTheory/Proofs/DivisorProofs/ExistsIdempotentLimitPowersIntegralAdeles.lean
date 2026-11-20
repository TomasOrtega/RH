import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmFiniteAdeleIntegralSeparatedComplete
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHalfIdem
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIdeleGenerator
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjSmulNeBot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockUpperOfMulEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCongruentOneDetSubOneMemIdealMulConj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CongLevRelIndexLe
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

open scoped Nat

namespace GlobalTheory.AlgIntIdem

/- English proof (translation)
Use `set I : Ideal (𝓞 E) := Ideal.span {(N : 𝓞 E)}`. Establish `hI : I ≠ ⊥`. Simplify using `only [I, ne_eq, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero]`. Use linear arithmetic over natural numbers and integers. Use `haveI : Finite (𝓞 E ⧸ I) := Ideal.finiteQuotientOfFreeOfNeBot I hI`.

Use `letI : Fintype (𝓞 E ⧸ I) := Fintype.ofFinite _`. Establish `hcard : Fintype.card (𝓞 E ⧸ I) = N ^ Module.finrank ℤ (𝓞 E)`. Rewrite using `[← Nat.card_eq_fintype_card, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, Ideal.absNorm_span_natCast]`. Establish `h` using `GlobalTheory.IdealIdele.pow_factorial_mul (Ideal.Quotient.mk I x) t ht`. Rewrite `h` using `[hcard, ← map_pow, ← map_pow, Ideal.Quotient.eq]`.

Conclude with `Ideal.mem_span_singleton.1 h`.
-/
theorem natCast_dvd_pow_sub {E : Type} [Field E] [NumberField E] (x : 𝓞 E) (N t : ℕ)
    (hN : 0 < N) (ht : 0 < t) :
    (N : 𝓞 E) ∣ x ^ ((N ^ Module.finrank ℤ (𝓞 E))! * t) - x ^ (N ^ Module.finrank ℤ (𝓞 E))! := by
  set I : Ideal (𝓞 E) := Ideal.span {(N : 𝓞 E)}
  have hI : I ≠ ⊥ := by
    simp only [I, ne_eq, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero]; omega
  haveI : Finite (𝓞 E ⧸ I) := Ideal.finiteQuotientOfFreeOfNeBot I hI
  letI : Fintype (𝓞 E ⧸ I) := Fintype.ofFinite _
  have hcard : Fintype.card (𝓞 E ⧸ I) = N ^ Module.finrank ℤ (𝓞 E) := by
    rw [← Nat.card_eq_fintype_card, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply,
      Ideal.absNorm_span_natCast]
  have h := GlobalTheory.IdealIdele.pow_factorial_mul (Ideal.Quotient.mk I x) t ht
  rw [hcard, ← map_pow, ← map_pow, Ideal.Quotient.eq] at h
  exact Ideal.mem_span_singleton.1 h

/- English proof (translation)
Introduce `D x`. Use `set d := Module.finrank ℤ (𝓞 D.host.E)`. Take `⟨hsep, hcpl⟩` from `GlobalTheory.IntAdeleComplete.integral_separated_complete D`. Establish `hx : inc D (x : D.host.E) ∈ OhE D` using `VacMove.inc_int D x`. Establish `key : ∀ N t : ℕ, 0 < N → 0 < t → ∃ w ∈ OhE D, inc D (x : D.host.E) ^ ((N ^ d)! * t) = inc D (x : D.host.E) ^ (N ^ d)! + (N : AE D) * w`.

Introduce `N t hN ht`. Take `⟨w, hw, h⟩` from `VacMove.inc_dvd D (natCast_dvd_pow_sub x N t hN ht)`. Use `⟨w, hw, ?_⟩` and prove the remaining obligations. Rewrite using `[← h]`. Use `push_cast`.

Rewrite using `[map_sub, map_pow, map_pow]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨e, he, h⟩` from `hcpl (fun N => inc D (x : D.host.E) ^ (N ^ d)!) (fun N => pow_mem hx _) (by`. Introduce `N m hN hm`. Take `⟨t, ht⟩` from `Nat.factorial_dvd_factorial (Nat.pow_le_pow_left (Nat.le_mul_of_pos_right N hm) d)`.

Establish `ht0 : 0 < t` using `Nat.pos_of_ne_zero (by`. Introduce and unpack `rfl`. Conclude with `(Nat.factorial_ne_zero _) (by simpa using ht))`. Take `⟨w, hw, hh⟩` from `key N t hN ht0`. Conclude with `⟨w, hw, by simp only [ht, hh]⟩)`.

Use `⟨e, he, ?_, fun N hN => ⟨(N ^ d)!, Nat.factorial_pos _, h N hN⟩⟩` and prove the remaining obligations. Rewrite using `[← sub_eq_zero]`. Use `hsep _ fun N hN => ?_` and prove the remaining obligations. Take `⟨w, hw, hh⟩` from `h N hN`. Take `⟨c, hc, hc'⟩` from `key N 2 hN two_pos`.

Use `⟨c + (2 * inc D (x : D.host.E) ^ (N ^ d)! * w + N * w * w - w), ?_, ?_⟩` and prove the remaining obligations. Conclude with `add_mem hc (sub_mem (add_mem (mul_mem (mul_mem (ofNat_mem _ 2) (pow_mem hx _)) hw) (mul_mem (mul_mem (natCast_mem _ _) hw) hw)) hw)`. Rewrite `hc'` using `[pow_mul]`. Rewrite using `[hh]`. Take the linear combination `hc'`.
-/
theorem idem : ∀ (D : D7) (x : 𝓞 D.host.E), ∃ e ∈ OhE D, e * e = e ∧ ∀ N : ℕ, 0 < N → ∃ n : ℕ, 0 < n ∧ ∃ w ∈ OhE D, e = inc D (x : D.host.E) ^ n + (N : AE D) * w := by
  intro D x
  set d := Module.finrank ℤ (𝓞 D.host.E)
  obtain ⟨hsep, hcpl⟩ := GlobalTheory.IntAdeleComplete.integral_separated_complete D
  have hx : inc D (x : D.host.E) ∈ OhE D := VacMove.inc_int D x
  have key : ∀ N t : ℕ, 0 < N → 0 < t → ∃ w ∈ OhE D,
      inc D (x : D.host.E) ^ ((N ^ d)! * t) = inc D (x : D.host.E) ^ (N ^ d)! + (N : AE D) * w := by
    intro N t hN ht
    obtain ⟨w, hw, h⟩ := VacMove.inc_dvd D (natCast_dvd_pow_sub x N t hN ht)
    refine ⟨w, hw, ?_⟩
    rw [← h]
    push_cast
    rw [map_sub, map_pow, map_pow]
    ring
  obtain ⟨e, he, h⟩ := hcpl (fun N => inc D (x : D.host.E) ^ (N ^ d)!) (fun N => pow_mem hx _) (by
    intro N m hN hm
    obtain ⟨t, ht⟩ := Nat.factorial_dvd_factorial
      (Nat.pow_le_pow_left (Nat.le_mul_of_pos_right N hm) d)
    have ht0 : 0 < t := Nat.pos_of_ne_zero (by
      rintro rfl
      exact (Nat.factorial_ne_zero _) (by simpa using ht))
    obtain ⟨w, hw, hh⟩ := key N t hN ht0
    exact ⟨w, hw, by simp only [ht, hh]⟩)
  refine ⟨e, he, ?_, fun N hN => ⟨(N ^ d)!, Nat.factorial_pos _, h N hN⟩⟩
  rw [← sub_eq_zero]
  refine hsep _ fun N hN => ?_
  obtain ⟨w, hw, hh⟩ := h N hN
  obtain ⟨c, hc, hc'⟩ := key N 2 hN two_pos
  refine ⟨c + (2 * inc D (x : D.host.E) ^ (N ^ d)! * w + N * w * w - w), ?_, ?_⟩
  · exact add_mem hc (sub_mem (add_mem (mul_mem (mul_mem (ofNat_mem _ 2) (pow_mem hx _)) hw)
      (mul_mem (mul_mem (natCast_mem _ _) hw) hw)) hw)
  · rw [pow_mul] at hc'
    rw [hh]; linear_combination hc'

end GlobalTheory.AlgIntIdem
