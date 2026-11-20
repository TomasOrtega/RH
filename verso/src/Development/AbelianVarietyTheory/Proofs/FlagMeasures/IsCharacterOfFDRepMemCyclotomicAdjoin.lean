import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsMirClass
open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

namespace GlobalTheory.GLm

/- English proof (translation)
Rewrite using `[Module.End.trace_eq_sum_roots_charpoly_of_splits (IsAlgClosed.splits _)]`. Use `multiset_sum_mem _ ?_` and prove the remaining obligations. Introduce `μ hμ`. Establish `hroot : f.charpoly.IsRoot μ` using `(Polynomial.mem_roots'.mp hμ).2`. Take `⟨v, hv⟩` from `((Module.End.hasEigenvalue_iff_isRoot_charpoly f μ).mpr hroot).exists_hasEigenvector`.

Establish `h1` using `hv.pow_apply N`. Rewrite `h1` using `[hf]`. Establish `h2 : μ ^ N = 1`. Establish `h3 : (μ ^ N - 1) • v = 0`. Rewrite using `[sub_smul, ← h1]`.

Simplify using the standard rewrite rules. Break down `smul_eq_zero.mp h3 with h | h` into its components or cases. Conclude with `sub_eq_zero.mp h`. Conclude with `absurd h hv.2`. Use `haveI : NeZero N := ⟨hN.ne'⟩`.

Take `⟨i, -, hi⟩` from `(Complex.isPrimitiveRoot_exp N hN.ne').eq_pow_of_pow_eq_one h2`. Rewrite using `[← hi]`. Conclude with `pow_mem (IntermediateField.mem_adjoin_simple_self ℚ _) i`.
-/
theorem trace_mem_adjoin_of_pow_eq_one (V : Type) [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (f : Module.End ℂ V) (N : ℕ) (hN : 0 < N) (hf : f ^ N = 1) :
    LinearMap.trace ℂ V f ∈
      IntermediateField.adjoin ℚ {Complex.exp (2 * Real.pi * Complex.I / (N : ℕ))} := by
  rw [Module.End.trace_eq_sum_roots_charpoly_of_splits (IsAlgClosed.splits _)]
  refine multiset_sum_mem _ ?_
  intro μ hμ
  have hroot : f.charpoly.IsRoot μ := (Polynomial.mem_roots'.mp hμ).2
  obtain ⟨v, hv⟩ :=
    ((Module.End.hasEigenvalue_iff_isRoot_charpoly f μ).mpr hroot).exists_hasEigenvector
  have h1 := hv.pow_apply N
  rw [hf] at h1
  have h2 : μ ^ N = 1 := by
    have h3 : (μ ^ N - 1) • v = 0 := by
      rw [sub_smul, ← h1]; simp
    rcases smul_eq_zero.mp h3 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hv.2
  haveI : NeZero N := ⟨hN.ne'⟩
  obtain ⟨i, -, hi⟩ := (Complex.isPrimitiveRoot_exp N hN.ne').eq_pow_of_pow_eq_one h2
  rw [← hi]
  exact pow_mem (IntermediateField.mem_adjoin_simple_self ℚ _) i

/- English proof (translation)
Introduce `G _ _ χ N hN hd hχ x`. Take `⟨V, hV⟩` from `hχ`. Rewrite using `[← hV x]`. Use `trace_mem_adjoin_of_pow_eq_one V (V.ρ x) N hN ?_` and prove the remaining obligations. Take `⟨k, rfl⟩` from `hd`.

Rewrite using `[← map_pow, pow_mul, pow_card_eq_one', one_pow, map_one]`.
-/
theorem isChar_mem_adjoin_exp :
    ∀ (G : Type) [Group G] [Fintype G] (χ : G → ℂ) (N : ℕ), 0 < N → Nat.card G ∣ N → IsChar χ →
      ∀ x, χ x ∈
        IntermediateField.adjoin ℚ {Complex.exp (2 * Real.pi * Complex.I / (N : ℕ))} := by
  intro G _ _ χ N hN hd hχ x
  obtain ⟨V, hV⟩ := hχ
  rw [← hV x]
  refine trace_mem_adjoin_of_pow_eq_one V (V.ρ x) N hN ?_
  obtain ⟨k, rfl⟩ := hd
  rw [← map_pow, pow_mul, pow_card_eq_one', one_pow, map_one]

end GlobalTheory.GLm
