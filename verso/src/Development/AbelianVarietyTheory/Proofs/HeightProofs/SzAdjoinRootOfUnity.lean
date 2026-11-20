import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz

set_option autoImplicit false

namespace GlobalTheory.FieldSize

open NumberField IsDedekindDomain GlobalTheory.FieldSize
open scoped IntermediateField nonZeroDivisors

/- English proof (translation)
Introduce `n hn`. Use `haveI : NeZero n := ⟨hn.ne'⟩`. Establish `hζ` using `Complex.isPrimitiveRoot_exp n hn.ne'`. Use `set F := ℚ⟮Complex.exp (2 * Real.pi * Complex.I / n)⟯ with hF`. Use `haveI hc : IsCyclotomicExtension {n} ℚ F := by`.

Express the relevant statement in the definitionally equal form `IsCyclotomicExtension {n} ℚ F.toSubalgebra`. Rewrite using `[hF, IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic ((hζ.isIntegral hn).tower_top (A := ℚ)).isAlgebraic]`. Conclude with `hζ.adjoin_isCyclotomicExtension ℚ`. Establish `hfd : FiniteDimensional ℚ F` using `IsCyclotomicExtension.finiteDimensional {n} ℚ F`. Use `⟨hfd, ?_⟩` and prove the remaining obligations.

Use `letI : NumberField F := NumberField.mk`. Establish `hrk : Module.finrank ℚ F = Nat.totient n` using `IsCyclotomicExtension.finrank F (Polynomial.cyclotomic.irreducible_rat hn)`. Establish `ht : 0 < Nat.totient n` using `Nat.totient_pos.2 hn`. Establish `htR : (0 : ℝ) < (Nat.totient n : ℝ)` using `by exact_mod_cast ht`. Establish `hd : (NumberField.discr F).natAbs ≤ n ^ Nat.totient n`.

Rewrite using `[IsCyclotomicExtension.Rat.natAbs_discr n F]`. Conclude with `Nat.div_le_self _ _`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hrk]`. Conclude with `Real.log_le_log htR (by exact_mod_cast Nat.totient_le n)`.

Rewrite using `[hrk, div_le_iff₀ htR, mul_comm, ← Real.log_pow]`. Establish `h0 : NumberField.discr F ≠ 0` using `NumberField.discr_ne_zero F`. Use `Real.log_le_log (abs_pos.2 (by exact_mod_cast h0)) ?_` and prove the remaining obligations. Rewrite using `[← Int.cast_abs, ← Int.natCast_natAbs]`. Conclude with `hd` after adjusting the coercions.
-/
theorem sz_adjoin_rootOfUnity :
    ∀ n : ℕ, 0 < n → Sz ℚ⟮Complex.exp (2 * Real.pi * Complex.I / n)⟯ (Real.log n) (Real.log n) := by
  intro n hn
  haveI : NeZero n := ⟨hn.ne'⟩
  have hζ := Complex.isPrimitiveRoot_exp n hn.ne'
  set F := ℚ⟮Complex.exp (2 * Real.pi * Complex.I / n)⟯ with hF
  haveI hc : IsCyclotomicExtension {n} ℚ F := by
    change IsCyclotomicExtension {n} ℚ F.toSubalgebra
    rw [hF, IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      ((hζ.isIntegral hn).tower_top (A := ℚ)).isAlgebraic]
    exact hζ.adjoin_isCyclotomicExtension ℚ
  have hfd : FiniteDimensional ℚ F := IsCyclotomicExtension.finiteDimensional {n} ℚ F
  refine ⟨hfd, ?_⟩
  letI : NumberField F := NumberField.mk
  have hrk : Module.finrank ℚ F = Nat.totient n :=
    IsCyclotomicExtension.finrank F (Polynomial.cyclotomic.irreducible_rat hn)
  have ht : 0 < Nat.totient n := Nat.totient_pos.2 hn
  have htR : (0 : ℝ) < (Nat.totient n : ℝ) := by exact_mod_cast ht
  have hd : (NumberField.discr F).natAbs ≤ n ^ Nat.totient n := by
    rw [IsCyclotomicExtension.Rat.natAbs_discr n F]
    exact Nat.div_le_self _ _
  refine ⟨?_, ?_⟩
  · rw [hrk]
    exact Real.log_le_log htR (by exact_mod_cast Nat.totient_le n)
  · rw [hrk, div_le_iff₀ htR, mul_comm, ← Real.log_pow]
    have h0 : NumberField.discr F ≠ 0 := NumberField.discr_ne_zero F
    refine Real.log_le_log (abs_pos.2 (by exact_mod_cast h0)) ?_
    rw [← Int.cast_abs, ← Int.natCast_natAbs]
    exact_mod_cast hd

end GlobalTheory.FieldSize
