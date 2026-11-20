import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Formalism.PairingDivisors.StatementH
open NumberField Polynomial IsDedekindDomain
open Formalism.DivisionValues (vw lw)

namespace GlobalTheory

/- English proof (translation)
Unfold `Formalism.PairingDivisionLocalBalance.meanInf`. Establish `hprod` using `InfinitePlace.prod_eq_abs_norm (K := K) a`. Establish `hmult : ∀ v : InfinitePlace K, v.mult = 2` using `fun v => by`. Rewrite using `[InfinitePlace.mult, if_neg (InfinitePlace.not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex v))]`. Establish `hpos : ∀ v : InfinitePlace K, 0 < v a` using `fun v => by`.

Rewrite using `[InfinitePlace.pos_iff]`. Conclude with `ha`. Establish `hsum : Real.log |((Algebra.norm ℚ a : ℚ) : ℝ)| = ∑ v : InfinitePlace K, 2 * Real.log (v a)`. Rewrite using `[show |((Algebra.norm ℚ a : ℚ) : ℝ)| = ((|Algebra.norm ℚ a| : ℚ) : ℝ) by push_cast; rfl, ← hprod, Real.log_prod]`. Use `Finset.sum_congr rfl fun v _ => ?_` and prove the remaining obligations.

Rewrite using `[hmult, Real.log_pow]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Introduce `v _`. Conclude with `pow_ne_zero _ (hpos v).ne'`.

Establish `he : ∀ v : InfinitePlace K, ‖v.embedding a‖ = v a` using `fun v => InfinitePlace.norm_embedding_eq v a`. Simplify using `only [he]`. Rewrite using `[hsum, ← Finset.mul_sum]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem meanInf_log_norm_embedding (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (a : K) (ha : a ≠ 0) :
    Formalism.PairingDivisionLocalBalance.meanInf K (fun v => Real.log ‖v.embedding a‖) = Real.log |((Algebra.norm ℚ a : ℚ) : ℝ)| / Module.finrank ℚ K := by
  unfold Formalism.PairingDivisionLocalBalance.meanInf
  have hprod := InfinitePlace.prod_eq_abs_norm (K := K) a
  have hmult : ∀ v : InfinitePlace K, v.mult = 2 := fun v => by
    rw [InfinitePlace.mult, if_neg (InfinitePlace.not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex v))]
  have hpos : ∀ v : InfinitePlace K, 0 < v a := fun v => by
    rw [InfinitePlace.pos_iff]; exact ha
  have hsum : Real.log |((Algebra.norm ℚ a : ℚ) : ℝ)| = ∑ v : InfinitePlace K, 2 * Real.log (v a) := by
    rw [show |((Algebra.norm ℚ a : ℚ) : ℝ)| = ((|Algebra.norm ℚ a| : ℚ) : ℝ) by push_cast; rfl, ← hprod, Real.log_prod]
    · refine Finset.sum_congr rfl fun v _ => ?_
      rw [hmult, Real.log_pow]; push_cast; ring
    · intro v _; exact pow_ne_zero _ (hpos v).ne'
  have he : ∀ v : InfinitePlace K, ‖v.embedding a‖ = v a := fun v => InfinitePlace.norm_embedding_eq v a
  simp only [he]
  rw [hsum, ← Finset.mul_sum]
  ring

end GlobalTheory
