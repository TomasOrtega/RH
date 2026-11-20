import Development.AbelianVarietyTheory.Definitions.Divisors.IsEulerContraction
open GlobalTheory GlobalTheory.LogDR

namespace GlobalTheory

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Rewrite using `[Finset.sum_antidiagonal_choose_succ_mul (fun i j => (⇑D)^[i] a * (⇑D)^[j] b) n, Function.iterate_succ_apply', ih, map_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun ij hij => ?_` and prove the remaining obligations.

Rewrite `hij` using `[Finset.HasAntidiagonal.mem_antidiagonal]`. Establish `hc : (n.choose ij.2 : R) = (n.choose ij.1 : R)`. Rewrite using `[← hij, Nat.choose_symm_add]`. Rewrite using `[hc, Derivation.leibniz, Derivation.leibniz, Derivation.map_natCast, smul_zero, add_zero, Function.iterate_succ_apply', Function.iterate_succ_apply']`. Simplify using `only [smul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem derivation_iterate_leibniz {R : Type} [CommRing R] (D : Derivation ℤ R R) (a b : R) (n : ℕ) :
    (⇑D)^[n] (a * b) =
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, (n.choose ij.1 : R) * ((⇑D)^[ij.1] a * (⇑D)^[ij.2] b) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_antidiagonal_choose_succ_mul (fun i j => (⇑D)^[i] a * (⇑D)^[j] b) n,
      Function.iterate_succ_apply', ih, map_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ij hij => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
    have hc : (n.choose ij.2 : R) = (n.choose ij.1 : R) := by
      rw [← hij, Nat.choose_symm_add]
    rw [hc, Derivation.leibniz, Derivation.leibniz, Derivation.map_natCast, smul_zero, add_zero,
      Function.iterate_succ_apply', Function.iterate_succ_apply']
    simp only [smul_eq_mul]
    ring

end GlobalTheory
