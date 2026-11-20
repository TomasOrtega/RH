import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormPrimitiveRootPrimePowSubOnePadicComplex
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormEqZpowOfMemMaxUnramifiedSubfield
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankCyclotomicExtAndCyclotomicCharSurjective

noncomputable section

namespace GlobalTheory.Cyc

open Formalism.BasicNotions Formalism.BasicNotions.Loc Polynomial
open scoped IntermediateField

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Establish `hl1 : (1 : ℝ) < l` using `by exact_mod_cast (Fact.out : l.Prime).one_lt`. Establish `hl0 : (0 : ℝ) < l` using `by linarith`. Establish `hN : (0 : ℝ) < N` using `by exact_mod_cast (Nat.zero_le _).trans_lt hd`. Establish `key : ∀ i ∈ p.support, ∃ n : ℤ, ‖p.coeff i • π ^ i‖ = (l : ℝ) ^ ((n : ℝ) - (i : ℝ) / N)`. Introduce `i hi`.

Establish `h0 : ((p.coeff i : ↥(K0 K)) : Om l) ≠ 0`. Use `mem_support_iff.1 hi` as an intermediate fact. Conclude with `fun h => this (Subtype.ext h)`. Take `⟨n, hn⟩` from `GlobalTheory.UnramValue.norm_of_mem_unramified_subfield l K _ (p.coeff i).2 h0`. Use `⟨n, ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `‖((p.coeff i : ↥(K0 K)) : Om l) * π ^ i‖ = _`. Rewrite using `[norm_mul, norm_pow, hn, hπ, ← Real.rpow_natCast, ← Real.rpow_mul hl0.le, ← Real.rpow_intCast, ← Real.rpow_add hl0]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `hpw : Set.Pairwise (p.support : Set ℕ) (fun i k => ‖p.coeff i • π ^ i‖₊ ≠ ‖p.coeff k • π ^ k‖₊)`.

Introduce `i hi k hk hik h`. Take `⟨n, hn⟩` from `key i hi`. Take `⟨m, hm⟩` from `key k hk`. Establish `h' : ‖p.coeff i • π ^ i‖ = ‖p.coeff k • π ^ k‖` using `congrArg NNReal.toReal h`. Rewrite `h'` using `[hn, hm]`.

Establish `h2` using `(Real.rpow_right_inj hl0 hl1.ne').1 h'`. Establish `h3 : ((n - m) * N : ℝ) = i - k`. Clear denominators, using `at h2` for the nonvanishing conditions. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h4 : ((n - m) * N : ℤ) = i - k` using `by exact_mod_cast h3`.

Establish `hi' : i < N` using `(le_natDegree_of_mem_supp i hi).trans_lt hd`. Establish `hk' : k < N` using `(le_natDegree_of_mem_supp k hk).trans_lt hd`. Establish `h5 : (i : ℤ) - k = 0`. Apply `Int.eq_zero_of_abs_lt_dvd (m := N) ⟨n - m, by rw [← h4]; ring⟩` to reduce the goal to its premises. Apply the tactic sequence `rw [abs_lt]; constructor <;> omega`.

Use linear arithmetic over natural numbers and integers. Establish `hs : ∑ i ∈ p.support, p.coeff i • π ^ i = aeval π p`. Rewrite using `[aeval_eq_sum_range' (Nat.lt_succ_self _)]`. Apply `Finset.sum_subset supp_subset_range_natDegree_succ` to reduce the goal to its premises. Introduce `i _ hi`.

Rewrite using `[notMem_support_iff.1 hi, zero_smul]`. Establish `h6` using `IsUltrametricDist.nnnorm_sum_eq_sup_of_pairwise_ne hpw`. Rewrite `h6` using `[hs]`. Take `⟨i, hi, hi'⟩` from `Finset.exists_mem_eq_sup p.support (support_nonempty.2 hp) (fun i => ‖p.coeff i • π ^ i‖₊)`. Take `⟨n, hn⟩` from `key i hi`.

Use `⟨n * N - i, ?_⟩` and prove the remaining obligations. Establish `h7 : ‖aeval π p‖ = ‖p.coeff i • π ^ i‖` using `congrArg NNReal.toReal (h6.trans hi')`. Rewrite using `[h7, hn]`. Use `congr 1`. Use `push_cast`.

Clear the denominators using the available nonvanishing facts.
-/
theorem norm_aeval_of_norm_eq (K : FinExt l) (N : ℕ) (π : Om l)
    (hπ : ‖π‖ = (l : ℝ) ^ (-(1 : ℝ) / (N : ℝ))) (p : (↥(K0 K))[X]) (hp : p ≠ 0)
    (hd : p.natDegree < N) : ∃ n : ℤ, ‖aeval π p‖ = (l : ℝ) ^ ((n : ℝ) / (N : ℝ)) := by
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl0 : (0 : ℝ) < l := by linarith
  have hN : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_le _).trans_lt hd
  have key : ∀ i ∈ p.support, ∃ n : ℤ,
      ‖p.coeff i • π ^ i‖ = (l : ℝ) ^ ((n : ℝ) - (i : ℝ) / N) := by
    intro i hi
    have h0 : ((p.coeff i : ↥(K0 K)) : Om l) ≠ 0 := by
      have := mem_support_iff.1 hi
      exact fun h => this (Subtype.ext h)
    obtain ⟨n, hn⟩ := GlobalTheory.UnramValue.norm_of_mem_unramified_subfield l K _ (p.coeff i).2 h0
    refine ⟨n, ?_⟩
    change ‖((p.coeff i : ↥(K0 K)) : Om l) * π ^ i‖ = _
    rw [norm_mul, norm_pow, hn, hπ, ← Real.rpow_natCast, ← Real.rpow_mul hl0.le,
      ← Real.rpow_intCast, ← Real.rpow_add hl0]
    congr 1
    ring
  have hpw : Set.Pairwise (p.support : Set ℕ)
      (fun i k => ‖p.coeff i • π ^ i‖₊ ≠ ‖p.coeff k • π ^ k‖₊) := by
    intro i hi k hk hik h
    obtain ⟨n, hn⟩ := key i hi
    obtain ⟨m, hm⟩ := key k hk
    have h' : ‖p.coeff i • π ^ i‖ = ‖p.coeff k • π ^ k‖ := congrArg NNReal.toReal h
    rw [hn, hm] at h'
    have h2 := (Real.rpow_right_inj hl0 hl1.ne').1 h'
    have h3 : ((n - m) * N : ℝ) = i - k := by
      field_simp at h2
      linarith
    have h4 : ((n - m) * N : ℤ) = i - k := by exact_mod_cast h3
    have hi' : i < N := (le_natDegree_of_mem_supp i hi).trans_lt hd
    have hk' : k < N := (le_natDegree_of_mem_supp k hk).trans_lt hd
    have h5 : (i : ℤ) - k = 0 := by
      apply Int.eq_zero_of_abs_lt_dvd (m := N) ⟨n - m, by rw [← h4]; ring⟩
      rw [abs_lt]; constructor <;> omega
    omega
  have hs : ∑ i ∈ p.support, p.coeff i • π ^ i = aeval π p := by
    rw [aeval_eq_sum_range' (Nat.lt_succ_self _)]
    apply Finset.sum_subset supp_subset_range_natDegree_succ
    intro i _ hi
    rw [notMem_support_iff.1 hi, zero_smul]
  have h6 := IsUltrametricDist.nnnorm_sum_eq_sup_of_pairwise_ne hpw
  rw [hs] at h6
  obtain ⟨i, hi, hi'⟩ := Finset.exists_mem_eq_sup p.support (support_nonempty.2 hp)
    (fun i => ‖p.coeff i • π ^ i‖₊)
  obtain ⟨n, hn⟩ := key i hi
  refine ⟨n * N - i, ?_⟩
  have h7 : ‖aeval π p‖ = ‖p.coeff i • π ^ i‖ := congrArg NNReal.toReal (h6.trans hi')
  rw [h7, hn]
  congr 1
  push_cast
  field_simp

/- English proof (translation)
Introduce `l _ K j hj x hx hx0`. Establish `hlp : l.Prime` using `Fact.out`. Take `⟨ζ, hζ⟩` from `exists_primitiveRoot_Om (l := l) j`. Establish `hint : IsIntegral ↥(K0 K) ζ` using `Algebra.IsIntegral.isIntegral ζ`. Rewrite `hx` using `[Ks_eq_restrictScalars K j ζ hζ, IntermediateField.mem_restrictScalars]`.

Establish `hx' : x ∈ Algebra.adjoin ↥(K0 K) {ζ}`. Rewrite using `[← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic]`. Conclude with `hx`. Rewrite `hx'` using `[Algebra.adjoin_singleton_eq_range_aeval]`. Take `⟨q, hq⟩` from `hx'`.

Establish `hcast : ((Nat.totient (l ^ j) : ℕ) : ℝ) = (l : ℝ) ^ (j - 1) * ((l : ℝ) - 1)`. Rewrite using `[Nat.totient_prime_pow hlp hj]`. Move the coercions through the operations in `[Nat.cast_sub hlp.one_le]`. Both sides reduce to the same expression. Establish `hnorm : ‖ζ - 1‖ = (l : ℝ) ^ (-(1 : ℝ) / ((Nat.totient (l ^ j) : ℕ) : ℝ))`.

Establish `h1` using `norm_primitiveRoot_sub_one l j hj (ζ : PadicComplex l) (hζ.map_of_injective (f := algebraMap (Om l) (PadicComplex l)) (RingHom.injective _))`. Rewrite using `[hcast, ← h1, ← PadicComplex.norm_extends]`. Use `congr 1`. Conclude with `(map_sub (algebraMap (Om l) (PadicComplex l)) ζ 1).trans (by rw [map_one]; rfl)`. Use `set r := q %ₘ minpoly ↥(K0 K) ζ with hr`.

Establish `hrx : aeval ζ r = x`. Rewrite using `[hr, aeval_modByMonic_eq_self_of_root (minpoly.aeval _ _)]`. Conclude with `hq`. Establish `hr0 : r ≠ 0`. Introduce `h`.

Rewrite `hrx` using `[h, map_zero]`. Conclude with `hx0 hrx.symm`. Establish `hdeg : r.natDegree < Nat.totient (l ^ j)`. Use `natDegree_lt_natDegree hr0 (degree_modByMonic_lt q (minpoly.monic hint))` as an intermediate fact. Rewrite `this` using `[minpoly_unramifiedSubfield_eq_cyclotomic K j hj ζ hζ, natDegree_cyclotomic]`. Then use the resulting hypothesis.

Take `⟨n, hn⟩` from `norm_aeval_of_norm_eq K _ (ζ - 1) hnorm (taylor 1 r) (fun h => hr0 (taylor_injective 1 (by rw [h, map_zero]))) (by rwa [natDegree_taylor])`. Use `⟨n, ?_⟩` and prove the remaining obligations. Rewrite using `[← hcast, ← hn, ← hrx, taylor_apply, aeval_comp]`. Simplify using the standard rewrite rules.
-/
theorem norm_of_mem_Ks : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (j : ℕ), 1 ≤ j →
    ∀ x : Om l, x ∈ Ks K j → x ≠ 0 →
      ∃ n : ℤ, ‖x‖ = (l : ℝ) ^ ((n : ℝ) / ((l : ℝ) ^ (j - 1) * ((l : ℝ) - 1))) := by
  intro l _ K j hj x hx hx0
  have hlp : l.Prime := Fact.out
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_Om (l := l) j
  have hint : IsIntegral ↥(K0 K) ζ := Algebra.IsIntegral.isIntegral ζ
  rw [Ks_eq_restrictScalars K j ζ hζ, IntermediateField.mem_restrictScalars] at hx
  have hx' : x ∈ Algebra.adjoin ↥(K0 K) {ζ} := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic]
    exact hx
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hx'
  obtain ⟨q, hq⟩ := hx'
  have hcast : ((Nat.totient (l ^ j) : ℕ) : ℝ) = (l : ℝ) ^ (j - 1) * ((l : ℝ) - 1) := by
    rw [Nat.totient_prime_pow hlp hj]
    push_cast [Nat.cast_sub hlp.one_le]
    rfl
  have hnorm : ‖ζ - 1‖ = (l : ℝ) ^ (-(1 : ℝ) / ((Nat.totient (l ^ j) : ℕ) : ℝ)) := by
    have h1 := norm_primitiveRoot_sub_one l j hj (ζ : PadicComplex l)
      (hζ.map_of_injective (f := algebraMap (Om l) (PadicComplex l)) (RingHom.injective _))
    rw [hcast, ← h1, ← PadicComplex.norm_extends]
    congr 1
    exact (map_sub (algebraMap (Om l) (PadicComplex l)) ζ 1).trans (by rw [map_one]; rfl)
  set r := q %ₘ minpoly ↥(K0 K) ζ with hr
  have hrx : aeval ζ r = x := by
    rw [hr, aeval_modByMonic_eq_self_of_root (minpoly.aeval _ _)]
    exact hq
  have hr0 : r ≠ 0 := by
    intro h
    rw [h, map_zero] at hrx
    exact hx0 hrx.symm
  have hdeg : r.natDegree < Nat.totient (l ^ j) := by
    have := natDegree_lt_natDegree hr0 (degree_modByMonic_lt q (minpoly.monic hint))
    rwa [minpoly_unramifiedSubfield_eq_cyclotomic K j hj ζ hζ, natDegree_cyclotomic] at this
  obtain ⟨n, hn⟩ := norm_aeval_of_norm_eq K _ (ζ - 1) hnorm (taylor 1 r)
    (fun h => hr0 (taylor_injective 1 (by rw [h, map_zero]))) (by rwa [natDegree_taylor])
  refine ⟨n, ?_⟩
  rw [← hcast, ← hn, ← hrx, taylor_apply, aeval_comp]
  simp

end GlobalTheory.Cyc
