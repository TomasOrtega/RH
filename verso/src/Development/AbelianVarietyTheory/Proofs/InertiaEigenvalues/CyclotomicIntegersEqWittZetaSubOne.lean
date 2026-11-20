import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EmbWInjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormPrimitiveRootPrimePowSubOnePadicComplex
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormEqZpowOfMemMaxUnramifiedSubfield
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankCyclotomicExtAndCyclotomicCharSurjective
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL GlobalTheory.Prism GlobalTheory.PrismS Polynomial
open scoped IntermediateField

namespace GlobalTheory.PrismS.Poly

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Establish `hi : IsIntegral ℚ_[l] (y : Om l)` using `Algebra.IsIntegral.isIntegral _`. Rewrite `h` using `[← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralValue_le_one_iff (minpoly.monic hi)]`. Establish `hl : minpoly ℚ_[l] (y : Om l) ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l])`. Rewrite using `[lifts_iff_coeff_lifts]`. Conclude with `fun n => ⟨⟨_, h n⟩, rfl⟩`.

Take `⟨q, hq, -, hm⟩` from `lifts_and_degree_eq_and_monic hl (minpoly.monic hi)`. Establish `h1 : IsIntegral ℤ_[l] (y : Om l)` using `⟨q, hm, by`. Rewrite using `[← aeval_def, ← aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]⟩`. Conclude with `(isIntegral_algHom_iff (K.1.val.restrictScalars ℤ_[l]) K.1.val.toRingHom.injective).1 h1`.
-/
theorem mem_OL_of_norm_le (K : FinExt l) (y : ↥K.1) (h : ‖(y : Om l)‖ ≤ 1) : y ∈ OL K := by
  have hi : IsIntegral ℚ_[l] (y : Om l) := Algebra.IsIntegral.isIntegral _
  rw [← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralValue_le_one_iff (minpoly.monic hi)] at h
  have hl : minpoly ℚ_[l] (y : Om l) ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l]) := by
    rw [lifts_iff_coeff_lifts]
    exact fun n => ⟨⟨_, h n⟩, rfl⟩
  obtain ⟨q, hq, -, hm⟩ := lifts_and_degree_eq_and_monic hl (minpoly.monic hi)
  have h1 : IsIntegral ℤ_[l] (y : Om l) := ⟨q, hm, by
    rw [← aeval_def, ← aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]⟩
  exact (isIntegral_algHom_iff (K.1.val.restrictScalars ℤ_[l]) K.1.val.toRingHom.injective).1 h1

/- English proof (translation)
Establish `hl1 : (1 : ℝ) < l` using `by exact_mod_cast (Fact.out : l.Prime).one_lt`. Establish `hl0 : (0 : ℝ) < l` using `by linarith`. Establish `hN : (0 : ℝ) < N` using `by exact_mod_cast (Nat.zero_le _).trans_lt hd`. Establish `key : ∀ i ∈ p.support, ∃ n : ℤ, ‖((p.coeff i : ↥(K0 K)) : Om l)‖ = (l : ℝ) ^ n ∧ ‖p.coeff i • π ^ i‖ = (l : ℝ) ^ ((n : ℝ) - (i : ℝ) / N)`. Introduce `i hi`.

Establish `h0 : ((p.coeff i : ↥(K0 K)) : Om l) ≠ 0`. Use `mem_support_iff.1 hi` as an intermediate fact. Conclude with `fun h => this (Subtype.ext h)`. Take `⟨n, hn⟩` from `GlobalTheory.UnramValue.norm_of_mem_unramified_subfield l K _ (p.coeff i).2 h0`. Use `⟨n, hn, ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `‖((p.coeff i : ↥(K0 K)) : Om l) * π ^ i‖ = _`. Rewrite using `[norm_mul, norm_pow, hn, hπ, ← Real.rpow_natCast, ← Real.rpow_mul hl0.le, ← Real.rpow_intCast, ← Real.rpow_add hl0]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `hpw : Set.Pairwise (p.support : Set ℕ) (fun i k => ‖p.coeff i • π ^ i‖₊ ≠ ‖p.coeff k • π ^ k‖₊)`.

Introduce `i hi k hk hik h`. Take `⟨n, -, hn⟩` from `key i hi`. Take `⟨m, -, hm⟩` from `key k hk`. Establish `h' : ‖p.coeff i • π ^ i‖ = ‖p.coeff k • π ^ k‖` using `congrArg NNReal.toReal h`. Rewrite `h'` using `[hn, hm]`.

Establish `h2` using `(Real.rpow_right_inj hl0 hl1.ne').1 h'`. Establish `h3 : ((n - m) * N : ℝ) = i - k`. Clear denominators, using `at h2` for the nonvanishing conditions. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h4 : ((n - m) * N : ℤ) = i - k` using `by exact_mod_cast h3`.

Establish `hi' : i < N` using `(le_natDegree_of_mem_supp i hi).trans_lt hd`. Establish `hk' : k < N` using `(le_natDegree_of_mem_supp k hk).trans_lt hd`. Establish `h5 : (i : ℤ) - k = 0`. Apply `Int.eq_zero_of_abs_lt_dvd (m := N) ⟨n - m, by rw [← h4]; ring⟩` to reduce the goal to its premises. Apply the tactic sequence `rw [abs_lt]; constructor <;> omega`.

Use linear arithmetic over natural numbers and integers. Distinguish the cases in `hj : j ∈ p.support`. Use `swap`. Rewrite using `[notMem_support_iff.1 hj]`. Simplify using the standard rewrite rules.

Establish `hs : ∑ i ∈ p.support, p.coeff i • π ^ i = aeval π p`. Rewrite using `[aeval_eq_sum_range' (Nat.lt_succ_self _)]`. Apply `Finset.sum_subset supp_subset_range_natDegree_succ` to reduce the goal to its premises. Introduce `i _ hi`. Rewrite using `[notMem_support_iff.1 hi, zero_smul]`.

Establish `h6` using `IsUltrametricDist.nnnorm_sum_eq_sup_of_pairwise_ne hpw`. Rewrite `h6` using `[hs]`. Establish `h7` using `Finset.le_sup (f := fun i => ‖p.coeff i • π ^ i‖₊) hj`. Rewrite `h7` using `[← h6]`. Take `⟨n, hn, hn'⟩` from `key _ hj`.

Establish `h8 : ‖p.coeff j • π ^ j‖ ≤ ‖aeval π p‖` using `h7`. Use `replace h8 := (h8.trans h1).trans (Real.rpow_zero (l : ℝ)).ge`. Rewrite `h8` using `[hn', Real.rpow_le_rpow_left_iff hl1]`. Establish `hj' : (j : ℝ) < N` using `by exact_mod_cast (le_natDegree_of_mem_supp j hj).trans_lt hd`. Establish `h9 : (j : ℝ) / N < 1` using `(div_lt_one hN).2 hj'`.

Establish `h10 : n < 1`. Establish `: (n : ℝ) < 1` using `by linarith`. Conclude with `this` after adjusting the coercions. Rewrite using `[hn]`. Conclude with `zpow_le_one_of_nonpos₀ hl1.le (by omega)`.
-/
theorem norm_coeff_le (K : FinExt l) (N : ℕ) (π : Om l)
    (hπ : ‖π‖ = (l : ℝ) ^ (-(1 : ℝ) / (N : ℝ))) (p : (↥(K0 K))[X])
    (hd : p.natDegree < N) (h1 : ‖aeval π p‖ ≤ 1) (j : ℕ) :
    ‖((p.coeff j : ↥(K0 K)) : Om l)‖ ≤ 1 := by
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl0 : (0 : ℝ) < l := by linarith
  have hN : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_le _).trans_lt hd
  have key : ∀ i ∈ p.support, ∃ n : ℤ, ‖((p.coeff i : ↥(K0 K)) : Om l)‖ = (l : ℝ) ^ n ∧
      ‖p.coeff i • π ^ i‖ = (l : ℝ) ^ ((n : ℝ) - (i : ℝ) / N) := by
    intro i hi
    have h0 : ((p.coeff i : ↥(K0 K)) : Om l) ≠ 0 := by
      have := mem_support_iff.1 hi
      exact fun h => this (Subtype.ext h)
    obtain ⟨n, hn⟩ := GlobalTheory.UnramValue.norm_of_mem_unramified_subfield l K _ (p.coeff i).2 h0
    refine ⟨n, hn, ?_⟩
    change ‖((p.coeff i : ↥(K0 K)) : Om l) * π ^ i‖ = _
    rw [norm_mul, norm_pow, hn, hπ, ← Real.rpow_natCast, ← Real.rpow_mul hl0.le,
      ← Real.rpow_intCast, ← Real.rpow_add hl0]
    congr 1
    ring
  have hpw : Set.Pairwise (p.support : Set ℕ)
      (fun i k => ‖p.coeff i • π ^ i‖₊ ≠ ‖p.coeff k • π ^ k‖₊) := by
    intro i hi k hk hik h
    obtain ⟨n, -, hn⟩ := key i hi
    obtain ⟨m, -, hm⟩ := key k hk
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
  by_cases hj : j ∈ p.support
  swap
  · rw [notMem_support_iff.1 hj]; simp
  have hs : ∑ i ∈ p.support, p.coeff i • π ^ i = aeval π p := by
    rw [aeval_eq_sum_range' (Nat.lt_succ_self _)]
    apply Finset.sum_subset supp_subset_range_natDegree_succ
    intro i _ hi
    rw [notMem_support_iff.1 hi, zero_smul]
  have h6 := IsUltrametricDist.nnnorm_sum_eq_sup_of_pairwise_ne hpw
  rw [hs] at h6
  have h7 := Finset.le_sup (f := fun i => ‖p.coeff i • π ^ i‖₊) hj
  rw [← h6] at h7
  obtain ⟨n, hn, hn'⟩ := key _ hj
  have h8 : ‖p.coeff j • π ^ j‖ ≤ ‖aeval π p‖ := h7
  replace h8 := (h8.trans h1).trans (Real.rpow_zero (l : ℝ)).ge
  rw [hn', Real.rpow_le_rpow_left_iff hl1] at h8
  have hj' : (j : ℝ) < N := by exact_mod_cast (le_natDegree_of_mem_supp j hj).trans_lt hd
  have h9 : (j : ℝ) / N < 1 := (div_lt_one hN).2 hj'
  have h10 : n < 1 := by
    have : (n : ℝ) < 1 := by linarith
    exact_mod_cast this
  rw [hn]
  exact zpow_le_one_of_nonpos₀ hl1.le (by omega)

/- English proof (translation)
Proceed by induction on `r using Polynomial.induction_on' with`. Consider the case `add p q hp hq`. Rewrite using `[eval₂_add, Polynomial.map_add, map_add, map_add, ← hp, ← hq]`. Both sides reduce to the same expression. Consider the case `monomial n a`.

Rewrite using `[eval₂_monomial, Polynomial.map_monomial, aeval_monomial, map_mul, map_pow]`. Use `push_cast`. Rewrite using `[ht]`. Both sides reduce to the same expression.
-/
theorem coe_eval₂ (K : FinExt l) (π : Om l) (t : OC l) (ht : (t : ℂ_[l]) = (π : ℂ_[l]))
    (r : (WK K)[X]) : ((r.eval₂ (intToOC (unr K)) t : OC l) : ℂ_[l]) =
      algebraMap (Om l) ℂ_[l] (aeval π (r.map ((OL (unr K)).val.toRingHom : WK K →+* ↥(K0 K)))) := by
  induction r using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [eval₂_add, Polynomial.map_add, map_add, map_add, ← hp, ← hq]; rfl
  | monomial n a =>
    rw [eval₂_monomial, Polynomial.map_monomial, aeval_monomial, map_mul, map_pow]
    push_cast
    rw [ht]
    rfl

/- English proof (translation)
Establish `hlp : l.Prime` using `Fact.out`. Establish `hint : IsIntegral ↥(K0 K) ζ` using `Algebra.IsIntegral.isIntegral ζ`. Rewrite `hx` using `[GlobalTheory.Cyc.Ks_eq_restrictScalars K s ζ hζ]`. Establish `hx' : x ∈ ((↥(K0 K))⟮ζ⟯).toSubalgebra` using `hx`. Rewrite `hx'` using `[IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic, Algebra.adjoin_singleton_eq_range_aeval]`.

Take `⟨q, rfl⟩` from `hx'`. Use `⟨taylor 1 (q %ₘ minpoly ↥(K0 K) ζ), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[natDegree_taylor, ← Nat.totient_prime_pow hlp hs, ← natDegree_cyclotomic (l ^ s) ↥(K0 K), ← GlobalTheory.Cyc.minpoly_unramifiedSubfield_eq_cyclotomic K s hs ζ hζ]`. Conclude with `natDegree_modByMonic_lt _ (minpoly.monic hint) (minpoly.ne_one _ _)`. Rewrite using `[taylor_apply, aeval_comp]`.

Simplify using `only [map_add, aeval_X, aeval_C, map_one, sub_add_cancel]`. Conclude with `aeval_modByMonic_eq_self_of_root (minpoly.aeval _ _)`.
-/
theorem exists_poly (K : FinExt l) (s : ℕ) (hs : 1 ≤ s) (ζ : Om l) (hζ : IsPrimitiveRoot ζ (l ^ s))
    (x : Om l) (hx : x ∈ Ks K s) :
    ∃ p : (↥(K0 K))[X], p.natDegree < l ^ (s - 1) * (l - 1) ∧ aeval (ζ - 1) p = x := by
  have hlp : l.Prime := Fact.out
  have hint : IsIntegral ↥(K0 K) ζ := Algebra.IsIntegral.isIntegral ζ
  rw [GlobalTheory.Cyc.Ks_eq_restrictScalars K s ζ hζ] at hx
  have hx' : x ∈ ((↥(K0 K))⟮ζ⟯).toSubalgebra := hx
  rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic,
    Algebra.adjoin_singleton_eq_range_aeval] at hx'
  obtain ⟨q, rfl⟩ := hx'
  refine ⟨taylor 1 (q %ₘ minpoly ↥(K0 K) ζ), ?_, ?_⟩
  · rw [natDegree_taylor, ← Nat.totient_prime_pow hlp hs,
      ← natDegree_cyclotomic (l ^ s) ↥(K0 K), ← GlobalTheory.Cyc.minpoly_unramifiedSubfield_eq_cyclotomic K s hs ζ hζ]
    exact natDegree_modByMonic_lt _ (minpoly.monic hint) (minpoly.ne_one _ _)
  · rw [taylor_apply, aeval_comp]
    simp only [map_add, aeval_X, aeval_C, map_one, sub_add_cancel]
    exact aeval_modByMonic_eq_self_of_root (minpoly.aeval _ _)

/- English proof (translation)
Introduce `l _ K s hs ζ hζ t ht`. Establish `hlp : l.Prime` using `Fact.out`. Establish `hnorm : ‖ζ - 1‖ = (l : ℝ) ^ (-(1 : ℝ) / ((l ^ (s - 1) * (l - 1) : ℕ) : ℝ))`. Establish `h1` using `GlobalTheory.Cyc.norm_primitiveRoot_sub_one l s hs (ζ : PadicComplex l) (hζ.map_of_injective (f := algebraMap (Om l) (PadicComplex l)) (RingHom.injective _))`. Move the coercions through the operations in `[Nat.cast_sub hlp.one_le]`.

Rewrite using `[← h1, ← PadicComplex.norm_extends]`. Use `congr 1`. Conclude with `(map_sub (algebraMap (Om l) (PadicComplex l)) ζ 1).trans (by rw [map_one]; rfl)`. Establish `hinj : Function.Injective ((OL (unr K)).val.toRingHom : WK K →+* ↥(K0 K))` using `Subtype.val_injective`. Use `⟨fun r hr h0 => ?_, fun hK x => ?_⟩` and prove the remaining obligations.

Assume the negation of the conclusion as `hne`. Establish `h1` using `coe_eval₂ K (ζ - 1) t ht r`. Rewrite `h1` using `[h0]`. Use `GlobalTheory.Cyc.aeval_ne_zero_of_norm_eq K _ (ζ - 1) hnorm _ ((Polynomial.map_ne_zero_iff hinj).2 hne) (natDegree_map_le.trans_lt hr) ?_` and prove the remaining obligations. Conclude with `(algebraMap (Om l) ℂ_[l]).injective (h1.symm.trans (map_zero _).symm)`.

Take `⟨p, hp, hpx⟩` from `exists_poly K s hs ζ hζ _ (hK (x : ↥K.1).2)`. Establish `hc` using `norm_coeff_le K _ _ hnorm p hp (hpx ▸ norm_le_one_of_mem_OL K x)`. Establish `hl : p ∈ Polynomial.lifts ((OL (unr K)).val.toRingHom : WK K →+* ↥(K0 K))`. Rewrite using `[lifts_iff_coeff_lifts]`. Conclude with `fun n => ⟨⟨_, mem_OL_of_norm_le (unr K) _ (hc n)⟩, rfl⟩`.

Take `⟨r, rfl⟩` from `(mem_lifts _).1 hl`. Use `⟨r, Subtype.ext ?_⟩` and prove the remaining obligations. Rewrite using `[coe_eval₂ K (ζ - 1) t ht r, hpx]`. Both sides reduce to the same expression.
-/
theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ), 1 ≤ s → ∀ ζ : Om l, IsPrimitiveRoot ζ (l ^ s) → ∀ t : OC l, (t : ℂ_[l]) = ((ζ - 1 : Om l) : ℂ_[l]) → (∀ r : Polynomial (WK K), r.natDegree < l ^ (s - 1) * (l - 1) → r.eval₂ (intToOC (unr K)) t = 0 → r = 0) ∧ (K.1 ≤ Ks K s → ∀ x : ↥(OL K), ∃ r : Polynomial (WK K), r.eval₂ (intToOC (unr K)) t = intToOC K x) := by
  intro l _ K s hs ζ hζ t ht
  have hlp : l.Prime := Fact.out
  have hnorm : ‖ζ - 1‖ = (l : ℝ) ^ (-(1 : ℝ) / ((l ^ (s - 1) * (l - 1) : ℕ) : ℝ)) := by
    have h1 := GlobalTheory.Cyc.norm_primitiveRoot_sub_one l s hs (ζ : PadicComplex l)
      (hζ.map_of_injective (f := algebraMap (Om l) (PadicComplex l)) (RingHom.injective _))
    push_cast [Nat.cast_sub hlp.one_le]
    rw [← h1, ← PadicComplex.norm_extends]
    congr 1
    exact (map_sub (algebraMap (Om l) (PadicComplex l)) ζ 1).trans (by rw [map_one]; rfl)
  have hinj : Function.Injective ((OL (unr K)).val.toRingHom : WK K →+* ↥(K0 K)) :=
    Subtype.val_injective
  refine ⟨fun r hr h0 => ?_, fun hK x => ?_⟩
  · by_contra hne
    have h1 := coe_eval₂ K (ζ - 1) t ht r
    rw [h0] at h1
    refine GlobalTheory.Cyc.aeval_ne_zero_of_norm_eq K _ (ζ - 1) hnorm _
      ((Polynomial.map_ne_zero_iff hinj).2 hne) (natDegree_map_le.trans_lt hr) ?_
    exact (algebraMap (Om l) ℂ_[l]).injective (h1.symm.trans (map_zero _).symm)
  · obtain ⟨p, hp, hpx⟩ := exists_poly K s hs ζ hζ _ (hK (x : ↥K.1).2)
    have hc := norm_coeff_le K _ _ hnorm p hp (hpx ▸ norm_le_one_of_mem_OL K x)
    have hl : p ∈ Polynomial.lifts ((OL (unr K)).val.toRingHom : WK K →+* ↥(K0 K)) := by
      rw [lifts_iff_coeff_lifts]
      exact fun n => ⟨⟨_, mem_OL_of_norm_le (unr K) _ (hc n)⟩, rfl⟩
    obtain ⟨r, rfl⟩ := (mem_lifts _).1 hl
    refine ⟨r, Subtype.ext ?_⟩
    rw [coe_eval₂ K (ζ - 1) t ht r, hpx]
    rfl

end GlobalTheory.PrismS.Poly
