import Mathlib
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.LocalRingCardinality.AdicCompletionLocal.InstIsAdicCompleteOCSpanSingletonSetCast
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOrbitPadicComplex
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormMemCyclotomicLayerPrimeRpow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAlgClosedTiltFieldAndValuationRing
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicTateMaximalIdealKillsFirstCohomologyStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicTowerFixedIffMemCompletedIntegersStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqOfPowEqOneOfNormSubLtOne

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc Polynomial

noncomputable section

namespace GlobalTheory.TiltInvariants

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Establish `hl1 : (1 : ℝ) < l` using `by exact_mod_cast (Fact.out : l.Prime).one_lt`. Establish `hl0 : (0 : ℝ) < l` using `by linarith`. Establish `hN : (0 : ℝ) < N` using `by exact_mod_cast (Nat.zero_le _).trans_lt hd`. Establish `key : ∀ i ∈ p.support, ∃ n : ℤ, ‖((p.coeff i : ↥(K0 K)) : Om l)‖ = (l : ℝ) ^ n ∧ ‖p.coeff i • π ^ i‖ = (l : ℝ) ^ ((n : ℝ) - (i : ℝ) / N)`. Introduce `i hi`.

Establish `h0 : ((p.coeff i : ↥(K0 K)) : Om l) ≠ 0`. Use `mem_support_iff.1 hi` as an intermediate fact. Conclude with `fun h => this (Subtype.ext h)`. Take `⟨n, hn⟩` from `GlobalTheory.UnramValue.norm_of_mem_unramified_subfield l K _ (p.coeff i).2 h0`. Use `⟨n, hn, ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `‖((p.coeff i : ↥(K0 K)) : Om l) * π ^ i‖ = _`. Rewrite using `[norm_mul, norm_pow, hn, hπ, ← Real.rpow_natCast, ← Real.rpow_mul hl0.le, ← Real.rpow_intCast, ← Real.rpow_add hl0]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `hpw : Set.Pairwise (p.support : Set ℕ) (fun i k => ‖p.coeff i • π ^ i‖₊ ≠ ‖p.coeff k • π ^ k‖₊)`.

Introduce `i hi k hk hik h`. Take `⟨n, -, hn⟩` from `key i hi`. Take `⟨m, -, hm⟩` from `key k hk`. Establish `h' : ‖p.coeff i • π ^ i‖ = ‖p.coeff k • π ^ k‖` using `congrArg NNReal.toReal h`. Rewrite `h'` using `[hn, hm]`.

Establish `h2` using `(Real.rpow_right_inj hl0 hl1.ne').1 h'`. Establish `h3 : ((n - m) * N : ℝ) = i - k`. Clear denominators, using `at h2` for the nonvanishing conditions. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h4 : ((n - m) * N : ℤ) = i - k` using `by exact_mod_cast h3`.

Establish `hi' : i < N` using `(le_natDegree_of_mem_supp i hi).trans_lt hd`. Establish `hk' : k < N` using `(le_natDegree_of_mem_supp k hk).trans_lt hd`. Establish `h5 : (i : ℤ) - k = 0`. Apply `Int.eq_zero_of_abs_lt_dvd (m := N) ⟨n - m, by rw [← h4]; ring⟩` to reduce the goal to its premises. Apply the tactic sequence `rw [abs_lt]; constructor <;> omega`.

Use linear arithmetic over natural numbers and integers. Establish `hs : ∑ i ∈ p.support, p.coeff i • π ^ i = aeval π p`. Rewrite using `[aeval_eq_sum_range' (Nat.lt_succ_self _)]`. Apply `Finset.sum_subset supp_subset_range_natDegree_succ` to reduce the goal to its premises. Introduce `i _ hi`.

Rewrite using `[notMem_support_iff.1 hi, zero_smul]`. Establish `h6` using `IsUltrametricDist.nnnorm_sum_eq_sup_of_pairwise_ne hpw`. Rewrite `h6` using `[hs]`. Distinguish the cases in `ha : a ∈ p.support`. Take `⟨n, hn, hn'⟩` from `key a ha`.

Establish `h7 : ‖p.coeff a • π ^ a‖₊ ≤ ‖aeval π p‖₊`. Rewrite using `[h6]`. Conclude with `Finset.le_sup (f := fun i => ‖p.coeff i • π ^ i‖₊) ha`. Establish `h8 : ‖p.coeff a • π ^ a‖ ≤ 1` using `le_trans (by exact_mod_cast h7) h1`. Rewrite `h8` using `[hn', ← Real.rpow_zero (l : ℝ), Real.rpow_le_rpow_left_iff hl1]`.

Establish `ha' : (a : ℝ) < N` using `by exact_mod_cast (le_natDegree_of_mem_supp a ha).trans_lt hd`. Establish `h9 : (a : ℝ) / N < 1` using `(div_lt_one hN).2 ha'`. Establish `h10 : n < 1` using `by exact_mod_cast (by linarith : (n : ℝ) < 1)`. Rewrite using `[hn]`. Conclude with `zpow_le_one_of_nonpos₀ hl1.le (by omega)`.

Rewrite using `[notMem_support_iff.1 ha]`. Simplify using the standard rewrite rules.
-/
theorem norm_coeff_le (K : FinExt l) (N : ℕ) (π : Om l)
    (hπ : ‖π‖ = (l : ℝ) ^ (-(1 : ℝ) / (N : ℝ))) (p : (↥(K0 K))[X])
    (hd : p.natDegree < N) (h1 : ‖aeval π p‖ ≤ 1) (a : ℕ) : ‖((p.coeff a : ↥(K0 K)) : Om l)‖ ≤ 1 := by
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
  have hs : ∑ i ∈ p.support, p.coeff i • π ^ i = aeval π p := by
    rw [aeval_eq_sum_range' (Nat.lt_succ_self _)]
    apply Finset.sum_subset supp_subset_range_natDegree_succ
    intro i _ hi
    rw [notMem_support_iff.1 hi, zero_smul]
  have h6 := IsUltrametricDist.nnnorm_sum_eq_sup_of_pairwise_ne hpw
  rw [hs] at h6
  by_cases ha : a ∈ p.support
  · obtain ⟨n, hn, hn'⟩ := key a ha
    have h7 : ‖p.coeff a • π ^ a‖₊ ≤ ‖aeval π p‖₊ := by
      rw [h6]
      exact Finset.le_sup (f := fun i => ‖p.coeff i • π ^ i‖₊) ha
    have h8 : ‖p.coeff a • π ^ a‖ ≤ 1 := le_trans (by exact_mod_cast h7) h1
    rw [hn', ← Real.rpow_zero (l : ℝ), Real.rpow_le_rpow_left_iff hl1] at h8
    have ha' : (a : ℝ) < N := by exact_mod_cast (le_natDegree_of_mem_supp a ha).trans_lt hd
    have h9 : (a : ℝ) / N < 1 := (div_lt_one hN).2 ha'
    have h10 : n < 1 := by exact_mod_cast (by linarith : (n : ℝ) < 1)
    rw [hn]
    exact zpow_le_one_of_nonpos₀ hl1.le (by omega)
  · rw [notMem_support_iff.1 ha]; simp

/- English proof (translation)
Establish `hlp : l.Prime` using `Fact.out`. Distinguish the cases in `hx0 : x = 0`. Rewrite using `[hx0]`. Conclude with `zero_mem _`. Establish `hint : IsIntegral ↥(K0 K) ζ` using `Algebra.IsIntegral.isIntegral ζ`.

Rewrite `hx` using `[Ks_eq_restrictScalars K j ζ hζ, IntermediateField.mem_restrictScalars]`. Establish `hx' : x ∈ Algebra.adjoin ↥(K0 K) {ζ}`. Rewrite using `[← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic]`. Conclude with `hx`. Rewrite `hx'` using `[Algebra.adjoin_singleton_eq_range_aeval]`.

Take `⟨q, hq⟩` from `hx'`. Establish `hcast : ((Nat.totient (l ^ j) : ℕ) : ℝ) = (l : ℝ) ^ (j - 1) * ((l : ℝ) - 1)`. Rewrite using `[Nat.totient_prime_pow hlp hj]`. Move the coercions through the operations in `[Nat.cast_sub hlp.one_le]`. Both sides reduce to the same expression.

Establish `hnorm : ‖ζ - 1‖ = (l : ℝ) ^ (-(1 : ℝ) / ((Nat.totient (l ^ j) : ℕ) : ℝ))`. Establish `h1` using `norm_primitiveRoot_sub_one l j hj (ζ : PadicComplex l) (hζ.map_of_injective (f := algebraMap (Om l) (PadicComplex l)) (RingHom.injective _))`. Rewrite using `[hcast, ← h1, ← PadicComplex.norm_extends]`. Use `congr 1`. Conclude with `(map_sub (algebraMap (Om l) (PadicComplex l)) ζ 1).trans (by rw [map_one]; rfl)`.

Use `set r := q %ₘ minpoly ↥(K0 K) ζ with hr`. Establish `hrx : aeval ζ r = x`. Rewrite using `[hr, aeval_modByMonic_eq_self_of_root (minpoly.aeval _ _)]`. Conclude with `hq`. Establish `hr0 : r ≠ 0`.

Introduce `h`. Rewrite `hrx` using `[h, map_zero]`. Conclude with `hx0 hrx.symm`. Establish `hdeg : r.natDegree < Nat.totient (l ^ j)`. Use `natDegree_lt_natDegree hr0 (degree_modByMonic_lt q (minpoly.monic hint))` as an intermediate fact.

Rewrite `this` using `[minpoly_unramifiedSubfield_eq_cyclotomic K j hj ζ hζ, natDegree_cyclotomic]`. Then use the resulting hypothesis. Establish `he : aeval (ζ - 1) (taylor 1 r) = x`. Rewrite using `[← hrx, taylor_apply, aeval_comp]`. Simplify using the standard rewrite rules. Establish `hc` using `norm_coeff_le K _ (ζ - 1) hnorm (taylor 1 r) (by rwa [natDegree_taylor]) (by rwa [he])`.

Rewrite using `[← he, aeval_eq_sum_range]`. Use `sum_mem fun i _ => ?_` and prove the remaining obligations. Conclude with `mul_mem (h0 _ (Subtype.property _) (hc i)) (pow_mem (sub_mem hζR (one_mem _)) _)`.
-/
theorem mem_of_mem_Ks (K : FinExt l) (j : ℕ) (hj : 1 ≤ j) (ζ : Om l) (hζ : IsPrimitiveRoot ζ (l ^ j))
    (R : Subring (Om l)) (hζR : ζ ∈ R) (h0 : ∀ c ∈ K0 K, ‖c‖ ≤ 1 → c ∈ R)
    (x : Om l) (hx : x ∈ Ks K j) (hx1 : ‖x‖ ≤ 1) : x ∈ R := by
  have hlp : l.Prime := Fact.out
  by_cases hx0 : x = 0
  · rw [hx0]; exact zero_mem _
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
  have he : aeval (ζ - 1) (taylor 1 r) = x := by
    rw [← hrx, taylor_apply, aeval_comp]
    simp
  have hc := norm_coeff_le K _ (ζ - 1) hnorm (taylor 1 r) (by rwa [natDegree_taylor]) (by rwa [he])
  rw [← he, aeval_eq_sum_range]
  refine sum_mem fun i _ => ?_
  exact mul_mem (h0 _ (Subtype.property _) (hc i)) (pow_mem (sub_mem hζR (one_mem _)) _)

/- English proof (translation)
Establish `hmono : Monotone (Ks K)`. Introduce `i j h`. Use `sup_le_sup_left (IntermediateField.adjoin.mono _ _ _ ?_) _` and prove the remaining obligations. Introduce `x hx`. Take `⟨d, rfl⟩` from `Nat.exists_eq_add_of_le h`.

Simplify using `only [Set.mem_setOf_eq] at hx ⊢`. Rewrite using `[pow_add, pow_mul, hx, one_pow]`. Establish `h : Kinf K ≤ ⨆ i, Ks K i`. Use `sup_le (le_trans (le_sup_left : _ ≤ Ks K 0) (le_iSup (Ks K) 0)) ?_` and prove the remaining obligations. Rewrite using `[IntermediateField.adjoin_le_iff]`.

Introduce and unpack `y ⟨i, hy⟩`. Conclude with `le_iSup (Ks K) i ((le_sup_right : _ ≤ Ks K i) (IntermediateField.subset_adjoin _ _ hy))`. Establish `h3 : x ∈ ((⨆ i, Ks K i : IntermediateField ℚ_[l] (Om l)) : Set (Om l))` using `h hx`. Rewrite `h3` using `[IntermediateField.coe_iSup_of_directed hmono.directed_le]`. Take `⟨i, hi⟩ : ∃ i, x ∈ Ks K i` from `by simpa using h3`.

Conclude with `⟨i + 1, by omega, hmono (Nat.le_succ i) hi⟩`.
-/
theorem exists_level (K : FinExt l) {x : Om l} (hx : x ∈ Kinf K) : ∃ i, 1 ≤ i ∧ x ∈ Ks K i := by
  have hmono : Monotone (Ks K) := by
    intro i j h
    refine sup_le_sup_left (IntermediateField.adjoin.mono _ _ _ ?_) _
    intro x hx
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    simp only [Set.mem_setOf_eq] at hx ⊢
    rw [pow_add, pow_mul, hx, one_pow]
  have h : Kinf K ≤ ⨆ i, Ks K i := by
    refine sup_le (le_trans (le_sup_left : _ ≤ Ks K 0) (le_iSup (Ks K) 0)) ?_
    rw [IntermediateField.adjoin_le_iff]
    rintro y ⟨i, hy⟩
    exact le_iSup (Ks K) i ((le_sup_right : _ ≤ Ks K i) (IntermediateField.subset_adjoin _ _ hy))
  have h3 : x ∈ ((⨆ i, Ks K i : IntermediateField ℚ_[l] (Om l)) : Set (Om l)) := h hx
  rw [IntermediateField.coe_iSup_of_directed hmono.directed_le] at h3
  obtain ⟨i, hi⟩ : ∃ i, x ∈ Ks K i := by simpa using h3
  exact ⟨i + 1, by omega, hmono (Nat.le_succ i) hi⟩

open GlobalTheory.UnramValue in

/- English proof (translation)
Establish `hp : l.Prime` using `Fact.out`. Establish `hl1 : (1 : ℝ) < l` using `by exact_mod_cast hp.one_lt`. Establish `hl0 : (l : Om l) ≠ 0` using `Nat.cast_ne_zero.mpr hp.ne_zero`. Take `⟨m, hm, hl, a, ha, h⟩` from `exists_mul_mem hc`. Use `⟨m, hm, hl, ?_⟩` and prove the remaining obligations.

Establish `key : ∀ n : ℕ, (l : Om l) ^ n * c ∈ rootRing l m → c ∈ rootRing l m`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`.

Introduce `hn`. Take `⟨z, hz, e⟩` from `exists_eq_mul hm hl hn (by`. Rewrite using `[norm_mul, norm_pow, norm_l]`. Conclude with `mul_lt_one_of_nonneg_of_lt_one_left (by positivity) (pow_lt_one₀ (by positivity) (inv_lt_one_of_one_lt₀ hl1) (Nat.succ_ne_zero n)) h1)`. Apply `ih` to reduce the goal to its premises.

Establish `: (l : Om l) ^ n * c = z` using `mul_left_cancel₀ hl0 (by rw [← e]; ring)`. Rewrite using `[this]` and apply the resulting hypothesis. Apply `key a.valuation` to reduce the goal to its premises. Establish `e` using `PadicInt.unitCoeff_spec ha`. Use `set u := PadicInt.unitCoeff ha`.

Establish `: (l : Om l) ^ a.valuation * c = algebraMap ℤ_[l] (Om l) ((u⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) * (algebraMap ℤ_[l] (Om l) a * c)`. Rewrite using `[← mul_assoc, ← map_mul]`. Use `congr 1`. Use `conv_rhs => rw [e]`. Rewrite using `[← mul_assoc, Units.inv_mul, one_mul, map_pow, map_natCast]`.

Rewrite using `[this]`. Conclude with `mul_mem (Subalgebra.algebraMap_mem _ _) h`.
-/
theorem mem_rootRing {c : Om l} (hc : c ∈ MaximalUnramifiedExtension l) (h1 : ‖c‖ ≤ 1) :
    ∃ m : ℕ, 0 < m ∧ ¬ l ∣ m ∧ c ∈ rootRing l m := by
  have hp : l.Prime := Fact.out
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hp.one_lt
  have hl0 : (l : Om l) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  obtain ⟨m, hm, hl, a, ha, h⟩ := exists_mul_mem hc
  refine ⟨m, hm, hl, ?_⟩
  have key : ∀ n : ℕ, (l : Om l) ^ n * c ∈ rootRing l m → c ∈ rootRing l m := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      intro hn
      obtain ⟨z, hz, e⟩ := exists_eq_mul hm hl hn (by
        rw [norm_mul, norm_pow, norm_l]
        exact mul_lt_one_of_nonneg_of_lt_one_left (by positivity)
          (pow_lt_one₀ (by positivity) (inv_lt_one_of_one_lt₀ hl1) (Nat.succ_ne_zero n)) h1)
      apply ih
      have : (l : Om l) ^ n * c = z := mul_left_cancel₀ hl0 (by rw [← e]; ring)
      rwa [this]
  apply key a.valuation
  have e := PadicInt.unitCoeff_spec ha
  set u := PadicInt.unitCoeff ha
  have : (l : Om l) ^ a.valuation * c =
      algebraMap ℤ_[l] (Om l) ((u⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) * (algebraMap ℤ_[l] (Om l) a * c) := by
    rw [← mul_assoc, ← map_mul]
    congr 1
    conv_rhs => rw [e]
    rw [← mul_assoc, Units.inv_mul, one_mul, map_pow, map_natCast]
  rw [this]
  exact mul_mem (Subalgebra.algebraMap_mem _ _) h

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.RootsOfUnityClose.eq_of_pow_eq_one_of_norm_sub_lt_one`. Consider the case `exact _root_.GlobalTheory.RootsOfUnityClose.eq_of_pow_eq_one_of_norm_sub_lt_one`. Consider the case `(apply _root_.GlobalTheory.RootsOfUnityClose.eq_of_pow_eq_one_of_norm_sub_lt_one <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.RootsOfUnityClose.eq_of_pow_eq_one_of_norm_sub_lt_one <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.RootsOfUnityClose.eq_of_pow_eq_one_of_norm_sub_lt_one <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.RootsOfUnityClose.eq_of_pow_eq_one_of_norm_sub_lt_one ..)`.
-/
theorem root_eq_of_norm_lt {m : ℕ} (hm : 0 < m) (hl : ¬ l ∣ m) {a b : Om l} (ha : a ^ m = 1)
    (hb : b ^ m = 1) (h : ‖a - b‖ < 1) : a = b := by
  first
  | exact @_root_.GlobalTheory.RootsOfUnityClose.eq_of_pow_eq_one_of_norm_sub_lt_one
  | exact _root_.GlobalTheory.RootsOfUnityClose.eq_of_pow_eq_one_of_norm_sub_lt_one
  | (apply _root_.GlobalTheory.RootsOfUnityClose.eq_of_pow_eq_one_of_norm_sub_lt_one <;> assumption)
  | (intros; apply _root_.GlobalTheory.RootsOfUnityClose.eq_of_pow_eq_one_of_norm_sub_lt_one <;> assumption)
  | (intros; apply @_root_.GlobalTheory.RootsOfUnityClose.eq_of_pow_eq_one_of_norm_sub_lt_one <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.RootsOfUnityClose.eq_of_pow_eq_one_of_norm_sub_lt_one ..)

open GlobalTheory.UnramValue in

/- English proof (translation)
Establish `hp : l.Prime` using `Fact.out`. Establish `hl1 : (1 : ℝ) < l` using `by exact_mod_cast hp.one_lt`. Take `⟨m, hm, hl, hcm⟩` from `mem_rootRing hc.2 h1.le`. Take `⟨z, hz, e⟩` from `pow_sub_mem hl hcm`. Establish `ht : 0 < m.totient` using `Nat.totient_pos.mpr hm`.

Establish `hq1 : 1 < l ^ m.totient` using `Nat.one_lt_pow ht.ne' hp.one_lt`. Take `⟨M, hM⟩ : ∃ M, l ^ m.totient = M + 1` from `⟨l ^ m.totient - 1, by omega⟩`. Establish `hM0 : 0 < M` using `by omega`. Establish `hlM : ¬ l ∣ M`. Introduce `h`.

Establish `h2 : l ∣ M + 1` using `hM ▸ dvd_pow_self l ht.ne'`. Conclude with `hp.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right h).1 h2))`. Establish `hn : ‖c ^ M - 1‖ < 1`. Establish `e2 : c * (c ^ M - 1) = l * z` using `by rw [hM] at e; linear_combination e`. Use `congrArg norm e2` as an intermediate fact.

Rewrite `this` using `[norm_mul, h1, one_mul, norm_mul, norm_l]`. Rewrite using `[this]`. Conclude with `mul_lt_one_of_nonneg_of_lt_one_left (by positivity) (inv_lt_one_of_one_lt₀ hl1) (norm_le_one hm hz)`. Use `haveI : NeZero M := ⟨hM0.ne'⟩`. Take `⟨μ, hμ⟩` from `HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) M`.

Establish `hprod` using `congrArg (eval c) (X_pow_sub_one_eq_prod hM0 hμ)`. Simplify using `only [eval_sub, eval_pow, eval_X, eval_one, eval_prod, eval_C] at hprod`. Choose the witnesses or unpack the hypotheses as in `⟨ω, hω, hcω⟩ : ∃ ω ∈ nthRootsFinset M (1 : Om l), ‖c - ω‖ < 1 := by`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`.

Rewrite `hn` using `[hprod, norm_prod]`. Conclude with `absurd hn (not_lt.2 (Finset.prod_induction _ (fun t : ℝ => 1 ≤ t) (fun a b ha hb => one_le_mul_of_one_le_of_one_le ha hb) le_rfl hcon))`. Rewrite `hω` using `[mem_nthRootsFinset hM0]`. Use `⟨ω, ?_, M, hM0, hlM, hω, hcω⟩` and prove the remaining obligations. Rewrite using `[← InfiniteGalois.fixedField_fixingSubgroup (K0 K), IntermediateField.mem_fixedField_iff]`.

Introduce `σ hσ`. Establish `hσc : σ c = c` using `(IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ c hc`. Use `root_eq_of_norm_lt hM0 hlM (by rw [← map_pow, hω, map_one]) hω ?_` and prove the remaining obligations. Establish `: σ ω - ω = (c - ω) + -σ (c - ω)` using `by rw [map_sub, hσc]; ring`. Rewrite using `[this]`.

Use `(IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt hcω ?_)` and prove the remaining obligations. Rewrite using `[norm_neg, GlobalTheory.RingBasics.norm_gal]` and apply the resulting hypothesis.
-/
theorem exists_root (K : FinExt l) {c : Om l} (hc : c ∈ K0 K) (h1 : ‖c‖ = 1) :
    ∃ ω ∈ K0 K, ∃ m : ℕ, 0 < m ∧ ¬ l ∣ m ∧ ω ^ m = 1 ∧ ‖c - ω‖ < 1 := by
  have hp : l.Prime := Fact.out
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hp.one_lt
  obtain ⟨m, hm, hl, hcm⟩ := mem_rootRing hc.2 h1.le
  obtain ⟨z, hz, e⟩ := pow_sub_mem hl hcm
  have ht : 0 < m.totient := Nat.totient_pos.mpr hm
  have hq1 : 1 < l ^ m.totient := Nat.one_lt_pow ht.ne' hp.one_lt
  obtain ⟨M, hM⟩ : ∃ M, l ^ m.totient = M + 1 := ⟨l ^ m.totient - 1, by omega⟩
  have hM0 : 0 < M := by omega
  have hlM : ¬ l ∣ M := by
    intro h
    have h2 : l ∣ M + 1 := hM ▸ dvd_pow_self l ht.ne'
    exact hp.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right h).1 h2))
  have hn : ‖c ^ M - 1‖ < 1 := by
    have e2 : c * (c ^ M - 1) = l * z := by rw [hM] at e; linear_combination e
    have := congrArg norm e2
    rw [norm_mul, h1, one_mul, norm_mul, norm_l] at this
    rw [this]
    exact mul_lt_one_of_nonneg_of_lt_one_left (by positivity)
      (inv_lt_one_of_one_lt₀ hl1) (norm_le_one hm hz)
  haveI : NeZero M := ⟨hM0.ne'⟩
  obtain ⟨μ, hμ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) M
  have hprod := congrArg (eval c) (X_pow_sub_one_eq_prod hM0 hμ)
  simp only [eval_sub, eval_pow, eval_X, eval_one, eval_prod, eval_C] at hprod
  obtain ⟨ω, hω, hcω⟩ : ∃ ω ∈ nthRootsFinset M (1 : Om l), ‖c - ω‖ < 1 := by
    by_contra hcon
    push Not at hcon
    rw [hprod, norm_prod] at hn
    exact absurd hn (not_lt.2 (Finset.prod_induction _ (fun t : ℝ => 1 ≤ t)
      (fun a b ha hb => one_le_mul_of_one_le_of_one_le ha hb) le_rfl hcon))
  rw [mem_nthRootsFinset hM0] at hω
  refine ⟨ω, ?_, M, hM0, hlM, hω, hcω⟩
  rw [← InfiniteGalois.fixedField_fixingSubgroup (K0 K), IntermediateField.mem_fixedField_iff]
  intro σ hσ
  have hσc : σ c = c := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ c hc
  refine root_eq_of_norm_lt hM0 hlM (by rw [← map_pow, hω, map_one]) hω ?_
  have : σ ω - ω = (c - ω) + -σ (c - ω) := by rw [map_sub, hσc]; ring
  rw [this]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt hcω ?_)
  rwa [norm_neg, GlobalTheory.RingBasics.norm_gal]

/- English proof (translation)
Establish `hl1 : (1 : ℝ) < l` using `by exact_mod_cast (Fact.out : l.Prime).one_lt`. Distinguish the cases in `h0 : c = 0`. Simplify using `[h0]`. Take `⟨n, hn⟩` from `GlobalTheory.UnramValue.norm_of_mem_unramified_subfield l K c hc h0`. Rewrite `h1`, the goal using `[hn]`.

Rewrite using `[GlobalTheory.UnramValue.norm_l, ← zpow_neg_one]`. Establish `: n < 0` using `(zpow_lt_one_iff_right₀ hl1).1 h1`. Conclude with `zpow_le_zpow_right₀ hl1.le (by omega)`.
-/
theorem norm_le_l (K : FinExt l) {c : Om l} (hc : c ∈ K0 K) (h1 : ‖c‖ < 1) : ‖c‖ ≤ ‖(l : Om l)‖ := by
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  by_cases h0 : c = 0
  · simp [h0]
  obtain ⟨n, hn⟩ := GlobalTheory.UnramValue.norm_of_mem_unramified_subfield l K c hc h0
  rw [hn] at h1 ⊢
  rw [GlobalTheory.UnramValue.norm_l, ← zpow_neg_one]
  have : n < 0 := (zpow_lt_one_iff_right₀ hl1).1 h1
  exact zpow_le_zpow_right₀ hl1.le (by omega)

/- English proof (translation)
Establish `hp : l.Prime` using `Fact.out`. Establish `hl2 : (2 : ℝ) ≤ l` using `by exact_mod_cast hp.two_le`. Establish `hl1 : (1 : ℝ) < l` using `by linarith`. Take `⟨ζ, hζ⟩` from `exists_primitiveRoot_Om (l := l) 2`. Establish `h1` using `norm_primitiveRoot_sub_one l 2 (by norm_num) (ζ : PadicComplex l) (hζ.map_of_injective (f := algebraMap (Om l) (PadicComplex l)) (RingHom.injective _))`.

Establish `hmem : ζ ∈ Kinf K` using `(le_sup_right : _ ≤ Kinf K) (IntermediateField.subset_adjoin _ _ ⟨2, hζ.pow_eq_one⟩)`. Establish `hl : ‖(l : PadicComplex l)‖ = (l : ℝ) ^ (-1 : ℝ)`. Rewrite using `[← map_natCast (algebraMap (Om l) (PadicComplex l)), Real.rpow_neg_one, ← GlobalTheory.UnramValue.norm_l]`. Conclude with `PadicComplex.norm_extends l _`. Establish `he : (1 : ℝ) < (l : ℝ) ^ (2 - 1) * ((l : ℝ) - 1)` using `by norm_num; nlinarith`.

Use `⟨(ζ : PadicComplex l) - 1, ⟨ζ - 1, sub_mem hmem (one_mem _), ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Conclude with `(map_sub (algebraMap (Om l) (PadicComplex l)) ζ 1).trans (by rw [map_one]; rfl)`. Rewrite using `[h1, hl, Real.rpow_lt_rpow_left_iff hl1, lt_div_iff₀ (by linarith)]`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[h1]`.

Conclude with `Real.rpow_lt_one_of_one_lt_of_neg hl1 (div_neg_of_neg_of_pos (by norm_num) (by linarith))`.
-/
theorem exists_between (K : FinExt l) :
    ∃ a ∈ inC (Kinf K), ‖(l : PadicComplex l)‖ < ‖a‖ ∧ ‖a‖ < 1 := by
  have hp : l.Prime := Fact.out
  have hl2 : (2 : ℝ) ≤ l := by exact_mod_cast hp.two_le
  have hl1 : (1 : ℝ) < l := by linarith
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_Om (l := l) 2
  have h1 := norm_primitiveRoot_sub_one l 2 (by norm_num) (ζ : PadicComplex l)
    (hζ.map_of_injective (f := algebraMap (Om l) (PadicComplex l)) (RingHom.injective _))
  have hmem : ζ ∈ Kinf K :=
    (le_sup_right : _ ≤ Kinf K) (IntermediateField.subset_adjoin _ _ ⟨2, hζ.pow_eq_one⟩)
  have hl : ‖(l : PadicComplex l)‖ = (l : ℝ) ^ (-1 : ℝ) := by
    rw [← map_natCast (algebraMap (Om l) (PadicComplex l)), Real.rpow_neg_one,
      ← GlobalTheory.UnramValue.norm_l]
    exact PadicComplex.norm_extends l _
  have he : (1 : ℝ) < (l : ℝ) ^ (2 - 1) * ((l : ℝ) - 1) := by
    norm_num; nlinarith
  refine ⟨(ζ : PadicComplex l) - 1, ⟨ζ - 1, sub_mem hmem (one_mem _), ?_⟩, ?_, ?_⟩
  · exact (map_sub (algebraMap (Om l) (PadicComplex l)) ζ 1).trans (by rw [map_one]; rfl)
  · rw [h1, hl, Real.rpow_lt_rpow_left_iff hl1, lt_div_iff₀ (by linarith)]
    linarith
  · rw [h1]
    exact Real.rpow_lt_one_of_one_lt_of_neg hl1 (div_neg_of_neg_of_pos (by norm_num) (by linarith))

/- English proof (translation)
Establish `hl0 : (l : PadicComplex l) ≠ 0` using `GlobalTheory.RingBasics.p_ne_zero`. Establish `hlpos : 0 < ‖(l : PadicComplex l)‖` using `norm_pos_iff.2 hl0`. Establish `hapos : 0 < ‖a‖` using `hlpos.trans hla`. Establish `ha0 : a ≠ 0` using `norm_pos_iff.1 hapos`. Establish `hfix : ∀ g ∈ Hinf K, act g a = a`.

Take `⟨a₀, ha₀, rfl⟩` from `ha`. Introduce `g hg`. Rewrite using `[hact.1, (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg a₀ ha₀]`. Establish `hcoc : CocOn (Hinf K) (fun g y k => act g (y k)) (ball l 1) (fun g _ => (act g y - y) / (l : PadicComplex l))`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations.

Use `Continuous.continuousOn (continuous_pi fun _ => ?_)` and prove the remaining obligations. Conclude with `((GlobalTheory.Cyc.IsActC.continuous_orbit l act hact y).sub continuous_const).div_const _`. Introduce `g hg _`. Rewrite using `[norm_div, div_le_one hlpos]`. Conclude with `hinv g hg`.

Introduce `g _ h _`. Use function extensionality and compare the values at `k`. Simplify using `only [Pi.add_apply, map_mul, RingAut.mul_apply, map_div₀, map_sub, map_natCast]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨b, hb, hb'⟩` from `GlobalTheory.T.cyclotomic_tate_maximalIdeal_kills_first_cohomology l act hact K 1 a ha ha1 _ hcoc`.

Establish `hn : ‖(l : PadicComplex l) / a * b 0‖ ≤ ‖(l : PadicComplex l)‖ / ‖a‖`. Rewrite using `[norm_mul, norm_div]`. Conclude with `mul_le_of_le_one_right (by positivity) (hb 0)`. Use `⟨y - l / a * b 0, ?_, by simpa using hn⟩` and prove the remaining obligations. Rewrite using `[← GlobalTheory.T.cyclotomicTower_fixed_iff_mem_completedIntegers l act hact K]`.

Introduce `h hh`. Use `congrFun (hb' h hh) 0` as an intermediate fact. Simplify using `only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply] at this`. Rewrite using `[map_sub, map_mul, map_div₀, map_natCast, hfix h hh]`. Clear denominators, using `at this ⊢` for the nonvanishing conditions.

Take the linear combination `this`. Rewrite using `[sub_eq_add_neg]`. Use `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le hy ?_)` and prove the remaining obligations. Rewrite using `[norm_neg]`. Conclude with `hn.trans ((div_le_one hapos).2 hla.le)`.
-/
theorem exists_near_Ohat (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (hact : IsActC act)
    (K : FinExt l) (a : PadicComplex l) (ha : a ∈ inC (Kinf K))
    (hla : ‖(l : PadicComplex l)‖ < ‖a‖) (ha1 : ‖a‖ < 1) (y : PadicComplex l) (hy : ‖y‖ ≤ 1)
    (hinv : ∀ h ∈ Hinf K, ‖act h y - y‖ ≤ ‖(l : PadicComplex l)‖) :
    ∃ y' ∈ Ohat K, ‖y - y'‖ ≤ ‖(l : PadicComplex l)‖ / ‖a‖ := by
  have hl0 : (l : PadicComplex l) ≠ 0 := GlobalTheory.RingBasics.p_ne_zero
  have hlpos : 0 < ‖(l : PadicComplex l)‖ := norm_pos_iff.2 hl0
  have hapos : 0 < ‖a‖ := hlpos.trans hla
  have ha0 : a ≠ 0 := norm_pos_iff.1 hapos
  have hfix : ∀ g ∈ Hinf K, act g a = a := by
    obtain ⟨a₀, ha₀, rfl⟩ := ha
    intro g hg
    rw [hact.1, (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg a₀ ha₀]
  have hcoc : CocOn (Hinf K) (fun g y k => act g (y k)) (ball l 1)
      (fun g _ => (act g y - y) / (l : PadicComplex l)) := by
    refine ⟨?_, ?_, ?_⟩
    · refine Continuous.continuousOn (continuous_pi fun _ => ?_)
      exact ((GlobalTheory.Cyc.IsActC.continuous_orbit l act hact y).sub continuous_const).div_const _
    · intro g hg _
      rw [norm_div, div_le_one hlpos]
      exact hinv g hg
    · intro g _ h _
      funext k
      simp only [Pi.add_apply, map_mul, RingAut.mul_apply, map_div₀, map_sub, map_natCast]
      ring
  obtain ⟨b, hb, hb'⟩ := GlobalTheory.T.cyclotomic_tate_maximalIdeal_kills_first_cohomology l act hact K 1 a ha ha1 _ hcoc
  have hn : ‖(l : PadicComplex l) / a * b 0‖ ≤ ‖(l : PadicComplex l)‖ / ‖a‖ := by
    rw [norm_mul, norm_div]
    exact mul_le_of_le_one_right (by positivity) (hb 0)
  refine ⟨y - l / a * b 0, ?_, by simpa using hn⟩
  rw [← GlobalTheory.T.cyclotomicTower_fixed_iff_mem_completedIntegers l act hact K]
  · intro h hh
    have := congrFun (hb' h hh) 0
    simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply] at this
    rw [map_sub, map_mul, map_div₀, map_natCast, hfix h hh]
    field_simp at this ⊢
    linear_combination this
  · rw [sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hy ?_)
    rw [norm_neg]
    exact hn.trans ((div_le_one hapos).2 hla.le)

def lifts (S : Subring (OCb l)) (N : ℕ) : Subring (PadicComplex l) :=
  ((S.map (PreTilt.coeff N)).comap (Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}))).map
    (PadicComplexInt l).subtype

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_lifts {S : Subring (OCb l)} {N : ℕ} {z : PadicComplex l} :
    z ∈ lifts S N ↔ ∃ y : OC l, (∃ w ∈ S, PreTilt.coeff N w =
      Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) y) ∧ (y : PadicComplex l) = z := Iff.rfl

/- English proof (translation)
Use `@GlobalTheory.RingBasics.mem_span_pow_OC l _ 1 (x - y)` as an intermediate fact. Rewrite `this` using `[pow_one, pow_one]`. Rewrite using `[Ideal.Quotient.eq, this]`. Both sides reduce to the same expression.
-/
theorem mk_eq_iff (x y : OC l) : Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) x =
    Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) y ↔
      ‖(x : PadicComplex l) - y‖ ≤ ‖(l : PadicComplex l)‖ := by
  have := @GlobalTheory.RingBasics.mem_span_pow_OC l _ 1 (x - y)
  rw [pow_one, pow_one] at this
  rw [Ideal.Quotient.eq, this]
  rfl

/- English proof (translation)
Establish `: z' - z ∈ lifts S N`. Use `mem_lifts.2 ⟨⟨z' - z, (GlobalTheory.RingBasics.mem_OC _).2 (h.trans GlobalTheory.RingBasics.norm_p_lt.le)⟩, ⟨0, zero_mem _, ?_⟩, rfl⟩` and prove the remaining obligations. Rewrite using `[map_zero, ← map_zero (Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)})), eq_comm, mk_eq_iff]`. Simplify using `using h`. Simplify using `using add_mem this hz`.
-/
theorem mem_lifts_of_near {S : Subring (OCb l)} {N : ℕ} {z z' : PadicComplex l} (hz : z ∈ lifts S N)
    (h : ‖z' - z‖ ≤ ‖(l : PadicComplex l)‖) : z' ∈ lifts S N := by
  have : z' - z ∈ lifts S N := by
    refine mem_lifts.2 ⟨⟨z' - z, (GlobalTheory.RingBasics.mem_OC _).2 (h.trans GlobalTheory.RingBasics.norm_p_lt.le)⟩,
      ⟨0, zero_mem _, ?_⟩, rfl⟩
    rw [map_zero, ← map_zero (Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)})), eq_comm, mk_eq_iff]
    simpa using h
  simpa using add_mem this hz

/- English proof (translation)
Establish `hcC : (ω : PadicComplex l) ^ m = 1`. Use `congrArg (algebraMap (Om l) (PadicComplex l)) hc` as an intermediate fact. Rewrite `this` using `[map_pow, map_one]`. Conclude with `this`. Establish `hn : ‖(ω : PadicComplex l)‖ = 1`.

Use `congrArg norm hcC` as an intermediate fact. Rewrite `this` using `[norm_pow, norm_one]`. Conclude with `(pow_eq_one_iff_of_nonneg (norm_nonneg _) hm.ne').1 this`. Set `W : OC l` to `⟨(ω : PadicComplex l), (GlobalTheory.RingBasics.mem_OC _).2 hn.le⟩`. Establish `hC : W ^ m = 1` using `Subtype.ext (by simpa using hcC)`.

Establish `hcop : Nat.Coprime l m` using `((Fact.out : l.Prime).coprime_iff_not_dvd).2 hl`. Choose the witnesses or unpack the hypotheses as in `⟨a, ha⟩ : ∃ a : ℕ, a * l ≡ 1 [MOD m] := by`. Use `⟨l ^ (Nat.totient m - 1), ?_⟩` and prove the remaining obligations. Rewrite using `[← pow_succ, Nat.sub_add_cancel (Nat.totient_pos.2 hm)]`. Conclude with `Nat.ModEq.pow_totient hcop`.

Set `y : ℕ → OC l` to `fun k => W ^ (l ^ N * a ^ k)`. Establish `hy : ∀ k, y (k + 1) ^ l = y k`. Introduce `k`. Simplify using `only [y]`. Rewrite using `[← pow_mul]`.

Use `pow_eq_pow_of_modEq ?_ hC` and prove the remaining obligations. Rewrite using `[pow_succ, mul_assoc, mul_assoc]`. Simplify using `using (ha.mul_left (a ^ k)).mul_left (l ^ N)`. Establish `hy0 : ∀ k, y k ^ (l ^ k) = W ^ l ^ N`. Introduce `k`.

Proceed by induction on `k with`. Consider the case `zero => simp [y]`. Consider the case `succ k ih => rw [pow_succ', pow_mul, hy, ih]`. Establish `hyN : y N = W`. Simplify using `only [y]`.

Use `conv_rhs => rw [← pow_one W]`. Use `pow_eq_pow_of_modEq ?_ hC` and prove the remaining obligations. Rewrite using `[← mul_pow, mul_comm]`. Simplify using `using ha.pow N`. Use `⟨(⟨fun k => Ideal.Quotient.mk _ (y k), fun k => ?_⟩ : Perfection (ModP (OC l) l) l), W, fun k => ⟨y k, ?_, ?_, rfl⟩, rfl, ?_⟩` and prove the remaining obligations.

Rewrite using `[← map_pow, hy]`. Establish `h1` using `congrArg Subtype.val (hy0 k)`. Establish `h2 : ((ω ^ l ^ N : Om l) : PadicComplex l) = (ω : PadicComplex l) ^ l ^ N` using `map_pow (algebraMap (Om l) (PadicComplex l)) _ _`. Rewrite using `[h2]`. Simplify using `using h1`.

Simplify using `only [y]`. Rewrite using `[← pow_mul, mul_comm, pow_mul, hC, one_pow]`. Rewrite using `[← hyN]`. Both sides reduce to the same expression.
-/
theorem exists_tilt (ω : Om l) (m : ℕ) (hm : 0 < m) (hl : ¬ l ∣ m) (hc : ω ^ m = 1) (N : ℕ) :
    ∃ (xb : OCb l) (y : OC l), IsTiltOf (ω ^ l ^ N) m xb ∧ (y : PadicComplex l) = ω ∧
      PreTilt.coeff N xb = Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) y := by
  have hcC : (ω : PadicComplex l) ^ m = 1 := by
    have := congrArg (algebraMap (Om l) (PadicComplex l)) hc
    rw [map_pow, map_one] at this
    exact this
  have hn : ‖(ω : PadicComplex l)‖ = 1 := by
    have := congrArg norm hcC
    rw [norm_pow, norm_one] at this
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm.ne').1 this
  let W : OC l := ⟨(ω : PadicComplex l), (GlobalTheory.RingBasics.mem_OC _).2 hn.le⟩
  have hC : W ^ m = 1 := Subtype.ext (by simpa using hcC)
  have hcop : Nat.Coprime l m := ((Fact.out : l.Prime).coprime_iff_not_dvd).2 hl
  obtain ⟨a, ha⟩ : ∃ a : ℕ, a * l ≡ 1 [MOD m] := by
    refine ⟨l ^ (Nat.totient m - 1), ?_⟩
    rw [← pow_succ, Nat.sub_add_cancel (Nat.totient_pos.2 hm)]
    exact Nat.ModEq.pow_totient hcop
  let y : ℕ → OC l := fun k => W ^ (l ^ N * a ^ k)
  have hy : ∀ k, y (k + 1) ^ l = y k := by
    intro k
    simp only [y]
    rw [← pow_mul]
    refine pow_eq_pow_of_modEq ?_ hC
    rw [pow_succ, mul_assoc, mul_assoc]
    simpa using (ha.mul_left (a ^ k)).mul_left (l ^ N)
  have hy0 : ∀ k, y k ^ (l ^ k) = W ^ l ^ N := by
    intro k
    induction k with
    | zero => simp [y]
    | succ k ih => rw [pow_succ', pow_mul, hy, ih]
  have hyN : y N = W := by
    simp only [y]
    conv_rhs => rw [← pow_one W]
    refine pow_eq_pow_of_modEq ?_ hC
    rw [← mul_pow, mul_comm]
    simpa using ha.pow N
  refine ⟨(⟨fun k => Ideal.Quotient.mk _ (y k), fun k => ?_⟩ : Perfection (ModP (OC l) l) l), W,
    fun k => ⟨y k, ?_, ?_, rfl⟩, rfl, ?_⟩
  · rw [← map_pow, hy]
  · have h1 := congrArg Subtype.val (hy0 k)
    have h2 : ((ω ^ l ^ N : Om l) : PadicComplex l) = (ω : PadicComplex l) ^ l ^ N :=
      map_pow (algebraMap (Om l) (PadicComplex l)) _ _
    rw [h2]
    simpa using h1
  · simp only [y]
    rw [← pow_mul, mul_comm, pow_mul, hC, one_pow]
  · rw [← hyN]; rfl

variable {P : LocPrime l} (AI : LocAinf l P)

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih => rw [pow_succ', pow_mul, ← add_assoc, AI.ζ_succ, ih]`.
-/
theorem zeta_pow (i k : ℕ) : AI.ζ (i + k) ^ l ^ k = AI.ζ i := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', pow_mul, ← add_assoc, AI.ζ_succ, ih]

/- English proof (translation)
Establish `h1 : AI.ζ (j + 1) ^ l ^ (j + 1) = 1`. Use `zeta_pow AI 0 (j + 1)` as an intermediate fact. Rewrite `this` using `[zero_add, AI.ζ_zero]`. Then use the resulting hypothesis. Establish `h2 : ¬ AI.ζ (j + 1) ^ l ^ j = 1`. Use `zeta_pow AI 1 j` as an intermediate fact.

Rewrite `this` using `[add_comm]`. Rewrite using `[this]`. Conclude with `AI.ζ_one`. Rewrite using `[← orderOf_eq_prime_pow h2 h1]`. Conclude with `IsPrimitiveRoot.orderOf _`.
-/
theorem zeta_primitive (j : ℕ) : IsPrimitiveRoot (AI.ζ (j + 1)) (l ^ (j + 1)) := by
  have h1 : AI.ζ (j + 1) ^ l ^ (j + 1) = 1 := by
    have := zeta_pow AI 0 (j + 1)
    rwa [zero_add, AI.ζ_zero] at this
  have h2 : ¬ AI.ζ (j + 1) ^ l ^ j = 1 := by
    have := zeta_pow AI 1 j
    rw [add_comm] at this
    rw [this]
    exact AI.ζ_one
  rw [← orderOf_eq_prime_pow h2 h1]
  exact IsPrimitiveRoot.orderOf _

def gen (K : FinExt l) : Subring (OCb l) :=
  Subring.closure (Set.range AI.εroot ∪
    {xb | ∃ c : Om l, c ∈ K0 K ∧ ∃ m : ℕ, 0 < m ∧ ¬ l ∣ m ∧ c ^ m = 1 ∧ IsTiltOf c m xb})

/- English proof (translation)
Establish `h : (AI.ζ (j + N) : PadicComplex l) ∈ lifts (gen AI K) N`. Use `mem_lifts.2 ⟨_, ⟨AI.εroot j, Subring.subset_closure (Or.inl ⟨j, rfl⟩), ?_⟩, rfl⟩` and prove the remaining obligations. Rewrite using `[LocAinf.εroot, PreTilt.coeff_iterate_frobeniusEquiv_symm, AI.ε_coeff, add_comm]`. Use `pow_mem h (l ^ N)` as an intermediate fact. Rewrite `this` using `[← SubmonoidClass.coe_pow, zeta_pow]`. Then use the resulting hypothesis.
-/
theorem zeta_mem (K : FinExt l) (N j : ℕ) : (AI.ζ j : PadicComplex l) ∈ lifts (gen AI K) N := by
  have h : (AI.ζ (j + N) : PadicComplex l) ∈ lifts (gen AI K) N := by
    refine mem_lifts.2 ⟨_, ⟨AI.εroot j, Subring.subset_closure (Or.inl ⟨j, rfl⟩), ?_⟩, rfl⟩
    rw [LocAinf.εroot, PreTilt.coeff_iterate_frobeniusEquiv_symm, AI.ε_coeff, add_comm]
  have := pow_mem h (l ^ N)
  rwa [← SubmonoidClass.coe_pow, zeta_pow] at this

/- English proof (translation)
Establish `key : ∀ ω ∈ K0 K, ‖c - ω‖ < 1 → ‖(c : PadicComplex l) - ω‖ ≤ ‖(l : PadicComplex l)‖`. Introduce `ω hω h`. Establish `h2` using `norm_le_l K (sub_mem hc hω) h`. Rewrite `h2` using `[← PadicComplex.norm_extends, ← PadicComplex.norm_extends l (l : Om l)]`. Establish `e1 : ((c - ω : Om l) : PadicComplex l) = c - ω` using `map_sub (algebraMap (Om l) (PadicComplex l)) _ _`.

Establish `e2 : ((l : Om l) : PadicComplex l) = l` using `map_natCast (algebraMap (Om l) (PadicComplex l)) _`. Rewrite `h2` using `[e1, e2]`. Then use the resulting hypothesis. Break down `h1.eq_or_lt with h | h` into its components or cases. Take `⟨ω, hω, m, hm, hl, hωm, hn⟩` from `exists_root K hc h`. Take `⟨xb, y, ht, hy, hx⟩` from `exists_tilt ω m hm hl hωm N`.

Use `mem_lifts_of_near (mem_lifts.2 ⟨y, ⟨xb, Subring.subset_closure (Or.inr ⟨_, pow_mem hω _, m, hm, hl, ?_, ht⟩), hx⟩, hy⟩) (key ω hω hn)` and prove the remaining obligations. Rewrite using `[← pow_mul, mul_comm, pow_mul, hωm, one_pow]`. Use `key 0 (zero_mem _) (by simpa using h)` as an intermediate fact. Establish `e : ((0 : Om l) : PadicComplex l) = 0` using `map_zero (algebraMap (Om l) (PadicComplex l))`. Rewrite `this` using `[e]`.

Conclude with `mem_lifts_of_near (zero_mem _) this`.
-/
theorem K0_mem (K : FinExt l) (N : ℕ) (c : Om l) (hc : c ∈ K0 K) (h1 : ‖c‖ ≤ 1) :
    (c : PadicComplex l) ∈ lifts (gen AI K) N := by
  have key : ∀ ω ∈ K0 K, ‖c - ω‖ < 1 →
      ‖(c : PadicComplex l) - ω‖ ≤ ‖(l : PadicComplex l)‖ := by
    intro ω hω h
    have h2 := norm_le_l K (sub_mem hc hω) h
    rw [← PadicComplex.norm_extends, ← PadicComplex.norm_extends l (l : Om l)] at h2
    have e1 : ((c - ω : Om l) : PadicComplex l) = c - ω :=
      map_sub (algebraMap (Om l) (PadicComplex l)) _ _
    have e2 : ((l : Om l) : PadicComplex l) = l := map_natCast (algebraMap (Om l) (PadicComplex l)) _
    rwa [e1, e2] at h2
  rcases h1.eq_or_lt with h | h
  · obtain ⟨ω, hω, m, hm, hl, hωm, hn⟩ := exists_root K hc h
    obtain ⟨xb, y, ht, hy, hx⟩ := exists_tilt ω m hm hl hωm N
    refine mem_lifts_of_near (mem_lifts.2 ⟨y, ⟨xb, Subring.subset_closure (Or.inr
      ⟨_, pow_mem hω _, m, hm, hl, ?_, ht⟩), hx⟩, hy⟩) (key ω hω hn)
    rw [← pow_mul, mul_comm, pow_mul, hωm, one_pow]
  · have := key 0 (zero_mem _) (by simpa using h)
    have e : ((0 : Om l) : PadicComplex l) = 0 := map_zero (algebraMap (Om l) (PadicComplex l))
    rw [e] at this
    exact mem_lifts_of_near (zero_mem _) this

/- English proof (translation)
Take `⟨z', ⟨⟨x, hx, rfl⟩, hx1⟩, hd⟩` from `Metric.mem_closure_iff.1 hz _ (norm_pos_iff.2 (@GlobalTheory.RingBasics.p_ne_zero l _))`. Rewrite `hd` using `[dist_eq_norm]`. Use `mem_lifts_of_near ?_ hd.le` and prove the remaining obligations. Take `⟨j, hj, hxj⟩` from `exists_level K hx`. Take `⟨j, rfl⟩ : ∃ i, j = i + 1` from `⟨j - 1, by omega⟩`.

Establish `hprim : IsPrimitiveRoot (P.ζQ (j + 1)) (l ^ (j + 1))`. Use `IsPrimitiveRoot.of_map_of_injective (f := algebraMap (Om l) (PadicComplex l)) ?_ (RingHom.injective _)` and prove the remaining obligations. Use `(zeta_primitive AI j).map_of_injective (f := (PadicComplexInt l).subtype) Subtype.val_injective` as an intermediate fact. Establish `e : algebraMap (Om l) (PadicComplex l) (P.ζQ (j + 1)) = (PadicComplexInt l).subtype (AI.ζ (j + 1))` using `(AI.ζ_eq (j + 1)).symm`. Rewrite using `[e]` and apply the resulting hypothesis.

Use `mem_of_mem_Ks K (j + 1) hj _ hprim ((lifts (gen AI K) N).comap (algebraMap (Om l) (PadicComplex l))) ?_ (fun c hc h1 => K0_mem AI K N c hc h1) x hxj (by simpa using hx1)` and prove the remaining obligations. Use `zeta_mem AI K N (j + 1)` as an intermediate fact. Rewrite `this` using `[AI.ζ_eq]`. Conclude with `this`.
-/
theorem Ohat_mem (K : FinExt l) (N : ℕ) (z : PadicComplex l) (hz : z ∈ Ohat K) :
    z ∈ lifts (gen AI K) N := by
  obtain ⟨z', ⟨⟨x, hx, rfl⟩, hx1⟩, hd⟩ := Metric.mem_closure_iff.1 hz _
    (norm_pos_iff.2 (@GlobalTheory.RingBasics.p_ne_zero l _))
  rw [dist_eq_norm] at hd
  refine mem_lifts_of_near ?_ hd.le
  obtain ⟨j, hj, hxj⟩ := exists_level K hx
  obtain ⟨j, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have hprim : IsPrimitiveRoot (P.ζQ (j + 1)) (l ^ (j + 1)) := by
    refine IsPrimitiveRoot.of_map_of_injective (f := algebraMap (Om l) (PadicComplex l)) ?_
      (RingHom.injective _)
    have := (zeta_primitive AI j).map_of_injective (f := (PadicComplexInt l).subtype)
      Subtype.val_injective
    have e : algebraMap (Om l) (PadicComplex l) (P.ζQ (j + 1)) =
        (PadicComplexInt l).subtype (AI.ζ (j + 1)) := (AI.ζ_eq (j + 1)).symm
    rwa [e]
  refine mem_of_mem_Ks K (j + 1) hj _ hprim
    ((lifts (gen AI K) N).comap (algebraMap (Om l) (PadicComplex l))) ?_
    (fun c hc h1 => K0_mem AI K N c hc h1) x hxj (by simpa using hx1)
  have := zeta_mem AI K N (j + 1)
  rw [AI.ζ_eq] at this
  exact this

/- English proof (translation)
Introduce `h`. Rewrite `h` using `[sub_eq_zero]`. Establish `hl2 : (2 : ℝ) ≤ l` using `by exact_mod_cast (Fact.out : l.Prime).two_le`. Establish `hl1 : (1 : ℝ) < l` using `by linarith`. Establish `h1` using `AI.ε_coeff 2`.

Rewrite `h1` using `[h, map_one, ← map_one (Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)})), eq_comm, mk_eq_iff]`. Establish `h2` using `norm_primitiveRoot_sub_one l 2 (by norm_num) (AI.ζ 2 : PadicComplex l) ((zeta_primitive AI 1).map_of_injective (f := (PadicComplexInt l).subtype) Subtype.val_injective)`. Establish `hl : ‖(l : PadicComplex l)‖ = (l : ℝ) ^ (-1 : ℝ)`. Rewrite using `[← map_natCast (algebraMap (Om l) (PadicComplex l)), Real.rpow_neg_one, ← GlobalTheory.UnramValue.norm_l]`. Conclude with `PadicComplex.norm_extends l _`.

Establish `he : (1 : ℝ) < (l : ℝ) ^ (2 - 1) * ((l : ℝ) - 1)` using `by norm_num; nlinarith`. Rewrite `h1` using `[OneMemClass.coe_one, h2, hl, Real.rpow_le_rpow_left_iff hl1, div_le_iff₀ (by linarith)]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem eps_ne_one : AI.ε - 1 ≠ 0 := by
  intro h
  rw [sub_eq_zero] at h
  have hl2 : (2 : ℝ) ≤ l := by exact_mod_cast (Fact.out : l.Prime).two_le
  have hl1 : (1 : ℝ) < l := by linarith
  have h1 := AI.ε_coeff 2
  rw [h, map_one, ← map_one (Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)})), eq_comm,
    mk_eq_iff] at h1
  have h2 := norm_primitiveRoot_sub_one l 2 (by norm_num) (AI.ζ 2 : PadicComplex l)
    ((zeta_primitive AI 1).map_of_injective (f := (PadicComplexInt l).subtype)
      Subtype.val_injective)
  have hl : ‖(l : PadicComplex l)‖ = (l : ℝ) ^ (-1 : ℝ) := by
    rw [← map_natCast (algebraMap (Om l) (PadicComplex l)), Real.rpow_neg_one,
      ← GlobalTheory.UnramValue.norm_l]
    exact PadicComplex.norm_extends l _
  have he : (1 : ℝ) < (l : ℝ) ^ (2 - 1) * ((l : ℝ) - 1) := by
    norm_num; nlinarith
  rw [OneMemClass.coe_one, h2, hl, Real.rpow_le_rpow_left_iff hl1, div_le_iff₀ (by linarith)] at h1
  linarith

open scoped Formalism.Per in
open GlobalTheory.TiltAlgClosed in

/- English proof (translation)
Introduce `l _ P AI K x hx n`. Establish `hp : l.Prime` using `Fact.out`. Take `⟨a, ha, hla, ha1⟩` from `exists_between K`. Establish `hlpos : 0 < ‖(l : PadicComplex l)‖` using `norm_pos_iff.2 GlobalTheory.RingBasics.p_ne_zero`. Establish `hapos : 0 < ‖a‖` using `hlpos.trans hla`.

Use `set δ := ‖(l : PadicComplex l)‖ / ‖a‖ with hδ`. Establish `hδ0 : 0 ≤ δ` using `by positivity`. Establish `hδ1 : δ < 1` using `(div_lt_one hapos).2 hla`. Establish `hlδ : ‖(l : PadicComplex l)‖ ≤ δ`. Rewrite using `[hδ, le_div_iff₀ hapos]`.

Conclude with `mul_le_of_le_one_right hlpos.le ha1.le`. Use `set e : OCb l := (AI.ε - 1) ^ n with he`. Establish `he0 : (e.untilt : PadicComplex l) ≠ 0`. Introduce `h`. Establish `h0 : e.untilt = 0` using `Subtype.ext h`.

Establish `: (0 : OCb l) ∣ e` using `dvd_of_untilt_dvd (by rw [h0]; exact dvd_zero _)`. Conclude with `pow_ne_zero n (eps_ne_one AI) (zero_dvd_iff.1 this)`. Take `⟨N, hN⟩` from `exists_pow_lt_of_lt_one (norm_pos_iff.2 he0) hδ1`. Establish `hN' : δ ^ l ^ N ≤ ‖(e.untilt : PadicComplex l)‖` using `(pow_le_pow_of_le_one hδ0 hδ1.le (Nat.lt_pow_self hp.one_lt).le).trans hN.le`. Take `⟨y, hy⟩` from `Ideal.Quotient.mk_surjective (I := Ideal.span {((l : ℕ) : OC l)}) (PreTilt.coeff N x)`.

Take `⟨y', hy', hyy'⟩` from `exists_near_Ohat AI.actC ⟨AI.actC_ext, AI.actC_norm⟩ K a ha hla ha1 (y : PadicComplex l) ((GlobalTheory.RingBasics.mem_OC _).1 y.2) (fun h hh => by`. Take `⟨y₁, h1, h2⟩` from `AI.actT_coeff h x N y hy.symm`. Rewrite `h2` using `[hx h hh, ← hy, eq_comm, mk_eq_iff, h1]`. Conclude with `h2)`. Take `⟨y₂, ⟨w, hw, hwy⟩, rfl⟩` from `mem_lifts.1 (Ohat_mem AI K N y' hy')`.

Use `⟨w, hw, dvd_of_untilt_dvd ?_⟩` and prove the remaining obligations. Establish `h1` using `mk_sharpRoot (x - w) N`. Rewrite `h1` using `[map_sub, ← hy, hwy, ← map_sub, mk_eq_iff]`. Establish `h2 : ‖((sharpRoot (x - w) N : OC l) : PadicComplex l)‖ ≤ δ`. Establish `: ((sharpRoot (x - w) N : OC l) : PadicComplex l) = (((sharpRoot (x - w) N : OC l) : PadicComplex l) - ((y - y₂ : OC l) : PadicComplex l)) + ((y : PadicComplex l) - y₂)` using `by push_cast; ring`.

Rewrite using `[this]`. Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le (h1.trans hlδ) hyy')`. Establish `h3 : ‖((x - w).untilt : PadicComplex l)‖ ≤ ‖(e.untilt : PadicComplex l)‖`. Rewrite using `[← sharpRoot_pow (x - w) N, SubmonoidClass.coe_pow, norm_pow]`. Conclude with `(pow_le_pow_left₀ (norm_nonneg _) h2 _).trans hN'`.

Use `⟨⟨((x - w).untilt : PadicComplex l) / e.untilt, (GlobalTheory.RingBasics.mem_OC _).2 ?_⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Rewrite using `[norm_div, div_le_one (norm_pos_iff.2 he0)]` and apply the resulting hypothesis. Use `push_cast`. Clear the denominators using the available nonvanishing facts.
-/
theorem invariant_approx : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (x : OCb l), (∀ h ∈ Hinf K, AI.actT h x = x) → ∀ n : ℕ, ∃ y ∈ Subring.closure (Set.range AI.εroot ∪ {xb | ∃ c : Om l, c ∈ K0 K ∧ ∃ m : ℕ, 0 < m ∧ ¬ l ∣ m ∧ c ^ m = 1 ∧ IsTiltOf c m xb}), (AI.ε - 1) ^ n ∣ x - y := by
  intro l _ P AI K x hx n
  have hp : l.Prime := Fact.out
  obtain ⟨a, ha, hla, ha1⟩ := exists_between K
  have hlpos : 0 < ‖(l : PadicComplex l)‖ := norm_pos_iff.2 GlobalTheory.RingBasics.p_ne_zero
  have hapos : 0 < ‖a‖ := hlpos.trans hla
  set δ := ‖(l : PadicComplex l)‖ / ‖a‖ with hδ
  have hδ0 : 0 ≤ δ := by positivity
  have hδ1 : δ < 1 := (div_lt_one hapos).2 hla
  have hlδ : ‖(l : PadicComplex l)‖ ≤ δ := by
    rw [hδ, le_div_iff₀ hapos]
    exact mul_le_of_le_one_right hlpos.le ha1.le
  set e : OCb l := (AI.ε - 1) ^ n with he
  have he0 : (e.untilt : PadicComplex l) ≠ 0 := by
    intro h
    have h0 : e.untilt = 0 := Subtype.ext h
    have : (0 : OCb l) ∣ e := dvd_of_untilt_dvd (by rw [h0]; exact dvd_zero _)
    exact pow_ne_zero n (eps_ne_one AI) (zero_dvd_iff.1 this)
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (norm_pos_iff.2 he0) hδ1
  have hN' : δ ^ l ^ N ≤ ‖(e.untilt : PadicComplex l)‖ :=
    (pow_le_pow_of_le_one hδ0 hδ1.le (Nat.lt_pow_self hp.one_lt).le).trans hN.le
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (I := Ideal.span {((l : ℕ) : OC l)})
    (PreTilt.coeff N x)
  obtain ⟨y', hy', hyy'⟩ := exists_near_Ohat AI.actC ⟨AI.actC_ext, AI.actC_norm⟩ K a ha hla ha1
    (y : PadicComplex l) ((GlobalTheory.RingBasics.mem_OC _).1 y.2) (fun h hh => by
      obtain ⟨y₁, h1, h2⟩ := AI.actT_coeff h x N y hy.symm
      rw [hx h hh, ← hy, eq_comm, mk_eq_iff, h1] at h2
      exact h2)
  obtain ⟨y₂, ⟨w, hw, hwy⟩, rfl⟩ := mem_lifts.1 (Ohat_mem AI K N y' hy')
  refine ⟨w, hw, dvd_of_untilt_dvd ?_⟩
  have h1 := mk_sharpRoot (x - w) N
  rw [map_sub, ← hy, hwy, ← map_sub, mk_eq_iff] at h1
  have h2 : ‖((sharpRoot (x - w) N : OC l) : PadicComplex l)‖ ≤ δ := by
    have : ((sharpRoot (x - w) N : OC l) : PadicComplex l) =
        (((sharpRoot (x - w) N : OC l) : PadicComplex l) - ((y - y₂ : OC l) : PadicComplex l)) +
          ((y : PadicComplex l) - y₂) := by
      push_cast; ring
    rw [this]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (h1.trans hlδ) hyy')
  have h3 : ‖((x - w).untilt : PadicComplex l)‖ ≤ ‖(e.untilt : PadicComplex l)‖ := by
    rw [← sharpRoot_pow (x - w) N, SubmonoidClass.coe_pow, norm_pow]
    exact (pow_le_pow_left₀ (norm_nonneg _) h2 _).trans hN'
  refine ⟨⟨((x - w).untilt : PadicComplex l) / e.untilt, (GlobalTheory.RingBasics.mem_OC _).2 ?_⟩, Subtype.ext ?_⟩
  · rwa [norm_div, div_le_one (norm_pos_iff.2 he0)]
  · push_cast
    field_simp

end GlobalTheory.TiltInvariants
