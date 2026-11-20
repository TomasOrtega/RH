import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.PowerSeriesHasSumAt
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MvPowerSeriesConvergentSubstHasSumAndBoundsStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MvPowerSeriesIntegralBoundedClosureStatement

open GlobalTheory.ConvSer

namespace GlobalTheory.ConvSer

section
variable {K : Type} [NormedField K] [IsUltrametricDist K] [CompleteSpace K] {σ τ : Type}
  [Fintype σ] {s : σ → MvPowerSeries τ K}

/- English proof (translation)
Use extensionality with `μ`. Establish `h1` using `(GlobalTheory.T.mvPowerSeriesConvergentSubst_hasSum_and_bounds K σ τ s S hs hS).1 μ`. Establish `h2` using `(GlobalTheory.T.mvPowerSeriesConvergentSubst_hasSum_and_bounds K σ τ s T hs hT).1 μ`. Establish `h3` using `(GlobalTheory.T.mvPowerSeriesConvergentSubst_hasSum_and_bounds K σ τ s _ hs ((GlobalTheory.T.mvPowerSeries_integral_bounded_closure K σ).2.1 S T hS hT).1).1 μ`. Rewrite using `[map_add]`.

Use `h3.unique ?_` and prove the remaining obligations. Simplify `h1.add h2` using `only [map_add, add_mul]`.
-/
theorem csub_add_of_bdd (hs : ∀ i, Small (s i)) {S T : MvPowerSeries σ K} (hS : Bdd S)
    (hT : Bdd T) : csub s (S + T) = csub s S + csub s T := by
  ext μ
  have h1 := (GlobalTheory.T.mvPowerSeriesConvergentSubst_hasSum_and_bounds K σ τ s S hs hS).1 μ
  have h2 := (GlobalTheory.T.mvPowerSeriesConvergentSubst_hasSum_and_bounds K σ τ s T hs hT).1 μ
  have h3 := (GlobalTheory.T.mvPowerSeriesConvergentSubst_hasSum_and_bounds K σ τ s _ hs ((GlobalTheory.T.mvPowerSeries_integral_bounded_closure K σ).2.1 S T hS hT).1).1 μ
  rw [map_add]
  refine h3.unique ?_
  simpa only [map_add, add_mul] using h1.add h2

/- English proof (translation)
Use extensionality with `μ`. Establish `h1` using `(GlobalTheory.T.mvPowerSeriesConvergentSubst_hasSum_and_bounds K σ τ s S hs hS).1 μ`. Establish `h2` using `(GlobalTheory.T.mvPowerSeriesConvergentSubst_hasSum_and_bounds K σ τ s T hs hT).1 μ`. Establish `h3` using `(GlobalTheory.T.mvPowerSeriesConvergentSubst_hasSum_and_bounds K σ τ s _ hs ((GlobalTheory.T.mvPowerSeries_integral_bounded_closure K σ).2.1 S T hS hT).2.1).1 μ`. Rewrite using `[map_sub]`.

Use `h3.unique ?_` and prove the remaining obligations. Simplify `h1.sub h2` using `only [map_sub, sub_mul]`.
-/
theorem csub_sub_of_bdd (hs : ∀ i, Small (s i)) {S T : MvPowerSeries σ K} (hS : Bdd S)
    (hT : Bdd T) : csub s (S - T) = csub s S - csub s T := by
  ext μ
  have h1 := (GlobalTheory.T.mvPowerSeriesConvergentSubst_hasSum_and_bounds K σ τ s S hs hS).1 μ
  have h2 := (GlobalTheory.T.mvPowerSeriesConvergentSubst_hasSum_and_bounds K σ τ s T hs hT).1 μ
  have h3 := (GlobalTheory.T.mvPowerSeriesConvergentSubst_hasSum_and_bounds K σ τ s _ hs ((GlobalTheory.T.mvPowerSeries_integral_bounded_closure K σ).2.1 S T hS hT).2.1).1 μ
  rw [map_sub]
  refine h3.unique ?_
  simpa only [map_sub, sub_mul] using h1.sub h2

/- English proof (translation)
Use extensionality with `μ`. Establish `h3` using `(GlobalTheory.T.mvPowerSeriesConvergentSubst_hasSum_and_bounds K σ τ s _ hs ((GlobalTheory.T.mvPowerSeries_integral_bounded_closure K σ).2.1 S T hS hT).2.2).1 μ`. Use `h3.unique ?_` and prove the remaining obligations. Use `haveI : NonarchimedeanRing K := ⟨NonarchimedeanAddGroup.is_nonarchimedean⟩`. Establish `h4 : HasSum (fun p : (σ →₀ ℕ) × (σ →₀ ℕ) => MvPowerSeries.coeff p.1 S * MvPowerSeries.coeff p.2 T * MvPowerSeries.coeff μ (∏ i, s i ^ (p.1 + p.2) i)) (MvPowerSeries.coeff μ (csub s S * csub s T))`.

Rewrite using `[MvPowerSeries.coeff_mul]`. Establish `h5` using `hasSum_sum (s := Finset.HasAntidiagonal.antidiagonal μ) (fun q _ => ((GlobalTheory.T.mvPowerSeriesConvergentSubst_hasSum_and_bounds K σ τ s S hs hS).1 q.1).mul_of_nonarchimedean ((GlobalTheory.T.mvPowerSeriesConvergentSubst_hasSum_and_bounds K σ τ s T hs hT).1 q.2))`. Use `h5 using 2 with p` and compare the differences between its conclusion and the goal. Simplify using `only [Finsupp.add_apply, pow_add, Finset.prod_mul_distrib, MvPowerSeries.coeff_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree. Establish `h6` using `Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.hasSum_iff.2 h4`. Use `h6.sigma fun ν => ?_` and prove the remaining obligations. Rewrite using `[MvPowerSeries.coeff_mul, Finset.sum_mul, ← Finset.sum_coe_sort]`. Use `hasSum_fintype _ using 2 with q` and compare the differences between its conclusion and the goal.

Use `Finset.HasAntidiagonal.mem_antidiagonal.1 q.2` as an intermediate fact. Simplify using `only [Function.comp, Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd_apply, this]`.
-/
theorem csub_mul_of_bdd (hs : ∀ i, Small (s i)) {S T : MvPowerSeries σ K} (hS : Bdd S)
    (hT : Bdd T) : csub s (S * T) = csub s S * csub s T := by
  classical
  ext μ
  have h3 := (GlobalTheory.T.mvPowerSeriesConvergentSubst_hasSum_and_bounds K σ τ s _ hs ((GlobalTheory.T.mvPowerSeries_integral_bounded_closure K σ).2.1 S T hS hT).2.2).1 μ
  refine h3.unique ?_
  haveI : NonarchimedeanRing K := ⟨NonarchimedeanAddGroup.is_nonarchimedean⟩
  have h4 : HasSum (fun p : (σ →₀ ℕ) × (σ →₀ ℕ) =>
      MvPowerSeries.coeff p.1 S * MvPowerSeries.coeff p.2 T *
        MvPowerSeries.coeff μ (∏ i, s i ^ (p.1 + p.2) i))
      (MvPowerSeries.coeff μ (csub s S * csub s T)) := by
    rw [MvPowerSeries.coeff_mul]
    have h5 := hasSum_sum (s := Finset.HasAntidiagonal.antidiagonal μ) (fun q _ =>
      ((GlobalTheory.T.mvPowerSeriesConvergentSubst_hasSum_and_bounds K σ τ s S hs hS).1 q.1).mul_of_nonarchimedean
        ((GlobalTheory.T.mvPowerSeriesConvergentSubst_hasSum_and_bounds K σ τ s T hs hT).1 q.2))
    convert h5 using 2 with p
    simp only [Finsupp.add_apply, pow_add, Finset.prod_mul_distrib, MvPowerSeries.coeff_mul,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    ring
  have h6 := Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.hasSum_iff.2 h4
  refine h6.sigma fun ν => ?_
  rw [MvPowerSeries.coeff_mul, Finset.sum_mul, ← Finset.sum_coe_sort]
  convert hasSum_fintype _ using 2 with q
  have := Finset.HasAntidiagonal.mem_antidiagonal.1 q.2
  simp only [Function.comp, Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd_apply, this]

omit [IsUltrametricDist K] [CompleteSpace K] in
/- English proof (translation)
Use extensionality with `μ`. Rewrite using `[MvPowerSeries.coeff_C_mul]`. Express the relevant statement in the definitionally equal form `∑' ν' : σ →₀ ℕ, MvPowerSeries.coeff ν' (MvPowerSeries.monomial ν a) * MvPowerSeries.coeff μ (∏ i, s i ^ ν' i) = _`. Rewrite using `[tsum_eq_single ν]`. Rewrite using `[MvPowerSeries.coeff_monomial_same]`.

Introduce `b hb`. Rewrite using `[MvPowerSeries.coeff_monomial_ne hb, zero_mul]`.
-/
theorem csub_monomial (s : σ → MvPowerSeries τ K) (ν : σ →₀ ℕ) (a : K) :
    csub s (MvPowerSeries.monomial ν a) = MvPowerSeries.C a * ∏ i, s i ^ ν i := by
  classical
  ext μ
  rw [MvPowerSeries.coeff_C_mul]
  change ∑' ν' : σ →₀ ℕ, MvPowerSeries.coeff ν' (MvPowerSeries.monomial ν a) *
    MvPowerSeries.coeff μ (∏ i, s i ^ ν' i) = _
  rw [tsum_eq_single ν]
  · rw [MvPowerSeries.coeff_monomial_same]
  · intro b hb
    rw [MvPowerSeries.coeff_monomial_ne hb, zero_mul]

omit [IsUltrametricDist K] [CompleteSpace K] in
/- English proof (translation)
Rewrite using `[← MvPowerSeries.monomial_zero_eq_C_apply, csub_monomial]`. Simplify using the standard rewrite rules.
-/
theorem csub_C (s : σ → MvPowerSeries τ K) (a : K) :
    csub s (MvPowerSeries.C a) = MvPowerSeries.C a := by
  rw [← MvPowerSeries.monomial_zero_eq_C_apply, csub_monomial]
  simp

omit [IsUltrametricDist K] [CompleteSpace K] in
/- English proof (translation)
Rewrite using `[MvPowerSeries.X_def, csub_monomial, map_one, one_mul, Finset.prod_eq_single i]`. Simplify using the standard rewrite rules. Introduce `b _ hb`. Rewrite using `[Finsupp.single_eq_of_ne hb, pow_zero]`. Simplify using the standard rewrite rules.
-/
theorem csub_X (s : σ → MvPowerSeries τ K) (i : σ) :
    csub s (MvPowerSeries.X i) = s i := by
  classical
  rw [MvPowerSeries.X_def, csub_monomial, map_one, one_mul, Finset.prod_eq_single i]
  · simp
  · intro b _ hb
    rw [Finsupp.single_eq_of_ne hb, pow_zero]
  · simp

omit [IsUltrametricDist K] [CompleteSpace K] in
/- English proof (translation)
Simplify using `using csub_C s (1 : K)`.
-/
theorem csub_one (s : σ → MvPowerSeries τ K) : csub s 1 = 1 := by
  simpa using csub_C s (1 : K)

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simpa using csub_one s`. Consider the case `succ n ih`. Rewrite using `[pow_succ, pow_succ, csub_mul_of_bdd hs (((GlobalTheory.T.mvPowerSeries_integral_bounded_closure K σ).2.2.1 S n).2.1 hS) hS, ih]`.
-/
theorem csub_pow_of_bdd (hs : ∀ i, Small (s i)) {S : MvPowerSeries σ K} (hS : Bdd S) (n : ℕ) :
    csub s (S ^ n) = csub s S ^ n := by
  induction n with
  | zero => simpa using csub_one s
  | succ n ih =>
    rw [pow_succ, pow_succ, csub_mul_of_bdd hs (((GlobalTheory.T.mvPowerSeries_integral_bounded_closure K σ).2.2.1 S n).2.1 hS) hS, ih]

/- English proof (translation)
Proceed by induction on `t using Finset.induction_on with`. Consider the case `empty => simpa using csub_one s`. Consider the case `insert a t ha ih`. Establish `ht : ∀ i ∈ t, Bdd (f i)` using `fun i hi => hf i (Finset.mem_insert_of_mem hi)`. Rewrite using `[Finset.prod_insert ha, Finset.prod_insert ha, csub_mul_of_bdd hs (hf a (Finset.mem_insert_self a t)) (((GlobalTheory.T.mvPowerSeries_integral_bounded_closure K σ).2.2.2.2.2.1 ι t f).2 ht).1, ih ht]`.
-/
theorem csub_prod_of_bdd (hs : ∀ i, Small (s i)) {ι : Type} (t : Finset ι)
    (f : ι → MvPowerSeries σ K) (hf : ∀ i ∈ t, Bdd (f i)) :
    csub s (∏ i ∈ t, f i) = ∏ i ∈ t, csub s (f i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using csub_one s
  | insert a t ha ih =>
    have ht : ∀ i ∈ t, Bdd (f i) := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    rw [Finset.prod_insert ha, Finset.prod_insert ha,
      csub_mul_of_bdd hs (hf a (Finset.mem_insert_self a t))
        (((GlobalTheory.T.mvPowerSeries_integral_bounded_closure K σ).2.2.2.2.2.1 ι t f).2 ht).1, ih ht]

/- English proof (translation)
Establish `hb` using `fun B => (GlobalTheory.T.mvPowerSeries_integral_bounded_closure K σ).2.2.2.2.2.2.2.2.1 k ι φ a B ha`. Proceed by induction on `A using MvPolynomial.induction_on with`. Consider the case `C c => simp [csub_C]`. Consider the case `add p q hp hq`. Rewrite using `[MvPolynomial.eval₂_add, MvPolynomial.eval₂_add, csub_add_of_bdd hs (hb p) (hb q), hp, hq]`.

Consider the case `mul_X p j hp`. Rewrite using `[MvPolynomial.eval₂_mul, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, MvPolynomial.eval₂_X, csub_mul_of_bdd hs (hb p) (ha j), hp]`.
-/
theorem csub_eval₂_of_bdd (hs : ∀ i, Small (s i)) {k ι : Type} [CommRing k] (φ : k →+* K)
    (a : ι → MvPowerSeries σ K) (A : MvPolynomial ι k) (ha : ∀ j, Bdd (a j)) :
    csub s (MvPolynomial.eval₂ ((MvPowerSeries.C : K →+* MvPowerSeries σ K).comp φ) a A) =
      MvPolynomial.eval₂ ((MvPowerSeries.C : K →+* MvPowerSeries τ K).comp φ)
        (fun j => csub s (a j)) A := by
  have hb := fun B => (GlobalTheory.T.mvPowerSeries_integral_bounded_closure K σ).2.2.2.2.2.2.2.2.1 k ι φ a B ha
  induction A using MvPolynomial.induction_on with
  | C c => simp [csub_C]
  | add p q hp hq =>
    rw [MvPolynomial.eval₂_add, MvPolynomial.eval₂_add, csub_add_of_bdd hs (hb p) (hb q), hp, hq]
  | mul_X p j hp =>
    rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, MvPolynomial.eval₂_X,
      csub_mul_of_bdd hs (hb p) (ha j), hp]

end

/- English proof (translation)
Introduce `K _ _ _ σ τ _ s hs`. Conclude with `⟨fun S T hS hT => ⟨csub_add_of_bdd hs hS hT, csub_sub_of_bdd hs hS hT, csub_mul_of_bdd hs hS hT⟩, csub_C s, csub_X s, fun S n hS => csub_pow_of_bdd hs hS n, fun ι t f hf => csub_prod_of_bdd hs t f hf, fun k ι _ φ a A ha => csub_eval₂_of_bdd hs φ a A ha⟩`.
-/
theorem csub_ring_map : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (σ τ : Type) [Fintype σ] (s : σ → MvPowerSeries τ K), (∀ i, Small (s i)) → (∀ S T : MvPowerSeries σ K, Bdd S → Bdd T → csub s (S + T) = csub s S + csub s T ∧ csub s (S - T) = csub s S - csub s T ∧ csub s (S * T) = csub s S * csub s T) ∧ (∀ a : K, csub s (MvPowerSeries.C a) = MvPowerSeries.C a) ∧ (∀ i, csub s (MvPowerSeries.X i) = s i) ∧ (∀ (S : MvPowerSeries σ K) (n : ℕ), Bdd S → csub s (S ^ n) = csub s S ^ n) ∧ (∀ (ι : Type) (t : Finset ι) (f : ι → MvPowerSeries σ K), (∀ i ∈ t, Bdd (f i)) → csub s (∏ i ∈ t, f i) = ∏ i ∈ t, csub s (f i)) ∧ (∀ (k ι : Type) [CommRing k] (φ : k →+* K) (a : ι → MvPowerSeries σ K) (A : MvPolynomial ι k), (∀ j, Bdd (a j)) → csub s (MvPolynomial.eval₂ ((MvPowerSeries.C : K →+* MvPowerSeries σ K).comp φ) a A) = MvPolynomial.eval₂ ((MvPowerSeries.C : K →+* MvPowerSeries τ K).comp φ) (fun j => csub s (a j)) A) := by
  intro K _ _ _ σ τ _ s hs
  exact ⟨fun S T hS hT => ⟨csub_add_of_bdd hs hS hT, csub_sub_of_bdd hs hS hT,
      csub_mul_of_bdd hs hS hT⟩, csub_C s, csub_X s, fun S n hS => csub_pow_of_bdd hs hS n,
    fun ι t f hf => csub_prod_of_bdd hs t f hf,
    fun k ι _ φ a A ha => csub_eval₂_of_bdd hs φ a A ha⟩

end GlobalTheory.ConvSer
