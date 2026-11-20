import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentApproximation.MemZeroLocusGLIff

noncomputable section

namespace PI.UnipApproxD.IntegersDenseFiniteAdeles

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K]

def IsInt (b : FiniteAdeleRing R K) : Prop := ∀ v, b v ∈ v.adicCompletionIntegers K

/- English proof (translation)
Use `first`. Consider the case `exact valuedAdicCompletion_eq_valuation' v k`. Consider the case `exact valuedAdicCompletion_eq_valuation' k`. Consider the case `exact valuedAdicCompletion_eq_valuation v k`. Consider the case `exact valuedAdicCompletion_eq_valuation k`.

Consider the case `rfl`.
-/
private theorem val_K_lemma (v : HeightOneSpectrum R) (k : K) :
    Valued.v (algebraMap K (v.adicCompletion K) k) = v.valuation K k := by
  first
  | exact valuedAdicCompletion_eq_valuation' v k
  | exact valuedAdicCompletion_eq_valuation' k
  | exact valuedAdicCompletion_eq_valuation v k
  | exact valuedAdicCompletion_eq_valuation k
  | rfl

/- English proof (translation)
Rewrite using `[mem_adicCompletionIntegers, val_K_lemma, valuation_of_algebraMap]`. Use `first`. Consider the case `exact v.intValuation_le_one r`. Consider the case `exact intValuation_le_one v r`. Consider the case `exact intValuation_le_one r`.
-/
theorem int_R (v : HeightOneSpectrum R) (r : R) :
    algebraMap K (v.adicCompletion K) (algebraMap R K r) ∈ v.adicCompletionIntegers K := by
  rw [mem_adicCompletionIntegers, val_K_lemma, valuation_of_algebraMap]
  first
  | exact v.intValuation_le_one r
  | exact intValuation_le_one v r
  | exact intValuation_le_one r

/- English proof (translation)
Rewrite using `[val_K_lemma]`. Use `first`. Consider the case `exact valuation_of_algebraMap v r`. Consider the case `exact v.valuation_of_algebraMap r`. Consider the case `simp [valuation_of_algebraMap]`.
-/
theorem val_R (v : HeightOneSpectrum R) (r : R) :
    Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K r)) = v.intValuation r := by
  rw [val_K_lemma]
  first
  | exact valuation_of_algebraMap v r
  | exact v.valuation_of_algebraMap r
  | simp [valuation_of_algebraMap]

/- English proof (translation)
Establish `hU : IsOpen ((fun z => z - y) ⁻¹' (v.adicCompletionIntegers K : Set (v.adicCompletion K)))` using `(Valued.isOpen_valuationSubring _).preimage (continuous_sub_right y)`. Take `⟨k, hk⟩` from `(denseRange_algebraMap (R := R) (K := K) v).exists_mem_open hU ⟨y, by simp⟩`. Use `⟨k, ?_⟩` and prove the remaining obligations. Establish `hk' : algebraMap K (v.adicCompletion K) k - y ∈ v.adicCompletionIntegers K` using `hk`. Use `neg_mem hk'` as an intermediate fact.

Simplify `this` using `[neg_sub]`.
-/
theorem exists_near (v : HeightOneSpectrum R) (y : v.adicCompletion K) :
    ∃ k : K, y - algebraMap K (v.adicCompletion K) k ∈ v.adicCompletionIntegers K := by
  have hU : IsOpen ((fun z => z - y) ⁻¹' (v.adicCompletionIntegers K : Set (v.adicCompletion K))) :=
    (Valued.isOpen_valuationSubring _).preimage (continuous_sub_right y)
  obtain ⟨k, hk⟩ := (denseRange_algebraMap (R := R) (K := K) v).exists_mem_open hU
    ⟨y, by simp⟩
  refine ⟨k, ?_⟩
  have hk' : algebraMap K (v.adicCompletion K) k - y ∈ v.adicCompletionIntegers K := hk
  have := neg_mem hk'
  simpa [neg_sub] using this

/- English proof (translation)
Take `⟨b, hb, h⟩` from `adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers (R := R) (K := K) v y`. Use `⟨b, nonZeroDivisors.ne_zero hb, ?_⟩` and prove the remaining obligations. Use `first`. Consider the case `(rw [← IsScalarTower.algebraMap_apply, mul_comm]; exact h)`. Consider the case `(rw [mul_comm, ← IsScalarTower.algebraMap_apply]; exact h)`.

Consider the case `(simpa [mul_comm, ← IsScalarTower.algebraMap_apply] using h)`. Consider the case `(convert h using 1; rw [mul_comm, IsScalarTower.algebraMap_apply R K]; rfl)`.
-/
theorem exists_den_local (v : HeightOneSpectrum R) (y : v.adicCompletion K) :
    ∃ s : R, s ≠ 0 ∧
      algebraMap K (v.adicCompletion K) (algebraMap R K s) * y ∈ v.adicCompletionIntegers K := by
  obtain ⟨b, hb, h⟩ := adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers (R := R) (K := K) v y
  refine ⟨b, nonZeroDivisors.ne_zero hb, ?_⟩
  first
  | (rw [← IsScalarTower.algebraMap_apply, mul_comm]; exact h)
  | (rw [mul_comm, ← IsScalarTower.algebraMap_apply]; exact h)
  | (simpa [mul_comm, ← IsScalarTower.algebraMap_apply] using h)
  | (convert h using 1; rw [mul_comm, IsScalarTower.algebraMap_apply R K]; rfl)

/- English proof (translation)
Establish `hfin : {v : HeightOneSpectrum R | b v ∉ v.adicCompletionIntegers K}.Finite` using `by first`. Consider the case `exact Filter.eventually_cofinite.mp b.2`. Consider the case `exact Filter.eventually_cofinite.mp b.prop`. Use `choose s hs0 hs using fun v => exists_den_local (R := R) (K := K) v (b v)`. Use `⟨∏ v ∈ hfin.toFinset, s v, Finset.prod_ne_zero_iff.mpr fun v _ => hs0 v, ?_⟩` and prove the remaining obligations.

Introduce `w`. Establish `hc : (algebraMap R (FiniteAdeleRing R K) (∏ v ∈ hfin.toFinset, s v) * b) w = algebraMap K (w.adicCompletion K) (algebraMap R K (∏ v ∈ hfin.toFinset, s v)) * b w` using `by first`. Consider the case `rfl`. Consider the case `(rw [← IsScalarTower.algebraMap_apply]; rfl)`. Consider the case `simp [IsScalarTower.algebraMap_apply R K (w.adicCompletion K)]`.

Rewrite using `[hc]`. Distinguish the cases in `hw : w ∈ hfin.toFinset`. Rewrite using `[← Finset.mul_prod_erase _ _ hw, map_mul, map_mul, mul_assoc, mul_left_comm]`. Conclude with `mul_mem (int_R w _) (hs w)`. Establish `hbw : b w ∈ w.adicCompletionIntegers K`.

Simplify using `using hw`. Conclude with `mul_mem (int_R w _) hbw`.
-/
theorem exists_den (b : FiniteAdeleRing R K) :
    ∃ r : R, r ≠ 0 ∧ IsInt (algebraMap R (FiniteAdeleRing R K) r * b) := by
  classical
  have hfin : {v : HeightOneSpectrum R | b v ∉ v.adicCompletionIntegers K}.Finite := by
    first
    | exact Filter.eventually_cofinite.mp b.2
    | exact Filter.eventually_cofinite.mp b.prop
  choose s hs0 hs using fun v => exists_den_local (R := R) (K := K) v (b v)
  refine ⟨∏ v ∈ hfin.toFinset, s v, Finset.prod_ne_zero_iff.mpr fun v _ => hs0 v, ?_⟩
  intro w
  have hc : (algebraMap R (FiniteAdeleRing R K) (∏ v ∈ hfin.toFinset, s v) * b) w
      = algebraMap K (w.adicCompletion K) (algebraMap R K (∏ v ∈ hfin.toFinset, s v)) * b w := by
    first
    | rfl
    | (rw [← IsScalarTower.algebraMap_apply]; rfl)
    | simp [IsScalarTower.algebraMap_apply R K (w.adicCompletion K)]
  rw [hc]
  by_cases hw : w ∈ hfin.toFinset
  · rw [← Finset.mul_prod_erase _ _ hw, map_mul, map_mul, mul_assoc, mul_left_comm]
    exact mul_mem (int_R w _) (hs w)
  · have hbw : b w ∈ w.adicCompletionIntegers K := by
      simpa using hw
    exact mul_mem (int_R w _) hbw

/- English proof (translation)
Establish `hrK : algebraMap R K r ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hr`. Establish `hrv : algebraMap K (v.adicCompletion K) (algebraMap R K r) ≠ 0` using `(map_ne_zero_iff _ (algebraMap K (v.adicCompletion K)).injective).mpr hrK`. Take `⟨k', hk'⟩` from `exists_near v ((algebraMap K (v.adicCompletion K) (algebraMap R K r))⁻¹ * c)`. Establish `h1 : Valued.v (c - algebraMap K _ (algebraMap R K r * k')) ≤ v.intValuation r`. Establish `: c - algebraMap K (v.adicCompletion K) (algebraMap R K r * k') = algebraMap K _ (algebraMap R K r) * ((algebraMap K (v.adicCompletion K) (algebraMap R K r))⁻¹ * c - algebraMap K _ k')`.

Rewrite using `[map_mul, mul_sub, ← mul_assoc, mul_inv_cancel₀ hrv, one_mul]`. Rewrite using `[this, Valuation.map_mul, val_R]`. Conclude with `mul_le_of_le_one_right' hk'`. Establish `hk : v.valuation K (algebraMap R K r * k') ≤ 1`. Rewrite using `[← valuedAdicCompletion_eq_valuation']`.

Establish `: (((algebraMap R K r * k' : K)) : v.adicCompletion K) = c - (c - algebraMap K (v.adicCompletion K) (algebraMap R K r * k'))`. Rewrite using `[sub_sub_cancel]`. Both sides reduce to the same expression. Rewrite using `[this]`. Conclude with `(Valuation.map_sub _ _ _).trans (max_le hc (h1.trans (v.intValuation_le_one r)))`.

Establish `hγ : v.intValuation r ≠ 0` using `v.intValuation_ne_zero r hr`. Take `⟨a, ha⟩` from `exists_valuation_sub_lt_of_integer v hk (Units.mk0 _ hγ)`. Use `⟨a, ?_⟩` and prove the remaining obligations. Establish `e : c - algebraMap K (v.adicCompletion K) (algebraMap R K a) = (c - algebraMap K _ (algebraMap R K r * k')) - algebraMap K _ (algebraMap R K a - algebraMap R K r * k')`. Rewrite using `[map_sub]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Use `(Valuation.map_sub _ _ _).trans (max_le h1 ?_)` and prove the remaining obligations. Use `valuedAdicCompletion_eq_valuation' v (algebraMap R K a - algebraMap R K r * k')` as an intermediate fact. Conclude with `this.trans_le ha.le`.
-/
theorem exists_approx_local (v : HeightOneSpectrum R) (c : v.adicCompletion K)
    (hc : c ∈ v.adicCompletionIntegers K) (r : R) (hr : r ≠ 0) :
    ∃ a : R, Valued.v (c - algebraMap K _ (algebraMap R K a)) ≤ v.intValuation r := by
  have hrK : algebraMap R K r ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hr
  have hrv : algebraMap K (v.adicCompletion K) (algebraMap R K r) ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap K (v.adicCompletion K)).injective).mpr hrK
  obtain ⟨k', hk'⟩ := exists_near v ((algebraMap K (v.adicCompletion K) (algebraMap R K r))⁻¹ * c)
  have h1 : Valued.v (c - algebraMap K _ (algebraMap R K r * k')) ≤ v.intValuation r := by
    have : c - algebraMap K (v.adicCompletion K) (algebraMap R K r * k') =
        algebraMap K _ (algebraMap R K r) *
          ((algebraMap K (v.adicCompletion K) (algebraMap R K r))⁻¹ * c - algebraMap K _ k') := by
      rw [map_mul, mul_sub, ← mul_assoc, mul_inv_cancel₀ hrv, one_mul]
    rw [this, Valuation.map_mul, val_R]
    exact mul_le_of_le_one_right' hk'
  have hk : v.valuation K (algebraMap R K r * k') ≤ 1 := by
    rw [← valuedAdicCompletion_eq_valuation']
    have : (((algebraMap R K r * k' : K)) : v.adicCompletion K) =
        c - (c - algebraMap K (v.adicCompletion K) (algebraMap R K r * k')) := by
      rw [sub_sub_cancel]; rfl
    rw [this]
    exact (Valuation.map_sub _ _ _).trans (max_le hc (h1.trans (v.intValuation_le_one r)))
  have hγ : v.intValuation r ≠ 0 := v.intValuation_ne_zero r hr
  obtain ⟨a, ha⟩ := exists_valuation_sub_lt_of_integer v hk (Units.mk0 _ hγ)
  refine ⟨a, ?_⟩
  have e : c - algebraMap K (v.adicCompletion K) (algebraMap R K a) =
      (c - algebraMap K _ (algebraMap R K r * k')) -
        algebraMap K _ (algebraMap R K a - algebraMap R K r * k') := by
    rw [map_sub]; ring
  rw [e]
  refine (Valuation.map_sub _ _ _).trans (max_le h1 ?_)
  have := valuedAdicCompletion_eq_valuation' v (algebraMap R K a - algebraMap R K r * k')
  exact this.trans_le ha.le

/- English proof (translation)
Establish `hT : {v : HeightOneSpectrum R | v.asIdeal ∣ Ideal.span {r}}.Finite` using `Ideal.finite_factors (by rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hr)`. Use `choose a0 ha0 using fun v => exists_approx_local v (c v) (hc v) r hr`. Take `⟨a, ha⟩` from `exists_forall_sub_mem_ideal (s := hT.toFinset) (fun v => v.asIdeal) (fun v => multiplicity v.asIdeal (Ideal.span {r})) (fun v _ => v.prime) (fun v _ w _ hvw h => hvw (HeightOneSpectrum.ext h)) (fun v => a0 v.1)`. Use `⟨a, fun v => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hv : v ∈ hT.toFinset`.

Establish `h1` using `ha v hv`. Rewrite `h1` using `[← intValuation_le_pow_iff_mem, ← intValuation_eq_exp_neg_multiplicity v hr]`. Establish `e : c v - algebraMap K (v.adicCompletion K) (algebraMap R K a) = (c v - algebraMap K _ (algebraMap R K (a0 v))) - algebraMap K _ (algebraMap R K (a - a0 v))`. Rewrite using `[map_sub, map_sub]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e]`. Use `(Valuation.map_sub _ _ _).trans (max_le (ha0 v) ?_)` and prove the remaining obligations. Rewrite using `[val_R]`. Conclude with `h1`. Establish `h1 : v.intValuation r = 1`.

Rewrite using `[intValuation_eq_one_iff_mem_primeCompl]`. Use `Ideal.mem_primeCompl_iff.mpr fun hmem => hv ?_` and prove the remaining obligations. Rewrite using `[Set.Finite.mem_toFinset]`. Conclude with `Ideal.dvd_span_singleton.mpr hmem`. Rewrite using `[h1]`.

Conclude with `sub_mem (hc v) (int_R v a)`.
-/
theorem exists_approx (c : FiniteAdeleRing R K) (hc : IsInt c) (r : R) (hr : r ≠ 0) :
    ∃ a : R, ∀ v, Valued.v (c v - algebraMap K _ (algebraMap R K a)) ≤ v.intValuation r := by
  classical
  have hT : {v : HeightOneSpectrum R | v.asIdeal ∣ Ideal.span {r}}.Finite :=
    Ideal.finite_factors (by rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hr)
  choose a0 ha0 using fun v => exists_approx_local v (c v) (hc v) r hr
  obtain ⟨a, ha⟩ := exists_forall_sub_mem_ideal (s := hT.toFinset) (fun v => v.asIdeal)
    (fun v => multiplicity v.asIdeal (Ideal.span {r})) (fun v _ => v.prime)
    (fun v _ w _ hvw h => hvw (HeightOneSpectrum.ext h)) (fun v => a0 v.1)
  refine ⟨a, fun v => ?_⟩
  by_cases hv : v ∈ hT.toFinset
  · have h1 := ha v hv
    rw [← intValuation_le_pow_iff_mem, ← intValuation_eq_exp_neg_multiplicity v hr] at h1
    have e : c v - algebraMap K (v.adicCompletion K) (algebraMap R K a) =
        (c v - algebraMap K _ (algebraMap R K (a0 v))) - algebraMap K _ (algebraMap R K (a - a0 v)) := by
      rw [map_sub, map_sub]; ring
    rw [e]
    refine (Valuation.map_sub _ _ _).trans (max_le (ha0 v) ?_)
    rw [val_R]; exact h1
  · have h1 : v.intValuation r = 1 := by
      rw [intValuation_eq_one_iff_mem_primeCompl]
      refine Ideal.mem_primeCompl_iff.mpr fun hmem => hv ?_
      rw [Set.Finite.mem_toFinset]; exact Ideal.dvd_span_singleton.mpr hmem
    rw [h1]; exact sub_mem (hc v) (int_R v a)

/- English proof (translation)
Take `⟨r, hr, hc⟩` from `exists_den (R := R) (K := K) b`. Take `⟨a, ha⟩` from `exists_approx (R := R) (K := K) _ hc r hr`. Use `⟨algebraMap R K a / algebraMap R K r, fun v => ?_⟩` and prove the remaining obligations. Establish `hinj : Function.Injective (algebraMap R K)` using `by first`. Consider the case `exact IsFractionRing.injective R K`.

Consider the case `exact IsFractionRing.injective`. Consider the case `exact NoZeroSMulDivisors.algebraMap_injective R K`. Establish `hrK : algebraMap R K r ≠ 0` using `fun h => hr (hinj (by rw [h, map_zero]))`. Establish `hx : algebraMap K (v.adicCompletion K) (algebraMap R K r) ≠ 0` using `(map_ne_zero _).mpr hrK`. Establish `e1 : (b - algebraMap K (FiniteAdeleRing R K) (algebraMap R K a / algebraMap R K r)) v = b v - algebraMap K (v.adicCompletion K) (algebraMap R K a / algebraMap R K r)` using `by first`.

Consider the case `rfl`. Consider the case `simp`. Establish `e2 : (algebraMap R (FiniteAdeleRing R K) r * b) v = algebraMap K (v.adicCompletion K) (algebraMap R K r) * b v` using `by first`. Consider the case `rfl`. Consider the case `(rw [← IsScalarTower.algebraMap_apply]; rfl)`.

Consider the case `simp [IsScalarTower.algebraMap_apply R K (v.adicCompletion K)]`. Establish `h1` using `ha v`. Rewrite `h1` using `[e2]`. Establish `e3 : b v - algebraMap K (v.adicCompletion K) (algebraMap R K a / algebraMap R K r) = (algebraMap K (v.adicCompletion K) (algebraMap R K r))⁻¹ * (algebraMap K (v.adicCompletion K) (algebraMap R K r) * b v - algebraMap K (v.adicCompletion K) (algebraMap R K a))`. Rewrite using `[map_div₀]`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[e1, e3, mem_adicCompletionIntegers, map_mul, map_inv₀, val_R]`. Establish `hne : v.intValuation r ≠ 0`. Rewrite using `[← val_R (K := K) v r]`. Conclude with `(Valuation.ne_zero_iff _).mpr hx`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem exists_approx_adele (b : FiniteAdeleRing R K) :
    ∃ u : K, IsInt (b - algebraMap K (FiniteAdeleRing R K) u) := by
  obtain ⟨r, hr, hc⟩ := exists_den (R := R) (K := K) b
  obtain ⟨a, ha⟩ := exists_approx (R := R) (K := K) _ hc r hr
  refine ⟨algebraMap R K a / algebraMap R K r, fun v => ?_⟩
  have hinj : Function.Injective (algebraMap R K) := by
    first
    | exact IsFractionRing.injective R K
    | exact IsFractionRing.injective
    | exact NoZeroSMulDivisors.algebraMap_injective R K
  have hrK : algebraMap R K r ≠ 0 := fun h => hr (hinj (by rw [h, map_zero]))
  have hx : algebraMap K (v.adicCompletion K) (algebraMap R K r) ≠ 0 := (map_ne_zero _).mpr hrK
  have e1 : (b - algebraMap K (FiniteAdeleRing R K) (algebraMap R K a / algebraMap R K r)) v
      = b v - algebraMap K (v.adicCompletion K) (algebraMap R K a / algebraMap R K r) := by
    first
    | rfl
    | simp
  have e2 : (algebraMap R (FiniteAdeleRing R K) r * b) v
      = algebraMap K (v.adicCompletion K) (algebraMap R K r) * b v := by
    first
    | rfl
    | (rw [← IsScalarTower.algebraMap_apply]; rfl)
    | simp [IsScalarTower.algebraMap_apply R K (v.adicCompletion K)]
  have h1 := ha v
  rw [e2] at h1
  have e3 : b v - algebraMap K (v.adicCompletion K) (algebraMap R K a / algebraMap R K r)
      = (algebraMap K (v.adicCompletion K) (algebraMap R K r))⁻¹ *
        (algebraMap K (v.adicCompletion K) (algebraMap R K r) * b v
          - algebraMap K (v.adicCompletion K) (algebraMap R K a)) := by
    rw [map_div₀]
    field_simp
  rw [e1, e3, mem_adicCompletionIntegers, map_mul, map_inv₀, val_R]
  have hne : v.intValuation r ≠ 0 := by
    rw [← val_R (K := K) v r]
    exact (Valuation.ne_zero_iff _).mpr hx
  calc (v.intValuation r)⁻¹ * Valued.v _ ≤ (v.intValuation r)⁻¹ * v.intValuation r :=
        by gcongr
    _ = 1 := inv_mul_cancel₀ hne

/- English proof (translation)
Take `⟨γ, hγ⟩` from `Valued.mem_nhds_zero.mp hU`. Establish `hpos : (0 : WithZero (Multiplicative ℤ)) < MonoidWithZeroHom.ValueGroup₀.embedding γ.1`. Use `MonoidWithZeroHom.ValueGroup₀.embedding_strictMono (zero_lt_iff.mpr γ.ne_zero)` as an intermediate fact. Simplify using `using this`. Take `⟨k, hk⟩` from `WithZero.exists_exp_neg_natCast_lt hpos.ne'`.

Establish `hI : v.asIdeal ^ k ≠ ⊥`. Rewrite using `[← Ideal.zero_eq_bot]; exact pow_ne_zero _ (by rw [Ideal.zero_eq_bot]; exact v.ne_bot)`. Take `⟨r, hrI, hr⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hI`. Use `⟨r, hr, fun y hy => hγ ?_⟩` and prove the remaining obligations. Use `show Valued.v.restrict y < γ.1`.

Rewrite using `[Valuation.restrict_lt_iff_lt_embedding]`. Conclude with `lt_of_le_of_lt (hy.trans ((v.intValuation_le_pow_iff_mem r k).mpr hrI)) hk`.
-/
theorem exists_small (v : HeightOneSpectrum R) {U : Set (v.adicCompletion K)}
    (hU : U ∈ nhds (0 : v.adicCompletion K)) :
    ∃ r : R, r ≠ 0 ∧ ∀ y : v.adicCompletion K, Valued.v y ≤ v.intValuation r → y ∈ U := by
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.mp hU
  have hpos : (0 : WithZero (Multiplicative ℤ)) < MonoidWithZeroHom.ValueGroup₀.embedding γ.1 := by
    have := MonoidWithZeroHom.ValueGroup₀.embedding_strictMono (zero_lt_iff.mpr γ.ne_zero)
    simpa using this
  obtain ⟨k, hk⟩ := WithZero.exists_exp_neg_natCast_lt hpos.ne'
  have hI : v.asIdeal ^ k ≠ ⊥ := by
    rw [← Ideal.zero_eq_bot]; exact pow_ne_zero _ (by rw [Ideal.zero_eq_bot]; exact v.ne_bot)
  obtain ⟨r, hrI, hr⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  refine ⟨r, hr, fun y hy => hγ ?_⟩
  show Valued.v.restrict y < γ.1
  rw [Valuation.restrict_lt_iff_lt_embedding]
  exact lt_of_le_of_lt (hy.trans ((v.intValuation_le_pow_iff_mem r k).mpr hrI)) hk

/- English proof (translation)
Use `choose! r hr0 hr using fun v (hv : v ∈ s) => exists_small (R := R) (K := K) v (hU v hv)`. Use `⟨∏ w ∈ s, r w, Finset.prod_ne_zero_iff.mpr hr0, ?_⟩` and prove the remaining obligations. Introduce `v hv y hy`. Apply `hr v hv y` to reduce the goal to its premises. Use `le_trans hy ?_` and prove the remaining obligations.

Rewrite using `[map_prod, ← Finset.mul_prod_erase s _ hv]`. Apply `mul_le_of_le_one_right'` to reduce the goal to its premises. Apply `Finset.prod_le_one'` to reduce the goal to its premises. Introduce `w _`. Use `first`.

Consider the case `exact v.intValuation_le_one (r w)`. Consider the case `exact intValuation_le_one v (r w)`. Consider the case `exact intValuation_le_one (r w)`.
-/
theorem exists_small_finset (s : Finset (HeightOneSpectrum R)) (U : ∀ v : HeightOneSpectrum R, Set (v.adicCompletion K))
    (hU : ∀ v ∈ s, U v ∈ nhds (0 : v.adicCompletion K)) :
    ∃ r : R, r ≠ 0 ∧ ∀ v ∈ s, ∀ y : v.adicCompletion K, Valued.v y ≤ v.intValuation r → y ∈ U v := by
  classical
  choose! r hr0 hr using fun v (hv : v ∈ s) => exists_small (R := R) (K := K) v (hU v hv)
  refine ⟨∏ w ∈ s, r w, Finset.prod_ne_zero_iff.mpr hr0, ?_⟩
  intro v hv y hy
  apply hr v hv y
  refine le_trans hy ?_
  rw [map_prod, ← Finset.mul_prod_erase s _ hv]
  apply mul_le_of_le_one_right'
  apply Finset.prod_le_one'
  intro w _
  first
  | exact v.intValuation_le_one (r w)
  | exact intValuation_le_one v (r w)
  | exact intValuation_le_one (r w)

/- English proof (translation)
Introduce `x`. Rewrite using `[mem_closure_iff_nhds]`. Introduce `t ht`. Establish `hc : Continuous (fun y : FiniteAdeleRing R K => x + y)` using `continuous_const.add continuous_id`. Establish `h1 : (fun y : FiniteAdeleRing R K => x + y) ⁻¹' t ∈ nhds (0 : FiniteAdeleRing R K)` using `hc.continuousAt.preimage_mem_nhds (by rwa [add_zero])`.

Establish `hAopen : ∀ v : HeightOneSpectrum R, IsOpen (v.adicCompletionIntegers K : Set (v.adicCompletion K))` using `fun v => Valued.isOpen_valuationSubring _`. Set `z0 : ∀ v : HeightOneSpectrum R, (v.adicCompletionIntegers K : Set (v.adicCompletion K))` to `fun v => ⟨0, (v.adicCompletionIntegers K).zero_mem⟩`. Establish `h1' : ((fun y : FiniteAdeleRing R K => x + y) ⁻¹' t : Set (RestrictedProduct (fun v : HeightOneSpectrum R => v.adicCompletion K) (fun v => (v.adicCompletionIntegers K : Set (v.adicCompletion K))) Filter.cofinite)) ∈ nhds (RestrictedProduct.structureMap (fun v : HeightOneSpectrum …` using `h1`. Rewrite `h1'` using `[RestrictedProduct.nhds_eq_map_structureMap hAopen, Filter.mem_map, nhds_pi, Filter.mem_pi']`. Take `⟨I, u, hu, hIu⟩` from `h1'`.

Establish `hW : ∀ v, ∃ W : Set (v.adicCompletion K), W ∈ nhds (0 : v.adicCompletion K) ∧ ∀ y : v.adicCompletion K, (hy : y ∈ (v.adicCompletionIntegers K : Set (v.adicCompletion K))) → y ∈ W → (⟨y, hy⟩ : (v.adicCompletionIntegers K : Set (v.adicCompletion K))) ∈ u v`. Introduce `v`. Take `⟨W, hW, hWu⟩` from `(mem_nhds_subtype _ (z0 v) (u v)).mp (hu v)`. Conclude with `⟨W, hW, fun y hy hyW => hWu hyW⟩`. Use `choose W hW0 hWu using hW`.

Take `⟨r, hr, hsmall⟩` from `exists_small_finset I W (fun v _ => hW0 v)`. Take `⟨u0, hu0⟩` from `exists_approx_adele x`. Take `⟨a, ha⟩` from `exists_approx _ hu0 r hr`. Use `⟨algebraMap K (FiniteAdeleRing R K) (u0 + algebraMap R K a), ?_, _, rfl⟩` and prove the remaining obligations. Establish `ey : ∀ v : HeightOneSpectrum R, (algebraMap K (FiniteAdeleRing R K) (u0 + algebraMap R K a) - x) v = -((x - algebraMap K (FiniteAdeleRing R K) u0) v - algebraMap K (v.adicCompletion K) (algebraMap R K a))`.

Introduce `v`. Use `show algebraMap K (v.adicCompletion K) (u0 + algebraMap R K a) - x v = -((x v - algebraMap K (v.adicCompletion K) u0) - algebraMap K (v.adicCompletion K) (algebraMap R K a))`. Rewrite using `[map_add]`. Expand and normalize the polynomial expressions, which then agree. Establish `hval : ∀ v : HeightOneSpectrum R, Valued.v ((algebraMap K (FiniteAdeleRing R K) (u0 + algebraMap R K a) - x) v) ≤ v.intValuation r`.

Introduce `v`. Rewrite using `[ey, Valuation.map_neg]`. Conclude with `ha v`. Establish `hint : ∀ v : HeightOneSpectrum R, (algebraMap K (FiniteAdeleRing R K) (u0 + algebraMap R K a) - x) v ∈ (v.adicCompletionIntegers K : Set (v.adicCompletion K))`. Introduce `v`.

Rewrite using `[SetLike.mem_coe, mem_adicCompletionIntegers]`. Conclude with `(hval v).trans (v.intValuation_le_one r)`. Set `z : ∀ v : HeightOneSpectrum R, (v.adicCompletionIntegers K : Set (v.adicCompletion K))` to `fun v => ⟨(algebraMap K (FiniteAdeleRing R K) (u0 + algebraMap R K a) - x) v, hint v⟩`. Establish `hz : z ∈ Set.pi (↑I) u` using `fun v hv => hWu v _ (hint v) (hsmall v hv _ (hval v))`. Establish `hmem` using `hIu hz`.

Establish `e : x + (algebraMap K (FiniteAdeleRing R K) (u0 + algebraMap R K a) - x) = algebraMap K (FiniteAdeleRing R K) (u0 + algebraMap R K a)` using `add_sub_cancel x _`. Rewrite using `[← e]`. Conclude with `hmem`.
-/
theorem denseRange : DenseRange (algebraMap K (FiniteAdeleRing R K)) := by
  classical
  intro x
  rw [mem_closure_iff_nhds]
  intro t ht
  have hc : Continuous (fun y : FiniteAdeleRing R K => x + y) := continuous_const.add continuous_id
  have h1 : (fun y : FiniteAdeleRing R K => x + y) ⁻¹' t ∈ nhds (0 : FiniteAdeleRing R K) :=
    hc.continuousAt.preimage_mem_nhds (by rwa [add_zero])
  have hAopen : ∀ v : HeightOneSpectrum R,
      IsOpen (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
    fun v => Valued.isOpen_valuationSubring _
  let z0 : ∀ v : HeightOneSpectrum R, (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
    fun v => ⟨0, (v.adicCompletionIntegers K).zero_mem⟩
  have h1' : ((fun y : FiniteAdeleRing R K => x + y) ⁻¹' t :
        Set (RestrictedProduct (fun v : HeightOneSpectrum R => v.adicCompletion K)
          (fun v => (v.adicCompletionIntegers K : Set (v.adicCompletion K))) Filter.cofinite)) ∈
      nhds (RestrictedProduct.structureMap (fun v : HeightOneSpectrum R => v.adicCompletion K)
        (fun v => (v.adicCompletionIntegers K : Set (v.adicCompletion K))) Filter.cofinite z0) := h1
  rw [RestrictedProduct.nhds_eq_map_structureMap hAopen, Filter.mem_map, nhds_pi,
    Filter.mem_pi'] at h1'
  obtain ⟨I, u, hu, hIu⟩ := h1'
  have hW : ∀ v, ∃ W : Set (v.adicCompletion K), W ∈ nhds (0 : v.adicCompletion K) ∧
      ∀ y : v.adicCompletion K, (hy : y ∈ (v.adicCompletionIntegers K : Set (v.adicCompletion K))) →
        y ∈ W → (⟨y, hy⟩ : (v.adicCompletionIntegers K : Set (v.adicCompletion K))) ∈ u v := by
    intro v
    obtain ⟨W, hW, hWu⟩ := (mem_nhds_subtype _ (z0 v) (u v)).mp (hu v)
    exact ⟨W, hW, fun y hy hyW => hWu hyW⟩
  choose W hW0 hWu using hW
  obtain ⟨r, hr, hsmall⟩ := exists_small_finset I W (fun v _ => hW0 v)
  obtain ⟨u0, hu0⟩ := exists_approx_adele x
  obtain ⟨a, ha⟩ := exists_approx _ hu0 r hr
  refine ⟨algebraMap K (FiniteAdeleRing R K) (u0 + algebraMap R K a), ?_, _, rfl⟩
  have ey : ∀ v : HeightOneSpectrum R,
      (algebraMap K (FiniteAdeleRing R K) (u0 + algebraMap R K a) - x) v =
        -((x - algebraMap K (FiniteAdeleRing R K) u0) v -
          algebraMap K (v.adicCompletion K) (algebraMap R K a)) := by
    intro v
    show algebraMap K (v.adicCompletion K) (u0 + algebraMap R K a) - x v =
      -((x v - algebraMap K (v.adicCompletion K) u0) - algebraMap K (v.adicCompletion K) (algebraMap R K a))
    rw [map_add]; ring
  have hval : ∀ v : HeightOneSpectrum R,
      Valued.v ((algebraMap K (FiniteAdeleRing R K) (u0 + algebraMap R K a) - x) v) ≤ v.intValuation r := by
    intro v
    rw [ey, Valuation.map_neg]
    exact ha v
  have hint : ∀ v : HeightOneSpectrum R,
      (algebraMap K (FiniteAdeleRing R K) (u0 + algebraMap R K a) - x) v ∈
        (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
    intro v
    rw [SetLike.mem_coe, mem_adicCompletionIntegers]
    exact (hval v).trans (v.intValuation_le_one r)
  let z : ∀ v : HeightOneSpectrum R, (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
    fun v => ⟨(algebraMap K (FiniteAdeleRing R K) (u0 + algebraMap R K a) - x) v, hint v⟩
  have hz : z ∈ Set.pi (↑I) u := fun v hv => hWu v _ (hint v) (hsmall v hv _ (hval v))
  have hmem := hIu hz
  have e : x + (algebraMap K (FiniteAdeleRing R K) (u0 + algebraMap R K a) - x) =
      algebraMap K (FiniteAdeleRing R K) (u0 + algebraMap R K a) := add_sub_cancel x _
  rw [← e]
  exact hmem

end PI.UnipApproxD.IntegersDenseFiniteAdeles

namespace PI.UnipApproxD

open NumberField IsDedekindDomain

/- English proof (translation)
Introduce `F _ _`. Conclude with `IntegersDenseFiniteAdeles.denseRange`.
-/
theorem additive_dense_integers : AddDense := by
  intro F _ _
  exact IntegersDenseFiniteAdeles.denseRange

end PI.UnipApproxD
