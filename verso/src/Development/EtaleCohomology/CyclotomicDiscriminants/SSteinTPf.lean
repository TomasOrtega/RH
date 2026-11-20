import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LemmaKOfSteps

noncomputable section

open NumberField IsDedekindDomain FractionalIdeal Matrix
open scoped nonZeroDivisors

namespace LateralTheory.Q.SSteinT

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

variable {R : Type} [CommRing R] [IsDedekindDomain R] {K : Type} [Field K] [Algebra R K] [IsFractionRing R K]

/- English proof (translation)
Take `⟨r, s, hs, rfl⟩` from `IsFractionRing.div_surjective (A := R) x`. Establish `hs0 : s ≠ 0` using `nonZeroDivisors.ne_zero hs`. Establish `hr0 : r ≠ 0`. Introduce and unpack `rfl`. Simplify using `at hx`.

Establish `h : spanSingleton R⁰ (algebraMap R K r / algebraMap R K s) = spanSingleton R⁰ (algebraMap R K s)⁻¹ * ((Ideal.span {r} : Ideal R) : FractionalIdeal R⁰ K)`. Rewrite using `[coeIdeal_span_singleton, spanSingleton_mul_spanSingleton, div_eq_inv_mul]`. Rewrite using `[count_well_defined K P (spanSingleton_ne_zero_iff.mpr hx) h, map_div₀, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_if_neg P hr0, HeightOneSpectrum.intValuation_if_neg P hs0, ← WithZero.exp_sub]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem val_eq_count (P : HeightOneSpectrum R) (x : K) (hx : x ≠ 0) :
    P.valuation K x = WithZero.exp (-count K P (spanSingleton R⁰ x)) := by
  obtain ⟨r, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
  have hr0 : r ≠ 0 := by
    rintro rfl
    simp at hx
  have h : spanSingleton R⁰ (algebraMap R K r / algebraMap R K s) =
      spanSingleton R⁰ (algebraMap R K s)⁻¹ * ((Ideal.span {r} : Ideal R) : FractionalIdeal R⁰ K) := by
    rw [coeIdeal_span_singleton, spanSingleton_mul_spanSingleton, div_eq_inv_mul]
  rw [count_well_defined K P (spanSingleton_ne_zero_iff.mpr hx) h, map_div₀,
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.intValuation_if_neg P hr0, HeightOneSpectrum.intValuation_if_neg P hs0,
    ← WithZero.exp_sub]
  congr 1
  ring

/- English proof (translation)
Distinguish the cases in `h0 : x = 0`. Simplify using `[h0]`. Rewrite using `[val_eq_count P x h0, WithZero.exp_le_exp, neg_le_neg_iff]`. Conclude with `count_mono K P (spanSingleton_ne_zero_iff.mpr h0) (spanSingleton_le_iff_mem.mpr hx)`.
-/
theorem val_le_of_mem (P : HeightOneSpectrum R) {I : FractionalIdeal R⁰ K} {x : K} (hx : x ∈ I) :
    P.valuation K x ≤ WithZero.exp (-count K P I) := by
  by_cases h0 : x = 0
  · simp [h0]
  rw [val_eq_count P x h0, WithZero.exp_le_exp, neg_le_neg_iff]
  exact count_mono K P (spanSingleton_ne_zero_iff.mpr h0) (spanSingleton_le_iff_mem.mpr hx)

/- English proof (translation)
Use `⟨d.prod fun P n => (P.asIdeal : FractionalIdeal R⁰ K) ^ n, ?_, fun P => count_finsuppProd K P d⟩` and prove the remaining obligations. Use `Finset.prod_ne_zero_iff.mpr fun P _ => zpow_ne_zero _ ?_` and prove the remaining obligations. Conclude with `coeIdeal_ne_zero.mpr P.ne_bot`.
-/
theorem exists_frac (d : HeightOneSpectrum R →₀ ℤ) :
    ∃ I : FractionalIdeal R⁰ K, I ≠ 0 ∧ ∀ P, count K P I = d P := by
  refine ⟨d.prod fun P n => (P.asIdeal : FractionalIdeal R⁰ K) ^ n, ?_, fun P => count_finsuppProd K P d⟩
  refine Finset.prod_ne_zero_iff.mpr fun P _ => zpow_ne_zero _ ?_
  exact coeIdeal_ne_zero.mpr P.ne_bot

/- English proof (translation)
Take `⟨C, hC, hCd⟩` from `exists_frac (K := K) d`. Take `⟨D, hD, hDe⟩` from `exists_frac (K := K) e`. Take `⟨p, hp0, hp⟩` from `exists_ne_zero_mem_isInteger hC`. Use `set p' := algebraMap R K p with hp'`. Establish `hp'0 : p' ≠ 0`.

Rewrite using `[hp']`. Conclude with `(map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hp0`. Establish `h1 : spanSingleton R⁰ p' * C⁻¹ ≤ 1`. Rewrite using `[← mul_inv_cancel₀ hC]`. Conclude with `mul_le_mul_left (spanSingleton_le_iff_mem.mpr hp) _`.

Take `⟨q, hq⟩` from `exists_add_spanSingleton_mul_eq h1 (mul_ne_zero (spanSingleton_ne_zero_iff.mpr hp'0) (inv_ne_zero hC)) (inv_ne_zero hD)`. Establish `hqD : q ∈ D`. Establish `h2 : spanSingleton R⁰ q * D⁻¹ ≤ 1`. Rewrite using `[← hq]`. Conclude with `le_sup_right`.

Establish `h3 : spanSingleton R⁰ q * D⁻¹ * D ≤ 1 * D` using `mul_le_mul_left h2 _`. Rewrite `h3` using `[inv_mul_cancel_right₀ hD, one_mul]`. Conclude with `spanSingleton_le_iff_mem.mp h3`. Establish `h4 : (1 : K) ∈ spanSingleton R⁰ p' * C⁻¹ + spanSingleton R⁰ q * D⁻¹`. Rewrite using `[hq]`.

Conclude with `one_mem_one _`. Take `⟨u, hu, w, hw, huw⟩` from `(mem_add _ _ _).mp h4`. Take `⟨s, hs, rfl⟩` from `mem_singleton_mul.mp hu`. Take `⟨r, hr, rfl⟩` from `mem_singleton_mul.mp hw`. Use `⟨p', q, -r, s, hp'0, by rw [← huw]; ring, fun P => ⟨?_, ?_, ?_, ?_⟩⟩` and prove the remaining obligations.

Rewrite using `[← hCd]`. Conclude with `val_le_of_mem P hp`. Rewrite using `[← hDe]`. Conclude with `val_le_of_mem P hqD`. Rewrite using `[← hDe, ← count_inv, Valuation.map_neg]`.

Conclude with `val_le_of_mem P hr`. Rewrite using `[← hCd, ← count_inv]`. Conclude with `val_le_of_mem P hs`.
-/
theorem exists_sl2_with_valuation_bounds (d e : HeightOneSpectrum R →₀ ℤ) :
    ∃ p q r s : K, p ≠ 0 ∧ p * s - q * r = 1 ∧ ∀ P : HeightOneSpectrum R,
      P.valuation K p ≤ WithZero.exp (-d P) ∧ P.valuation K q ≤ WithZero.exp (-e P) ∧
      P.valuation K r ≤ WithZero.exp (-(-e P)) ∧ P.valuation K s ≤ WithZero.exp (-(-d P)) := by
  obtain ⟨C, hC, hCd⟩ := exists_frac (K := K) d
  obtain ⟨D, hD, hDe⟩ := exists_frac (K := K) e
  obtain ⟨p, hp0, hp⟩ := exists_ne_zero_mem_isInteger hC
  set p' := algebraMap R K p with hp'
  have hp'0 : p' ≠ 0 := by
    rw [hp']
    exact (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hp0
  have h1 : spanSingleton R⁰ p' * C⁻¹ ≤ 1 := by
    rw [← mul_inv_cancel₀ hC]
    exact mul_le_mul_left (spanSingleton_le_iff_mem.mpr hp) _
  obtain ⟨q, hq⟩ := exists_add_spanSingleton_mul_eq h1
    (mul_ne_zero (spanSingleton_ne_zero_iff.mpr hp'0) (inv_ne_zero hC)) (inv_ne_zero hD)
  have hqD : q ∈ D := by
    have h2 : spanSingleton R⁰ q * D⁻¹ ≤ 1 := by
      rw [← hq]
      exact le_sup_right
    have h3 : spanSingleton R⁰ q * D⁻¹ * D ≤ 1 * D := mul_le_mul_left h2 _
    rw [inv_mul_cancel_right₀ hD, one_mul] at h3
    exact spanSingleton_le_iff_mem.mp h3
  have h4 : (1 : K) ∈ spanSingleton R⁰ p' * C⁻¹ + spanSingleton R⁰ q * D⁻¹ := by
    rw [hq]
    exact one_mem_one _
  obtain ⟨u, hu, w, hw, huw⟩ := (mem_add _ _ _).mp h4
  obtain ⟨s, hs, rfl⟩ := mem_singleton_mul.mp hu
  obtain ⟨r, hr, rfl⟩ := mem_singleton_mul.mp hw
  refine ⟨p', q, -r, s, hp'0, by rw [← huw]; ring, fun P => ⟨?_, ?_, ?_, ?_⟩⟩
  · rw [← hCd]; exact val_le_of_mem P hp
  · rw [← hDe]; exact val_le_of_mem P hqD
  · rw [← hDe, ← count_inv, Valuation.map_neg]; exact val_le_of_mem P hr
  · rw [← hCd, ← count_inv]; exact val_le_of_mem P hs

/- English proof (translation)
Use `Valuation.map_add_le _ ?_ ?_` and prove the remaining obligations. Rewrite using `[map_mul, h, neg_add, WithZero.exp_add]`. Conclude with `mul_le_mul' hu hx`. Rewrite using `[map_mul, h', neg_add, WithZero.exp_add]`. Conclude with `mul_le_mul' hu' hx'`.
-/
theorem val_comb (P : HeightOneSpectrum R) {u x u' x' : K} {m a m' a' c : ℤ}
    (hu : P.valuation K u ≤ WithZero.exp (-m)) (hx : P.valuation K x ≤ WithZero.exp (-a))
    (hu' : P.valuation K u' ≤ WithZero.exp (-m')) (hx' : P.valuation K x' ≤ WithZero.exp (-a'))
    (h : c = m + a) (h' : c = m' + a') : P.valuation K (u * x + u' * x') ≤ WithZero.exp (-c) := by
  refine Valuation.map_add_le _ ?_ ?_
  · rw [map_mul, h, neg_add, WithZero.exp_add]; exact mul_le_mul' hu hx
  · rw [map_mul, h', neg_add, WithZero.exp_add]; exact mul_le_mul' hu' hx'

variable {J : Type} [Fintype J] [DecidableEq J]

def Lat (𝔞 : J → HeightOneSpectrum R →₀ ℤ) (x : J → K) : Prop :=
  ∀ j P, P.valuation K (x j) ≤ WithZero.exp (-𝔞 j P)

def Rel (𝔞 𝔟 : J → HeightOneSpectrum R →₀ ℤ) (β : K) : Prop :=
  ∃ M : Matrix J J K, M.det = β ∧ ∀ x : J → K, Lat 𝔞 x ↔ Lat 𝔟 (M *ᵥ x)

/- English proof (translation)
Assemble the required witnesses or components as `⟨1, det_one, fun x => by rw [one_mulVec]⟩`.
-/
theorem Rel.refl (𝔞 : J → HeightOneSpectrum R →₀ ℤ) : Rel 𝔞 𝔞 (1 : K) :=
  ⟨1, det_one, fun x => by rw [one_mulVec]⟩

/- English proof (translation)
Take `⟨M, hM, h⟩` from `h`. Take `⟨N, hN, h'⟩` from `h'`. Conclude with `⟨N * M, by rw [det_mul, hM, hN], fun x => by rw [h, h', mulVec_mulVec]⟩`.
-/
theorem Rel.trans {𝔞 𝔟 𝔠 : J → HeightOneSpectrum R →₀ ℤ} {β γ : K} (h : Rel 𝔞 𝔟 β) (h' : Rel 𝔟 𝔠 γ) :
    Rel 𝔞 𝔠 (γ * β) := by
  obtain ⟨M, hM, h⟩ := h
  obtain ⟨N, hN, h'⟩ := h'
  exact ⟨N * M, by rw [det_mul, hM, hN], fun x => by rw [h, h', mulVec_mulVec]⟩

/- English proof (translation)
Use `⟨transvection j i (r / p) * diagonal (Pi.mulSingle i p * Pi.mulSingle j p⁻¹) * transvection i j (q / p), ?_, fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[det_mul, det_mul, det_transvection_of_ne _ _ hij, det_transvection_of_ne _ _ hij.symm, det_diagonal]`. Simplify using `[Finset.prod_mul_distrib, Finset.prod_pi_mulSingle', hp]`. Establish `hs : s = (1 + q * r) / p`. Rewrite using `[← h]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← mulVec_mulVec, ← mulVec_mulVec]`. Use `⟨?_, ?_, fun k hk hk' => ?_⟩` and prove the remaining obligations. Simplify using `[-mulVec_mulVec, transvection, add_mulVec, single_mulVec, mulVec_diagonal, hij, hij.symm]`.

Clear the denominators using the available nonvanishing facts. Simplify using `[-mulVec_mulVec, transvection, add_mulVec, single_mulVec, mulVec_diagonal, hij, hij.symm, hs]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Simplify using `[-mulVec_mulVec, transvection, add_mulVec, single_mulVec, mulVec_diagonal, hk, hk']`.
-/
theorem exists_block {i j : J} (hij : i ≠ j) {p q r s : K} (hp : p ≠ 0) (h : p * s - q * r = 1) :
    ∃ M : Matrix J J K, M.det = 1 ∧ ∀ x : J → K, (M *ᵥ x) i = p * x i + q * x j ∧
      (M *ᵥ x) j = r * x i + s * x j ∧ ∀ k, k ≠ i → k ≠ j → (M *ᵥ x) k = x k := by
  refine ⟨transvection j i (r / p) * diagonal (Pi.mulSingle i p * Pi.mulSingle j p⁻¹) *
    transvection i j (q / p), ?_, fun x => ?_⟩
  · rw [det_mul, det_mul, det_transvection_of_ne _ _ hij, det_transvection_of_ne _ _ hij.symm, det_diagonal]
    simp [Finset.prod_mul_distrib, Finset.prod_pi_mulSingle', hp]
  · have hs : s = (1 + q * r) / p := by
      rw [← h]; field_simp; ring
    rw [← mulVec_mulVec, ← mulVec_mulVec]
    refine ⟨?_, ?_, fun k hk hk' => ?_⟩
    · simp [-mulVec_mulVec, transvection, add_mulVec, single_mulVec, mulVec_diagonal, hij, hij.symm]
      field_simp
    · simp [-mulVec_mulVec, transvection, add_mulVec, single_mulVec, mulVec_diagonal, hij, hij.symm, hs]
      field_simp
      ring
    · simp [-mulVec_mulVec, transvection, add_mulVec, single_mulVec, mulVec_diagonal, hk, hk']

/- English proof (translation)
Take `⟨p, q, r, s, hp, h, hv⟩` from `exists_sl2_with_valuation_bounds (K := K) d (𝔞 i + d - 𝔞 j)`. Take `⟨M, hM, hx⟩` from `exists_block hij hp h`. Use `⟨M, hM, fun x => ?_⟩` and prove the remaining obligations. Take `⟨hi, hj, hk⟩` from `hx x`. Prove the components needed by the constructor for the conclusion.

Introduce `H k P`. Take `⟨h1, h2, h3, h4⟩` from `hv P`. Distinguish the cases in `hki : k = i`. Substitute `hki` using the available equality. Rewrite using `[hi]`.

Apply the tactic sequence `refine val_comb P h1 (H k P) h2 (H j P) ?_ ?_ <;> simp [hij] <;> ring`. Distinguish the cases in `hkj : k = j`. Substitute `hkj` using the available equality. Rewrite using `[hj]`. Apply the tactic sequence `refine val_comb P h3 (H i P) h4 (H k P) ?_ ?_ <;> simp [hij.symm] <;> ring`.

Rewrite using `[hk k hki hkj]`. Simplify `H k P` using `[hki, hkj]`. Introduce `H k P`. Take `⟨h1, h2, h3, h4⟩` from `hv P`. Distinguish the cases in `hki : k = i`.

Substitute `hki` using the available equality. Establish `: x k = s * (M *ᵥ x) k + (-q) * (M *ᵥ x) j`. Rewrite using `[hi, hj]`. Take the linear combination `(-x k) * h`. Rewrite using `[this]`.

Rewrite `h2` using `[← Valuation.map_neg]`. Apply the tactic sequence `refine val_comb P h4 (H k P) h2 (H j P) ?_ ?_ <;> simp [hij, hij.symm] <;> ring`. Distinguish the cases in `hkj : k = j`. Substitute `hkj` using the available equality. Establish `: x k = (-r) * (M *ᵥ x) i + p * (M *ᵥ x) k`.

Rewrite using `[hi, hj]`. Take the linear combination `(-x k) * h`. Rewrite using `[this]`. Rewrite `h3` using `[← Valuation.map_neg]`. Apply the tactic sequence `refine val_comb P h3 (H i P) h1 (H k P) ?_ ?_ <;> simp [hij, hij.symm] <;> ring`.

Use `H k P` as an intermediate fact. Rewrite `this` using `[hk k hki hkj]`. Simplify `this` using `[hki, hkj]`.
-/
theorem rel_move {i j : J} (hij : i ≠ j) (𝔞 : J → HeightOneSpectrum R →₀ ℤ) (d : HeightOneSpectrum R →₀ ℤ) :
    Rel 𝔞 (𝔞 + Pi.single i d - Pi.single j d) (1 : K) := by
  obtain ⟨p, q, r, s, hp, h, hv⟩ := exists_sl2_with_valuation_bounds (K := K) d (𝔞 i + d - 𝔞 j)
  obtain ⟨M, hM, hx⟩ := exists_block hij hp h
  refine ⟨M, hM, fun x => ?_⟩
  obtain ⟨hi, hj, hk⟩ := hx x
  constructor
  · intro H k P
    obtain ⟨h1, h2, h3, h4⟩ := hv P
    by_cases hki : k = i
    · subst hki
      rw [hi]
      refine val_comb P h1 (H k P) h2 (H j P) ?_ ?_ <;> simp [hij] <;> ring
    by_cases hkj : k = j
    · subst hkj
      rw [hj]
      refine val_comb P h3 (H i P) h4 (H k P) ?_ ?_ <;> simp [hij.symm] <;> ring
    · rw [hk k hki hkj]
      simpa [hki, hkj] using H k P
  · intro H k P
    obtain ⟨h1, h2, h3, h4⟩ := hv P
    by_cases hki : k = i
    · subst hki
      have : x k = s * (M *ᵥ x) k + (-q) * (M *ᵥ x) j := by
        rw [hi, hj]; linear_combination (-x k) * h
      rw [this]
      rw [← Valuation.map_neg] at h2
      refine val_comb P h4 (H k P) h2 (H j P) ?_ ?_ <;> simp [hij, hij.symm] <;> ring
    by_cases hkj : k = j
    · subst hkj
      have : x k = (-r) * (M *ᵥ x) i + p * (M *ᵥ x) k := by
        rw [hi, hj]; linear_combination (-x k) * h
      rw [this]
      rw [← Valuation.map_neg] at h3
      refine val_comb P h3 (H i P) h1 (H k P) ?_ ?_ <;> simp [hij, hij.symm] <;> ring
    · have := H k P
      rw [hk k hki hkj] at this
      simpa [hki, hkj] using this

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty`. Introduce `𝔞 𝔟 h hs`. Establish `: 𝔞 = 𝔟`. Use function extensionality and compare the values at `j`.

Distinguish the cases in `hj : j = j₀`. Substitute `hj` using the available equality. Rewrite `hs` using `[← Finset.add_sum_erase _ _ (Finset.mem_univ j), ← Finset.add_sum_erase _ 𝔟 (Finset.mem_univ j), Finset.sum_congr rfl fun k hk => h k (by simp) (Finset.ne_of_mem_erase hk)]`. Conclude with `add_right_cancel hs`. Conclude with `h j (by simp) hj`.

Rewrite using `[this]`. Conclude with `Rel.refl 𝔟`. Consider the case `insert i S hi ih`. Introduce `𝔞 𝔟 h hs`. Distinguish the cases in `hi₀ : i = j₀`.

Conclude with `ih 𝔞 𝔟 (fun j hj hj' => h j (by simp [hj, hi₀, hj']) hj') hs`. Establish `h1` using `rel_move (K := K) hi₀ 𝔞 (𝔟 i - 𝔞 i)`. Establish `h2` using `ih (𝔞 + Pi.single i (𝔟 i - 𝔞 i) - Pi.single j₀ (𝔟 i - 𝔞 i)) 𝔟 (fun j hj hj' => by`. Distinguish the cases in `hji : j = i`. Substitute `hji` using the available equality.

Simplify using `[hj']`. Simplify `h j (by simp [hj, hji]) hj') (by` using `[hji, hj']`. Simplify using `[Finset.sum_add_distrib, Finset.sum_sub_distrib, hs])`. Simplify using `using h1.trans h2`.
-/
theorem rel_of_sum_eq (j₀ : J) (S : Finset J) : ∀ 𝔞 𝔟 : J → HeightOneSpectrum R →₀ ℤ,
    (∀ j, j ∉ S → j ≠ j₀ → 𝔞 j = 𝔟 j) → ∑ j, 𝔞 j = ∑ j, 𝔟 j → Rel 𝔞 𝔟 (1 : K) := by
  induction S using Finset.induction_on with
  | empty =>
    intro 𝔞 𝔟 h hs
    have : 𝔞 = 𝔟 := by
      funext j
      by_cases hj : j = j₀
      · subst hj
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j), ← Finset.add_sum_erase _ 𝔟 (Finset.mem_univ j),
          Finset.sum_congr rfl fun k hk => h k (by simp) (Finset.ne_of_mem_erase hk)] at hs
        exact add_right_cancel hs
      · exact h j (by simp) hj
    rw [this]
    exact Rel.refl 𝔟
  | insert i S hi ih =>
    intro 𝔞 𝔟 h hs
    by_cases hi₀ : i = j₀
    · exact ih 𝔞 𝔟 (fun j hj hj' => h j (by simp [hj, hi₀, hj']) hj') hs
    have h1 := rel_move (K := K) hi₀ 𝔞 (𝔟 i - 𝔞 i)
    have h2 := ih (𝔞 + Pi.single i (𝔟 i - 𝔞 i) - Pi.single j₀ (𝔟 i - 𝔞 i)) 𝔟 (fun j hj hj' => by
      by_cases hji : j = i
      · subst hji; simp [hj']
      · simpa [hji, hj'] using h j (by simp [hj, hji]) hj') (by
      simp [Finset.sum_add_distrib, Finset.sum_sub_distrib, hs])
    simpa using h1.trans h2

/- English proof (translation)
Use `⟨diagonal (Pi.mulSingle j₀ β), by simp [det_diagonal, Finset.prod_pi_mulSingle'], fun x => ?_⟩` and prove the remaining obligations. Use `forall_congr' fun j => forall_congr' fun P => ?_` and prove the remaining obligations. Distinguish the cases in `hj : j = j₀`. Substitute `hj` using the available equality. Rewrite using `[mulVec_diagonal, Pi.mulSingle_eq_same, map_mul, hβ, Pi.add_apply, Pi.single_eq_same, Finsupp.add_apply, neg_add, WithZero.exp_add, mul_comm, mul_le_mul_iff_left₀ WithZero.exp_pos]`.

Simplify using `[mulVec_diagonal, hj]`.
-/
theorem rel_scale (j₀ : J) (𝔞 : J → HeightOneSpectrum R →₀ ℤ) (d : HeightOneSpectrum R →₀ ℤ) (β : K)
    (hβ : ∀ P : HeightOneSpectrum R, P.valuation K β = WithZero.exp (-d P)) :
    Rel 𝔞 (𝔞 + Pi.single j₀ d) β := by
  refine ⟨diagonal (Pi.mulSingle j₀ β), by simp [det_diagonal, Finset.prod_pi_mulSingle'], fun x => ?_⟩
  refine forall_congr' fun j => forall_congr' fun P => ?_
  by_cases hj : j = j₀
  · subst hj
    rw [mulVec_diagonal, Pi.mulSingle_eq_same, map_mul, hβ, Pi.add_apply, Pi.single_eq_same, Finsupp.add_apply,
      neg_add, WithZero.exp_add, mul_comm, mul_le_mul_iff_left₀ WithZero.exp_pos]
  · simp [mulVec_diagonal, hj]

open UpperTheory.V.ZK in
/- English proof (translation)
Introduce `F _ _ J _ 𝔞 𝔟 β hJ hβ`. Establish `key : Rel (R` using `𝓞 F) (K := F) 𝔞 𝔟 (β : F) := by`. Break down `isEmpty_or_nonempty J with hE | ⟨⟨j₀⟩⟩` into its components or cases. Establish `h1 : β = 1` using `hJ.resolve_left (not_nonempty_iff.mpr hE)`. Rewrite using `[h1, Units.val_one, Subsingleton.elim 𝔞 𝔟]`.

Conclude with `@Rel.refl _ _ _ _ _ _ _ _ _ (_) 𝔟`. Establish `h1` using `rel_scale (K := F) j₀ 𝔞 (∑ j, (𝔟 j - 𝔞 j)) β fun P => by`. Establish `h0 : P.valuation F (β : F) ≠ 0` using `(Valuation.ne_zero_iff _).mpr β.ne_zero`. Establish `h2 : (∑ j, (𝔟 j - 𝔞 j)) P = ordP P β`. Rewrite using `[hβ, Finsupp.finsetSum_apply]`.

Both sides reduce to the same expression. Rewrite using `[h2, ordP, neg_neg, WithZero.exp_log h0]`. Establish `h2` using `rel_of_sum_eq (K := F) j₀ Finset.univ (𝔞 + Pi.single j₀ (∑ j, (𝔟 j - 𝔞 j))) 𝔟 (by simp) (by simp [Finset.sum_add_distrib, Finset.sum_sub_distrib])`. Simplify using `using h1.trans h2`. Take `⟨M, hM, h⟩` from `key`.

Establish `hU : IsUnit M.det` using `hM ▸ β.isUnit`. Use `⟨Matrix.toLinearEquiv (Pi.basisFun F J) M hU, ?_, fun x => ?_⟩` and prove the remaining obligations. Use `ext`. Rewrite using `[LinearEquiv.coe_det, ← hM, ← LinearMap.det_toLin (Pi.basisFun F J) M]`. Use `congr 1`.

Establish `: Matrix.toLinearEquiv (Pi.basisFun F J) M hU x = M *ᵥ x`. Rewrite using `[Matrix.toLinearEquiv_apply, Matrix.toLin_eq_toLin', Matrix.toLin'_apply]`. Rewrite using `[this]`. Conclude with `h x`.
-/
theorem SStein_of : UpperTheory.V.ZK.SStein := by
  intro F _ _ J _ 𝔞 𝔟 β hJ hβ
  classical
  have key : Rel (R := 𝓞 F) (K := F) 𝔞 𝔟 (β : F) := by
    rcases isEmpty_or_nonempty J with hE | ⟨⟨j₀⟩⟩
    · have h1 : β = 1 := hJ.resolve_left (not_nonempty_iff.mpr hE)
      rw [h1, Units.val_one, Subsingleton.elim 𝔞 𝔟]
      exact @Rel.refl _ _ _ _ _ _ _ _ _ (_) 𝔟
    · have h1 := rel_scale (K := F) j₀ 𝔞 (∑ j, (𝔟 j - 𝔞 j)) β fun P => by
        have h0 : P.valuation F (β : F) ≠ 0 := (Valuation.ne_zero_iff _).mpr β.ne_zero
        have h2 : (∑ j, (𝔟 j - 𝔞 j)) P = ordP P β := by
          rw [hβ, Finsupp.finsetSum_apply]; rfl
        rw [h2, ordP, neg_neg, WithZero.exp_log h0]
      have h2 := rel_of_sum_eq (K := F) j₀ Finset.univ (𝔞 + Pi.single j₀ (∑ j, (𝔟 j - 𝔞 j))) 𝔟 (by simp)
        (by simp [Finset.sum_add_distrib, Finset.sum_sub_distrib])
      simpa using h1.trans h2
  obtain ⟨M, hM, h⟩ := key
  have hU : IsUnit M.det := hM ▸ β.isUnit
  refine ⟨Matrix.toLinearEquiv (Pi.basisFun F J) M hU, ?_, fun x => ?_⟩
  · ext
    rw [LinearEquiv.coe_det, ← hM, ← LinearMap.det_toLin (Pi.basisFun F J) M]
    congr 1
  · have : Matrix.toLinearEquiv (Pi.basisFun F J) M hU x = M *ᵥ x := by
      rw [Matrix.toLinearEquiv_apply, Matrix.toLin_eq_toLin', Matrix.toLin'_apply]
    rw [this]
    exact h x

end LateralTheory.Q.SSteinT
