import Mathlib

noncomputable section

namespace ReciprocityTheory.Aut

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

section Gen

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K] (v : HeightOneSpectrum R)

/- English proof (translation)
The claim follows from `valuedAdicCompletion_eq_valuation' v k`.
-/
theorem adic_valued_algebraMap (k : K) :
    Valued.v (algebraMap K (v.adicCompletion K) k) = v.valuation K k :=
  valuedAdicCompletion_eq_valuation' v k

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem adic_algebraMap_R (a : R) :
    algebraMap R (v.adicCompletion K) a = algebraMap K (v.adicCompletion K) (algebraMap R K a) := rfl

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨k, hk⟩ : ∃ k : K, Valued.v (y - algebraMap K (v.adicCompletion K) k) < 1 := by`. Establish `hn : {w : v.adicCompletion K | Valued.v (w - y) < 1} ∈ nhds y` using `Valued.mem_nhds.mpr ⟨1, fun w hw => by simpa using hw⟩`. Take `⟨w, hw, k, rfl⟩` from `mem_closure_iff_nhds.mp (denseRange_algebraMap K v y) _ hn`. Use `⟨k, ?_⟩` and prove the remaining obligations. Rewrite using `[← Valuation.map_neg, neg_sub]`.

Conclude with `hw`. Establish `hk1 : v.valuation K k ≤ 1`. Rewrite using `[← adic_valued_algebraMap]`. Establish `e : algebraMap K (v.adicCompletion K) k = y - (y - algebraMap K _ k)` using `by ring`. Rewrite using `[e]`.

Conclude with `le_trans (Valuation.map_sub _ _ _) (max_le hy hk.le)`. Choose the witnesses or unpack the hypotheses as in `⟨c, hc⟩ : ∃ c : R, v.valuation K (k - algebraMap R K c) < 1 := by`. Take `⟨a, b, hb, rfl⟩` from `IsFractionRing.div_surjective (A := R) k`. Establish `hb0 : algebraMap R K b ≠ 0` using `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb`. Use `haveI := v.isPrime`.

Establish `hex : ∃ N, b ∉ v.asIdeal ^ N`. Assume the negation of the conclusion as `hall`. Use `push_neg at hall`. Establish `hmem : b ∈ ⨅ i, v.asIdeal ^ i` using `Submodule.mem_iInf _ |>.mpr hall`. Rewrite `hmem` using `[Ideal.iInf_pow_eq_bot_of_isDomain _ v.isPrime.ne_top, Ideal.mem_bot]`.

Conclude with `hb0 (by rw [hmem, map_zero])`. Establish `hspec` using `Nat.find_spec hex`. Establish `hmin : ∀ m < Nat.find hex, b ∈ v.asIdeal ^ m` using `fun m hm => by`. Assume the negation of the conclusion as `h'`. Conclude with `Nat.find_min hex hm h'`.

Take `⟨n, hn⟩ : ∃ n, Nat.find hex = n + 1` from `Nat.exists_eq_succ_of_ne_zero (by`. Introduce `h0`. Rewrite `hspec` using `[h0, pow_zero]`. Conclude with `hspec (by simp))`. Rewrite `hspec` using `[hn]`.

Establish `hbn : b ∈ v.asIdeal ^ n` using `hmin n (by omega)`. Establish `hvb : 0 < v.valuation K (algebraMap R K b)` using `zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hb0)`. Establish `hk1'` using `hk1`. Rewrite `hk1'` using `[map_div₀, div_le_one₀ hvb, valuation_of_algebraMap, valuation_of_algebraMap]`. Establish `ha : a ∈ v.asIdeal ^ n`.

Rewrite using `[← intValuation_le_pow_iff_mem]`. Conclude with `hk1'.trans ((intValuation_le_pow_iff_mem v b n).mpr hbn)`. Establish `hI : Ideal.span {b} ⊔ v.asIdeal ^ (n + 1) = v.asIdeal ^ n`. Apply `Ideal.eq_prime_pow_of_succ_lt_of_le v.ne_bot` to reduce the goal to its premises. Use `lt_of_le_of_ne le_sup_right ?_` and prove the remaining obligations.

Introduce `heq`. Apply `hspec` to reduce the goal to its premises. Rewrite using `[heq]`. Conclude with `Ideal.mem_sup_left (Ideal.mem_span_singleton_self b)`. Conclude with `sup_le ((Ideal.span_singleton_le_iff_mem _).mpr hbn) (Ideal.pow_le_pow_right (Nat.le_succ n))`.

Rewrite `ha` using `[← hI]`. Take `⟨y1, hy1, z, hz, hyz⟩` from `Submodule.mem_sup.mp ha`. Take `⟨r, rfl⟩` from `Ideal.mem_span_singleton'.mp hy1`. Use `⟨r, ?_⟩` and prove the remaining obligations. Establish `hkz : algebraMap R K a / algebraMap R K b - algebraMap R K r = algebraMap R K z / algebraMap R K b`.

Rewrite using `[← hyz, map_add, map_mul]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hkz, map_div₀, div_lt_one₀ hvb, valuation_of_algebraMap, valuation_of_algebraMap]`. Establish `h1` using `(intValuation_le_pow_iff_mem v z (n + 1)).mpr hz`.

Establish `h2 : ¬ v.intValuation b ≤ WithZero.exp (-((n + 1 : ℕ) : ℤ))` using `fun h => hspec ((intValuation_le_pow_iff_mem v b (n + 1)).mp h)`. Conclude with `lt_of_le_of_lt h1 (not_le.mp h2)`. Use `⟨c, ?_⟩` and prove the remaining obligations. Establish `e : y - algebraMap R (v.adicCompletion K) c = (y - algebraMap K _ k) + algebraMap K _ (k - algebraMap R K c)`. Rewrite using `[adic_algebraMap_R, map_sub]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Use `lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt hk ?_)` and prove the remaining obligations. Rewrite using `[adic_valued_algebraMap]`. Conclude with `hc`.
-/
theorem adic_exists_approx (y : v.adicCompletion K) (hy : Valued.v y ≤ 1) :
    ∃ a : R, Valued.v (y - algebraMap R (v.adicCompletion K) a) < 1 := by
  classical
  obtain ⟨k, hk⟩ : ∃ k : K, Valued.v (y - algebraMap K (v.adicCompletion K) k) < 1 := by
    have hn : {w : v.adicCompletion K | Valued.v (w - y) < 1} ∈ nhds y :=
      Valued.mem_nhds.mpr ⟨1, fun w hw => by simpa using hw⟩
    obtain ⟨w, hw, k, rfl⟩ := mem_closure_iff_nhds.mp (denseRange_algebraMap K v y) _ hn
    refine ⟨k, ?_⟩
    rw [← Valuation.map_neg, neg_sub]
    exact hw
  have hk1 : v.valuation K k ≤ 1 := by
    rw [← adic_valued_algebraMap]
    have e : algebraMap K (v.adicCompletion K) k = y - (y - algebraMap K _ k) := by ring
    rw [e]
    exact le_trans (Valuation.map_sub _ _ _) (max_le hy hk.le)
  obtain ⟨c, hc⟩ : ∃ c : R, v.valuation K (k - algebraMap R K c) < 1 := by
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) k
    have hb0 : algebraMap R K b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    haveI := v.isPrime
    have hex : ∃ N, b ∉ v.asIdeal ^ N := by
      by_contra hall
      push_neg at hall
      have hmem : b ∈ ⨅ i, v.asIdeal ^ i := Submodule.mem_iInf _ |>.mpr hall
      rw [Ideal.iInf_pow_eq_bot_of_isDomain _ v.isPrime.ne_top, Ideal.mem_bot] at hmem
      exact hb0 (by rw [hmem, map_zero])
    have hspec := Nat.find_spec hex
    have hmin : ∀ m < Nat.find hex, b ∈ v.asIdeal ^ m := fun m hm => by
      by_contra h'
      exact Nat.find_min hex hm h'
    obtain ⟨n, hn⟩ : ∃ n, Nat.find hex = n + 1 := Nat.exists_eq_succ_of_ne_zero (by
      intro h0
      rw [h0, pow_zero] at hspec
      exact hspec (by simp))
    rw [hn] at hspec
    have hbn : b ∈ v.asIdeal ^ n := hmin n (by omega)
    have hvb : 0 < v.valuation K (algebraMap R K b) := zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hb0)
    have hk1' := hk1
    rw [map_div₀, div_le_one₀ hvb, valuation_of_algebraMap, valuation_of_algebraMap] at hk1'
    have ha : a ∈ v.asIdeal ^ n := by
      rw [← intValuation_le_pow_iff_mem]
      exact hk1'.trans ((intValuation_le_pow_iff_mem v b n).mpr hbn)
    have hI : Ideal.span {b} ⊔ v.asIdeal ^ (n + 1) = v.asIdeal ^ n := by
      apply Ideal.eq_prime_pow_of_succ_lt_of_le v.ne_bot
      · refine lt_of_le_of_ne le_sup_right ?_
        intro heq
        apply hspec
        rw [heq]
        exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self b)
      · exact sup_le ((Ideal.span_singleton_le_iff_mem _).mpr hbn)
          (Ideal.pow_le_pow_right (Nat.le_succ n))
    rw [← hI] at ha
    obtain ⟨y1, hy1, z, hz, hyz⟩ := Submodule.mem_sup.mp ha
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hy1
    refine ⟨r, ?_⟩
    have hkz : algebraMap R K a / algebraMap R K b - algebraMap R K r =
        algebraMap R K z / algebraMap R K b := by
      rw [← hyz, map_add, map_mul]
      field_simp
      ring
    rw [hkz, map_div₀, div_lt_one₀ hvb, valuation_of_algebraMap, valuation_of_algebraMap]
    have h1 := (intValuation_le_pow_iff_mem v z (n + 1)).mpr hz
    have h2 : ¬ v.intValuation b ≤ WithZero.exp (-((n + 1 : ℕ) : ℤ)) := fun h =>
      hspec ((intValuation_le_pow_iff_mem v b (n + 1)).mp h)
    exact lt_of_le_of_lt h1 (not_le.mp h2)
  refine ⟨c, ?_⟩
  have e : y - algebraMap R (v.adicCompletion K) c =
      (y - algebraMap K _ k) + algebraMap K _ (k - algebraMap R K c) := by
    rw [adic_algebraMap_R, map_sub]
    ring
  rw [e]
  refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt hk ?_)
  rw [adic_valued_algebraMap]
  exact hc

/- English proof (translation)
Establish `hint : IsIntegral (Valued.v : Valuation (v.adicCompletion K) _).integer x`. Use `⟨p.map (Int.castRingHom _), hm.map _, ?_⟩` and prove the remaining obligations. Rewrite using `[Polynomial.eval₂_map, RingHom.ext_int (RingHom.comp _ _) (Int.castRingHom _)]`. Conclude with `hp`. Establish `hmem` using `(Valuation.integer.integers _).mem_of_integral hint`.

Conclude with `hmem`.
-/
theorem adic_le_one_of_poly {x : v.adicCompletion K} (p : Polynomial ℤ) (hm : p.Monic)
    (hp : p.eval₂ (Int.castRingHom _) x = 0) : Valued.v x ≤ 1 := by
  have hint : IsIntegral (Valued.v : Valuation (v.adicCompletion K) _).integer x := by
    refine ⟨p.map (Int.castRingHom _), hm.map _, ?_⟩
    rw [Polynomial.eval₂_map, RingHom.ext_int (RingHom.comp _ _) (Int.castRingHom _)]
    exact hp
  have hmem := (Valuation.integer.integers _).mem_of_integral hint
  exact hmem

end Gen

end ReciprocityTheory.Aut
