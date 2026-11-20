import Mathlib

namespace UpperTheory.Reformulated.B.SquareOfApproximation

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero Filter Topology in
/- English proof (translation)
Establish `hg : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0` using `MonoidWithZeroHom.ValueGroup₀.embedding_unit_ne_zero γ`. Take `⟨k, hk⟩ : ∃ k : ℤ, MonoidWithZeroHom.ValueGroup₀.embedding γ.1 = exp k` from `⟨log _, (exp_log hg).symm⟩`. Use `⟨(-k + 1).toNat, fun x hx => ?_⟩` and prove the remaining obligations. Rewrite using `[Valuation.restrict_lt_iff_lt_embedding, hk]`. Use `lt_of_le_of_lt hx ?_` and prove the remaining obligations.

Rewrite using `[exp_lt_exp]`. Use `Int.self_le_toNat (-k + 1)` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
private lemma small_power_bound {A : Type*} [Ring A] [_i : Valued A (WithZero (Multiplicative ℤ))]
    (γ : (MonoidWithZeroHom.ValueGroup₀ (.ofClass _i.v))ˣ) :
    ∃ N : ℕ, ∀ x : A, Valued.v x ≤ exp (-(N : ℤ)) → _i.v.restrict x < γ.1 := by
  have hg : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0 :=
    MonoidWithZeroHom.ValueGroup₀.embedding_unit_ne_zero γ
  obtain ⟨k, hk⟩ : ∃ k : ℤ, MonoidWithZeroHom.ValueGroup₀.embedding γ.1 = exp k :=
    ⟨log _, (exp_log hg).symm⟩
  refine ⟨(-k + 1).toNat, fun x hx => ?_⟩
  rw [Valuation.restrict_lt_iff_lt_embedding, hk]
  refine lt_of_le_of_lt hx ?_
  rw [exp_lt_exp]
  have := Int.self_le_toNat (-k + 1)
  omega

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero Filter Topology in
/- English proof (translation)
Use `set f : ℕ → v.adicCompletion K := fun m => algebraMap K (v.adicCompletion K) (algebraMap R K (b m)) with hf`. Use `set D := algebraMap K (v.adicCompletion K) (algebraMap R K d) with hD`. Establish `hval : ∀ (r : R) (m : ℕ), r ∈ v.asIdeal ^ m → Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K r)) ≤ exp (-(m : ℤ))`. Introduce `r m hr`. Establish `h1 : Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K r)) = v.valuation K (algebraMap R K r)` using `valuedAdicCompletion_eq_valuation' v _`.

Rewrite using `[h1, valuation_of_algebraMap]`. Conclude with `(intValuation_le_pow_iff_mem v r m).2 hr`. Establish `hcau : CauchySeq f`. Rewrite using `[CauchySeq, Valued.cauchy_iff]`. Use `⟨inferInstance, fun γ => ?_⟩` and prove the remaining obligations.

Take `⟨N, hN⟩` from `small_power_bound γ`. Use `⟨f '' Set.Ici N, Filter.image_mem_map (Filter.mem_atTop N), ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨m, hm, rfl⟩ _ ⟨k, hk, rfl⟩`. Apply `hN` to reduce the goal to its premises. Establish `hm' : N ≤ m` using `hm`.

Establish `hk' : N ≤ k` using `hk`. Establish `: b k - b m ∈ v.asIdeal ^ N`. Break down `le_total m k with h | h` into its components or cases. Conclude with `Ideal.pow_le_pow_right hm' (hb m k h)`. Use `Ideal.pow_le_pow_right hk' (hb k m h)` as an intermediate fact.

Rewrite using `[← neg_sub]`. Conclude with `neg_mem this`. Establish `h2` using `hval _ _ this`. Simplify `h2` using `[hf, map_sub]`. Take `⟨L, hL⟩` from `cauchySeq_tendsto_of_complete hcau`.

Establish `h0 : Tendsto (fun m => f m * f m - D) atTop (𝓝 0)`. Rewrite using `[(Valued.hasBasis_nhds_zero _ _).tendsto_right_iff]`. Introduce `γ _`. Take `⟨N, hN⟩` from `small_power_bound γ`. Use `filter_upwards [Filter.eventually_ge_atTop N] with m hm`.

Apply `hN` to reduce the goal to its premises. Use `hval _ _ (Ideal.pow_le_pow_right hm (hd m))` as an intermediate fact. Simplify `this` using `[hf, hD, map_sub, map_mul]`. Establish `h1 : Tendsto (fun m => f m * f m - D) atTop (𝓝 (L * L - D))` using `(hL.mul hL).sub_const D`. Establish `h2 : L * L - D = 0` using `tendsto_nhds_unique h1 h0`.

Conclude with `⟨L, (sub_eq_zero.1 h2).symm⟩`.
-/
private lemma square_of_approx {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] (v : HeightOneSpectrum R) (b : ℕ → R) (d : R)
    (hb : ∀ m k, m ≤ k → b k - b m ∈ v.asIdeal ^ m)
    (hd : ∀ m, b m * b m - d ∈ v.asIdeal ^ m) :
    IsSquare (algebraMap K (v.adicCompletion K) (algebraMap R K d)) := by
  set f : ℕ → v.adicCompletion K := fun m => algebraMap K (v.adicCompletion K) (algebraMap R K (b m))
    with hf
  set D := algebraMap K (v.adicCompletion K) (algebraMap R K d) with hD
  have hval : ∀ (r : R) (m : ℕ), r ∈ v.asIdeal ^ m →
      Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K r)) ≤ exp (-(m : ℤ)) := by
    intro r m hr
    have h1 : Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K r)) =
        v.valuation K (algebraMap R K r) := valuedAdicCompletion_eq_valuation' v _
    rw [h1, valuation_of_algebraMap]
    exact (intValuation_le_pow_iff_mem v r m).2 hr
  have hcau : CauchySeq f := by
    rw [CauchySeq, Valued.cauchy_iff]
    refine ⟨inferInstance, fun γ => ?_⟩
    obtain ⟨N, hN⟩ := small_power_bound γ
    refine ⟨f '' Set.Ici N, Filter.image_mem_map (Filter.mem_atTop N), ?_⟩
    rintro _ ⟨m, hm, rfl⟩ _ ⟨k, hk, rfl⟩
    apply hN
    have hm' : N ≤ m := hm
    have hk' : N ≤ k := hk
    have : b k - b m ∈ v.asIdeal ^ N := by
      rcases le_total m k with h | h
      · exact Ideal.pow_le_pow_right hm' (hb m k h)
      · have := Ideal.pow_le_pow_right hk' (hb k m h)
        rw [← neg_sub]; exact neg_mem this
    have h2 := hval _ _ this
    simpa [hf, map_sub] using h2
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcau
  have h0 : Tendsto (fun m => f m * f m - D) atTop (𝓝 0) := by
    rw [(Valued.hasBasis_nhds_zero _ _).tendsto_right_iff]
    intro γ _
    obtain ⟨N, hN⟩ := small_power_bound γ
    filter_upwards [Filter.eventually_ge_atTop N] with m hm
    apply hN
    have := hval _ _ (Ideal.pow_le_pow_right hm (hd m))
    simpa [hf, hD, map_sub, map_mul] using this
  have h1 : Tendsto (fun m => f m * f m - D) atTop (𝓝 (L * L - D)) :=
    (hL.mul hL).sub_const D
  have h2 : L * L - D = 0 := tendsto_nhds_unique h1 h0
  exact ⟨L, (sub_eq_zero.1 h2).symm⟩

/- English proof (translation)
Establish `hsurj : Function.Surjective σ` using `fun x => ⟨σ x, hσ x⟩`. Establish `hP'max : (P.comap σ).IsMaximal` using `Ideal.comap_isMaximal_of_surjective σ hsurj`. Establish `hne' : P ≠ P.comap σ`. Introduce `h`. Choose the witnesses or unpack the hypotheses as in `⟨x, hxQ, hxP⟩ : ∃ x ∈ Q, x ∉ P := by`.

Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Conclude with `hne ((hQ.eq_of_le hP.ne_top hcon).symm)`. Take `⟨r, hr⟩` from `hnm x`. Establish `h1 : r ∈ Q.comap (algebraMap R S)`.

Rewrite using `[Ideal.mem_comap, hr]`. Conclude with `Q.mul_mem_right _ hxQ`. Rewrite `h1` using `[← hc, Ideal.mem_comap, hr]`. Break down `hP.isPrime.mem_or_mem h1 with h2 | h2` into its components or cases. Conclude with `hxP h2`.

Apply `hxP` to reduce the goal to its premises. Rewrite using `[h]`. Conclude with `h2`. Establish `hcop : IsCoprime (P ^ n) ((P.comap σ) ^ n)` using `IsCoprime.pow ((Ideal.isCoprime_iff_sup_eq).2 (Ideal.IsMaximal.coprime_of_ne hP hP'max hne'))`. Take `⟨p, hp, q, hq, hpq⟩` from `Ideal.isCoprime_iff_exists.1 hcop`.

Take `⟨a, ha⟩` from `htr (t * q)`. Use `⟨a, ?_⟩` and prove the remaining obligations. Establish `hsq : σ q ∈ P ^ n`. Establish `h1 : σ q ∈ ((P.comap σ) ^ n).map σ` using `Ideal.mem_map_of_mem σ hq`. Rewrite `h1` using `[Ideal.map_pow]`.

Conclude with `Ideal.pow_right_mono (Ideal.map_comap_le) n h1`. Rewrite using `[ha, map_mul]`. Establish `h3 : t - (t * q + σ t * σ q) = t * p - σ t * σ q`. Establish `: q = 1 - p` using `by rw [← hpq]; ring`. Rewrite using `[this]`.

Simplify using `only [map_sub, map_one]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h3]`. Conclude with `sub_mem (Ideal.mul_mem_left _ _ hp) (Ideal.mul_mem_left _ _ hsq)`.
-/
private lemma approx {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (σ : S →+* S)
    (hσ : ∀ x, σ (σ x) = x)
    (htr : ∀ y, ∃ r : R, algebraMap R S r = y + σ y)
    (hnm : ∀ y, ∃ r : R, algebraMap R S r = y * σ y)
    (P Q : Ideal S) [hP : P.IsMaximal] [hQ : Q.IsMaximal] (hne : P ≠ Q)
    (hc : P.comap (algebraMap R S) = Q.comap (algebraMap R S)) (t : S) (n : ℕ) :
    ∃ a : R, t - algebraMap R S a ∈ P ^ n := by
  have hsurj : Function.Surjective σ := fun x => ⟨σ x, hσ x⟩
  have hP'max : (P.comap σ).IsMaximal := Ideal.comap_isMaximal_of_surjective σ hsurj
  have hne' : P ≠ P.comap σ := by
    intro h
    obtain ⟨x, hxQ, hxP⟩ : ∃ x ∈ Q, x ∉ P := by
      by_contra hcon
      push Not at hcon
      exact hne ((hQ.eq_of_le hP.ne_top hcon).symm)
    obtain ⟨r, hr⟩ := hnm x
    have h1 : r ∈ Q.comap (algebraMap R S) := by
      rw [Ideal.mem_comap, hr]; exact Q.mul_mem_right _ hxQ
    rw [← hc, Ideal.mem_comap, hr] at h1
    rcases hP.isPrime.mem_or_mem h1 with h2 | h2
    · exact hxP h2
    · apply hxP; rw [h]; exact h2
  have hcop : IsCoprime (P ^ n) ((P.comap σ) ^ n) :=
    IsCoprime.pow ((Ideal.isCoprime_iff_sup_eq).2 (Ideal.IsMaximal.coprime_of_ne hP hP'max hne'))
  obtain ⟨p, hp, q, hq, hpq⟩ := Ideal.isCoprime_iff_exists.1 hcop
  obtain ⟨a, ha⟩ := htr (t * q)
  refine ⟨a, ?_⟩
  have hsq : σ q ∈ P ^ n := by
    have h1 : σ q ∈ ((P.comap σ) ^ n).map σ := Ideal.mem_map_of_mem σ hq
    rw [Ideal.map_pow] at h1
    exact Ideal.pow_right_mono (Ideal.map_comap_le) n h1
  rw [ha, map_mul]
  have h3 : t - (t * q + σ t * σ q) = t * p - σ t * σ q := by
    have : q = 1 - p := by rw [← hpq]; ring
    rw [this]; simp only [map_sub, map_one]; ring
  rw [h3]
  exact sub_mem (Ideal.mul_mem_left _ _ hp) (Ideal.mul_mem_left _ _ hsq)

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero in
/- English proof (translation)
Establish `hsp' : ∀ x : E, ∃ u w : F, x = algebraMap F E u + algebraMap F E w * θ`. Introduce `x`. Take `⟨u, w, h⟩` from `hsp x`. Conclude with `⟨u, w, by rw [h, Algebra.smul_def, Algebra.smul_def, mul_one]⟩`. Establish `hθ0 : θ ≠ 0`.

Introduce and unpack `rfl`. Apply `hd` to reduce the goal to its premises. Establish `h0 : algebraMap F E d = 0` using `by rw [← hθ]; simp`. Conclude with `(map_eq_zero (algebraMap F E)).1 h0`. Establish `hσσ : ∀ x, σ (σ x) = x`.

Introduce `x`. Take `⟨u, w, rfl⟩` from `hsp' x`. Simplify using `only [map_add, map_mul, AlgHom.commutes, hσ, map_neg, mul_neg, neg_neg]`. Establish `hfix : ∀ x, σ x = x → ∃ u : F, x = algebraMap F E u`. Introduce `x hx`.

Take `⟨u, w, rfl⟩` from `hsp' x`. Simplify using `only [map_add, map_mul, AlgHom.commutes, hσ, mul_neg] at hx`. Establish `h2 : (2 : E) * (algebraMap F E w * θ) = 0`. Establish `h3` using `add_left_cancel hx`. Take the linear combination `-h3`.

Establish `hw : w = 0`. Break down `mul_eq_zero.1 h2 with h | h` into its components or cases. Conclude with `absurd h two_ne_zero`. Break down `mul_eq_zero.1 h with h | h` into its components or cases. Conclude with `(map_eq_zero (algebraMap F E)).1 h`.

Conclude with `absurd h hθ0`. Conclude with `⟨u, by simp [hw]⟩`. Set `s : 𝓞 E →+* 𝓞 E` to `RingOfIntegers.mapRingHom (σ : E →+* E)`. Establish `hs : ∀ y : 𝓞 E, ((s y : 𝓞 E) : E) = σ y` using `fun y => rfl`. Establish `hss : ∀ y, s (s y) = y`.

Introduce `y`. Apply `RingOfIntegers.ext` to reduce the goal to its premises. Rewrite using `[hs, hs, hσσ]`. Establish `hfixO : ∀ y : 𝓞 E, s y = y → ∃ r : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) r = y`. Introduce `y hy`.

Take `⟨u, hu⟩` from `hfix (y : E) (by rw [← hs, hy])`. Establish `hint : IsIntegral ℤ u`. Establish `h1 : IsIntegral ℤ (algebraMap F E u)` using `hu ▸ RingOfIntegers.isIntegral_coe y`. Conclude with `(isIntegral_algebraMap_iff (algebraMap F E).injective).1 h1`. Use `⟨⟨u, hint⟩, ?_⟩` and prove the remaining obligations.

Apply `RingOfIntegers.ext` to reduce the goal to its premises. Conclude with `hu.symm`. Establish `htr : ∀ y, ∃ r : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) r = y + s y` using `fun y => hfixO _ (by rw [map_add, hss, add_comm])`. Establish `hnm : ∀ y, ∃ r : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) r = y * s y` using `fun y => hfixO _ (by rw [map_mul, hss, mul_comm])`. Establish `hint : IsIntegral ℤ θ`.

Establish `h1 : IsIntegral ℤ (θ ^ 2)`. Rewrite using `[pow_two, hθ]`. Conclude with `(RingOfIntegers.isIntegral_coe d).algebraMap`. Conclude with `h1.of_pow (by norm_num)`. Set `t : 𝓞 E` to `⟨θ, hint⟩`.

Establish `ht : t * t = algebraMap (𝓞 F) (𝓞 E) d`. Apply `RingOfIntegers.ext` to reduce the goal to its premises. Conclude with `hθ`. Use `haveI := P.isMaximal`. Use `haveI := Q.isMaximal`.

Establish `hne' : P.asIdeal ≠ Q.asIdeal` using `fun h => hne (HeightOneSpectrum.ext h)`. Use `choose a ha using approx (R := 𝓞 F) s hss htr hnm P.asIdeal Q.asIdeal hne' (hP.trans hQ.symm) t`. Use `haveI : P.asIdeal.LiesOver v.asIdeal := ⟨hP.symm⟩`. Establish `he : v.asIdeal.ramificationIdx' P.asIdeal ≠ 0` using `Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver P.asIdeal v.ne_bot`. Use `set e := v.asIdeal.ramificationIdx' P.asIdeal with he'`.

Establish `hdown : ∀ (x : 𝓞 F) (m : ℕ), algebraMap (𝓞 F) (𝓞 E) x ∈ P.asIdeal ^ (e * m) → x ∈ v.asIdeal ^ m`. Introduce `x m hx`. Rewrite `hx`, the goal using `[← intValuation_le_pow_iff_mem]`. Rewrite `hx` using `[← intValuation_liesOver v P x]`. Establish `h1 : exp (-((e * m : ℕ) : ℤ)) = (exp (-(m : ℤ))) ^ e`.

Rewrite using `[← exp_nsmul]`. Use `congr 1`. Simplify using the standard rewrite rules. Rewrite `hx` using `[h1]`. Conclude with `(pow_le_pow_iff_left₀ zero_le' zero_le' he).1 hx`.

Establish `hb : ∀ m k, m ≤ k → a (e * k) - a (e * m) ∈ v.asIdeal ^ m`. Introduce `m k hmk`. Apply `hdown` to reduce the goal to its premises. Establish `h1` using `ha (e * m)`. Establish `h2` using `Ideal.pow_le_pow_right (Nat.mul_le_mul_left e hmk) (ha (e * k))`.

Establish `h3` using `sub_mem h1 h2`. Establish `h4 : t - algebraMap (𝓞 F) (𝓞 E) (a (e * m)) - (t - algebraMap (𝓞 F) (𝓞 E) (a (e * k))) = algebraMap (𝓞 F) (𝓞 E) (a (e * k) - a (e * m))`. Rewrite using `[map_sub]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `h3` using `[h4]`. Then use the resulting hypothesis.

Establish `hdd : ∀ m, a (e * m) * a (e * m) - d ∈ v.asIdeal ^ m`. Introduce `m`. Apply `hdown` to reduce the goal to its premises. Establish `h1` using `Ideal.mul_mem_left _ (-(t + algebraMap (𝓞 F) (𝓞 E) (a (e * m)))) (ha (e * m))`. Establish `h2 : -(t + algebraMap (𝓞 F) (𝓞 E) (a (e * m))) * (t - algebraMap (𝓞 F) (𝓞 E) (a (e * m))) = algebraMap (𝓞 F) (𝓞 E) (a (e * m) * a (e * m) - d)`.

Rewrite using `[map_sub, map_mul, ← ht]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `h1` using `[h2]`. Then use the resulting hypothesis. Conclude with `square_of_approx v (fun m => a (e * m)) d hb hdd`.
-/
private theorem core {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {θ : E} {d : 𝓞 F} (hd : (d : F) ≠ 0) (hσ : σ θ = -θ)
    (hθ : θ * θ = algebraMap F E d)
    (hsp : ∀ x : E, ∃ u w : F, x = u • (1 : E) + w • θ)
    {v : HeightOneSpectrum (𝓞 F)} (P Q : HeightOneSpectrum (𝓞 E)) (hne : P ≠ Q)
    (hP : P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) = v.asIdeal)
    (hQ : Q.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) = v.asIdeal) :
    IsSquare (algebraMap F (v.adicCompletion F) (d : F)) := by
  have hsp' : ∀ x : E, ∃ u w : F, x = algebraMap F E u + algebraMap F E w * θ := by
    intro x
    obtain ⟨u, w, h⟩ := hsp x
    exact ⟨u, w, by rw [h, Algebra.smul_def, Algebra.smul_def, mul_one]⟩
  have hθ0 : θ ≠ 0 := by
    rintro rfl
    apply hd
    have h0 : algebraMap F E d = 0 := by rw [← hθ]; simp
    exact (map_eq_zero (algebraMap F E)).1 h0
  have hσσ : ∀ x, σ (σ x) = x := by
    intro x
    obtain ⟨u, w, rfl⟩ := hsp' x
    simp only [map_add, map_mul, AlgHom.commutes, hσ, map_neg, mul_neg, neg_neg]
  have hfix : ∀ x, σ x = x → ∃ u : F, x = algebraMap F E u := by
    intro x hx
    obtain ⟨u, w, rfl⟩ := hsp' x
    simp only [map_add, map_mul, AlgHom.commutes, hσ, mul_neg] at hx
    have h2 : (2 : E) * (algebraMap F E w * θ) = 0 := by
      have h3 := add_left_cancel hx
      linear_combination -h3
    have hw : w = 0 := by
      rcases mul_eq_zero.1 h2 with h | h
      · exact absurd h two_ne_zero
      · rcases mul_eq_zero.1 h with h | h
        · exact (map_eq_zero (algebraMap F E)).1 h
        · exact absurd h hθ0
    exact ⟨u, by simp [hw]⟩
  let s : 𝓞 E →+* 𝓞 E := RingOfIntegers.mapRingHom (σ : E →+* E)
  have hs : ∀ y : 𝓞 E, ((s y : 𝓞 E) : E) = σ y := fun y => rfl
  have hss : ∀ y, s (s y) = y := by
    intro y
    apply RingOfIntegers.ext
    rw [hs, hs, hσσ]
  have hfixO : ∀ y : 𝓞 E, s y = y → ∃ r : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) r = y := by
    intro y hy
    obtain ⟨u, hu⟩ := hfix (y : E) (by rw [← hs, hy])
    have hint : IsIntegral ℤ u := by
      have h1 : IsIntegral ℤ (algebraMap F E u) := hu ▸ RingOfIntegers.isIntegral_coe y
      exact (isIntegral_algebraMap_iff (algebraMap F E).injective).1 h1
    refine ⟨⟨u, hint⟩, ?_⟩
    apply RingOfIntegers.ext
    exact hu.symm
  have htr : ∀ y, ∃ r : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) r = y + s y := fun y =>
    hfixO _ (by rw [map_add, hss, add_comm])
  have hnm : ∀ y, ∃ r : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) r = y * s y := fun y =>
    hfixO _ (by rw [map_mul, hss, mul_comm])
  have hint : IsIntegral ℤ θ := by
    have h1 : IsIntegral ℤ (θ ^ 2) := by
      rw [pow_two, hθ]
      exact (RingOfIntegers.isIntegral_coe d).algebraMap
    exact h1.of_pow (by norm_num)
  let t : 𝓞 E := ⟨θ, hint⟩
  have ht : t * t = algebraMap (𝓞 F) (𝓞 E) d := by
    apply RingOfIntegers.ext
    exact hθ
  haveI := P.isMaximal
  haveI := Q.isMaximal
  have hne' : P.asIdeal ≠ Q.asIdeal := fun h => hne (HeightOneSpectrum.ext h)
  choose a ha using
    approx (R := 𝓞 F) s hss htr hnm P.asIdeal Q.asIdeal hne' (hP.trans hQ.symm) t
  haveI : P.asIdeal.LiesOver v.asIdeal := ⟨hP.symm⟩
  have he : v.asIdeal.ramificationIdx' P.asIdeal ≠ 0 :=
    Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver P.asIdeal v.ne_bot
  set e := v.asIdeal.ramificationIdx' P.asIdeal with he'
  have hdown : ∀ (x : 𝓞 F) (m : ℕ), algebraMap (𝓞 F) (𝓞 E) x ∈ P.asIdeal ^ (e * m) →
      x ∈ v.asIdeal ^ m := by
    intro x m hx
    rw [← intValuation_le_pow_iff_mem] at hx ⊢
    rw [← intValuation_liesOver v P x] at hx
    have h1 : exp (-((e * m : ℕ) : ℤ)) = (exp (-(m : ℤ))) ^ e := by
      rw [← exp_nsmul]
      congr 1
      simp
    rw [h1] at hx
    exact (pow_le_pow_iff_left₀ zero_le' zero_le' he).1 hx
  have hb : ∀ m k, m ≤ k → a (e * k) - a (e * m) ∈ v.asIdeal ^ m := by
    intro m k hmk
    apply hdown
    have h1 := ha (e * m)
    have h2 := Ideal.pow_le_pow_right (Nat.mul_le_mul_left e hmk) (ha (e * k))
    have h3 := sub_mem h1 h2
    have h4 : t - algebraMap (𝓞 F) (𝓞 E) (a (e * m)) - (t - algebraMap (𝓞 F) (𝓞 E) (a (e * k))) =
        algebraMap (𝓞 F) (𝓞 E) (a (e * k) - a (e * m)) := by
      rw [map_sub]; ring
    rwa [h4] at h3
  have hdd : ∀ m, a (e * m) * a (e * m) - d ∈ v.asIdeal ^ m := by
    intro m
    apply hdown
    have h1 := Ideal.mul_mem_left _ (-(t + algebraMap (𝓞 F) (𝓞 E) (a (e * m)))) (ha (e * m))
    have h2 : -(t + algebraMap (𝓞 F) (𝓞 E) (a (e * m))) * (t - algebraMap (𝓞 F) (𝓞 E) (a (e * m))) =
        algebraMap (𝓞 F) (𝓞 E) (a (e * m) * a (e * m) - d) := by
      rw [map_sub, map_mul, ← ht]; ring
    rwa [h2] at h1
  exact square_of_approx v (fun m => a (e * m)) d hb hdd

end UpperTheory.Reformulated.B.SquareOfApproximation

noncomputable def UpperTheory.Reformulated.B.SquareOfApproximation.IsCMExt :
    (F E : Type) →
      [inst : Field F] →
        [@NumberField F inst] →
          [inst_2 : Field E] →
            [@NumberField E inst_2] →
              [inst_4 :
                  @Algebra F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))] →
                @AlgHom F E E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))) inst_4
                    inst_4 →
                  Prop :=
    fun (F E : Type) [inst : Field F] [@NumberField F inst] [inst_2 : Field E] [@NumberField E inst_2]
        [inst_4 :
          @Algebra F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
            (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))]
        (σ :
          @AlgHom F E E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
            (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
            (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))) inst_4
            inst_4) ↦
      And (@NumberField.IsTotallyReal F inst)
        (And (@NumberField.IsTotallyComplex E inst_2)
          (And
            (@Eq Nat
              (@Module.finrank F E
                (@DivisionSemiring.toSemiring F (@Semifield.toDivisionSemiring F (@Field.toSemifield F inst)))
                (@Semiring.toAddCommMonoid E
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))) inst_4))
              (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (∀
              (τ :
                @RingHom E Complex
                  (@Semiring.toNonAssocSemiring E
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                  (@Semiring.toNonAssocSemiring Complex Complex.instSemiring))
              (x : E),
              @Eq Complex
                (@DFunLike.coe
                  (@RingHom E Complex
                    (@Semiring.toNonAssocSemiring E
                      (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                    (@Semiring.toNonAssocSemiring Complex Complex.instSemiring))
                  E (fun (x : E) ↦ Complex)
                  (@RingHom.instFunLike E Complex
                    (@Semiring.toNonAssocSemiring E
                      (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                    (@Semiring.toNonAssocSemiring Complex Complex.instSemiring))
                  τ
                  (@DFunLike.coe
                    (@AlgHom F E E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                      (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                      inst_4 inst_4)
                    E (fun (x : E) ↦ E)
                    (@AlgHom.funLike F E E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                      (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                      inst_4 inst_4)
                    σ x))
                (@Star.star Complex
                  (@InvolutiveStar.toStar Complex
                    (@StarAddMonoid.toInvolutiveStar Complex
                      (@AddCommMonoid.toAddMonoid Complex
                        (@NonUnitalNonAssocSemiring.toAddCommMonoid Complex
                          (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring Complex
                            (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing Complex
                              (@NonUnitalCommRing.toNonUnitalNonAssocCommRing Complex Complex.instNonUnitalCommRing)))))
                      (@StarRing.toStarAddMonoid Complex
                        (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring Complex
                          (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing Complex
                            (@NonUnitalCommRing.toNonUnitalNonAssocCommRing Complex Complex.instNonUnitalCommRing)))
                        Complex.instStarRing)))
                  (@DFunLike.coe
                    (@RingHom E Complex
                      (@Semiring.toNonAssocSemiring E
                        (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                      (@Semiring.toNonAssocSemiring Complex Complex.instSemiring))
                    E (fun (x : E) ↦ Complex)
                    (@RingHom.instFunLike E Complex
                      (@Semiring.toNonAssocSemiring E
                        (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                      (@Semiring.toNonAssocSemiring Complex Complex.instSemiring))
                    τ x)))))

/- English proof (translation)
Introduce `F E _ _`. Use `infer_instance`.
-/
theorem UpperTheory.Reformulated.B.SquareOfApproximation.aux2 :
    ∀ {F E : Type} [inst : Field F] [inst_1 : Field E],
      @RingHomClass
        (@RingHom (@NumberField.RingOfIntegers F inst) (@NumberField.RingOfIntegers E inst_1)
          (@Semiring.toNonAssocSemiring (@NumberField.RingOfIntegers F inst)
            (@CommSemiring.toSemiring (@NumberField.RingOfIntegers F inst)
              (@CommRing.toCommSemiring (@NumberField.RingOfIntegers F inst)
                (@NumberField.instCommRingRingOfIntegers F inst))))
          (@Semiring.toNonAssocSemiring (@NumberField.RingOfIntegers E inst_1)
            (@CommSemiring.toSemiring (@NumberField.RingOfIntegers E inst_1)
              (@CommRing.toCommSemiring (@NumberField.RingOfIntegers E inst_1)
                (@NumberField.instCommRingRingOfIntegers E inst_1)))))
        (@NumberField.RingOfIntegers F inst) (@NumberField.RingOfIntegers E inst_1)
        (@Semiring.toNonAssocSemiring (@NumberField.RingOfIntegers F inst)
          (@CommSemiring.toSemiring (@NumberField.RingOfIntegers F inst)
            (@CommRing.toCommSemiring (@NumberField.RingOfIntegers F inst)
              (@NumberField.instCommRingRingOfIntegers F inst))))
        (@Semiring.toNonAssocSemiring (@NumberField.RingOfIntegers E inst_1)
          (@CommSemiring.toSemiring (@NumberField.RingOfIntegers E inst_1)
            (@CommRing.toCommSemiring (@NumberField.RingOfIntegers E inst_1)
              (@NumberField.instCommRingRingOfIntegers E inst_1))))
        (@RingHom.instFunLike (@NumberField.RingOfIntegers F inst) (@NumberField.RingOfIntegers E inst_1)
          (@Semiring.toNonAssocSemiring (@NumberField.RingOfIntegers F inst)
            (@CommSemiring.toSemiring (@NumberField.RingOfIntegers F inst)
              (@CommRing.toCommSemiring (@NumberField.RingOfIntegers F inst)
                (@NumberField.instCommRingRingOfIntegers F inst))))
          (@Semiring.toNonAssocSemiring (@NumberField.RingOfIntegers E inst_1)
            (@CommSemiring.toSemiring (@NumberField.RingOfIntegers E inst_1)
              (@CommRing.toCommSemiring (@NumberField.RingOfIntegers E inst_1)
                (@NumberField.instCommRingRingOfIntegers E inst_1))))) := by
  intro F E _ _
  infer_instance

noncomputable def UpperTheory.Reformulated.B.SquareOfApproximation.IsSplit :
    {F E : Type} →
      [inst : Field F] →
        [inst_1 : Field E] →
          [@Algebra F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1)))] →
            @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                (@NumberField.instCommRingRingOfIntegers F inst) →
              Prop :=
    fun {F E : Type} [inst : Field F] [inst_1 : Field E]
        [inst_2 :
          @Algebra F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
            (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1)))]
        (w :
          @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
            (@NumberField.instCommRingRingOfIntegers F inst)) ↦
      ∃ (P :
        @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers E inst_1)
          (@NumberField.instCommRingRingOfIntegers E inst_1))
        (Q :
        @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers E inst_1)
          (@NumberField.instCommRingRingOfIntegers E inst_1)),
        And
          (@Ne
            (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers E inst_1)
              (@NumberField.instCommRingRingOfIntegers E inst_1))
            P Q)
          (And
            (@Eq
              (@Ideal (@NumberField.RingOfIntegers F inst)
                (@CommSemiring.toSemiring (@NumberField.RingOfIntegers F inst)
                  (@CommRing.toCommSemiring (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst))))
              (@Ideal.comap (@NumberField.RingOfIntegers F inst) (@NumberField.RingOfIntegers E inst_1)
                (@RingHom (@NumberField.RingOfIntegers F inst) (@NumberField.RingOfIntegers E inst_1)
                  (@Semiring.toNonAssocSemiring (@NumberField.RingOfIntegers F inst)
                    (@CommSemiring.toSemiring (@NumberField.RingOfIntegers F inst)
                      (@CommRing.toCommSemiring (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst))))
                  (@Semiring.toNonAssocSemiring (@NumberField.RingOfIntegers E inst_1)
                    (@CommSemiring.toSemiring (@NumberField.RingOfIntegers E inst_1)
                      (@CommRing.toCommSemiring (@NumberField.RingOfIntegers E inst_1)
                        (@NumberField.instCommRingRingOfIntegers E inst_1)))))
                (@CommSemiring.toSemiring (@NumberField.RingOfIntegers F inst)
                  (@CommRing.toCommSemiring (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)))
                (@CommSemiring.toSemiring (@NumberField.RingOfIntegers E inst_1)
                  (@CommRing.toCommSemiring (@NumberField.RingOfIntegers E inst_1)
                    (@NumberField.instCommRingRingOfIntegers E inst_1)))
                (@RingHom.instFunLike (@NumberField.RingOfIntegers F inst) (@NumberField.RingOfIntegers E inst_1)
                  (@Semiring.toNonAssocSemiring (@NumberField.RingOfIntegers F inst)
                    (@CommSemiring.toSemiring (@NumberField.RingOfIntegers F inst)
                      (@CommRing.toCommSemiring (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst))))
                  (@Semiring.toNonAssocSemiring (@NumberField.RingOfIntegers E inst_1)
                    (@CommSemiring.toSemiring (@NumberField.RingOfIntegers E inst_1)
                      (@CommRing.toCommSemiring (@NumberField.RingOfIntegers E inst_1)
                        (@NumberField.instCommRingRingOfIntegers E inst_1)))))
                (@Algebra.algebraMap (@NumberField.RingOfIntegers F inst) (@NumberField.RingOfIntegers E inst_1)
                  (@CommRing.toCommSemiring (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst))
                  (@CommSemiring.toSemiring (@NumberField.RingOfIntegers E inst_1)
                    (@CommRing.toCommSemiring (@NumberField.RingOfIntegers E inst_1)
                      (@NumberField.instCommRingRingOfIntegers E inst_1)))
                  (@NumberField.inst_ringOfIntegersAlgebra F E inst inst_1 inst_2))
                (@UpperTheory.Reformulated.B.SquareOfApproximation.aux2 F E inst inst_1)
                (@IsDedekindDomain.HeightOneSpectrum.asIdeal (@NumberField.RingOfIntegers E inst_1)
                  (@NumberField.instCommRingRingOfIntegers E inst_1) P))
              (@IsDedekindDomain.HeightOneSpectrum.asIdeal (@NumberField.RingOfIntegers F inst)
                (@NumberField.instCommRingRingOfIntegers F inst) w))
            (@Eq
              (@Ideal (@NumberField.RingOfIntegers F inst)
                (@CommSemiring.toSemiring (@NumberField.RingOfIntegers F inst)
                  (@CommRing.toCommSemiring (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst))))
              (@Ideal.comap (@NumberField.RingOfIntegers F inst) (@NumberField.RingOfIntegers E inst_1)
                (@RingHom (@NumberField.RingOfIntegers F inst) (@NumberField.RingOfIntegers E inst_1)
                  (@Semiring.toNonAssocSemiring (@NumberField.RingOfIntegers F inst)
                    (@CommSemiring.toSemiring (@NumberField.RingOfIntegers F inst)
                      (@CommRing.toCommSemiring (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst))))
                  (@Semiring.toNonAssocSemiring (@NumberField.RingOfIntegers E inst_1)
                    (@CommSemiring.toSemiring (@NumberField.RingOfIntegers E inst_1)
                      (@CommRing.toCommSemiring (@NumberField.RingOfIntegers E inst_1)
                        (@NumberField.instCommRingRingOfIntegers E inst_1)))))
                (@CommSemiring.toSemiring (@NumberField.RingOfIntegers F inst)
                  (@CommRing.toCommSemiring (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)))
                (@CommSemiring.toSemiring (@NumberField.RingOfIntegers E inst_1)
                  (@CommRing.toCommSemiring (@NumberField.RingOfIntegers E inst_1)
                    (@NumberField.instCommRingRingOfIntegers E inst_1)))
                (@RingHom.instFunLike (@NumberField.RingOfIntegers F inst) (@NumberField.RingOfIntegers E inst_1)
                  (@Semiring.toNonAssocSemiring (@NumberField.RingOfIntegers F inst)
                    (@CommSemiring.toSemiring (@NumberField.RingOfIntegers F inst)
                      (@CommRing.toCommSemiring (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst))))
                  (@Semiring.toNonAssocSemiring (@NumberField.RingOfIntegers E inst_1)
                    (@CommSemiring.toSemiring (@NumberField.RingOfIntegers E inst_1)
                      (@CommRing.toCommSemiring (@NumberField.RingOfIntegers E inst_1)
                        (@NumberField.instCommRingRingOfIntegers E inst_1)))))
                (@Algebra.algebraMap (@NumberField.RingOfIntegers F inst) (@NumberField.RingOfIntegers E inst_1)
                  (@CommRing.toCommSemiring (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst))
                  (@CommSemiring.toSemiring (@NumberField.RingOfIntegers E inst_1)
                    (@CommRing.toCommSemiring (@NumberField.RingOfIntegers E inst_1)
                      (@NumberField.instCommRingRingOfIntegers E inst_1)))
                  (@NumberField.inst_ringOfIntegersAlgebra F E inst inst_1 inst_2))
                (@UpperTheory.Reformulated.B.SquareOfApproximation.aux2 F E inst inst_1)
                (@IsDedekindDomain.HeightOneSpectrum.asIdeal (@NumberField.RingOfIntegers E inst_1)
                  (@NumberField.instCommRingRingOfIntegers E inst_1) Q))
              (@IsDedekindDomain.HeightOneSpectrum.asIdeal (@NumberField.RingOfIntegers F inst)
                (@NumberField.instCommRingRingOfIntegers F inst) w)))

@[reducible] noncomputable def UpperTheory.Reformulated.B.SquareOfApproximation.Fv :
    (F : Type) →
      [inst : Field F] →
        [@NumberField F inst] →
          @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
              (@NumberField.instCommRingRingOfIntegers F inst) →
            Type :=
    fun (F : Type) [inst : Field F] [inst_1 : @NumberField F inst]
        (v :
          @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
            (@NumberField.instCommRingRingOfIntegers F inst)) ↦
      @IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
        (@NumberField.instCommRingRingOfIntegers F inst) (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F
        inst (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ _ θ d hd hσ hθ hsp v hv`. Take `⟨P, Q, hne, hP, hQ⟩` from `hv`. Conclude with `UpperTheory.Reformulated.B.SquareOfApproximation.core σ hd hσ hθ hsp P Q hne hP hQ`.
-/
theorem UpperTheory.Reformulated.B.SquareOfApproximation.main :
    ∀ {F E : Type} [inst : Field F] [inst_1 : @NumberField F inst] [inst_2 : Field E] [inst_3 : @NumberField E inst_2]
      [inst_4 :
        @Algebra F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
          (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))]
      {σ :
        @AlgHom F E E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
          (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
          (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))) inst_4 inst_4},
      @UpperTheory.Reformulated.B.SquareOfApproximation.IsCMExt F E inst inst_1 inst_2 inst_3 inst_4 σ →
        ∀ {θ : E} {d : @NumberField.RingOfIntegers F inst},
          @Ne F (@NumberField.RingOfIntegers.val F inst d)
              (@OfNat.ofNat F (nat_lit 0)
                (@Zero.toOfNat0 F
                  (@MulZeroClass.toZero F
                    (@instMulZeroClassOfSemiring F
                      (@DivisionSemiring.toSemiring F (@Semifield.toDivisionSemiring F (@Field.toSemifield F inst))))))) →
            @Eq E
                (@DFunLike.coe
                  (@AlgHom F E E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))) inst_4
                    inst_4)
                  E (fun (x : E) ↦ E)
                  (@AlgHom.funLike F E E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))) inst_4
                    inst_4)
                  σ θ)
                (@Neg.neg E
                  (@NegZeroClass.toNeg E
                    (@SubNegZeroMonoid.toNegZeroClass E
                      (@SubtractionMonoid.toSubNegZeroMonoid E
                        (@SubtractionCommMonoid.toSubtractionMonoid E
                          (@AddCommGroup.toDivisionAddCommMonoid E
                            (@Ring.toAddCommGroup E (@DivisionRing.toRing E (@Field.toDivisionRing E inst_2))))))))
                  θ) →
              @Eq E
                  (@HMul.hMul E E E
                    (@instHMul E
                      (@Distrib.toMul E
                        (@instDistribOfSemiring E
                          (@DivisionSemiring.toSemiring E
                            (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))))
                    θ θ)
                  (@DFunLike.coe
                    (@RingHom F E
                      (@Semiring.toNonAssocSemiring F
                        (@CommSemiring.toSemiring F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))))
                      (@Semiring.toNonAssocSemiring E
                        (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))))
                    F (fun (x : F) ↦ E)
                    (@RingHom.instFunLike F E
                      (@Semiring.toNonAssocSemiring F
                        (@CommSemiring.toSemiring F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))))
                      (@Semiring.toNonAssocSemiring E
                        (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))))
                    (@Algebra.algebraMap F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                      inst_4)
                    (@NumberField.RingOfIntegers.val F inst d)) →
                (∀ (x : E),
                    ∃ (u : F) (w : F),
                      @Eq E x
                        (@HAdd.hAdd E E E
                          (@instHAdd E
                            (@Distrib.toAdd E
                              (@instDistribOfSemiring E
                                (@DivisionSemiring.toSemiring E
                                  (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))))
                          (@HSMul.hSMul F E E
                            (@instHSMul F E
                              (@Algebra.toSMul F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                                (@DivisionSemiring.toSemiring E
                                  (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                                inst_4))
                            u
                            (@OfNat.ofNat E (nat_lit 1)
                              (@One.toOfNat1 E
                                (@AddMonoidWithOne.toOne E
                                  (@AddGroupWithOne.toAddMonoidWithOne E
                                    (@Ring.toAddGroupWithOne E
                                      (@DivisionRing.toRing E (@Field.toDivisionRing E inst_2))))))))
                          (@HSMul.hSMul F E E
                            (@instHSMul F E
                              (@Algebra.toSMul F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                                (@DivisionSemiring.toSemiring E
                                  (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                                inst_4))
                            w θ))) →
                  ∀
                    {v :
                      @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst)},
                    @UpperTheory.Reformulated.B.SquareOfApproximation.IsSplit F E inst inst_2 inst_4 v →
                      @IsSquare (@UpperTheory.Reformulated.B.SquareOfApproximation.Fv F inst inst_1 v)
                        (@Distrib.toMul (@UpperTheory.Reformulated.B.SquareOfApproximation.Fv F inst inst_1 v)
                          (@instDistribOfSemiring (@UpperTheory.Reformulated.B.SquareOfApproximation.Fv F inst inst_1 v)
                            (@DivisionSemiring.toSemiring (@UpperTheory.Reformulated.B.SquareOfApproximation.Fv F inst inst_1 v)
                              (@Semifield.toDivisionSemiring (@UpperTheory.Reformulated.B.SquareOfApproximation.Fv F inst inst_1 v)
                                (@Field.toSemifield (@UpperTheory.Reformulated.B.SquareOfApproximation.Fv F inst inst_1 v)
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                    (@NumberField.RingOfIntegers F inst) (@NumberField.instCommRingRingOfIntegers F inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v))))))
                        (@DFunLike.coe
                          (@RingHom F (@UpperTheory.Reformulated.B.SquareOfApproximation.Fv F inst inst_1 v)
                            (@Semiring.toNonAssocSemiring F
                              (@CommSemiring.toSemiring F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))))
                            (@Semiring.toNonAssocSemiring (@UpperTheory.Reformulated.B.SquareOfApproximation.Fv F inst inst_1 v)
                              (@DivisionSemiring.toSemiring
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                                  (@NumberField.instCommRingRingOfIntegers F inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
                                (@Semifield.toDivisionSemiring
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                                    (@NumberField.instCommRingRingOfIntegers F inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
                                  (@Field.toSemifield
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                                      (@NumberField.instCommRingRingOfIntegers F inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                      (@NumberField.RingOfIntegers F inst) (@NumberField.instCommRingRingOfIntegers F inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v))))))
                          F (fun (x : F) ↦ @UpperTheory.Reformulated.B.SquareOfApproximation.Fv F inst inst_1 v)
                          (@RingHom.instFunLike F (@UpperTheory.Reformulated.B.SquareOfApproximation.Fv F inst inst_1 v)
                            (@Semiring.toNonAssocSemiring F
                              (@CommSemiring.toSemiring F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))))
                            (@Semiring.toNonAssocSemiring (@UpperTheory.Reformulated.B.SquareOfApproximation.Fv F inst inst_1 v)
                              (@DivisionSemiring.toSemiring
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                                  (@NumberField.instCommRingRingOfIntegers F inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
                                (@Semifield.toDivisionSemiring
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                                    (@NumberField.instCommRingRingOfIntegers F inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
                                  (@Field.toSemifield
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                                      (@NumberField.instCommRingRingOfIntegers F inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                      (@NumberField.RingOfIntegers F inst) (@NumberField.instCommRingRingOfIntegers F inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v))))))
                          (@Algebra.algebraMap F (@UpperTheory.Reformulated.B.SquareOfApproximation.Fv F inst inst_1 v)
                            (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                            (@DivisionSemiring.toSemiring
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                                (@NumberField.instCommRingRingOfIntegers F inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
                              (@Semifield.toDivisionSemiring
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                                  (@NumberField.instCommRingRingOfIntegers F inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
                                (@Field.toSemifield
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                                    (@NumberField.instCommRingRingOfIntegers F inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v)
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                    (@NumberField.RingOfIntegers F inst) (@NumberField.instCommRingRingOfIntegers F inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v))))
                            (@IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
                              (@NumberField.RingOfIntegers F inst) (@NumberField.instCommRingRingOfIntegers F inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F F inst
                              (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v
                              (@Algebra.id F (@Semifield.toCommSemiring F (@Field.toSemifield F inst)))))
                          (@NumberField.RingOfIntegers.val F inst d)) := by
  intro F E _ _ _ _ _ σ _ θ d hd hσ hθ hsp v hv
  obtain ⟨P, Q, hne, hP, hQ⟩ := hv
  exact UpperTheory.Reformulated.B.SquareOfApproximation.core σ hd hσ hθ hsp P Q hne hP hQ
