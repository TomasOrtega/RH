import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.CBlockValAlt

open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK UpperTheory.V.ZK.Cl

/- English proof (translation)
Take `⟨p, q, hq, hpq⟩` from `IsFractionRing.div_surjective (𝓞 F) x`. Establish `hpq' : (p : F) / q = x` using `hpq`. Establish `hq0 : q ≠ 0` using `nonZeroDivisors.ne_zero hq`. Establish `hq0' : (q : F) ≠ 0` using `by exact_mod_cast hq0`. Set `T : Ideal (𝓞 F)` to `(LinearMap.range (Algebra.linearMap (𝓞 F) F)).comap (LinearMap.toSpanSingleton (𝓞 F) F x)`.

Establish `memT : ∀ y : 𝓞 F, y ∈ T ↔ ∃ a : 𝓞 F, (y : F) * x = a`. Introduce `y`. Simplify using `only [T, Submodule.mem_comap, LinearMap.mem_range, LinearMap.toSpanSingleton_apply, Algebra.linearMap_apply, Algebra.smul_def]`. Apply the tactic sequence `constructor <;> rintro ⟨a, ha⟩ <;> exact ⟨a, ha.symm⟩`. Establish `hqT : q ∈ T` using `(memT q).2 ⟨p, by rw [← hpq']; field_simp⟩`.

Establish `hrad : c ∈ T.radical`. Rewrite using `[Ideal.radical_eq_sInf, Ideal.mem_sInf]`. Introduce and unpack `P ⟨hTP, hP⟩`. Assume the negation of the conclusion as `hc`. Establish `hPne : P ≠ ⊥`.

Introduce `h0`. Use `hTP hqT` as an intermediate fact. Rewrite `this` using `[h0]`. Conclude with `hq0 (Ideal.mem_bot.1 this)`. Set `v : HeightOneSpectrum (𝓞 F)` to `⟨P, hP, hPne⟩`.

Establish `hv` using `h v hc`. Establish `hspan : Ideal.span {q} ≠ 0`. Rewrite using `[Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]`. Conclude with `hq0`. Establish `hPunit : ¬ IsUnit P`.

Rewrite using `[Ideal.isUnit_iff]`. Conclude with `hP.ne_top`. Take `⟨n, J, hPJ, hJ⟩` from `WfDvdMonoid.max_power_factor' hspan hPunit`. Rewrite `hPJ` using `[Ideal.dvd_iff_le]`. Take `⟨s, hsJ, hsP⟩` from `Set.not_subset.1 hPJ`.

Establish `hvq : v.intValuation q ≤ WithZero.exp (-(n : ℤ))` using `(v.intValuation_le_pow_iff_dvd q n).2 ⟨J, hJ⟩`. Establish `hq' : v.intValuation q ≠ 0`. Rewrite using `[← v.valuation_of_algebraMap (K := F)]`. Simplify using `using hq0'`. Establish `hvp : v.intValuation p ≤ WithZero.exp (-(n : ℤ))`.

Establish `hx : HeightOneSpectrum.valuation F v x = v.intValuation p / v.intValuation q`. Rewrite using `[← hpq', map_div₀, v.valuation_of_algebraMap, v.valuation_of_algebraMap]`. Rewrite `hv` using `[hx, div_le_one₀ (zero_lt_iff.2 hq')]`. Conclude with `hv.trans hvq`. Establish `hpn` using `(v.intValuation_le_pow_iff_dvd p n).1 hvp`.

Rewrite `hpn` using `[Ideal.dvd_iff_le]`. Establish `hps : p * s ∈ Ideal.span {q}`. Rewrite using `[hJ]`. Conclude with `Ideal.mul_mem_mul (hpn (Ideal.mem_span_singleton_self p)) hsJ`. Take `⟨d, hd⟩` from `Ideal.mem_span_singleton'.1 hps`.

Establish `hd' : (d : F) * q = p * s` using `by exact_mod_cast hd`. Use `hsP (hTP ((memT s).2 ⟨d, ?_⟩))` and prove the remaining obligations. Rewrite using `[← hpq']`. Clear the denominators using the available nonvanishing facts. Take the linear combination `-hd'`.

Take `⟨n, hn⟩` from `hrad`. Take `⟨a, ha⟩` from `(memT _).1 hn`. Conclude with `⟨n, a, by push_cast at ha; exact ha⟩`.
-/
private theorem exists_pow_mul_isIntegral_of_valuation_le_one_away {F : Type} [Field F] [NumberField F] (c : 𝓞 F) (x : F)
    (h : ∀ P : HeightOneSpectrum (𝓞 F), c ∉ P.asIdeal → HeightOneSpectrum.valuation F P x ≤ 1) :
    ∃ n : ℕ, ∃ a : 𝓞 F, (c : F) ^ n * x = a := by
  obtain ⟨p, q, hq, hpq⟩ := IsFractionRing.div_surjective (𝓞 F) x
  have hpq' : (p : F) / q = x := hpq
  have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
  have hq0' : (q : F) ≠ 0 := by exact_mod_cast hq0
  let T : Ideal (𝓞 F) := (LinearMap.range (Algebra.linearMap (𝓞 F) F)).comap
    (LinearMap.toSpanSingleton (𝓞 F) F x)
  have memT : ∀ y : 𝓞 F, y ∈ T ↔ ∃ a : 𝓞 F, (y : F) * x = a := by
    intro y
    simp only [T, Submodule.mem_comap, LinearMap.mem_range, LinearMap.toSpanSingleton_apply,
      Algebra.linearMap_apply, Algebra.smul_def]
    constructor <;> rintro ⟨a, ha⟩ <;> exact ⟨a, ha.symm⟩
  have hqT : q ∈ T := (memT q).2 ⟨p, by rw [← hpq']; field_simp⟩
  have hrad : c ∈ T.radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro P ⟨hTP, hP⟩
    by_contra hc
    have hPne : P ≠ ⊥ := by
      intro h0
      have := hTP hqT
      rw [h0] at this
      exact hq0 (Ideal.mem_bot.1 this)
    let v : HeightOneSpectrum (𝓞 F) := ⟨P, hP, hPne⟩
    have hv := h v hc
    have hspan : Ideal.span {q} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact hq0
    have hPunit : ¬ IsUnit P := by
      rw [Ideal.isUnit_iff]
      exact hP.ne_top
    obtain ⟨n, J, hPJ, hJ⟩ := WfDvdMonoid.max_power_factor' hspan hPunit
    rw [Ideal.dvd_iff_le] at hPJ
    obtain ⟨s, hsJ, hsP⟩ := Set.not_subset.1 hPJ
    have hvq : v.intValuation q ≤ WithZero.exp (-(n : ℤ)) :=
      (v.intValuation_le_pow_iff_dvd q n).2 ⟨J, hJ⟩
    have hq' : v.intValuation q ≠ 0 := by
      rw [← v.valuation_of_algebraMap (K := F)]
      simpa using hq0'
    have hvp : v.intValuation p ≤ WithZero.exp (-(n : ℤ)) := by
      have hx : HeightOneSpectrum.valuation F v x = v.intValuation p / v.intValuation q := by
        rw [← hpq', map_div₀, v.valuation_of_algebraMap, v.valuation_of_algebraMap]
      rw [hx, div_le_one₀ (zero_lt_iff.2 hq')] at hv
      exact hv.trans hvq
    have hpn := (v.intValuation_le_pow_iff_dvd p n).1 hvp
    rw [Ideal.dvd_iff_le] at hpn
    have hps : p * s ∈ Ideal.span {q} := by
      rw [hJ]
      exact Ideal.mul_mem_mul (hpn (Ideal.mem_span_singleton_self p)) hsJ
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.1 hps
    have hd' : (d : F) * q = p * s := by exact_mod_cast hd
    refine hsP (hTP ((memT s).2 ⟨d, ?_⟩))
    rw [← hpq']
    field_simp
    linear_combination -hd'
  obtain ⟨n, hn⟩ := hrad
  obtain ⟨a, ha⟩ := (memT _).1 hn
  exact ⟨n, a, by push_cast at ha; exact ha⟩

/- English proof (translation)
Introduce `L F _ _ _ _ _ k _ r`. Establish `uniq : ∀ (x : F) (u u' : k), ResF r x u → ResF r x u' → u = u'`. Introduce and unpack `x u u' ⟨a, b, hb, hx, hu⟩ ⟨a', b', hb', hx', hu'⟩`. Establish `h1 : a * b' = a' * b`. Establish `: (a : F) * b' = a' * b`.

Rewrite using `[← hx, ← hx']`. Expand and normalize the polynomial expressions, which then agree. Conclude with `this` after adjusting the coercions. Establish `h2` using `congrArg r h1`. Rewrite `h2` using `[map_mul, map_mul, hu, hu']`.

Establish `h3 : (u - u') * (r b * r b') = 0` using `by linear_combination h2`. Break down `mul_eq_zero.1 h3 with h | h` into its components or cases. Conclude with `sub_eq_zero.1 h`. Conclude with `absurd h (mul_ne_zero hb hb')`. Establish `base : ∀ a : 𝓞 F, ResF r (a : F) (r a)` using `fun a => ⟨a, 1, by simp, by simp, by simp⟩`.

Establish `arith : ∀ (x y : F) (u w : k), ResF r x u → ResF r y w → ResF r (x + y) (u + w) ∧ ResF r (x * y) (u * w)`. Introduce and unpack `x y u w ⟨a, b, hb, hx, hu⟩ ⟨a', b', hb', hy, hw⟩`. Use `⟨⟨a * b' + a' * b, b * b', by simpa using mul_ne_zero hb hb', ?_, ?_⟩, ⟨a * a', b * b', by simpa using mul_ne_zero hb hb', ?_, ?_⟩⟩` and prove the remaining obligations. Establish `e : ((a * b' + a' * b : 𝓞 F) : F) = (a : F) * b' + a' * b` using `by push_cast; rfl`. Establish `e' : ((b * b' : 𝓞 F) : F) = (b : F) * b'` using `by push_cast; rfl`.

Rewrite using `[e, e', ← hx, ← hy]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [map_add, map_mul, hu, hw]`. Expand and normalize the polynomial expressions, which then agree. Establish `e : ((a * a' : 𝓞 F) : F) = (a : F) * a'` using `by push_cast; rfl`.

Establish `e' : ((b * b' : 𝓞 F) : F) = (b : F) * b'` using `by push_cast; rfl`. Rewrite using `[e, e', ← hx, ← hy]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [map_mul, hu, hw]`. Expand and normalize the polynomial expressions, which then agree.

Establish `integ : ∀ b : 𝓞 L, r (algebraMap (𝓞 L) (𝓞 F) b) ≠ 0 → ∀ x : F, (∀ P : HeightOneSpectrum (𝓞 F), algebraMap (𝓞 L) (𝓞 F) b ∉ P.asIdeal → HeightOneSpectrum.valuation F P x ≤ 1) → (∃ n, ∃ a : 𝓞 F, algebraMap (𝓞 L) F b ^ n * x = a) ∧ ∃ u, ResF r x u`. Introduce `b hb x hx`. Take `⟨n, a, ha⟩` from `exists_pow_mul_isIntegral_of_valuation_le_one_away _ x hx`. Establish `hcast : algebraMap (𝓞 L) F b = ((algebraMap (𝓞 L) (𝓞 F) b : 𝓞 F) : F)`. Rewrite using `[IsScalarTower.algebraMap_apply (𝓞 L) (𝓞 F) F]`.

Use `⟨⟨n, a, by rw [hcast]; exact ha⟩, ⟨r a / r (algebraMap (𝓞 L) (𝓞 F) b ^ n), a, algebraMap (𝓞 L) (𝓞 F) b ^ n, by rw [map_pow]; exact pow_ne_zero _ hb, ?_, ?_⟩⟩` and prove the remaining obligations. Establish `e : ((algebraMap (𝓞 L) (𝓞 F) b ^ n : 𝓞 F) : F) = ((algebraMap (𝓞 L) (𝓞 F) b : 𝓞 F) : F) ^ n` using `by push_cast; rfl`. Rewrite using `[e, mul_comm]`. Conclude with `ha`. Rewrite using `[div_mul_cancel₀]`.

Rewrite using `[map_pow]`. Conclude with `pow_ne_zero _ hb`. Use `⟨uniq, base, arith, fun b hb => ⟨integ b hb, ?_⟩⟩` and prove the remaining obligations. Introduce `α hα`. Establish `hval : ∀ P : HeightOneSpectrum (𝓞 F), algebraMap (𝓞 L) (𝓞 F) b ∉ P.asIdeal → HeightOneSpectrum.valuation F P (α : F) = 1`.

Introduce `P hP`. Establish `h0` using `hα P hP`. Unfold `ordP at h0`. Establish `hne : HeightOneSpectrum.valuation F P (α : F) ≠ 0` using `by simp`. Rewrite using `[← WithZero.exp_log hne]`.

Establish `: (HeightOneSpectrum.valuation F P (α : F)).log = 0` using `by linarith`. Rewrite using `[this]`. Both sides reduce to the same expression. Take `⟨-, u, hu⟩` from `integ b hb (α : F) (fun P hP => (hval P hP).le)`. Take `⟨-, u', hu'⟩` from `integ b hb ((α⁻¹ : Fˣ) : F) (fun P hP => by`.

Rewrite using `[Units.val_inv_eq_inv_val, map_inv₀, hval P hP, inv_one])`. Establish `hmul` using `(arith _ _ _ _ hu hu').2`. Rewrite `hmul` using `[← Units.val_mul, mul_inv_cancel, Units.val_one]`. Establish `h1 : ResF r (1 : F) 1` using `by simpa using base 1`. Establish `huu : u * u' = 1` using `uniq _ _ _ hmul h1`.

Conclude with `⟨⟨u, u', huu, by rw [mul_comm]; exact huu⟩, hu⟩`.
-/
theorem UpperTheory.V.ZK.Cl.cRes :
    UpperTheory.V.ZK.Cl.CRes := by
  intro L F _ _ _ _ _ k _ r
  have uniq : ∀ (x : F) (u u' : k), ResF r x u → ResF r x u' → u = u' := by
    rintro x u u' ⟨a, b, hb, hx, hu⟩ ⟨a', b', hb', hx', hu'⟩
    have h1 : a * b' = a' * b := by
      have : (a : F) * b' = a' * b := by
        rw [← hx, ← hx']
        ring
      exact_mod_cast this
    have h2 := congrArg r h1
    rw [map_mul, map_mul, hu, hu'] at h2
    have h3 : (u - u') * (r b * r b') = 0 := by linear_combination h2
    rcases mul_eq_zero.1 h3 with h | h
    · exact sub_eq_zero.1 h
    · exact absurd h (mul_ne_zero hb hb')
  have base : ∀ a : 𝓞 F, ResF r (a : F) (r a) := fun a => ⟨a, 1, by simp, by simp, by simp⟩
  have arith : ∀ (x y : F) (u w : k), ResF r x u → ResF r y w →
      ResF r (x + y) (u + w) ∧ ResF r (x * y) (u * w) := by
    rintro x y u w ⟨a, b, hb, hx, hu⟩ ⟨a', b', hb', hy, hw⟩
    refine ⟨⟨a * b' + a' * b, b * b', by simpa using mul_ne_zero hb hb', ?_, ?_⟩,
      ⟨a * a', b * b', by simpa using mul_ne_zero hb hb', ?_, ?_⟩⟩
    · have e : ((a * b' + a' * b : 𝓞 F) : F) = (a : F) * b' + a' * b := by push_cast; rfl
      have e' : ((b * b' : 𝓞 F) : F) = (b : F) * b' := by push_cast; rfl
      rw [e, e', ← hx, ← hy]
      ring
    · simp only [map_add, map_mul, hu, hw]
      ring
    · have e : ((a * a' : 𝓞 F) : F) = (a : F) * a' := by push_cast; rfl
      have e' : ((b * b' : 𝓞 F) : F) = (b : F) * b' := by push_cast; rfl
      rw [e, e', ← hx, ← hy]
      ring
    · simp only [map_mul, hu, hw]
      ring
  have integ : ∀ b : 𝓞 L, r (algebraMap (𝓞 L) (𝓞 F) b) ≠ 0 → ∀ x : F,
      (∀ P : HeightOneSpectrum (𝓞 F), algebraMap (𝓞 L) (𝓞 F) b ∉ P.asIdeal →
        HeightOneSpectrum.valuation F P x ≤ 1) →
      (∃ n, ∃ a : 𝓞 F, algebraMap (𝓞 L) F b ^ n * x = a) ∧ ∃ u, ResF r x u := by
    intro b hb x hx
    obtain ⟨n, a, ha⟩ := exists_pow_mul_isIntegral_of_valuation_le_one_away _ x hx
    have hcast : algebraMap (𝓞 L) F b = ((algebraMap (𝓞 L) (𝓞 F) b : 𝓞 F) : F) := by
      rw [IsScalarTower.algebraMap_apply (𝓞 L) (𝓞 F) F]
    refine ⟨⟨n, a, by rw [hcast]; exact ha⟩, ⟨r a / r (algebraMap (𝓞 L) (𝓞 F) b ^ n), a,
      algebraMap (𝓞 L) (𝓞 F) b ^ n, by rw [map_pow]; exact pow_ne_zero _ hb, ?_, ?_⟩⟩
    · have e : ((algebraMap (𝓞 L) (𝓞 F) b ^ n : 𝓞 F) : F)
          = ((algebraMap (𝓞 L) (𝓞 F) b : 𝓞 F) : F) ^ n := by push_cast; rfl
      rw [e, mul_comm]
      exact ha
    · rw [div_mul_cancel₀]
      rw [map_pow]
      exact pow_ne_zero _ hb
  refine ⟨uniq, base, arith, fun b hb => ⟨integ b hb, ?_⟩⟩
  intro α hα
  have hval : ∀ P : HeightOneSpectrum (𝓞 F), algebraMap (𝓞 L) (𝓞 F) b ∉ P.asIdeal →
      HeightOneSpectrum.valuation F P (α : F) = 1 := by
    intro P hP
    have h0 := hα P hP
    unfold ordP at h0
    have hne : HeightOneSpectrum.valuation F P (α : F) ≠ 0 := by simp
    rw [← WithZero.exp_log hne]
    have : (HeightOneSpectrum.valuation F P (α : F)).log = 0 := by linarith
    rw [this]
    rfl
  obtain ⟨-, u, hu⟩ := integ b hb (α : F) (fun P hP => (hval P hP).le)
  obtain ⟨-, u', hu'⟩ := integ b hb ((α⁻¹ : Fˣ) : F) (fun P hP => by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hval P hP, inv_one])
  have hmul := (arith _ _ _ _ hu hu').2
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one] at hmul
  have h1 : ResF r (1 : F) 1 := by simpa using base 1
  have huu : u * u' = 1 := uniq _ _ _ hmul h1
  exact ⟨⟨u, u', huu, by rw [mul_comm]; exact huu⟩, hu⟩
