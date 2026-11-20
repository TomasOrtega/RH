import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.FixedIntegersIsUnitOfNotMemPrimeSpan

noncomputable section

open GlobalTheory.Col

namespace UpperTheory.Kd.C7

/- English proof (translation)
Establish `h` using `Polynomial.cyclotomic_mul_prime_pow_eq S (p := p) (m := 1) (by simpa using hp.out.one_lt.ne') (k := j + 1) (Nat.succ_pos j)`. Rewrite `h` using `[mul_one, Polynomial.cyclotomic_one]`. Rewrite using `[cyc, h, Polynomial.eval₂_pow]`. Simplify using the standard rewrite rules.
-/
private theorem cyc_charP (S : Type) [CommRing S] (p : ℕ) [hp : Fact p.Prime] [CharP S p] (j : ℕ) :
    cyc S p (j + 1) = PowerSeries.X ^ (p ^ (j + 1) - p ^ j) := by
  have h := Polynomial.cyclotomic_mul_prime_pow_eq S (p := p) (m := 1) (by simpa using hp.out.one_lt.ne') (k := j + 1) (Nat.succ_pos j)
  rw [mul_one, Polynomial.cyclotomic_one] at h
  rw [cyc, h, Polynomial.eval₂_pow]
  simp

/- English proof (translation)
Establish `: ∀ k, ∃ y : R, y * p = PowerSeries.coeff k h`. Introduce `k`. Use `congrArg (PowerSeries.coeff k) H` as an intermediate fact. Rewrite `this` using `[PowerSeries.coeff_map, map_zero, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `Ideal.mem_span_singleton'.1 this`.

Use `choose y hy using this`. Use `⟨PowerSeries.mk y, ?_⟩` and prove the remaining obligations. Use extensionality with `k`. Rewrite using `[← map_natCast (PowerSeries.C (R := R)), PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, ← hy, mul_comm]`.
-/
private theorem dvd_of_map {R : Type} [CommRing R] (p : ℕ) (h : PowerSeries R)
    (H : PowerSeries.map (Ideal.Quotient.mk (Ideal.span {(p : R)})) h = 0) :
    ∃ h' : PowerSeries R, h = (p : PowerSeries R) * h' := by
  have : ∀ k, ∃ y : R, y * p = PowerSeries.coeff k h := by
    intro k
    have := congrArg (PowerSeries.coeff k) H
    rw [PowerSeries.coeff_map, map_zero, Ideal.Quotient.eq_zero_iff_mem] at this
    exact Ideal.mem_span_singleton'.1 this
  choose y hy using this
  refine ⟨PowerSeries.mk y, ?_⟩
  ext k
  rw [← map_natCast (PowerSeries.C (R := R)), PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, ← hy, mul_comm]

/- English proof (translation)
Use `set π := Ideal.Quotient.mk (Ideal.span {(p : R)}) with hπ`. Use `haveI : Nontrivial (R ⧸ Ideal.span {(p : R)}) := Ideal.Quotient.nontrivial_iff.2 (by rw [Ne, Ideal.span_singleton_eq_top]; exact hpr.not_isUnit)`. Establish `hp0 : ((p : ℕ) : R ⧸ Ideal.span {(p : R)}) = 0`. Rewrite using `[← map_natCast π]`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)`.

Use `haveI : CharP (R ⧸ Ideal.span {(p : R)}) p := (CharP.charP_iff_prime_eq_zero hp.out).2 hp0`. Establish `hp1 : ((p : ℕ) : PowerSeries (R ⧸ Ideal.span {(p : R)})) = 0`. Rewrite using `[← map_natCast (PowerSeries.C (R := R ⧸ Ideal.span {(p : R)})), hp0, map_zero]`. Establish `key : ∀ j, c ≤ j → ∀ a b : PowerSeries R, h = (p : PowerSeries R) ^ (j + 1 - c) * a + cyc R p (j + 1) * b → PowerSeries.map π h = PowerSeries.X ^ (p ^ (j + 1) - p ^ j) * PowerSeries.map π b`. Introduce `j hj a b hab`.

Rewrite using `[hab, map_add, map_mul, map_mul, map_pow, map_natCast, hp1, zero_pow (by omega), zero_mul, zero_add, coeffMap_cyc, cyc_charP]`. Establish `h0 : PowerSeries.map π h = 0`. Use extensionality with `k`. Take `⟨a, b, hab⟩` from `H (m₀ + c + k + 1) (by omega)`. Establish `h1` using `key (m₀ + c + k) (by omega) a b hab`.

Establish `h2 : k < p ^ (m₀ + c + k + 1) - p ^ (m₀ + c + k)`. Establish `h3 : m₀ + c + k < p ^ (m₀ + c + k)` using `Nat.lt_pow_self hp.out.one_lt`. Establish `h4 : p ^ (m₀ + c + k) * 2 ≤ p ^ (m₀ + c + k + 1)`. Rewrite using `[pow_succ]`. Conclude with `Nat.mul_le_mul_left _ hp.out.two_le`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[map_zero]`. Conclude with `PowerSeries.X_pow_dvd_iff.1 ⟨_, h1⟩ k h2`. Take `⟨h', hh'⟩` from `dvd_of_map p h h0`. Use `⟨h', hh', fun m hm => ?_⟩` and prove the remaining obligations.

Take `⟨j, rfl⟩ : ∃ j, m = j + 1` from `⟨m - 1, by omega⟩`. Take `⟨a, b, hab⟩` from `H (j + 1) (by omega)`. Establish `h1` using `key j (by omega) a b hab`. Rewrite `h1` using `[h0]`. Establish `h2 : PowerSeries.map π b = 0`.

Use extensionality with `k`. Use `congrArg (PowerSeries.coeff (k + (p ^ (j + 1) - p ^ j))) h1` as an intermediate fact. Rewrite `this` using `[PowerSeries.coeff_X_pow_mul]`. Simplify using `using this.symm`. Take `⟨b', hb'⟩` from `dvd_of_map p b h2`.

Use `⟨a, b', ?_⟩` and prove the remaining obligations. Establish `hne : ((p : ℕ) : PowerSeries R) ≠ 0`. Rewrite using `[← map_natCast (PowerSeries.C (R := R))]`. Introduce `h3`. Conclude with `hpr.ne_zero (by simpa using congrArg (PowerSeries.coeff 0) h3)`.

Apply `mul_left_cancel₀ hne` to reduce the goal to its premises. Establish `e : j + 1 - c = (j + 1 - (c + 1)) + 1` using `by omega`. Rewrite using `[← hh', hab, hb', e]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem step {R : Type} [CommRing R] [IsDomain R] (p : ℕ) [hp : Fact p.Prime] (hpr : Prime (p : R))
    (h : PowerSeries R) (c m₀ : ℕ)
    (H : ∀ m, m₀ ≤ m → ∃ a b : PowerSeries R, h = (p : PowerSeries R) ^ (m - c) * a + cyc R p m * b) :
    ∃ h' : PowerSeries R, h = (p : PowerSeries R) * h' ∧ ∀ m, m₀ + c + 1 ≤ m →
      ∃ a b : PowerSeries R, h' = (p : PowerSeries R) ^ (m - (c + 1)) * a + cyc R p m * b := by
  set π := Ideal.Quotient.mk (Ideal.span {(p : R)}) with hπ
  haveI : Nontrivial (R ⧸ Ideal.span {(p : R)}) :=
    Ideal.Quotient.nontrivial_iff.2 (by rw [Ne, Ideal.span_singleton_eq_top]; exact hpr.not_isUnit)
  have hp0 : ((p : ℕ) : R ⧸ Ideal.span {(p : R)}) = 0 := by
    rw [← map_natCast π]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
  haveI : CharP (R ⧸ Ideal.span {(p : R)}) p := (CharP.charP_iff_prime_eq_zero hp.out).2 hp0
  have hp1 : ((p : ℕ) : PowerSeries (R ⧸ Ideal.span {(p : R)})) = 0 := by
    rw [← map_natCast (PowerSeries.C (R := R ⧸ Ideal.span {(p : R)})), hp0, map_zero]
  have key : ∀ j, c ≤ j → ∀ a b : PowerSeries R, h = (p : PowerSeries R) ^ (j + 1 - c) * a + cyc R p (j + 1) * b →
      PowerSeries.map π h = PowerSeries.X ^ (p ^ (j + 1) - p ^ j) * PowerSeries.map π b := by
    intro j hj a b hab
    rw [hab, map_add, map_mul, map_mul, map_pow, map_natCast, hp1, zero_pow (by omega), zero_mul, zero_add,
      coeffMap_cyc, cyc_charP]
  have h0 : PowerSeries.map π h = 0 := by
    ext k
    obtain ⟨a, b, hab⟩ := H (m₀ + c + k + 1) (by omega)
    have h1 := key (m₀ + c + k) (by omega) a b hab
    have h2 : k < p ^ (m₀ + c + k + 1) - p ^ (m₀ + c + k) := by
      have h3 : m₀ + c + k < p ^ (m₀ + c + k) := Nat.lt_pow_self hp.out.one_lt
      have h4 : p ^ (m₀ + c + k) * 2 ≤ p ^ (m₀ + c + k + 1) := by
        rw [pow_succ]; exact Nat.mul_le_mul_left _ hp.out.two_le
      omega
    rw [map_zero]
    exact PowerSeries.X_pow_dvd_iff.1 ⟨_, h1⟩ k h2
  obtain ⟨h', hh'⟩ := dvd_of_map p h h0
  refine ⟨h', hh', fun m hm => ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  obtain ⟨a, b, hab⟩ := H (j + 1) (by omega)
  have h1 := key j (by omega) a b hab
  rw [h0] at h1
  have h2 : PowerSeries.map π b = 0 := by
    ext k
    have := congrArg (PowerSeries.coeff (k + (p ^ (j + 1) - p ^ j))) h1
    rw [PowerSeries.coeff_X_pow_mul] at this
    simpa using this.symm
  obtain ⟨b', hb'⟩ := dvd_of_map p b h2
  refine ⟨a, b', ?_⟩
  have hne : ((p : ℕ) : PowerSeries R) ≠ 0 := by
    rw [← map_natCast (PowerSeries.C (R := R))]
    intro h3
    exact hpr.ne_zero (by simpa using congrArg (PowerSeries.coeff 0) h3)
  apply mul_left_cancel₀ hne
  have e : j + 1 - c = (j + 1 - (c + 1)) + 1 := by omega
  rw [← hh', hab, hb', e]
  ring

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => intro h _ _ _; exact ⟨h, by simp⟩`. Consider the case `succ n ih`. Introduce `h c m₀ H`. Take `⟨h', e, H'⟩` from `step p hpr h c m₀ H`.

Take `⟨h'', e'⟩` from `ih h' (c + 1) (m₀ + c + 1) H'`. Conclude with `⟨h'', by rw [e, e']; ring⟩`.
-/
private theorem allDvd {R : Type} [CommRing R] [IsDomain R] (p : ℕ) [hp : Fact p.Prime] (hpr : Prime (p : R)) (n : ℕ) :
    ∀ (h : PowerSeries R) (c m₀ : ℕ),
    (∀ m, m₀ ≤ m → ∃ a b : PowerSeries R, h = (p : PowerSeries R) ^ (m - c) * a + cyc R p m * b) →
    ∃ h' : PowerSeries R, h = (p : PowerSeries R) ^ n * h' := by
  induction n with
  | zero => intro h _ _ _; exact ⟨h, by simp⟩
  | succ n ih =>
    intro h c m₀ H
    obtain ⟨h', e, H'⟩ := step p hpr h c m₀ H
    obtain ⟨h'', e'⟩ := ih h' (c + 1) (m₀ + c + 1) H'
    exact ⟨h'', by rw [e, e']; ring⟩

/- English proof (translation)
Proceed by induction on `m generalizing x with`. Consider the case `zero => simp`. Consider the case `succ m ih`. Rewrite using `[pow_succ (σ : R →+* R), pow_succ' ((σ.symm : R ≃+* R) : R →+* R)]`. Simplify using `only [RingHom.mul_def, RingHom.comp_apply, RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply]`.

Conclude with `ih x`.
-/
private theorem pow_comp_pow {R : Type} [CommRing R] (σ : R ≃+* R) (m : ℕ) (x : R) :
    ((σ : R →+* R) ^ m) ((((σ.symm : R ≃+* R) : R →+* R) ^ m) x) = x := by
  induction m generalizing x with
  | zero => simp
  | succ m ih =>
    rw [pow_succ (σ : R →+* R), pow_succ' ((σ.symm : R ≃+* R) : R →+* R)]
    simp only [RingHom.mul_def, RingHom.comp_apply, RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply]
    exact ih x

/- English proof (translation)
Introduce `R _ p hp σ hF h c m₀ H`. Use `haveI := hF.dom`. Use `haveI := hF.complete`. Establish `H' : ∀ m, m₀ ≤ m → ∃ a b : PowerSeries R, h = (p : PowerSeries R) ^ (m - c) * a + cyc R p m * b`. Introduce `m hm`.

Establish `h1` using `H m hm`. Rewrite `h1` using `[LC, map_zero, sub_zero]`. Take `⟨y, hy⟩` from `Ideal.mem_span_singleton'.1 h1`. Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective y`. Rewrite `hy` using `[← map_natCast (ev R p m), ← map_pow, ← map_mul, eq_comm, Ideal.Quotient.eq]`.

Take `⟨b, hb⟩` from `Ideal.mem_span_singleton'.1 hy`. Establish `h2` using `congrArg (PowerSeries.map ((σ : R →+* R) ^ m)) hb`. Establish `h3 : PowerSeries.map ((σ : R →+* R) ^ m) (PowerSeries.map (((σ.symm : R ≃+* R) : R →+* R) ^ m) h) = h`. Use extensionality with `k`. Rewrite using `[PowerSeries.coeff_map, PowerSeries.coeff_map, pow_comp_pow]`.

Rewrite `h2` using `[map_sub, h3, map_mul, map_mul, map_pow, map_natCast, coeffMap_cyc]`. Conclude with `⟨PowerSeries.map ((σ : R →+* R) ^ m) a, PowerSeries.map ((σ : R →+* R) ^ m) b, by linear_combination -h2⟩`. Use extensionality with `k`. Rewrite using `[map_zero]`. Use `IsHausdorff.haus (I := Ideal.span {(p : R)}) inferInstance _ fun n => ?_` and prove the remaining obligations.

Take `⟨h', e⟩` from `allDvd p hF.prime n h c m₀ H'`. Rewrite using `[SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton']`. Use `⟨PowerSeries.coeff k h', ?_⟩` and prove the remaining obligations. Rewrite using `[e, ← map_natCast (PowerSeries.C (R := R)), ← map_pow, PowerSeries.coeff_C_mul, mul_comm]`.
-/
theorem pUniq : SUniq := by
  intro R _ p hp σ hF h c m₀ H
  haveI := hF.dom
  haveI := hF.complete
  have H' : ∀ m, m₀ ≤ m → ∃ a b : PowerSeries R, h = (p : PowerSeries R) ^ (m - c) * a + cyc R p m * b := by
    intro m hm
    have h1 := H m hm
    rw [LC, map_zero, sub_zero] at h1
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 h1
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [← map_natCast (ev R p m), ← map_pow, ← map_mul, eq_comm, Ideal.Quotient.eq] at hy
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 hy
    have h2 := congrArg (PowerSeries.map ((σ : R →+* R) ^ m)) hb
    have h3 : PowerSeries.map ((σ : R →+* R) ^ m) (PowerSeries.map (((σ.symm : R ≃+* R) : R →+* R) ^ m) h) = h := by
      ext k
      rw [PowerSeries.coeff_map, PowerSeries.coeff_map, pow_comp_pow]
    rw [map_sub, h3, map_mul, map_mul, map_pow, map_natCast, coeffMap_cyc] at h2
    exact ⟨PowerSeries.map ((σ : R →+* R) ^ m) a, PowerSeries.map ((σ : R →+* R) ^ m) b, by linear_combination -h2⟩
  ext k
  rw [map_zero]
  refine IsHausdorff.haus (I := Ideal.span {(p : R)}) inferInstance _ fun n => ?_
  obtain ⟨h', e⟩ := allDvd p hF.prime n h c m₀ H'
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
  refine ⟨PowerSeries.coeff k h', ?_⟩
  rw [e, ← map_natCast (PowerSeries.C (R := R)), ← map_pow, PowerSeries.coeff_C_mul, mul_comm]

end UpperTheory.Kd.C7
