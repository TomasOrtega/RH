import Development.AutomorphicArithmetic.Foundations.LocalLanglands.RecTTransport
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq

/- English proof (translation)
Proceed by induction on `N with`. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `succ n ih`. Take `⟨r, hr⟩` from `ih`. Use `⟨n + r + z * r, ?_⟩` and prove the remaining obligations.

Rewrite using `[pow_succ, hr]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem one_add_pow_expansion' {R : Type} [CommRing R] (z : R) (N : ℕ) :
    ∃ r : R, (1 + z) ^ N = 1 + N * z + z ^ 2 * r := by
  induction N with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨r, hr⟩ := ih
    refine ⟨n + r + z * r, ?_⟩
    rw [pow_succ, hr]; push_cast; ring

/- English proof (translation)
Introduce `C Γ K _ _ _ v ϖ h0 h1 hmax ρ hsurj hker N hN hpow hNK`. Establish `hv0 : v ϖ ≠ 0` using `by simpa using h0`. Establish `hvpos : 0 < v ϖ` using `zero_lt_iff.mpr hv0`. Set `abelian₂ : Cˣ → K` to `fun a => if hy : ((a : C) ^ N - 1) / ϖ ∈ v.valuationSubring then ρ ⟨_, hy⟩ else 0`. Establish `hlt : ∀ a : C, v a = 1 → v (a ^ N - 1) < 1`.

Introduce `a ha`. Establish `hm : a ∈ v.valuationSubring`. Rewrite using `[Valuation.mem_valuationSubring_iff]`. Conclude with `ha.le`. Establish `hne : ρ ⟨a, hm⟩ ≠ 0`.

Introduce `h`. Use `(hker _).1 h` as an intermediate fact. Simplify using `[ha] at this`. Establish `h2 : ρ ((⟨a, hm⟩ : v.valuationSubring) ^ N - 1) = 0`. Rewrite using `[map_sub, map_pow, hpow _ hne, map_one, sub_self]`.

Use `(hker _).1 h2` as an intermediate fact. Simplify using `using this`. Establish `hint : ∀ a : C, v a = 1 → (a ^ N - 1) / ϖ ∈ v.valuationSubring`. Introduce `a ha`. Rewrite using `[Valuation.mem_valuationSubring_iff, map_div₀, div_le_one₀ hvpos]`.

Conclude with `hmax _ (hlt a ha)`. Establish `key : ∀ (a : Cˣ) (y : v.valuationSubring), (y : C) = ((a : C) ^ N - 1) / ϖ → abelian₂ a = ρ y`. Introduce `a y hy`. Establish `hm : ((a : C) ^ N - 1) / ϖ ∈ v.valuationSubring` using `hy ▸ y.2`. Simplify using `only [abelian₂, dif_pos hm]`.

Use `congr 1`. Conclude with `Subtype.ext hy.symm`. Establish `hϖm : ϖ ∈ v.valuationSubring`. Rewrite using `[Valuation.mem_valuationSubring_iff]`. Conclude with `h1.le`.

Establish `hρϖ : ρ ⟨ϖ, hϖm⟩ = 0` using `(hker _).2 h1`. Use `⟨abelian₂, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `a b ha hb`. Establish `hbm : (b : C) ^ N - 1 ∈ v.valuationSubring`. Rewrite using `[Valuation.mem_valuationSubring_iff]`.

Conclude with `(hlt _ hb).le`. Establish `hb0 : ρ ⟨_, hbm⟩ = 0` using `(hker _).2 (hlt _ hb)`. Rewrite using `[key a ⟨_, hint _ ha⟩ rfl, key b ⟨_, hint _ hb⟩ rfl, key (a * b) (⟨_, hint _ ha⟩ + ⟨_, hint _ hb⟩ + ⟨_, hint _ ha⟩ * ⟨_, hbm⟩) ?_]`. Rewrite using `[map_add, map_add, map_mul, hb0, mul_zero, add_zero]`. Use `push_cast`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Introduce `y`. Take `⟨x, hx⟩` from `hsurj (-y)`. Establish `hx1 : v (x : C) ≤ 1` using `(Valuation.mem_valuationSubring_iff _ _).1 x.2`.

Establish `hz : v (ϖ * x) < 1`. Rewrite using `[map_mul]`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_right' hx1) h1`. Establish `ha : v (1 + ϖ * x) = 1` using `v.map_one_add_of_lt hz`. Establish `hne : (1 + ϖ * x : C) ≠ 0`.

Introduce `h`. Rewrite `ha` using `[h]`. Simplify using `at ha`. Take `⟨r, hr⟩` from `one_add_pow_expansion' ((⟨ϖ, hϖm⟩ : v.valuationSubring) * x) N`. Establish `hr' : (1 + ϖ * x : C) ^ N = 1 + N * (ϖ * x) + (ϖ * x) ^ 2 * r`.

Use `congrArg (fun t : v.valuationSubring => (t : C)) hr` as an intermediate fact. Simplify using `using this`. Use `⟨Units.mk0 _ hne, ha, ?_⟩` and prove the remaining obligations. Rewrite using `[key _ ((N : v.valuationSubring) * x + ⟨ϖ, hϖm⟩ * (x ^ 2 * r)) ?_]`. Rewrite using `[map_add, map_mul, map_mul, hρϖ, map_natCast, hNK, hx]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Units.val_mk0, hr']`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Introduce `a ha`. Establish `ha1 : v (a : C) = 1`. Use `v.map_one_add_of_lt (lt_trans ha h1)` as an intermediate fact. Simplify using `using this`. Rewrite using `[key a ⟨_, hint _ ha1⟩ rfl, hker]`.

Establish `ham : (a : C) ∈ v.valuationSubring`. Rewrite using `[Valuation.mem_valuationSubring_iff]`. Conclude with `ha1.le`. Take `⟨s, hs⟩` from `sub_one_dvd_pow_sub_one (⟨_, ham⟩ : v.valuationSubring) N`. Establish `hs' : (a : C) ^ N - 1 = ((a : C) - 1) * s`.

Use `congrArg (fun t : v.valuationSubring => (t : C)) hs` as an intermediate fact. Simplify using `using this`. Establish `hs1 : v (s : C) ≤ 1` using `(Valuation.mem_valuationSubring_iff _ _).1 s.2`. Use `show v (((a : C) ^ N - 1) / ϖ) < 1`. Rewrite using `[map_div₀, div_lt_one₀ hvpos, hs', map_mul]`.

Conclude with `lt_of_le_of_lt (mul_le_of_le_one_right' hs1) ha`. Introduce `i f hi hv hf a ha`. Establish `hia : v ((Units.map i.toRingHom.toMonoidHom a : Cˣ) : C) = 1` using `by show v (i a) = 1`. Rewrite using `[hv, ha]`. Rewrite using `[key a ⟨_, hint _ ha⟩ rfl, key _ ⟨_, hint _ hia⟩ rfl]`.

Apply `hf` to reduce the goal to its premises. Use `show ((i a) ^ N - 1) / ϖ = i (((a : C) ^ N - 1) / ϖ)`. Rewrite using `[map_div₀, map_sub, map_pow, map_one, hi]`.
-/
theorem UpperTheory.exists_unit_residue_logarithm_of_roots_of_unity :
    ∀ {C Γ K : Type} [Field C] [LinearOrderedCommGroupWithZero Γ] [Field K] (v : Valuation C Γ) (ϖ : C),
        ϖ ≠ 0 → v ϖ < 1 → (∀ x, v x < 1 → v x ≤ v ϖ) → ∀ (ρ : v.valuationSubring →+* K), Function.Surjective ρ →
        (∀ x : v.valuationSubring, ρ x = 0 ↔ v (x : C) < 1) → ∀ N : ℕ, 0 < N → (∀ z : K, z ≠ 0 → z ^ N = 1) → (N : K) = -1 →
        ∃ abelian₂ : Cˣ → K,
          (∀ a b : Cˣ, v (a : C) = 1 → v (b : C) = 1 → abelian₂ (a * b) = abelian₂ a + abelian₂ b) ∧
          (∀ y : K, ∃ a : Cˣ, v (a : C) = 1 ∧ abelian₂ a = y) ∧
          (∀ a : Cˣ, v ((a : C) - 1) < v ϖ → abelian₂ a = 0) ∧
          ∀ (i : C ≃+* C) (f : K ≃+* K), i ϖ = ϖ → (∀ x, v (i x) = v x) →
            (∀ (x y : v.valuationSubring), (y : C) = i x → ρ y = f (ρ x)) →
            ∀ a : Cˣ, v (a : C) = 1 → abelian₂ (Units.map i.toRingHom.toMonoidHom a) = f (abelian₂ a) := by
  intro C Γ K _ _ _ v ϖ h0 h1 hmax ρ hsurj hker N hN hpow hNK
  classical
  have hv0 : v ϖ ≠ 0 := by simpa using h0
  have hvpos : 0 < v ϖ := zero_lt_iff.mpr hv0
  let abelian₂ : Cˣ → K := fun a =>
    if hy : ((a : C) ^ N - 1) / ϖ ∈ v.valuationSubring then ρ ⟨_, hy⟩ else 0
  have hlt : ∀ a : C, v a = 1 → v (a ^ N - 1) < 1 := by
    intro a ha
    have hm : a ∈ v.valuationSubring := by
      rw [Valuation.mem_valuationSubring_iff]; exact ha.le
    have hne : ρ ⟨a, hm⟩ ≠ 0 := by
      intro h
      have := (hker _).1 h
      simp [ha] at this
    have h2 : ρ ((⟨a, hm⟩ : v.valuationSubring) ^ N - 1) = 0 := by
      rw [map_sub, map_pow, hpow _ hne, map_one, sub_self]
    have := (hker _).1 h2
    simpa using this
  have hint : ∀ a : C, v a = 1 → (a ^ N - 1) / ϖ ∈ v.valuationSubring := by
    intro a ha
    rw [Valuation.mem_valuationSubring_iff, map_div₀, div_le_one₀ hvpos]
    exact hmax _ (hlt a ha)
  have key : ∀ (a : Cˣ) (y : v.valuationSubring), (y : C) = ((a : C) ^ N - 1) / ϖ → abelian₂ a = ρ y := by
    intro a y hy
    have hm : ((a : C) ^ N - 1) / ϖ ∈ v.valuationSubring := hy ▸ y.2
    simp only [abelian₂, dif_pos hm]
    congr 1
    exact Subtype.ext hy.symm
  have hϖm : ϖ ∈ v.valuationSubring := by
    rw [Valuation.mem_valuationSubring_iff]; exact h1.le
  have hρϖ : ρ ⟨ϖ, hϖm⟩ = 0 := (hker _).2 h1
  refine ⟨abelian₂, ?_, ?_, ?_, ?_⟩
  · intro a b ha hb
    have hbm : (b : C) ^ N - 1 ∈ v.valuationSubring := by
      rw [Valuation.mem_valuationSubring_iff]; exact (hlt _ hb).le
    have hb0 : ρ ⟨_, hbm⟩ = 0 := (hker _).2 (hlt _ hb)
    rw [key a ⟨_, hint _ ha⟩ rfl, key b ⟨_, hint _ hb⟩ rfl,
      key (a * b) (⟨_, hint _ ha⟩ + ⟨_, hint _ hb⟩ + ⟨_, hint _ ha⟩ * ⟨_, hbm⟩) ?_]
    · rw [map_add, map_add, map_mul, hb0, mul_zero, add_zero]
    · push_cast
      field_simp
      ring
  · intro y
    obtain ⟨x, hx⟩ := hsurj (-y)
    have hx1 : v (x : C) ≤ 1 := (Valuation.mem_valuationSubring_iff _ _).1 x.2
    have hz : v (ϖ * x) < 1 := by
      rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_right' hx1) h1
    have ha : v (1 + ϖ * x) = 1 := v.map_one_add_of_lt hz
    have hne : (1 + ϖ * x : C) ≠ 0 := by
      intro h
      rw [h] at ha
      simp at ha
    obtain ⟨r, hr⟩ := one_add_pow_expansion' ((⟨ϖ, hϖm⟩ : v.valuationSubring) * x) N
    have hr' : (1 + ϖ * x : C) ^ N = 1 + N * (ϖ * x) + (ϖ * x) ^ 2 * r := by
      have := congrArg (fun t : v.valuationSubring => (t : C)) hr
      simpa using this
    refine ⟨Units.mk0 _ hne, ha, ?_⟩
    rw [key _ ((N : v.valuationSubring) * x + ⟨ϖ, hϖm⟩ * (x ^ 2 * r)) ?_]
    · rw [map_add, map_mul, map_mul, hρϖ, map_natCast, hNK, hx]; ring
    · rw [Units.val_mk0, hr']
      push_cast
      field_simp
      ring
  · intro a ha
    have ha1 : v (a : C) = 1 := by
      have := v.map_one_add_of_lt (lt_trans ha h1)
      simpa using this
    rw [key a ⟨_, hint _ ha1⟩ rfl, hker]
    have ham : (a : C) ∈ v.valuationSubring := by
      rw [Valuation.mem_valuationSubring_iff]; exact ha1.le
    obtain ⟨s, hs⟩ := sub_one_dvd_pow_sub_one (⟨_, ham⟩ : v.valuationSubring) N
    have hs' : (a : C) ^ N - 1 = ((a : C) - 1) * s := by
      have := congrArg (fun t : v.valuationSubring => (t : C)) hs
      simpa using this
    have hs1 : v (s : C) ≤ 1 := (Valuation.mem_valuationSubring_iff _ _).1 s.2
    show v (((a : C) ^ N - 1) / ϖ) < 1
    rw [map_div₀, div_lt_one₀ hvpos, hs', map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' hs1) ha
  · intro i f hi hv hf a ha
    have hia : v ((Units.map i.toRingHom.toMonoidHom a : Cˣ) : C) = 1 := by
      show v (i a) = 1
      rw [hv, ha]
    rw [key a ⟨_, hint _ ha⟩ rfl, key _ ⟨_, hint _ hia⟩ rfl]
    apply hf
    show ((i a) ^ N - 1) / ϖ = i (((a : C) ^ N - 1) / ϖ)
    rw [map_div₀, map_sub, map_pow, map_one, hi]
