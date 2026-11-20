import Mathlib

namespace GlobalTheory

/- English proof (translation)
Establish `hp0 : (p : ℚ) ≠ 0` using `by exact_mod_cast hp.out.ne_zero`. Establish `hp1 : (1 : ℚ) < p` using `by exact_mod_cast hp.out.one_lt`. Establish `hpt : (p : ℚ) * t ^ 2 ≠ 0` using `mul_ne_zero hp0 (pow_ne_zero _ ht)`. Distinguish the cases in `hs : s = 0`. Substitute `hs` using the available equality.

Introduce `h`. Simplify using `only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, padicNorm.zero] at h`. Conclude with `padicNorm.nonzero hpt h.symm`. Introduce `h`. Rewrite `h` using `[padicNorm.eq_zpow_of_nonzero (pow_ne_zero _ hs), padicNorm.eq_zpow_of_nonzero hpt, padicValRat.mul hp0 (pow_ne_zero _ ht), padicValRat.pow s, padicValRat.pow t, padicValRat.self hp.out.one_lt]`.

Use `zpow_right_injective₀ (by linarith) hp1.ne' h` as an intermediate fact. Move the coercions through the operations in `at this`. Use linear arithmetic over natural numbers and integers.
-/
theorem padicNorm_prime_mul_sq_ne_sq (p : ℕ) [hp : Fact p.Prime] (s t : ℚ) (ht : t ≠ 0) :
    padicNorm p (s ^ 2) ≠ padicNorm p ((p : ℚ) * t ^ 2) := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hp1 : (1 : ℚ) < p := by exact_mod_cast hp.out.one_lt
  have hpt : (p : ℚ) * t ^ 2 ≠ 0 := mul_ne_zero hp0 (pow_ne_zero _ ht)
  by_cases hs : s = 0
  · subst hs
    intro h
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, padicNorm.zero] at h
    exact padicNorm.nonzero hpt h.symm
  · intro h
    rw [padicNorm.eq_zpow_of_nonzero (pow_ne_zero _ hs), padicNorm.eq_zpow_of_nonzero hpt,
      padicValRat.mul hp0 (pow_ne_zero _ ht), padicValRat.pow s, padicValRat.pow t,
      padicValRat.self hp.out.one_lt] at h
    have := zpow_right_injective₀ (by linarith) hp1.ne' h
    push_cast at this
    omega

/- English proof (translation)
Establish `key : padicNorm p (s ^ 2) ≤ 1 ∧ padicNorm p ((p : ℚ) * t ^ 2) < 1`. Distinguish the cases in `ht : t = 0`. Substitute `ht` using the available equality. Simplify using `at h ⊢`. Conclude with `h.le`.

Rewrite `h` using `[padicNorm.add_eq_max_of_ne (padicNorm_prime_mul_sq_ne_sq p s t ht)]`. Establish `h1` using `padicNorm_prime_mul_sq_ne_sq p 1 t ht`. Rewrite `h1` using `[one_pow, padicNorm.one]`. Conclude with `⟨h ▸ le_max_left _ _, lt_of_le_of_ne (h ▸ le_max_right _ _) h1.symm⟩`. Use `⟨?_, key.2⟩` and prove the remaining obligations.

Establish `h1` using `key.1`. Rewrite `h1` using `[sq, padicNorm.mul]`. Use `padicNorm.nonneg (p := p) s` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem padicNorm_of_sq_add_prime_mul_sq (p : ℕ) [hp : Fact p.Prime] (s t : ℚ)
    (h : padicNorm p (s ^ 2 + (p : ℚ) * t ^ 2) = 1) :
    padicNorm p s ≤ 1 ∧ padicNorm p ((p : ℚ) * t ^ 2) < 1 := by
  have key : padicNorm p (s ^ 2) ≤ 1 ∧ padicNorm p ((p : ℚ) * t ^ 2) < 1 := by
    by_cases ht : t = 0
    · subst ht
      simp at h ⊢
      exact h.le
    · rw [padicNorm.add_eq_max_of_ne (padicNorm_prime_mul_sq_ne_sq p s t ht)] at h
      have h1 := padicNorm_prime_mul_sq_ne_sq p 1 t ht
      rw [one_pow, padicNorm.one] at h1
      exact ⟨h ▸ le_max_left _ _, lt_of_le_of_ne (h ▸ le_max_right _ _) h1.symm⟩
  refine ⟨?_, key.2⟩
  have h1 := key.1
  rw [sq, padicNorm.mul] at h1
  have := padicNorm.nonneg (p := p) s
  nlinarith

/- English proof (translation)
Introduce `K V _ _ _ _ σ h p d θ O L hp hd hθ hσθ hK hσO hω hO hh hdef hL hLO hbig hab hun W hW ⟨e, heW, he⟩`. Use `haveI : Fact p.Prime := ⟨hp⟩`. Establish `he0 : e ≠ 0`. Introduce and unpack `rfl`. Simplify using `at he`.

Take `⟨y1, hy1L, hy1W, u1, hu1, hu1n⟩` from `hun W hW ⟨e, heW, he0⟩`. Establish `hu10 : u1 ≠ 0`. Introduce and unpack `rfl`. Simplify using `at hu1n`. Establish `hu10K : (u1 : K) ≠ 0` using `by exact_mod_cast hu10`.

Establish `hinv : (u1 : K)⁻¹ ∈ O`. Establish `: ((u1⁻¹ : ℚ) : K) ∈ O`. Rewrite using `[hO, ← one_div, padicNorm.div, hu1n]`. Simplify using the standard rewrite rules. Simplify using `using this`.

Establish `hθO : θ ∈ O`. Establish `h2 : θ = (1 + θ) / 2 + (1 + θ) / 2 - 1` using `by ring`. Rewrite using `[h2]`. Conclude with `O.sub_mem (O.add_mem hω hω) O.one_mem`. Establish `hperp : ∀ y : V, h (y - (h y y1 * (u1 : K)⁻¹) • y1) y1 = 0`.

Introduce `y`. Simplify using `only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hu1]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `hnorm : ∀ s t : ℚ, h (((s : K) + (t : K) * θ) • y1) (((s : K) + (t : K) * θ) • y1) = (((s ^ 2 + (d : ℚ) * t ^ 2) * u1 : ℚ) : K)`.

Introduce `s t`. Simplify using `only [map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_eq_mul, hu1, map_add, map_mul, map_ratCast, hσθ]`. Use `push_cast`. Take the linear combination `(-(t : K) ^ 2 * (u1 : K)) * hθ`. Use `set W' : Submodule K V := W ⊓ LinearMap.ker (h.flip y1) with hW'`.

Establish `hmem : ∀ x, x ∈ W' ↔ x ∈ W ∧ h x y1 = 0`. Introduce `x`. Simplify using `[hW']`. Distinguish the cases in `hne : ∃ x ∈ W', x ≠ 0`. Establish `hsd : ∀ x ∈ W', (∀ y ∈ L, y ∈ W' → h x y ∈ O) → x ∈ L`.

Introduce `x hx hxO`. Take `⟨hxW, hx1⟩` from `(hmem x).1 hx`. Use `hW x hxW fun y hyL hyW => ?_` and prove the remaining obligations. Use `hxO (y - (h y y1 * (u1 : K)⁻¹) • y1) (L.sub_mem hyL (hL _ (O.mul_mem (hLO _ hyL _ hy1L) hinv) _ hy1L)) ((hmem _).2 ⟨W.sub_mem hyW (W.smul_mem _ hy1W), hperp y⟩)` as an intermediate fact. Simplify `this` using `[map_sub, LinearMap.map_smulₛₗ, hx1]`.

Take `⟨y2, hy2L, hy2W', u2, hu2, hu2n⟩` from `hun W' hsd hne`. Take `⟨hy2W, h21⟩` from `(hmem y2).1 hy2W'`. Establish `h12 : h y1 y2 = 0` using `by rw [hh, h21, map_zero]`. Take `⟨a, b, hab'⟩` from `hab u1 u2 hu1n hu2n`. Use `⟨(a : K) • y1 + (b : K) • y2, L.add_mem (hL _ (intCast_mem O a) _ hy1L) (hL _ (intCast_mem O b) _ hy2L), W.add_mem (W.smul_mem _ hy1W) (W.smul_mem _ hy2W), _, ?_, hab'⟩` and prove the remaining obligations.

Simplify using `only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_eq_mul, hu1, hu2, h12, h21, map_intCast]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Distinguish the cases in `hpd : p = d`. Substitute `hpd` using the available equality.

Establish `h0 : e - (h e y1 * (u1 : K)⁻¹) • y1 = 0`. Assume the negation of the conclusion as `hc`. Conclude with `hne ⟨_, (hmem _).2 ⟨W.sub_mem heW (W.smul_mem _ hy1W), hperp e⟩, hc⟩`. Take `⟨s, t, hst⟩` from `hK (h e y1 * (u1 : K)⁻¹)`. Rewrite `h0` using `[hst, sub_eq_zero]`.

Establish `h1` using `hnorm s t`. Rewrite `h1` using `[← h0, he]`. Establish `h2 : (s ^ 2 + (p : ℚ) * t ^ 2) * u1 = 1` using `by exact_mod_cast h1.symm`. Establish `h3 : padicNorm p (s ^ 2 + (p : ℚ) * t ^ 2) = 1`. Use `congrArg (padicNorm p) h2` as an intermediate fact.

Rewrite `this` using `[padicNorm.mul, hu1n, mul_one, padicNorm.one]`. Then use the resulting hypothesis. Take `⟨hs, ht⟩` from `padicNorm_of_sq_add_prime_mul_sq p s t h3`. Establish `h4` using `hnorm s 0`. Use `⟨_, hL _ ?_ _ hy1L, W.smul_mem _ hy1W, _, h4, ?_⟩` and prove the remaining obligations. Simplify using `using (hO s).2 hs`.

Establish `: (s ^ 2 + (p : ℚ) * 0 ^ 2) * u1 - 1 = -((p : ℚ) * t ^ 2 * u1)`. Take the linear combination `h2`. Rewrite using `[this, padicNorm.neg, padicNorm.mul, hu1n, mul_one]`. Conclude with `ht`. Use `haveI : Fact d.Prime := ⟨hd⟩`.

Establish `hdn : padicNorm p (d : ℚ) = 1` using `padicNorm.padicNorm_of_prime_of_ne hpd`. Take `⟨a, b, hab'⟩` from `hab u1 (u1 * d) hu1n (by rw [padicNorm.mul, hu1n, hdn, mul_one])`. Establish `h4` using `hnorm a b`. Use `⟨_, hL _ ?_ _ hy1L, W.smul_mem _ hy1W, _, h4, ?_⟩` and prove the remaining obligations. Use `push_cast`.

Conclude with `O.add_mem (intCast_mem O a) (O.mul_mem (intCast_mem O b) hθO)`. Use `hab' using 2` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree.
-/
theorem selfDual_lattice_exists_norm_one_mod :
    ∀ (K V : Type) [Field K] [CharZero K] [AddCommGroup V] [Module K V] (σ : K →+* K) (h : V →ₗ[K] V →ₛₗ[σ] K) (p d : ℕ) (θ : K) (O : Subring K) (L : AddSubgroup V), p.Prime → d.Prime → θ ^ 2 = -(d : K) → σ θ = -θ → (∀ x : K, ∃ a b : ℚ, x = (a : K) + (b : K) * θ) → (∀ x ∈ O, σ x ∈ O) → (1 + θ) / 2 ∈ O → (∀ r : ℚ, (r : K) ∈ O ↔ padicNorm p r ≤ 1) → (∀ x y : V, h y x = σ (h x y)) → (∀ x : V, h x x = 0 → x = 0) → (∀ a ∈ O, ∀ x ∈ L, a • x ∈ L) → (∀ x ∈ L, ∀ y ∈ L, h x y ∈ O) → (∀ x : V, ∃ m : ℕ, (p : K) ^ m • x ∈ L) → (∀ u v : ℚ, padicNorm p u = 1 → padicNorm p v = 1 → ∃ a b : ℤ, padicNorm p (u * (a : ℚ) ^ 2 + v * (b : ℚ) ^ 2 - 1) < 1) → (∀ W : Submodule K V, (∀ x ∈ W, (∀ y ∈ L, y ∈ W → h x y ∈ O) → x ∈ L) → (∃ x ∈ W, x ≠ 0) → ∃ y ∈ L, y ∈ W ∧ ∃ u : ℚ, h y y = (u : K) ∧ padicNorm p u = 1) → ∀ W : Submodule K V, (∀ x ∈ W, (∀ y ∈ L, y ∈ W → h x y ∈ O) → x ∈ L) → (∃ e ∈ W, h e e = 1) → ∃ y ∈ L, y ∈ W ∧ ∃ u : ℚ, h y y = (u : K) ∧ padicNorm p (u - 1) < 1 := by
  intro K V _ _ _ _ σ h p d θ O L hp hd hθ hσθ hK hσO hω hO hh hdef hL hLO hbig hab hun W hW
    ⟨e, heW, he⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have he0 : e ≠ 0 := by
    rintro rfl
    simp at he
  obtain ⟨y1, hy1L, hy1W, u1, hu1, hu1n⟩ := hun W hW ⟨e, heW, he0⟩
  have hu10 : u1 ≠ 0 := by
    rintro rfl
    simp at hu1n
  have hu10K : (u1 : K) ≠ 0 := by exact_mod_cast hu10
  have hinv : (u1 : K)⁻¹ ∈ O := by
    have : ((u1⁻¹ : ℚ) : K) ∈ O := by
      rw [hO, ← one_div, padicNorm.div, hu1n]
      simp
    simpa using this
  have hθO : θ ∈ O := by
    have h2 : θ = (1 + θ) / 2 + (1 + θ) / 2 - 1 := by ring
    rw [h2]
    exact O.sub_mem (O.add_mem hω hω) O.one_mem
  have hperp : ∀ y : V, h (y - (h y y1 * (u1 : K)⁻¹) • y1) y1 = 0 := by
    intro y
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hu1]
    field_simp
    ring
  have hnorm : ∀ s t : ℚ, h (((s : K) + (t : K) * θ) • y1) (((s : K) + (t : K) * θ) • y1)
      = (((s ^ 2 + (d : ℚ) * t ^ 2) * u1 : ℚ) : K) := by
    intro s t
    simp only [map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_eq_mul, hu1, map_add,
      map_mul, map_ratCast, hσθ]
    push_cast
    linear_combination (-(t : K) ^ 2 * (u1 : K)) * hθ
  set W' : Submodule K V := W ⊓ LinearMap.ker (h.flip y1) with hW'
  have hmem : ∀ x, x ∈ W' ↔ x ∈ W ∧ h x y1 = 0 := by
    intro x
    simp [hW']
  by_cases hne : ∃ x ∈ W', x ≠ 0
  · have hsd : ∀ x ∈ W', (∀ y ∈ L, y ∈ W' → h x y ∈ O) → x ∈ L := by
      intro x hx hxO
      obtain ⟨hxW, hx1⟩ := (hmem x).1 hx
      refine hW x hxW fun y hyL hyW => ?_
      have := hxO (y - (h y y1 * (u1 : K)⁻¹) • y1)
        (L.sub_mem hyL (hL _ (O.mul_mem (hLO _ hyL _ hy1L) hinv) _ hy1L))
        ((hmem _).2 ⟨W.sub_mem hyW (W.smul_mem _ hy1W), hperp y⟩)
      simpa [map_sub, LinearMap.map_smulₛₗ, hx1] using this
    obtain ⟨y2, hy2L, hy2W', u2, hu2, hu2n⟩ := hun W' hsd hne
    obtain ⟨hy2W, h21⟩ := (hmem y2).1 hy2W'
    have h12 : h y1 y2 = 0 := by rw [hh, h21, map_zero]
    obtain ⟨a, b, hab'⟩ := hab u1 u2 hu1n hu2n
    refine ⟨(a : K) • y1 + (b : K) • y2,
      L.add_mem (hL _ (intCast_mem O a) _ hy1L) (hL _ (intCast_mem O b) _ hy2L),
      W.add_mem (W.smul_mem _ hy1W) (W.smul_mem _ hy2W), _, ?_, hab'⟩
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      LinearMap.map_smulₛₗ, smul_eq_mul, hu1, hu2, h12, h21, map_intCast]
    push_cast
    ring
  · by_cases hpd : p = d
    · subst hpd
      have h0 : e - (h e y1 * (u1 : K)⁻¹) • y1 = 0 := by
        by_contra hc
        exact hne ⟨_, (hmem _).2 ⟨W.sub_mem heW (W.smul_mem _ hy1W), hperp e⟩, hc⟩
      obtain ⟨s, t, hst⟩ := hK (h e y1 * (u1 : K)⁻¹)
      rw [hst, sub_eq_zero] at h0
      have h1 := hnorm s t
      rw [← h0, he] at h1
      have h2 : (s ^ 2 + (p : ℚ) * t ^ 2) * u1 = 1 := by exact_mod_cast h1.symm
      have h3 : padicNorm p (s ^ 2 + (p : ℚ) * t ^ 2) = 1 := by
        have := congrArg (padicNorm p) h2
        rwa [padicNorm.mul, hu1n, mul_one, padicNorm.one] at this
      obtain ⟨hs, ht⟩ := padicNorm_of_sq_add_prime_mul_sq p s t h3
      have h4 := hnorm s 0
      refine ⟨_, hL _ ?_ _ hy1L, W.smul_mem _ hy1W, _, h4, ?_⟩
      · simpa using (hO s).2 hs
      · have : (s ^ 2 + (p : ℚ) * 0 ^ 2) * u1 - 1 = -((p : ℚ) * t ^ 2 * u1) := by
          linear_combination h2
        rw [this, padicNorm.neg, padicNorm.mul, hu1n, mul_one]
        exact ht
    · haveI : Fact d.Prime := ⟨hd⟩
      have hdn : padicNorm p (d : ℚ) = 1 := padicNorm.padicNorm_of_prime_of_ne hpd
      obtain ⟨a, b, hab'⟩ := hab u1 (u1 * d) hu1n (by rw [padicNorm.mul, hu1n, hdn, mul_one])
      have h4 := hnorm a b
      refine ⟨_, hL _ ?_ _ hy1L, W.smul_mem _ hy1W, _, h4, ?_⟩
      · push_cast
        exact O.add_mem (intCast_mem O a) (O.mul_mem (intCast_mem O b) hθO)
      · convert hab' using 2
        ring

end GlobalTheory
