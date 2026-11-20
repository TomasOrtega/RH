import Mathlib

namespace GlobalTheory

/- English proof (translation)
Introduce `K V _ _ _ _ σ h p d θ O L hp hd hθ hσθ hK _ hω hO hherm hdef hL hLO hscale W hW hne`. Use `haveI : Fact p.Prime := ⟨hp⟩`. Establish `hpK : (p : K) ≠ 0` using `by exact_mod_cast hp.ne_zero`. Establish `hpQ : (p : ℚ) ≠ 0` using `by exact_mod_cast hp.ne_zero`. Establish `hp1 : (1 : ℚ) < p` using `by exact_mod_cast hp.one_lt`.

Establish `hθ0 : θ ≠ 0`. Introduce and unpack `rfl`. Establish `: (d : K) = 0` using `by simpa using hθ`. Conclude with `hd.ne_zero (by exact_mod_cast this)`. Establish `hrat : ∀ x : V, ∃ u : ℚ, h x x = (u : K)`.

Introduce `x`. Take `⟨a, b, hab⟩` from `hK (h x x)`. Establish `h1` using `hherm x x`. Rewrite `h1` using `[hab, map_add, map_mul, map_ratCast, map_ratCast, hσθ]`. Establish `h2 : (b : K) * θ = 0`.

Establish `: (2 : K) * ((b : K) * θ) = 0` using `by linear_combination h1`. Simplify using `using this`. Conclude with `⟨a, by rw [hab, h2, add_zero]⟩`. Establish `hnp : padicNorm p (p : ℚ) = (p : ℚ)⁻¹` using `padicNorm.padicNorm_p_of_prime`. Assume the negation of the conclusion as `hcon`.

Use `push_neg at hcon`. Establish `hdiv : ∀ y ∈ L, y ∈ W → h y y / p ∈ O`. Introduce `y hy hyW`. Take `⟨u, hu⟩` from `hrat y`. Establish `h1 : padicNorm p u ≤ 1` using `(hO u).1 (hu ▸ hLO y hy y hy)`.

Establish `h2` using `hcon y hy hyW u hu`. Establish `h3 : ((u / p : ℚ) : K) ∈ O`. Rewrite using `[hO, padicNorm.div, hnp]`. Distinguish the cases in `hu0 : u = 0`. Simplify using `[hu0]`.

Take `⟨z, hz⟩` from `padicNorm.values_discrete (p := p) hu0`. Rewrite `h1`, `h2`, the goal using `[hz]`. Establish `hz0 : -z < 0`. Use `lt_of_le_of_ne h1 h2` as an intermediate fact. Conclude with `(zpow_lt_one_iff_right₀ hp1).1 this`.

Rewrite using `[div_inv_eq_mul, ← zpow_add_one₀ hpQ]`. Conclude with `zpow_le_one_of_nonpos₀ hp1.le (by omega)`. Rewrite using `[hu]`. Simplify using `using h3`. Establish `htr : ∀ x ∈ L, x ∈ W → ∀ y ∈ L, y ∈ W → (h x y + σ (h x y)) / p ∈ O`.

Introduce `x hx hxW y hy hyW`. Establish `h1` using `O.sub_mem (O.sub_mem (hdiv _ (L.add_mem hx hy) (W.add_mem hxW hyW)) (hdiv x hx hxW)) (hdiv y hy hyW)`. Use `h1 using 1` and compare the differences between its conclusion and the goal. Simplify using `only [map_add, LinearMap.add_apply]`. Rewrite using `[← hherm x y]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hstep : ∀ x ∈ L, x ∈ W → (θ / p) • x ∈ L`. Introduce `x hx hxW`. Use `hW _ (W.smul_mem _ hxW) ?_` and prove the remaining obligations. Introduce `y hy hyW`.

Establish `r1` using `htr x hx hxW y hy hyW`. Establish `r2` using `htr _ (hL _ hω x hx) (W.smul_mem _ hxW) y hy hyW`. Establish `h1` using `O.add_mem r2 (O.mul_mem (O.sub_mem hω O.one_mem) r1)`. Use `h1 using 1` and compare the differences between its conclusion and the goal. Simplify using `only [map_smul, LinearMap.smul_apply, smul_eq_mul, map_mul, map_div₀, map_add, map_one, hσθ, map_ofNat]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Take `⟨x, hxW, hx0⟩` from `hne`. Take `⟨m, hm⟩` from `hscale x`. Use `set x0 := (p : K) ^ m • x with hx0def`.

Establish `hx0W : x0 ∈ W` using `W.smul_mem _ hxW`. Establish `hx00 : x0 ≠ 0` using `smul_ne_zero (pow_ne_zero _ hpK) hx0`. Establish `hiter : ∀ k : ℕ, (θ / p) ^ k • x0 ∈ L`. Introduce `k`. Proceed by induction on `k with`.

Consider the case `zero => simpa using hm`. Consider the case `succ k ih`. Rewrite using `[pow_succ', mul_smul]`. Conclude with `hstep _ ih (W.smul_mem _ hx0W)`. Take `⟨u, hu⟩` from `hrat x0`.

Establish `hu0 : u ≠ 0`. Introduce and unpack `rfl`. Conclude with `hx00 (hdef _ (by simpa using hu))`. Establish `hupos : 0 < padicNorm p u` using `lt_of_le_of_ne (padicNorm.nonneg _) (padicNorm.nonzero hu0).symm`. Establish `hnd : (p : ℚ)⁻¹ ≤ padicNorm p (d : ℚ)`.

Distinguish the cases in `hpd : p = d`. Rewrite using `[← hpd, hnp]`. Use `haveI : Fact d.Prime := ⟨hd⟩`. Rewrite using `[padicNorm.padicNorm_of_prime_of_ne hpd]`. Conclude with `inv_le_one_of_one_le₀ hp1.le`.

Establish `hc : (p : ℚ) ≤ padicNorm p ((d : ℚ) / (p * p))`. Rewrite using `[padicNorm.div, padicNorm.mul, hnp, le_div_iff₀ (by positivity)]`. Combine the equalities or inequalities in the displayed calculation. Establish `hpow : ∀ (q : ℚ) (k : ℕ), padicNorm p (q ^ k) = padicNorm p q ^ k`. Introduce `q k`.

Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih => rw [pow_succ, pow_succ, padicNorm.mul, ih]`. Establish `hbound : ∀ k : ℕ, (p : ℚ) ^ k * padicNorm p u ≤ 1`. Introduce `k`.

Establish `h1` using `hLO _ (hiter k) _ (hiter k)`. Establish `h2 : h ((θ / p) ^ k • x0) ((θ / p) ^ k • x0) = ((((d : ℚ) / (p * p)) ^ k * u : ℚ) : K)`. Rewrite using `[h.map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, hu, smul_eq_mul, smul_eq_mul, map_pow, map_div₀, hσθ, map_natCast, ← mul_assoc, ← mul_pow]`. Use `push_cast`. Use `congr 2`.

Clear the denominators using the available nonvanishing facts. Take the linear combination `-hθ`. Rewrite `h1` using `[h2, hO, padicNorm.mul, hpow]`. Use `le_trans ?_ h1` and prove the remaining obligations. Use `gcongr`.

Take `⟨k, hk⟩` from `pow_unbounded_of_one_lt (padicNorm p u)⁻¹ hp1`. Use `hbound k` as an intermediate fact. Rewrite `hk` using `[inv_lt_iff_one_lt_mul₀ hupos]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem exists_unit_norm_of_selfDual_hermitian_lattice :
    ∀ (K V : Type) [Field K] [CharZero K] [AddCommGroup V] [Module K V] (σ : K →+* K) (h : V →ₗ[K] V →ₛₗ[σ] K) (p d : ℕ) (θ : K) (O : Subring K) (L : AddSubgroup V), p.Prime → d.Prime → θ ^ 2 = -(d : K) → σ θ = -θ → (∀ x : K, ∃ a b : ℚ, x = (a : K) + (b : K) * θ) → (∀ x ∈ O, σ x ∈ O) → (1 + θ) / 2 ∈ O → (∀ r : ℚ, (r : K) ∈ O ↔ padicNorm p r ≤ 1) → (∀ x y : V, h y x = σ (h x y)) → (∀ x : V, h x x = 0 → x = 0) → (∀ a ∈ O, ∀ x ∈ L, a • x ∈ L) → (∀ x ∈ L, ∀ y ∈ L, h x y ∈ O) → (∀ x : V, ∃ m : ℕ, (p : K) ^ m • x ∈ L) → ∀ W : Submodule K V, (∀ x ∈ W, (∀ y ∈ L, y ∈ W → h x y ∈ O) → x ∈ L) → (∃ x ∈ W, x ≠ 0) → ∃ y ∈ L, y ∈ W ∧ ∃ u : ℚ, h y y = (u : K) ∧ padicNorm p u = 1 := by
  intro K V _ _ _ _ σ h p d θ O L hp hd hθ hσθ hK _ hω hO hherm hdef hL hLO hscale W hW hne
  haveI : Fact p.Prime := ⟨hp⟩
  have hpK : (p : K) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp1 : (1 : ℚ) < p := by exact_mod_cast hp.one_lt
  have hθ0 : θ ≠ 0 := by
    rintro rfl
    have : (d : K) = 0 := by simpa using hθ
    exact hd.ne_zero (by exact_mod_cast this)

  have hrat : ∀ x : V, ∃ u : ℚ, h x x = (u : K) := by
    intro x
    obtain ⟨a, b, hab⟩ := hK (h x x)
    have h1 := hherm x x
    rw [hab, map_add, map_mul, map_ratCast, map_ratCast, hσθ] at h1
    have h2 : (b : K) * θ = 0 := by
      have : (2 : K) * ((b : K) * θ) = 0 := by linear_combination h1
      simpa using this
    exact ⟨a, by rw [hab, h2, add_zero]⟩
  have hnp : padicNorm p (p : ℚ) = (p : ℚ)⁻¹ := padicNorm.padicNorm_p_of_prime
  by_contra hcon
  push_neg at hcon
  have hdiv : ∀ y ∈ L, y ∈ W → h y y / p ∈ O := by
    intro y hy hyW
    obtain ⟨u, hu⟩ := hrat y
    have h1 : padicNorm p u ≤ 1 := (hO u).1 (hu ▸ hLO y hy y hy)
    have h2 := hcon y hy hyW u hu
    have h3 : ((u / p : ℚ) : K) ∈ O := by
      rw [hO, padicNorm.div, hnp]
      by_cases hu0 : u = 0
      · simp [hu0]
      obtain ⟨z, hz⟩ := padicNorm.values_discrete (p := p) hu0
      rw [hz] at h1 h2 ⊢
      have hz0 : -z < 0 := by
        have := lt_of_le_of_ne h1 h2
        exact (zpow_lt_one_iff_right₀ hp1).1 this
      rw [div_inv_eq_mul, ← zpow_add_one₀ hpQ]
      exact zpow_le_one_of_nonpos₀ hp1.le (by omega)
    rw [hu]
    simpa using h3
  have htr : ∀ x ∈ L, x ∈ W → ∀ y ∈ L, y ∈ W → (h x y + σ (h x y)) / p ∈ O := by
    intro x hx hxW y hy hyW
    have h1 := O.sub_mem (O.sub_mem (hdiv _ (L.add_mem hx hy) (W.add_mem hxW hyW)) (hdiv x hx hxW))
      (hdiv y hy hyW)
    convert h1 using 1
    simp only [map_add, LinearMap.add_apply]
    rw [← hherm x y]
    ring
  have hstep : ∀ x ∈ L, x ∈ W → (θ / p) • x ∈ L := by
    intro x hx hxW
    refine hW _ (W.smul_mem _ hxW) ?_
    intro y hy hyW
    have r1 := htr x hx hxW y hy hyW
    have r2 := htr _ (hL _ hω x hx) (W.smul_mem _ hxW) y hy hyW
    have h1 := O.add_mem r2 (O.mul_mem (O.sub_mem hω O.one_mem) r1)
    convert h1 using 1
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, map_mul, map_div₀, map_add, map_one,
      hσθ, map_ofNat]
    field_simp
    ring
  obtain ⟨x, hxW, hx0⟩ := hne
  obtain ⟨m, hm⟩ := hscale x
  set x0 := (p : K) ^ m • x with hx0def
  have hx0W : x0 ∈ W := W.smul_mem _ hxW
  have hx00 : x0 ≠ 0 := smul_ne_zero (pow_ne_zero _ hpK) hx0
  have hiter : ∀ k : ℕ, (θ / p) ^ k • x0 ∈ L := by
    intro k
    induction k with
    | zero => simpa using hm
    | succ k ih =>
      rw [pow_succ', mul_smul]
      exact hstep _ ih (W.smul_mem _ hx0W)
  obtain ⟨u, hu⟩ := hrat x0
  have hu0 : u ≠ 0 := by
    rintro rfl
    exact hx00 (hdef _ (by simpa using hu))
  have hupos : 0 < padicNorm p u :=
    lt_of_le_of_ne (padicNorm.nonneg _) (padicNorm.nonzero hu0).symm
  have hnd : (p : ℚ)⁻¹ ≤ padicNorm p (d : ℚ) := by
    by_cases hpd : p = d
    · rw [← hpd, hnp]
    · haveI : Fact d.Prime := ⟨hd⟩
      rw [padicNorm.padicNorm_of_prime_of_ne hpd]
      exact inv_le_one_of_one_le₀ hp1.le
  have hc : (p : ℚ) ≤ padicNorm p ((d : ℚ) / (p * p)) := by
    rw [padicNorm.div, padicNorm.mul, hnp, le_div_iff₀ (by positivity)]
    calc (p : ℚ) * ((p : ℚ)⁻¹ * (p : ℚ)⁻¹) = (p : ℚ)⁻¹ := by field_simp
      _ ≤ _ := hnd
  have hpow : ∀ (q : ℚ) (k : ℕ), padicNorm p (q ^ k) = padicNorm p q ^ k := by
    intro q k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, pow_succ, padicNorm.mul, ih]
  have hbound : ∀ k : ℕ, (p : ℚ) ^ k * padicNorm p u ≤ 1 := by
    intro k
    have h1 := hLO _ (hiter k) _ (hiter k)
    have h2 : h ((θ / p) ^ k • x0) ((θ / p) ^ k • x0) = ((((d : ℚ) / (p * p)) ^ k * u : ℚ) : K) := by
      rw [h.map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, hu, smul_eq_mul, smul_eq_mul,
        map_pow, map_div₀, hσθ, map_natCast, ← mul_assoc, ← mul_pow]
      push_cast
      congr 2
      field_simp
      linear_combination -hθ
    rw [h2, hO, padicNorm.mul, hpow] at h1
    refine le_trans ?_ h1
    gcongr
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (padicNorm p u)⁻¹ hp1
  have := hbound k
  rw [inv_lt_iff_one_lt_mul₀ hupos] at hk
  linarith

end GlobalTheory
