import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PresDefs

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

/- English proof (translation)
Introduce `h2`. Establish `h3 : ((2 : ℕ) : k) = 0` using `by simpa using h2`. Rewrite `h3` using `[CharP.cast_eq_zero_iff k l]`. Conclude with `h ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 h3)`.
-/
private theorem two_ne {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] (h : l ≠ 2) : (2 : k) ≠ 0 := by
  intro h2
  have h3 : ((2 : ℕ) : k) = 0 := by simpa using h2
  rw [CharP.cast_eq_zero_iff k l] at h3
  exact h ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 h3)

/- English proof (translation)
Establish `h0 : (t : k) ≠ 0` using `t.ne_zero`. Establish `h1 : (t : k) ≠ 1` using `fun e => h (by ext; simp [e])`. Use `⟨fun e => h ?_, h1, fun e => h1 (inv_eq_one.1 e)⟩` and prove the remaining obligations. Use `ext`. Rewrite using `[Units.val_pow_eq_pow_val, sq, Units.val_one]`.

Use `nth_rewrite 2 [e]`. Conclude with `mul_inv_cancel₀ h0`.
-/
private theorem sq_facts {k : Type} [Field k] {t : kˣ} (h : t ^ 2 ≠ 1) :
    (t : k) ≠ (t : k)⁻¹ ∧ (t : k) ≠ 1 ∧ (t : k)⁻¹ ≠ 1 := by
  have h0 : (t : k) ≠ 0 := t.ne_zero
  have h1 : (t : k) ≠ 1 := fun e => h (by ext; simp [e])
  refine ⟨fun e => h ?_, h1, fun e => h1 (inv_eq_one.1 e)⟩
  ext
  rw [Units.val_pow_eq_pow_val, sq, Units.val_one]
  nth_rewrite 2 [e]
  exact mul_inv_cancel₀ h0

/- English proof (translation)
Take `⟨a, b, c⟩` from `sq_facts h`. Apply the tactic sequence `rcases hn with rfl | rfl <;> fin_cases i <;> fin_cases j <;> first`. Consider the case `exact absurd rfl hij`. Consider the case `simp [w, a, b, c, a.symm, b.symm, c.symm]`.
-/
private theorem pow_inj {k : Type} [Field k] {t : kˣ} (h : t ^ 2 ≠ 1) {n : ℕ} (hn : n = 2 ∨ n = 3)
    (i j : Fin n) (hij : i ≠ j) : ((t ^ w n i : kˣ) : k) ≠ ((t ^ w n j : kˣ) : k) := by
  obtain ⟨a, b, c⟩ := sq_facts h
  rcases hn with rfl | rfl <;> fin_cases i <;> fin_cases j <;>
    first
    | exact absurd rfl hij
    | simp [w, a, b, c, a.symm, b.symm, c.symm]

/- English proof (translation)
Take `⟨a, -, -⟩` from `sq_facts h`. Establish `b : (t : k) - (t : k)⁻¹ ≠ 0` using `sub_ne_zero.2 a`. Establish `c : (t : k)⁻¹ - (t : k) ≠ 0` using `sub_ne_zero.2 a.symm`. Establish `d : (t : k) - (t : k)⁻¹ ≠ (t : k)⁻¹ - (t : k)` using `fun e => mul_ne_zero h2 b (by linear_combination e)`. Apply the tactic sequence `rcases hn with rfl | rfl <;> fin_cases i <;> fin_cases j <;> first`.

Consider the case `exact absurd rfl hij`. Consider the case `simp [w, b, c, d, b.symm, c.symm, d.symm]`.
-/
private theorem diff_inj {k : Type} [Field k] (h2 : (2 : k) ≠ 0) {t : kˣ} (h : t ^ 2 ≠ 1) {n : ℕ}
    (hn : n = 2 ∨ n = 3) (i j : Fin n) (hij : i ≠ j) :
    ((t ^ w n i : kˣ) : k) - ((t⁻¹ ^ w n i : kˣ) : k) ≠ ((t ^ w n j : kˣ) : k) - ((t⁻¹ ^ w n j : kˣ) : k) := by
  obtain ⟨a, -, -⟩ := sq_facts h
  have b : (t : k) - (t : k)⁻¹ ≠ 0 := sub_ne_zero.2 a
  have c : (t : k)⁻¹ - (t : k) ≠ 0 := sub_ne_zero.2 a.symm
  have d : (t : k) - (t : k)⁻¹ ≠ (t : k)⁻¹ - (t : k) := fun e =>
    mul_ne_zero h2 b (by linear_combination e)
  rcases hn with rfl | rfl <;> fin_cases i <;> fin_cases j <;>
    first
    | exact absurd rfl hij
    | simp [w, b, c, d, b.symm, c.symm, d.symm]

/- English proof (translation)
Introduce `l _ k _ _ F C₀ n hF hn K _ φ ρ hρ`. Establish `h2 : (2 : k) ≠ 0` using `two_ne hF.l_odd`. Establish `hs : F.Ψ (F.star F.g0) = (F.Ψ F.g0)⁻¹`. Establish `e : ((F.star F.g0 : F.G0) : F.Γ) = F.c * (F.g0 : F.Γ)⁻¹ * F.c⁻¹` using `rfl`. Rewrite using `[e, map_mul, map_mul, map_inv, map_inv, hF.Ψ_c]`.

Simplify using the standard rewrite rules. Use `⟨⟨?_, fun i j hij => ?_, fun v => ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Use `(map_ne_zero φ).2 h2` as an intermediate fact. Rewrite `this` using `[map_ofNat]`. Then use the resulting hypothesis. Rewrite using `[Matrix.sub_apply, Matrix.sub_apply, hρ.1, hρ.1, hρ.1, hρ.1, hs, ← map_sub, ← map_sub]`.

Conclude with `fun e => diff_inj h2 hF.baseSubgroup_spec hn i j hij (φ.injective e)`. Take `⟨s, hs⟩` from `hF.f3 v`. Use `⟨s, fun i j hij e => pow_inj hs hn i j hij (φ.injective ?_)⟩` and prove the remaining obligations. Rewrite using `[← hρ.2, ← hρ.2, e]`. Introduce `e`.

Break down `hn with rfl | rfl` into its components or cases. Use `congrFun (congrFun e 0) 0` as an intermediate fact. Simplify using `[lieT, w] at this`. Use `congrFun (congrFun e 0) 0` as an intermediate fact. Simplify using `[lieT, w] at this`.

Break down `hn with rfl | rfl` into its components or cases. Apply the tactic sequence `ext i j fin_cases i <;> fin_cases j <;>`. Apply the tactic sequence `simp [thetaLie, lieT, w, Matrix.mul_apply, Fin.sum_univ_two, Jmat, Matrix.diagonal, Fin.rev] <;> norm_num`. Apply the tactic sequence `ext i j fin_cases i <;> fin_cases j <;>`. Apply the tactic sequence `simp [thetaLie, lieT, w, Matrix.mul_apply, Fin.sum_univ_three, Jmat, Matrix.diagonal, Fin.rev] <;> norm_num`.
-/
theorem UpperTheory.V.Fr.pr_good :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ (K : Type) [Field K] (φ : k →+* K) (ρ : NRep F n K), ρ.IsBar φ → ρ.Good ∧ lieT K n ≠ 0 ∧ thetaLie (lieT K n) = lieT K n := by
  intro l _ k _ _ F C₀ n hF hn K _ φ ρ hρ
  have h2 : (2 : k) ≠ 0 := two_ne hF.l_odd
  have hs : F.Ψ (F.star F.g0) = (F.Ψ F.g0)⁻¹ := by
    have e : ((F.star F.g0 : F.G0) : F.Γ) = F.c * (F.g0 : F.Γ)⁻¹ * F.c⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv, map_inv, hF.Ψ_c]
    simp
  refine ⟨⟨?_, fun i j hij => ?_, fun v => ?_⟩, ?_, ?_⟩
  · have := (map_ne_zero φ).2 h2
    rwa [map_ofNat] at this
  · rw [Matrix.sub_apply, Matrix.sub_apply, hρ.1, hρ.1, hρ.1, hρ.1, hs, ← map_sub, ← map_sub]
    exact fun e => diff_inj h2 hF.baseSubgroup_spec hn i j hij (φ.injective e)
  · obtain ⟨s, hs⟩ := hF.f3 v
    refine ⟨s, fun i j hij e => pow_inj hs hn i j hij (φ.injective ?_)⟩
    rw [← hρ.2, ← hρ.2, e]
  · intro e
    rcases hn with rfl | rfl
    · have := congrFun (congrFun e 0) 0
      simp [lieT, w] at this
    · have := congrFun (congrFun e 0) 0
      simp [lieT, w] at this
  · rcases hn with rfl | rfl
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [thetaLie, lieT, w, Matrix.mul_apply, Fin.sum_univ_two, Jmat, Matrix.diagonal, Fin.rev] <;> norm_num
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [thetaLie, lieT, w, Matrix.mul_apply, Fin.sum_univ_three, Jmat, Matrix.diagonal, Fin.rev] <;> norm_num
