import Mathlib

namespace GlobalTheory

/- English proof (translation)
Introduce `Γ F O LL _ _ _ _ n hn f hone hmul hx ι hι ζ hζ t`. Use `haveI : NeZero n := ⟨hn.ne'⟩`. Establish `h1 : ∀ σ, f 1 σ = 1`. Introduce `σ`. Establish `hne : f 1 σ ≠ 0`.

Introduce `h`. Use `hmul 1 one_ne_zero σ σ⁻¹` as an intermediate fact. Rewrite `this` using `[mul_inv_cancel, hone 1 one_ne_zero, h, zero_mul]`. Conclude with `one_ne_zero this`. Use `hx 1 1 one_ne_zero one_ne_zero σ` as an intermediate fact.

Rewrite `this` using `[mul_one]`. Conclude with `(mul_left_cancel₀ hne (by rw [mul_one]; exact this)).symm`. Establish `hpow : ∀ x, x ≠ 0 → ∀ σ (k : ℕ), f (x ^ k) σ = f x σ ^ k`. Introduce `x hx0 σ k`. Proceed by induction on `k with`.

Consider the case `zero => simp [h1]`. Consider the case `succ k ih => rw [pow_succ, hx _ _ (pow_ne_zero k hx0) hx0, ih, pow_succ]`. Establish `hex : ∀ (u : rootsOfUnity n F) (σ : Γ), ∃ o : O, ι o = f ((u : Fˣ) : F) σ`. Introduce `u σ`. Establish `hu : (((u : Fˣ) : F)) ^ n = 1`.

Use `u.2` as an intermediate fact. Rewrite `this` using `[mem_rootsOfUnity']`. Conclude with `this`. Establish `h2 : f ((u : Fˣ) : F) σ ^ n = 1`. Rewrite using `[← hpow _ (Units.ne_zero _), hu, h1]`.

Take `⟨j, -, hj⟩` from `(hζ.map_of_injective hι).eq_pow_of_pow_eq_one h2`. Conclude with `⟨ζ ^ j, by rw [map_pow, hj]⟩`. Use `choose o ho using hex`. Set `g : rootsOfUnity n F → (Γ →* LL)` to `fun u => { toFun := fun σ => t (o u σ) map_one' := by`. Establish `: o u 1 = 1` using `hι (by rw [ho, map_one, hone _ (Units.ne_zero _)])`.

Rewrite using `[this, map_one]`. Use the proof step `map_mul' := by`. Introduce `a b`. Establish `: o u (a * b) = o u a * o u b` using `hι (by rw [map_mul, ho, ho, ho, hmul _ (Units.ne_zero _)])`. Rewrite using `[this, map_mul] }`.

Use `⟨MonoidHom.mk' (fun u => (g u).toHomUnits) ?_, fun u σ => ⟨o u σ, ho u σ, rfl⟩⟩` and prove the remaining obligations. Introduce `u v`. Use extensionality with `σ`. Establish `: o (u * v) σ = o u σ * o v σ` using `hι (by`. Rewrite using `[map_mul, ho, ho, ho, Subgroup.coe_mul, Units.val_mul, hx _ _ (Units.ne_zero _) (Units.ne_zero _)])`.

Use `show t (o (u * v) σ) = t (o u σ) * t (o v σ)`. Rewrite using `[this, map_mul]`.
-/
theorem exists_rootsOfUnity_character_hom : ∀ {Γ F O LL : Type} [Group Γ] [Field F] [CommRing O] [Field LL] (n : ℕ), 0 < n → ∀ (f : F → Γ → ℂ), (∀ x, x ≠ 0 → f x 1 = 1) → (∀ x, x ≠ 0 → ∀ σ σ', f x (σ * σ') = f x σ * f x σ') → (∀ x y, x ≠ 0 → y ≠ 0 → ∀ σ, f (x * y) σ = f x σ * f y σ) → ∀ (ι : O →+* ℂ), Function.Injective ι → ∀ (ζ : O), IsPrimitiveRoot ζ n → ∀ (t : O →+* LL), ∃ Ψ : ↥(rootsOfUnity n F) →* (Γ →* LLˣ), ∀ (u : ↥(rootsOfUnity n F)) (σ : Γ), ∃ o : O, ι o = f (((u : Fˣ)) : F) σ ∧ ((Ψ u σ : LLˣ) : LL) = t o := by
  intro Γ F O LL _ _ _ _ n hn f hone hmul hx ι hι ζ hζ t
  haveI : NeZero n := ⟨hn.ne'⟩
  have h1 : ∀ σ, f 1 σ = 1 := by
    intro σ
    have hne : f 1 σ ≠ 0 := by
      intro h
      have := hmul 1 one_ne_zero σ σ⁻¹
      rw [mul_inv_cancel, hone 1 one_ne_zero, h, zero_mul] at this
      exact one_ne_zero this
    have := hx 1 1 one_ne_zero one_ne_zero σ
    rw [mul_one] at this
    exact (mul_left_cancel₀ hne (by rw [mul_one]; exact this)).symm
  have hpow : ∀ x, x ≠ 0 → ∀ σ (k : ℕ), f (x ^ k) σ = f x σ ^ k := by
    intro x hx0 σ k
    induction k with
    | zero => simp [h1]
    | succ k ih => rw [pow_succ, hx _ _ (pow_ne_zero k hx0) hx0, ih, pow_succ]
  have hex : ∀ (u : rootsOfUnity n F) (σ : Γ), ∃ o : O, ι o = f ((u : Fˣ) : F) σ := by
    intro u σ
    have hu : (((u : Fˣ) : F)) ^ n = 1 := by
      have := u.2
      rw [mem_rootsOfUnity'] at this
      exact this
    have h2 : f ((u : Fˣ) : F) σ ^ n = 1 := by
      rw [← hpow _ (Units.ne_zero _), hu, h1]
    obtain ⟨j, -, hj⟩ := (hζ.map_of_injective hι).eq_pow_of_pow_eq_one h2
    exact ⟨ζ ^ j, by rw [map_pow, hj]⟩
  choose o ho using hex
  let g : rootsOfUnity n F → (Γ →* LL) := fun u =>
    { toFun := fun σ => t (o u σ)
      map_one' := by
        have : o u 1 = 1 := hι (by rw [ho, map_one, hone _ (Units.ne_zero _)])
        rw [this, map_one]
      map_mul' := by
        intro a b
        have : o u (a * b) = o u a * o u b :=
          hι (by rw [map_mul, ho, ho, ho, hmul _ (Units.ne_zero _)])
        rw [this, map_mul] }
  refine ⟨MonoidHom.mk' (fun u => (g u).toHomUnits) ?_, fun u σ => ⟨o u σ, ho u σ, rfl⟩⟩
  intro u v
  ext σ
  have : o (u * v) σ = o u σ * o v σ :=
    hι (by
      rw [map_mul, ho, ho, ho, Subgroup.coe_mul, Units.val_mul,
        hx _ _ (Units.ne_zero _) (Units.ne_zero _)])
  show t (o (u * v) σ) = t (o u σ) * t (o v σ)
  rw [this, map_mul]

end GlobalTheory
