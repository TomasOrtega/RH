import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin.CosetFourier

/- English proof (translation)
Establish `h1 : ‖w‖ = 1` using `Complex.norm_eq_one_of_pow_eq_one hw hn`. Establish `h2 : Complex.normSq w = 1`. Rewrite using `[Complex.normSq_eq_norm_sq, h1]`. Evaluate the numerical expressions. Rewrite using `[Complex.inv_def, h2]`.

Simplify using `[Complex.star_def]`.
-/
theorem star_eq_inv_of_pow_eq_one {w : ℂ} {n : ℕ} (hn : n ≠ 0) (hw : w ^ n = 1) :
    star w = w⁻¹ := by
  have h1 : ‖w‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hw hn
  have h2 : Complex.normSq w = 1 := by
    rw [Complex.normSq_eq_norm_sq, h1]; norm_num
  rw [Complex.inv_def, h2]; simp [Complex.star_def]

/- English proof (translation)
Use `split_ifs with h`. Simplify using `[h]`. Rewrite using `[geom_sum_eq h, hw]`. Simplify using the standard rewrite rules.
-/
theorem geom_sum_root_of_unity {w : ℂ} {n : ℕ} (hw : w ^ n = 1) :
    ∑ a ∈ Finset.range n, w ^ a = if w = 1 then (n : ℂ) else 0 := by
  split_ifs with h
  · simp [h]
  · rw [geom_sum_eq h, hw]; simp

/- English proof (translation)
Introduce `G Γ _ _ _ _ φ s hs ζ hζ`. Establish `hn0 : Nat.card Γ ≠ 0` using `Nat.card_pos.ne'`. Establish `hord : orderOf s = Nat.card Γ` using `orderOf_eq_card_of_forall_mem_zpowers hs`. Set `u : ℂˣ` to `Units.mk0 ζ (hζ.ne_zero hn0)`. Establish `hu : orderOf u ∣ orderOf s`.

Apply `orderOf_dvd_of_pow_eq_one` to reduce the goal to its premises. Rewrite using `[hord]`. Use `ext`. Simplify using `only [Units.val_pow_eq_pow_val, Units.val_one, u, Units.val_mk0]`. Conclude with `hζ.pow_eq_one`.

Set `η₀ : Γ →* ℂˣ` to `monoidHomOfForallMemZpowers hs hu`. Establish `hη₀s : η₀ s = u` using `monoidHomOfForallMemZpowers_apply_gen hs hu`. Establish `hinj : Function.Injective η₀`. Rewrite using `[injective_iff_map_eq_one]`. Introduce `t ht`.

Take `⟨k, rfl⟩` from `Subgroup.mem_zpowers_iff.mp (hs t)`. Rewrite `ht` using `[map_zpow, hη₀s]`. Establish `hk : ζ ^ k = 1`. Use `congrArg Units.val ht` as an intermediate fact. Simplify `this` using `[u, Units.val_zpow_eq_zpow_val]`.

Rewrite `hk` using `[hζ.zpow_eq_one_iff_dvd]`. Rewrite using `[← orderOf_dvd_iff_zpow_eq_one, hord]`. Conclude with `hk`. Set `η : G ⋊[φ] Γ →* ℂˣ` to `η₀.comp rightHom`. Establish `hηx : ∀ x, η x = η₀ x.right` using `fun x => rfl`.

Establish `hpow : ∀ x, (η x : ℂ) ^ Nat.card Γ = 1`. Introduce `x`. Rewrite using `[hηx, ← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one']`. Simplify using the standard rewrite rules. Establish `hstar : ∀ x, star (η x : ℂ) = (η x : ℂ)⁻¹` using `fun x => star_eq_inv_of_pow_eq_one hn0 (hpow x)`.

Establish `hone : ∀ x : G ⋊[φ] Γ, (η x : ℂ)⁻¹ = 1 ↔ x.right = 1`. Introduce `x`. Rewrite using `[inv_eq_one, Units.val_eq_one, hηx, ← map_one η₀, hinj.eq_iff]`. Establish `hzeta : ∀ x : G ⋊[φ] Γ, ζ * (η x : ℂ)⁻¹ = 1 ↔ x.right = s`. Introduce `x`.

Establish `hne : (η x : ℂ) ≠ 0` using `(η x).ne_zero`. Rewrite using `[mul_inv_eq_one₀ hne, eq_comm, hηx]`. Establish `: ζ = ((η₀ s : ℂˣ) : ℂ)` using `by rw [hη₀s]; rfl`. Rewrite using `[this, Units.val_inj, hinj.eq_iff]`. Use `⟨η, fun g => by simp [η], by rw [show η (inr s) = η₀ s from by simp [η], hη₀s]; rfl, ?_⟩` and prove the remaining obligations.

Introduce `X Y`. Use `haveI : Fintype G := Fintype.ofFinite G`. Set `e : G ⋊[φ] Γ ≃ G × Γ` to `⟨fun x => (x.left, x.right), fun p => ⟨p.1, p.2⟩, fun _ => rfl, fun _ => rfl⟩`. Use `haveI : Fintype (G ⋊[φ] Γ) := Fintype.ofEquiv (G × Γ) e.symm`. Establish `key : ∀ (c : ℂ) (t : Γ), (∀ x : G ⋊[φ] Γ, c * (η x : ℂ)⁻¹ = 1 ↔ x.right = t) → c ^ Nat.card Γ = 1 → ∑ a ∈ Finset.range (Nat.card Γ), c ^ a * ∑ᶠ x, X x * star (Y x * (η x : ℂ) ^ a) = (Nat.card Γ : ℂ) * ∑ g : G, X ⟨g, t⟩ * star (Y ⟨g, t⟩)`.

Introduce `c t hct hc`. Repeatedly rewrite using `[finsum_eq_sum_of_fintype, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Establish `hterm : ∀ x : G ⋊[φ] Γ, ∑ a ∈ Finset.range (Nat.card Γ), c ^ a * (X x * star (Y x * (η x : ℂ) ^ a)) = X x * star (Y x) * (if x.right = t then (Nat.card Γ : ℂ) else 0)`. Introduce `x`.

Establish `: ∀ a, c ^ a * (X x * star (Y x * (η x : ℂ) ^ a)) = X x * star (Y x) * (c * (η x : ℂ)⁻¹) ^ a`. Introduce `a`. Rewrite using `[star_mul', star_pow, hstar, mul_pow]`. Expand and normalize the polynomial expressions, which then agree. Repeatedly rewrite using `[this]`.

Rewrite using `[← Finset.mul_sum, geom_sum_root_of_unity (by rw [mul_pow, inv_pow, hc, hpow, inv_one, one_mul])]`. Simplify using `only [hct]`. Repeatedly rewrite using `[hterm]`. Rewrite using `[← e.symm.sum_comp, Fintype.sum_prod_type]`. Use `Finset.sum_congr rfl fun g _ => ?_` and prove the remaining obligations.

Simplify using `[e, mul_comm]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `key 1 1 (fun x => by rw [one_mul]; exact hone x) (one_pow _)` as an intermediate fact. Simplify using `only [one_pow, one_mul] at this`. Rewrite using `[this, finsum_eq_sum_of_fintype]`.

Both sides reduce to the same expression. Rewrite using `[key ζ s hzeta hζ.pow_eq_one, finsum_eq_sum_of_fintype]`. Use `congr 1`. Use `Finset.sum_congr rfl fun g _ => ?_` and prove the remaining obligations. Apply the tactic sequence `have : (inl g * inr s : G ⋊[φ] Γ) = ⟨g, s⟩ := by ext <;> simp`.

Rewrite using `[this]`.
-/
theorem fourier_coset_sums : ∀ (G Γ : Type) [Group G] [Finite G] [Group Γ] [Fintype Γ] (φ : Γ →* MulAut G) (s : Γ), (∀ t : Γ, t ∈ Subgroup.zpowers s) → ∀ ζ : ℂ, IsPrimitiveRoot ζ (Nat.card Γ) → ∃ η : G ⋊[φ] Γ →* ℂˣ, (∀ g, η (inl g) = 1) ∧ (η (inr s) : ℂ) = ζ ∧ ∀ X Y : G ⋊[φ] Γ → ℂ, ((Nat.card Γ : ℂ) * ∑ᶠ g, X (inl g) * star (Y (inl g)) = ∑ a ∈ Finset.range (Nat.card Γ), ∑ᶠ x, X x * star (Y x * (η x : ℂ) ^ a)) ∧ (Nat.card Γ : ℂ) * ∑ᶠ g, X (inl g * inr s) * star (Y (inl g * inr s)) = ∑ a ∈ Finset.range (Nat.card Γ), ζ ^ a * ∑ᶠ x, X x * star (Y x * (η x : ℂ) ^ a) := by
  intro G Γ _ _ _ _ φ s hs ζ hζ
  have hn0 : Nat.card Γ ≠ 0 := Nat.card_pos.ne'
  have hord : orderOf s = Nat.card Γ := orderOf_eq_card_of_forall_mem_zpowers hs
  let u : ℂˣ := Units.mk0 ζ (hζ.ne_zero hn0)
  have hu : orderOf u ∣ orderOf s := by
    apply orderOf_dvd_of_pow_eq_one
    rw [hord]; ext
    simp only [Units.val_pow_eq_pow_val, Units.val_one, u, Units.val_mk0]
    exact hζ.pow_eq_one
  let η₀ : Γ →* ℂˣ := monoidHomOfForallMemZpowers hs hu
  have hη₀s : η₀ s = u := monoidHomOfForallMemZpowers_apply_gen hs hu
  have hinj : Function.Injective η₀ := by
    rw [injective_iff_map_eq_one]
    intro t ht
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hs t)
    rw [map_zpow, hη₀s] at ht
    have hk : ζ ^ k = 1 := by
      have := congrArg Units.val ht
      simpa [u, Units.val_zpow_eq_zpow_val] using this
    rw [hζ.zpow_eq_one_iff_dvd] at hk
    rw [← orderOf_dvd_iff_zpow_eq_one, hord]; exact hk
  let η : G ⋊[φ] Γ →* ℂˣ := η₀.comp rightHom
  have hηx : ∀ x, η x = η₀ x.right := fun x => rfl
  have hpow : ∀ x, (η x : ℂ) ^ Nat.card Γ = 1 := by
    intro x
    rw [hηx, ← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one']; simp
  have hstar : ∀ x, star (η x : ℂ) = (η x : ℂ)⁻¹ := fun x => star_eq_inv_of_pow_eq_one hn0 (hpow x)
  have hone : ∀ x : G ⋊[φ] Γ, (η x : ℂ)⁻¹ = 1 ↔ x.right = 1 := by
    intro x
    rw [inv_eq_one, Units.val_eq_one, hηx, ← map_one η₀, hinj.eq_iff]
  have hzeta : ∀ x : G ⋊[φ] Γ, ζ * (η x : ℂ)⁻¹ = 1 ↔ x.right = s := by
    intro x
    have hne : (η x : ℂ) ≠ 0 := (η x).ne_zero
    rw [mul_inv_eq_one₀ hne, eq_comm, hηx]
    have : ζ = ((η₀ s : ℂˣ) : ℂ) := by rw [hη₀s]; rfl
    rw [this, Units.val_inj, hinj.eq_iff]
  refine ⟨η, fun g => by simp [η], by rw [show η (inr s) = η₀ s from by simp [η], hη₀s]; rfl, ?_⟩
  intro X Y
  haveI : Fintype G := Fintype.ofFinite G
  let e : G ⋊[φ] Γ ≃ G × Γ :=
    ⟨fun x => (x.left, x.right), fun p => ⟨p.1, p.2⟩, fun _ => rfl, fun _ => rfl⟩
  haveI : Fintype (G ⋊[φ] Γ) := Fintype.ofEquiv (G × Γ) e.symm

  have key : ∀ (c : ℂ) (t : Γ), (∀ x : G ⋊[φ] Γ, c * (η x : ℂ)⁻¹ = 1 ↔ x.right = t) →
      c ^ Nat.card Γ = 1 →
      ∑ a ∈ Finset.range (Nat.card Γ), c ^ a * ∑ᶠ x, X x * star (Y x * (η x : ℂ) ^ a) =
        (Nat.card Γ : ℂ) * ∑ g : G, X ⟨g, t⟩ * star (Y ⟨g, t⟩) := by
    intro c t hct hc
    simp_rw [finsum_eq_sum_of_fintype, Finset.mul_sum]
    rw [Finset.sum_comm]
    have hterm : ∀ x : G ⋊[φ] Γ, ∑ a ∈ Finset.range (Nat.card Γ), c ^ a * (X x * star (Y x * (η x : ℂ) ^ a))
        = X x * star (Y x) * (if x.right = t then (Nat.card Γ : ℂ) else 0) := by
      intro x
      have : ∀ a, c ^ a * (X x * star (Y x * (η x : ℂ) ^ a)) = X x * star (Y x) * (c * (η x : ℂ)⁻¹) ^ a := by
        intro a
        rw [star_mul', star_pow, hstar, mul_pow]; ring
      simp_rw [this]
      rw [← Finset.mul_sum, geom_sum_root_of_unity (by rw [mul_pow, inv_pow, hc, hpow, inv_one, one_mul])]
      simp only [hct]
    simp_rw [hterm]
    rw [← e.symm.sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun g _ => ?_
    simp [e, mul_comm]
  refine ⟨?_, ?_⟩
  · have := key 1 1 (fun x => by rw [one_mul]; exact hone x) (one_pow _)
    simp only [one_pow, one_mul] at this
    rw [this, finsum_eq_sum_of_fintype]
    rfl
  · rw [key ζ s hzeta hζ.pow_eq_one, finsum_eq_sum_of_fintype]
    congr 1
    refine Finset.sum_congr rfl fun g _ => ?_
    have : (inl g * inr s : G ⋊[φ] Γ) = ⟨g, s⟩ := by ext <;> simp
    rw [this]

end GlobalTheory.Shin.CosetFourier
