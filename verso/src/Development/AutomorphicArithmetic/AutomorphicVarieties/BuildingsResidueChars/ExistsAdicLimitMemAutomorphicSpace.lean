import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.SpStab
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.IwahoriProUnipotentFiniteIndex
open IsLocalRing Matrix UpperTheory.V.Hi

/- English proof (translation)
Establish `h1 : ∀ m n, m ≤ n → x n - x m ∈ I ^ m`. Introduce `m n hmn`. Proceed by induction on `n, hmn using Nat.le_induction with`. Consider the case `base => simp`. Consider the case `succ n hmn ih`.

Use `add_mem (Ideal.pow_le_pow_right hmn (h n)) ih` as an intermediate fact. Rewrite `this` using `[sub_add_sub_cancel]`. Then use the resulting hypothesis. Take `⟨L, hL⟩` from `IsPrecomplete.prec (I := I) (M := A) inferInstance (f := x) (fun {m n} hmn => by`. Rewrite using `[SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← neg_sub]`. Conclude with `neg_mem (h1 m n hmn))`.

Use `⟨L, fun k => ?_⟩` and prove the remaining obligations. Use `hL k` as an intermediate fact. Rewrite `this` using `[SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]`. Rewrite using `[← neg_sub]`. Conclude with `neg_mem this`.
-/
private theorem spC_lim {A : Type} [CommRing A] (I : Ideal A) [IsPrecomplete I A] (x : ℕ → A)
    (h : ∀ k, x (k + 1) - x k ∈ I ^ k) : ∃ L, ∀ k, L - x k ∈ I ^ k := by
  have h1 : ∀ m n, m ≤ n → x n - x m ∈ I ^ m := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      have := add_mem (Ideal.pow_le_pow_right hmn (h n)) ih
      rwa [sub_add_sub_cancel] at this
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := I) (M := A) inferInstance (f := x) (fun {m n} hmn => by
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← neg_sub]
    exact neg_mem (h1 m n hmn))
  refine ⟨L, fun k => ?_⟩
  have := hL k
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at this
  rw [← neg_sub]
  exact neg_mem this

/- English proof (translation)
Rewrite using `[← sub_eq_zero]`. Use `IsHausdorff.haus (I := I) inferInstance _ fun k => ?_` and prove the remaining obligations. Rewrite using `[SModEq.zero, smul_eq_mul, Ideal.mul_top]`. Conclude with `h k`.
-/
private theorem spC_eq {A : Type} [CommRing A] (I : Ideal A) [IsHausdorff I A] {x y : A}
    (h : ∀ k, x - y ∈ I ^ k) : x = y := by
  rw [← sub_eq_zero]
  refine IsHausdorff.haus (I := I) inferInstance _ fun k => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  exact h k

/- English proof (translation)
Introduce `Γ Ga Gp _ _ _ X A _ _ m τ θ U a ha hc`. Establish `hv : ∀ (k : ℕ) (f : X.Fn A m), f ∈ X.valIn A m k ↔ ∀ g i, f g i ∈ maximalIdeal A ^ k`. Introduce `k f`. Simplify using `[Frame.valIn, Submodule.mem_pi]`. Use `choose L hL using fun g i => spC_lim (maximalIdeal A) (fun k => a k g i) fun k => (hv _ _).1 (hc k) g i`.

Establish `key : ∀ φ ψ : X.Fn A m →ₗ[A] X.Fn A m, (∀ k, ∀ f ∈ X.valIn A m k, φ f ∈ X.valIn A m k) → (∀ k, ∀ f ∈ X.valIn A m k, ψ f ∈ X.valIn A m k) → (∀ k, φ (a k) = ψ (a k)) → φ L = ψ L`. Introduce `φ ψ h1 h2 h3`. Use function extensionality and compare the values at `g i`. Use `spC_eq (maximalIdeal A) fun k => ?_` and prove the remaining obligations. Establish `hk : L - a k ∈ X.valIn A m k` using `(hv _ _).2 fun g i => hL g i k`.

Use `sub_mem (h1 k _ hk) (h2 k _ hk)` as an intermediate fact. Rewrite `this` using `[map_sub, map_sub, h3 k, sub_sub_sub_cancel_right]`. Conclude with `(hv _ _).1 this g i`. Establish `hrp : ∀ b k, ∀ f ∈ X.valIn A m k, X.rp A m b f ∈ X.valIn A m k` using `fun b k f hf => (hv _ _).2 fun g i => (hv _ _).1 hf _ i`. Use `⟨L, ⟨⟨fun γ g => ?_, fun x hx => ?_, fun t => ?_, fun k => ?_⟩, fun u hu => ?_⟩, fun k => (hv _ _).2 fun g i => hL g i k⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `i`. Use `spC_eq (maximalIdeal A) fun k => ?_` and prove the remaining obligations. Use `sub_mem (hL (X.glob γ * g) i k) (hL g i k)` as an intermediate fact. Rewrite `this` using `[(ha k).1.1 γ g, sub_sub_sub_cancel_right]`. Then use the resulting hypothesis. Conclude with `key _ LinearMap.id (hrp x) (fun _ _ h => h) fun k => (ha k).1.2.1 x hx`.

Conclude with `key _ ((((θ t)⁻¹ : Aˣ) : A) • LinearMap.id) (hrp t) (fun _ _ h => Submodule.smul_mem _ _ h) fun k => (ha k).1.2.2.1 t`. Take `⟨c, h⟩` from `(ha k).1.2.2.2 k`. Use `⟨c, fun y hy g i => ?_⟩` and prove the remaining obligations. Use `add_mem (sub_mem (hL (g * (1, y)) i k) (hL g i k)) (h y hy g i)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Expand and normalize the polynomial expressions, which then agree. Use `key _ LinearMap.id (fun k f hf => (hv _ _).2 fun g i => ?_) (fun _ _ h => h) fun k => (ha k).2 u hu` and prove the remaining obligations. Rewrite using `[Frame.ra_apply]`. Simplify using `only [mulVec, dotProduct]`. Conclude with `Submodule.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ ((hv _ _).1 hf _ j)`.
-/
theorem UpperTheory.exists_adic_limit_mem_automorphicSpace :
    ∀ (Γ Ga Gp : Type) [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) (A : Type) [CommRing A] [IsCNL A] (m : ℕ) (τ : X.Ub →* GL (Fin m) A) (θ : X.I.T →* Aˣ) (U : Subgroup X.Ub) (a : ℕ → X.Fn A m), (∀ k, a k ∈ X.Sp τ θ U) → (∀ k, a (k + 1) - a k ∈ X.valIn A m k) → ∃ L ∈ X.Sp τ θ U, ∀ k, L - a k ∈ X.valIn A m k := by
  intro Γ Ga Gp _ _ _ X A _ _ m τ θ U a ha hc
  have hv : ∀ (k : ℕ) (f : X.Fn A m), f ∈ X.valIn A m k ↔ ∀ g i, f g i ∈ maximalIdeal A ^ k := by
    intro k f
    simp [Frame.valIn, Submodule.mem_pi]
  choose L hL using fun g i => spC_lim (maximalIdeal A) (fun k => a k g i) fun k => (hv _ _).1 (hc k) g i
  have key : ∀ φ ψ : X.Fn A m →ₗ[A] X.Fn A m, (∀ k, ∀ f ∈ X.valIn A m k, φ f ∈ X.valIn A m k) →
      (∀ k, ∀ f ∈ X.valIn A m k, ψ f ∈ X.valIn A m k) → (∀ k, φ (a k) = ψ (a k)) → φ L = ψ L := by
    intro φ ψ h1 h2 h3
    funext g i
    refine spC_eq (maximalIdeal A) fun k => ?_
    have hk : L - a k ∈ X.valIn A m k := (hv _ _).2 fun g i => hL g i k
    have := sub_mem (h1 k _ hk) (h2 k _ hk)
    rw [map_sub, map_sub, h3 k, sub_sub_sub_cancel_right] at this
    exact (hv _ _).1 this g i
  have hrp : ∀ b k, ∀ f ∈ X.valIn A m k, X.rp A m b f ∈ X.valIn A m k := fun b k f hf =>
    (hv _ _).2 fun g i => (hv _ _).1 hf _ i
  refine ⟨L, ⟨⟨fun γ g => ?_, fun x hx => ?_, fun t => ?_, fun k => ?_⟩, fun u hu => ?_⟩,
    fun k => (hv _ _).2 fun g i => hL g i k⟩
  · funext i
    refine spC_eq (maximalIdeal A) fun k => ?_
    have := sub_mem (hL (X.glob γ * g) i k) (hL g i k)
    rwa [(ha k).1.1 γ g, sub_sub_sub_cancel_right] at this
  · exact key _ LinearMap.id (hrp x) (fun _ _ h => h) fun k => (ha k).1.2.1 x hx
  · exact key _ ((((θ t)⁻¹ : Aˣ) : A) • LinearMap.id) (hrp t) (fun _ _ h => Submodule.smul_mem _ _ h)
      fun k => (ha k).1.2.2.1 t
  · obtain ⟨c, h⟩ := (ha k).1.2.2.2 k
    refine ⟨c, fun y hy g i => ?_⟩
    have := add_mem (sub_mem (hL (g * (1, y)) i k) (hL g i k)) (h y hy g i)
    convert this using 1
    ring
  · refine key _ LinearMap.id (fun k f hf => (hv _ _).2 fun g i => ?_) (fun _ _ h => h) fun k => (ha k).2 u hu
    rw [Frame.ra_apply]
    simp only [mulVec, dotProduct]
    exact Submodule.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ ((hv _ _).1 hf _ j)
