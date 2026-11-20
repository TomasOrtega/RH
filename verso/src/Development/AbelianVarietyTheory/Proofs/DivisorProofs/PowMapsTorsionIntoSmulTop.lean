import Mathlib

namespace GlobalTheory

open Submodule in

/- English proof (translation)
Introduce `hI hJ hf`. Take `⟨Q, hIQ, hJQ⟩` from `Ideal.eq_prime_pow_mul_coprime hJ I`. Use `set k := Multiset.count I (UniqueFactorizationMonoid.normalizedFactors J)`. Establish `hstab : ∀ (n : ℕ) (z : M), z ∈ J • (⊤ : Submodule R M) → (f ^ n) z ∈ J • (⊤ : Submodule R M)`. Introduce `n z hz`.

Establish `: (J • (⊤ : Submodule R M)).map (f ^ n) ≤ J • (⊤ : Submodule R M)`. Rewrite using `[Submodule.map_smul'']`. Conclude with `Submodule.smul_mono le_rfl le_top`. Conclude with `this ⟨z, hz, rfl⟩`. Establish `hmap : (⊤ : Submodule R M).map (f ^ m) ≤ I • (⊤ : Submodule R M)`.

Introduce and unpack `_ ⟨x, -, rfl⟩`. Conclude with `hf x`. Establish `hpow : ∀ (i : ℕ) (x : M), (f ^ (m * i)) x ∈ I ^ i • (⊤ : Submodule R M)`. Introduce `i`. Proceed by induction on `i with`.

Consider the case `zero => intro x`. Simplify using the standard rewrite rules. Consider the case `succ i ih`. Introduce `x`. Establish `h1 : (f ^ (m * (i + 1))) x = (f ^ m) ((f ^ (m * i)) x)`.

Rewrite using `[Nat.mul_succ, add_comm, pow_add, Module.End.mul_apply]`. Rewrite using `[h1]`. Establish `h2 : (I ^ i • (⊤ : Submodule R M)).map (f ^ m) ≤ I ^ (i + 1) • (⊤ : Submodule R M)`. Rewrite using `[Submodule.map_smul'', pow_succ, Submodule.mul_smul]`. Conclude with `Submodule.smul_mono le_rfl hmap`.

Conclude with `h2 ⟨_, ih x, rfl⟩`. Use `⟨m * k, fun y hy => ?_⟩` and prove the remaining obligations. Use `set Z := (f ^ (m * k)) y with hZ`. Establish `hZk : Z ∈ I ^ k • (⊤ : Submodule R M)` using `hpow k y`. Establish `hIZ : ∀ a ∈ I, a • Z ∈ J • (⊤ : Submodule R M)`.

Introduce `a ha`. Rewrite using `[hZ, ← LinearMap.map_smul]`. Conclude with `hstab _ _ (hy a ha)`. Establish `hJle : J ≤ Q` using `by rw [hJQ]; exact Ideal.mul_le_inf.trans inf_le_right`. Establish `hZQ : Z ∈ Q • (⊤ : Submodule R M)`.

Establish `h1 : (1 : R) ∈ I ⊔ Q` using `by rw [hIQ]; trivial`. Take `⟨t, ht, s, hs, hts⟩` from `Submodule.mem_sup.1 h1`. Establish `: Z = t • Z + s • Z` using `by rw [← add_smul, hts, one_smul]`. Rewrite using `[this]`. Use `Submodule.add_mem _ ?_ (Submodule.smul_mem_smul hs trivial)` and prove the remaining obligations.

Conclude with `Submodule.smul_mono_left hJle (hIZ t ht)`. Establish `hkQ : I ^ k ⊔ Q = ⊤`. Rewrite `hIQ`, the goal using `[← Ideal.isCoprime_iff_sup_eq]`. Conclude with `hIQ.pow_left`. Establish `h1 : (1 : R) ∈ I ^ k ⊔ Q` using `by rw [hkQ]; trivial`.

Take `⟨t, ht, s, hs, hts⟩` from `Submodule.mem_sup.1 h1`. Establish `: Z = t • Z + s • Z` using `by rw [← add_smul, hts, one_smul]`. Rewrite using `[this]`. Use `Submodule.add_mem _ ?_ ?_` and prove the remaining obligations. Establish `: t • Z ∈ I ^ k • Q • (⊤ : Submodule R M)` using `Submodule.smul_mem_smul ht hZQ`.

Rewrite `this` using `[← Submodule.mul_smul, ← hJQ]`. Then use the resulting hypothesis. Establish `: s • Z ∈ Q • I ^ k • (⊤ : Submodule R M)` using `Submodule.smul_mem_smul hs hZk`. Rewrite `this` using `[← Submodule.mul_smul, mul_comm, ← hJQ]`. Then use the resulting hypothesis.
-/
theorem pow_maps_torsion_into_smul_top (R : Type) [CommRing R] [IsDedekindDomain R] (M : Type)
    [AddCommGroup M] [Module R M] (I J : Ideal R) (f : M →ₗ[R] M) (m : ℕ) :
    I.IsMaximal → J ≠ ⊥ → (∀ x, (f ^ m) x ∈ I • (⊤ : Submodule R M)) →
      ∃ j : ℕ, ∀ y : M, (∀ a ∈ I, a • y ∈ J • (⊤ : Submodule R M)) →
        (f ^ j) y ∈ J • (⊤ : Submodule R M) := by
  intro hI hJ hf
  obtain ⟨Q, hIQ, hJQ⟩ := Ideal.eq_prime_pow_mul_coprime hJ I
  set k := Multiset.count I (UniqueFactorizationMonoid.normalizedFactors J)

  have hstab : ∀ (n : ℕ) (z : M), z ∈ J • (⊤ : Submodule R M) → (f ^ n) z ∈ J • (⊤ : Submodule R M) := by
    intro n z hz
    have : (J • (⊤ : Submodule R M)).map (f ^ n) ≤ J • (⊤ : Submodule R M) := by
      rw [Submodule.map_smul'']
      exact Submodule.smul_mono le_rfl le_top
    exact this ⟨z, hz, rfl⟩

  have hmap : (⊤ : Submodule R M).map (f ^ m) ≤ I • (⊤ : Submodule R M) := by
    rintro _ ⟨x, -, rfl⟩
    exact hf x
  have hpow : ∀ (i : ℕ) (x : M), (f ^ (m * i)) x ∈ I ^ i • (⊤ : Submodule R M) := by
    intro i
    induction i with
    | zero => intro x; simp
    | succ i ih =>
      intro x
      have h1 : (f ^ (m * (i + 1))) x = (f ^ m) ((f ^ (m * i)) x) := by
        rw [Nat.mul_succ, add_comm, pow_add, Module.End.mul_apply]
      rw [h1]
      have h2 : (I ^ i • (⊤ : Submodule R M)).map (f ^ m) ≤ I ^ (i + 1) • (⊤ : Submodule R M) := by
        rw [Submodule.map_smul'', pow_succ, Submodule.mul_smul]
        exact Submodule.smul_mono le_rfl hmap
      exact h2 ⟨_, ih x, rfl⟩
  refine ⟨m * k, fun y hy => ?_⟩
  set Z := (f ^ (m * k)) y with hZ
  have hZk : Z ∈ I ^ k • (⊤ : Submodule R M) := hpow k y
  have hIZ : ∀ a ∈ I, a • Z ∈ J • (⊤ : Submodule R M) := by
    intro a ha
    rw [hZ, ← LinearMap.map_smul]
    exact hstab _ _ (hy a ha)
  have hJle : J ≤ Q := by rw [hJQ]; exact Ideal.mul_le_inf.trans inf_le_right
  have hZQ : Z ∈ Q • (⊤ : Submodule R M) := by
    have h1 : (1 : R) ∈ I ⊔ Q := by rw [hIQ]; trivial
    obtain ⟨t, ht, s, hs, hts⟩ := Submodule.mem_sup.1 h1
    have : Z = t • Z + s • Z := by rw [← add_smul, hts, one_smul]
    rw [this]
    refine Submodule.add_mem _ ?_ (Submodule.smul_mem_smul hs trivial)
    exact Submodule.smul_mono_left hJle (hIZ t ht)
  have hkQ : I ^ k ⊔ Q = ⊤ := by
    rw [← Ideal.isCoprime_iff_sup_eq] at hIQ ⊢
    exact hIQ.pow_left
  have h1 : (1 : R) ∈ I ^ k ⊔ Q := by rw [hkQ]; trivial
  obtain ⟨t, ht, s, hs, hts⟩ := Submodule.mem_sup.1 h1
  have : Z = t • Z + s • Z := by rw [← add_smul, hts, one_smul]
  rw [this]
  refine Submodule.add_mem _ ?_ ?_
  · have : t • Z ∈ I ^ k • Q • (⊤ : Submodule R M) := Submodule.smul_mem_smul ht hZQ
    rwa [← Submodule.mul_smul, ← hJQ] at this
  · have : s • Z ∈ Q • I ^ k • (⊤ : Submodule R M) := Submodule.smul_mem_smul hs hZk
    rwa [← Submodule.mul_smul, mul_comm, ← hJQ] at this

end GlobalTheory
