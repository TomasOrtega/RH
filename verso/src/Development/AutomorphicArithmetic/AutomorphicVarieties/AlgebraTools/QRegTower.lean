import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.UltraDefs

open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

/- English proof (translation)
Introduce `R σ _ _ y M _ _ P _ _ q hs hk hq`. Rewrite using `[isQuasiRegularSeq_iff_qRegAt]`. Introduce `a c hc α`. Simplify using `only [sup_bot_eq] at hc ⊢`. Establish `h` using `hq a (a + 1) (Nat.lt_succ_self a) (fun β => q (a + 1) (c β)) (by`.

Rewrite `hc` using `[← hk, LinearMap.mem_ker, map_sum]`. Simplify using `only [map_smul] at hc`. Rewrite using `[hc]`. Conclude with `zero_mem _) α`. Simplify using `only [sup_bot_eq] at h`.

Establish `htop : (⊤ : Submodule R (P (a + 1))) = Submodule.map (q (a + 1)) ⊤`. Rewrite using `[Submodule.map_top, LinearMap.range_eq_top.2 (hs _)]`. Rewrite `h` using `[htop, ← Submodule.map_smul'']`. Establish `h2 : c α ∈ Submodule.comap (q (a + 1)) (Submodule.map (q (a + 1)) (Ideal.span (Set.range y) • ⊤ : Submodule R M))` using `h`. Rewrite `h2` using `[Submodule.comap_map_eq, hk]`.

Establish `hle : (Ideal.span (Set.range y) ^ (a + 1) • ⊤ : Submodule R M) ≤ Ideal.span (Set.range y) • ⊤` using `Submodule.smul_mono_left (Ideal.pow_le_self (Nat.succ_ne_zero a))`. Rewrite `h2` using `[sup_eq_left.2 hle]`. Then use the resulting hypothesis.
-/
theorem UpperTheory.V.AlgebraTools.isQuasiRegularSeq_of_tower :
    ∀ (R σ : Type) [CommRing R] [Finite σ] (y : σ → R) (M : Type) [AddCommGroup M] [Module R M] (P : ℕ → Type) [∀ i, AddCommGroup (P i)] [∀ i, Module R (P i)] (q : ∀ k, M →ₗ[R] P k),
      (∀ k, Function.Surjective (q k)) → (∀ k, LinearMap.ker (q k) = Ideal.span (Set.range y) ^ k • ⊤) →
      (∀ a k, a < k → QRegAt (P k) y ⊥ a) → GlobalTheory.IsQuasiRegularSeq M y := by
  intro R σ _ _ y M _ _ P _ _ q hs hk hq
  rw [isQuasiRegularSeq_iff_qRegAt]
  intro a c hc α
  simp only [sup_bot_eq] at hc ⊢
  have h := hq a (a + 1) (Nat.lt_succ_self a) (fun β => q (a + 1) (c β)) (by
    rw [← hk, LinearMap.mem_ker, map_sum] at hc
    simp only [map_smul] at hc
    rw [hc]
    exact zero_mem _) α
  simp only [sup_bot_eq] at h
  have htop : (⊤ : Submodule R (P (a + 1))) = Submodule.map (q (a + 1)) ⊤ := by
    rw [Submodule.map_top, LinearMap.range_eq_top.2 (hs _)]
  rw [htop, ← Submodule.map_smul''] at h
  have h2 : c α ∈ Submodule.comap (q (a + 1))
      (Submodule.map (q (a + 1)) (Ideal.span (Set.range y) • ⊤ : Submodule R M)) := h
  rw [Submodule.comap_map_eq, hk] at h2
  have hle : (Ideal.span (Set.range y) ^ (a + 1) • ⊤ : Submodule R M) ≤ Ideal.span (Set.range y) • ⊤ :=
    Submodule.smul_mono_left (Ideal.pow_le_self (Nat.succ_ne_zero a))
  rwa [sup_eq_left.2 hle] at h2
