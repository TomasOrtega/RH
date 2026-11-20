import Mathlib

namespace GlobalTheory.CompanionTheory.CommStep

open Module

/- English proof (translation)
Proceed by induction on `hy using Algebra.adjoin_induction with`. Consider the case `mem x hx`. Take `⟨j, rfl⟩` from `hx`. Conclude with `hc j i`. Consider the case `algebraMap r => exact Algebra.commutes r (a i)`.

Consider the case `add x y _ _ hx hy => exact hx.add_left hy`. Consider the case `mul x y _ _ hx hy => exact hx.mul_left hy`.
-/
theorem commute_of_mem_adjoin {V : Type} [AddCommGroup V] [Module ℂ V] {l : ℕ}
    (a : Fin (l + 1) → Module.End ℂ V) (hc : ∀ i j, Commute (a i) (a j)) (i : Fin (l + 1))
    {y : Module.End ℂ V} (hy : y ∈ Algebra.adjoin ℂ (Set.range a)) : Commute y (a i) := by
  induction hy using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    exact hc j i
  | algebraMap r => exact Algebra.commutes r (a i)
  | add x y _ _ hx hy => exact hx.add_left hy
  | mul x y _ _ hx hy => exact hx.mul_left hy

/- English proof (translation)
Establish `hBC : Algebra.adjoin ℂ (Set.range fun i : Fin l => a i.succ) ≤ Algebra.adjoin ℂ (Set.range a)` using `Algebra.adjoin_mono (Set.range_subset_iff.2 fun k => ⟨k.succ, rfl⟩)`. Establish `ha0 : a 0 ∈ Algebra.adjoin ℂ (Set.range a)` using `Algebra.subset_adjoin ⟨0, rfl⟩`. Introduce `y hy`. Rewrite `hy` using `[Subalgebra.mem_toSubmodule]`. Proceed by induction on `hy using Algebra.adjoin_induction with`.

Consider the case `mem x hx`. Take `⟨j, rfl⟩` from `hx`. Proceed by induction on `j using Fin.cases with`. Consider the case `zero`. Use `Submodule.mem_sup_right (Submodule.mem_map.2 ⟨1, ?_, ?_⟩)` and prove the remaining obligations.

Conclude with `(Subalgebra.mem_toSubmodule _).2 (one_mem _)`. Rewrite using `[LinearMap.mulRight_apply, one_mul]`. Consider the case `succ k => exact Submodule.mem_sup_left (Algebra.subset_adjoin ⟨k, rfl⟩)`. Consider the case `algebraMap r => exact Submodule.mem_sup_left (Subalgebra.algebraMap_mem _ r)`. Consider the case `add x y _ _ hx hy => exact Submodule.add_mem _ hx hy`.

Consider the case `mul x y _ _ hx hy`. Take `⟨p₁, hp₁, z₁, hz₁, rfl⟩` from `Submodule.mem_sup.1 hx`. Take `⟨p₂, hp₂, z₂, hz₂, rfl⟩` from `Submodule.mem_sup.1 hy`. Take `⟨q₁, hq₁, rfl⟩` from `Submodule.mem_map.1 hz₁`. Take `⟨q₂, hq₂, rfl⟩` from `Submodule.mem_map.1 hz₂`.

Rewrite `hp₁`, `hp₂`, `hq₁`, `hq₂` using `[Subalgebra.mem_toSubmodule]`. Rewrite using `[LinearMap.mulRight_apply, LinearMap.mulRight_apply]`. Establish `hp₂c : Commute p₂ (a 0)` using `GlobalTheory.CompanionTheory.CommStep.commute_of_mem_adjoin a hc 0 (hBC hp₂)`. Establish `hq₂c : Commute q₂ (a 0)` using `GlobalTheory.CompanionTheory.CommStep.commute_of_mem_adjoin a hc 0 hq₂`. Establish `e₁ : q₁ * a 0 * p₂ = q₁ * p₂ * a 0`.

Rewrite using `[mul_assoc, ← hp₂c.eq, ← mul_assoc]`. Establish `e₂ : q₁ * a 0 * (q₂ * a 0) = q₁ * q₂ * a 0 * a 0`. Rewrite using `[← mul_assoc, mul_assoc q₁, ← hq₂c.eq, ← mul_assoc]`. Establish `key : (p₁ + q₁ * a 0) * (p₂ + q₂ * a 0) = p₁ * p₂ + (p₁ * q₂ + q₁ * p₂ + q₁ * q₂ * a 0) * a 0`. Rewrite using `[add_mul, mul_add, mul_add, e₁, e₂]`.

Simplify using `only [add_mul, mul_assoc, add_assoc]`. Rewrite using `[key]`. Use `Submodule.add_mem_sup ((Subalgebra.mem_toSubmodule _).2 (mul_mem hp₁ hp₂)) (Submodule.mem_map.2 ⟨p₁ * q₂ + q₁ * p₂ + q₁ * q₂ * a 0, ?_, LinearMap.mulRight_apply _ _ _⟩)` and prove the remaining obligations. Rewrite using `[Subalgebra.mem_toSubmodule]`. Conclude with `add_mem (add_mem (mul_mem (hBC hp₁) hq₂) (mul_mem hq₁ (hBC hp₂))) (mul_mem (mul_mem hq₁ hq₂) ha0)`.
-/
theorem adjoin_le_sup {V : Type} [AddCommGroup V] [Module ℂ V] {l : ℕ}
    (a : Fin (l + 1) → Module.End ℂ V) (hc : ∀ i j, Commute (a i) (a j)) :
    Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range a)) ≤
      Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range fun i : Fin l => a i.succ)) ⊔
        (Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range a))).map
          (LinearMap.mulRight ℂ (a 0)) := by
  have hBC : Algebra.adjoin ℂ (Set.range fun i : Fin l => a i.succ) ≤
      Algebra.adjoin ℂ (Set.range a) :=
    Algebra.adjoin_mono (Set.range_subset_iff.2 fun k => ⟨k.succ, rfl⟩)
  have ha0 : a 0 ∈ Algebra.adjoin ℂ (Set.range a) := Algebra.subset_adjoin ⟨0, rfl⟩
  intro y hy
  rw [Subalgebra.mem_toSubmodule] at hy
  induction hy using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    induction j using Fin.cases with
    | zero =>
      refine Submodule.mem_sup_right (Submodule.mem_map.2 ⟨1, ?_, ?_⟩)
      · exact (Subalgebra.mem_toSubmodule _).2 (one_mem _)
      · rw [LinearMap.mulRight_apply, one_mul]
    | succ k => exact Submodule.mem_sup_left (Algebra.subset_adjoin ⟨k, rfl⟩)
  | algebraMap r => exact Submodule.mem_sup_left (Subalgebra.algebraMap_mem _ r)
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | mul x y _ _ hx hy =>
    obtain ⟨p₁, hp₁, z₁, hz₁, rfl⟩ := Submodule.mem_sup.1 hx
    obtain ⟨p₂, hp₂, z₂, hz₂, rfl⟩ := Submodule.mem_sup.1 hy
    obtain ⟨q₁, hq₁, rfl⟩ := Submodule.mem_map.1 hz₁
    obtain ⟨q₂, hq₂, rfl⟩ := Submodule.mem_map.1 hz₂
    rw [Subalgebra.mem_toSubmodule] at hp₁ hp₂ hq₁ hq₂
    rw [LinearMap.mulRight_apply, LinearMap.mulRight_apply]
    have hp₂c : Commute p₂ (a 0) := GlobalTheory.CompanionTheory.CommStep.commute_of_mem_adjoin a hc 0 (hBC hp₂)
    have hq₂c : Commute q₂ (a 0) := GlobalTheory.CompanionTheory.CommStep.commute_of_mem_adjoin a hc 0 hq₂
    have e₁ : q₁ * a 0 * p₂ = q₁ * p₂ * a 0 := by
      rw [mul_assoc, ← hp₂c.eq, ← mul_assoc]
    have e₂ : q₁ * a 0 * (q₂ * a 0) = q₁ * q₂ * a 0 * a 0 := by
      rw [← mul_assoc, mul_assoc q₁, ← hq₂c.eq, ← mul_assoc]
    have key : (p₁ + q₁ * a 0) * (p₂ + q₂ * a 0) =
        p₁ * p₂ + (p₁ * q₂ + q₁ * p₂ + q₁ * q₂ * a 0) * a 0 := by
      rw [add_mul, mul_add, mul_add, e₁, e₂]
      simp only [add_mul, mul_assoc, add_assoc]
    rw [key]
    refine Submodule.add_mem_sup ((Subalgebra.mem_toSubmodule _).2 (mul_mem hp₁ hp₂))
      (Submodule.mem_map.2 ⟨p₁ * q₂ + q₁ * p₂ + q₁ * q₂ * a 0, ?_, LinearMap.mulRight_apply _ _ _⟩)
    rw [Subalgebra.mem_toSubmodule]
    exact add_mem (add_mem (mul_mem (hBC hp₁) hq₂) (mul_mem hq₁ (hBC hp₂)))
      (mul_mem (mul_mem hq₁ hq₂) ha0)

/- English proof (translation)
Establish `h` using `Submodule.map_mono (f := LinearMap.mulRight ℂ (a 0 ^ k)) (GlobalTheory.CompanionTheory.CommStep.adjoin_le_sup a hc)`. Establish `hcomp : (LinearMap.mulRight ℂ (a 0 ^ k)).comp (LinearMap.mulRight ℂ (a 0)) = LinearMap.mulRight ℂ (a 0 ^ (k + 1))` using `LinearMap.ext fun b => by`. Simplify using `only [LinearMap.comp_apply, LinearMap.mulRight_apply, pow_succ', mul_assoc]`. Rewrite `h` using `[Submodule.map_sup, ← Submodule.map_comp, hcomp]`. Establish `h1` using `Submodule.finrank_mono h`.

Establish `h2` using `Submodule.finrank_add_le_finrank_add_finrank ((Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range fun i : Fin l => a i.succ))).map (LinearMap.mulRight ℂ (a 0 ^ k))) ((Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range a))).map (LinearMap.mulRight ℂ (a 0 ^ (k + 1))))`. Establish `h3` using `Submodule.finrank_map_le (LinearMap.mulRight ℂ (a 0 ^ k)) (Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range fun i : Fin l => a i.succ)))`. Rewrite `h3` using `[Subalgebra.finrank_toSubmodule]`. Use linear arithmetic over natural numbers and integers.
-/
theorem finrank_map_pow_le {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] {l : ℕ}
    (a : Fin (l + 1) → Module.End ℂ V) (hc : ∀ i j, Commute (a i) (a j)) (k : ℕ) :
    finrank ℂ ((Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range a))).map
        (LinearMap.mulRight ℂ (a 0 ^ k))) ≤
      finrank ℂ (Algebra.adjoin ℂ (Set.range fun i : Fin l => a i.succ)) +
        finrank ℂ ((Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range a))).map
          (LinearMap.mulRight ℂ (a 0 ^ (k + 1)))) := by
  have h := Submodule.map_mono (f := LinearMap.mulRight ℂ (a 0 ^ k))
    (GlobalTheory.CompanionTheory.CommStep.adjoin_le_sup a hc)
  have hcomp : (LinearMap.mulRight ℂ (a 0 ^ k)).comp (LinearMap.mulRight ℂ (a 0)) =
      LinearMap.mulRight ℂ (a 0 ^ (k + 1)) :=
    LinearMap.ext fun b => by
      simp only [LinearMap.comp_apply, LinearMap.mulRight_apply, pow_succ', mul_assoc]
  rw [Submodule.map_sup, ← Submodule.map_comp, hcomp] at h
  have h1 := Submodule.finrank_mono h
  have h2 := Submodule.finrank_add_le_finrank_add_finrank
    ((Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range fun i : Fin l => a i.succ))).map
      (LinearMap.mulRight ℂ (a 0 ^ k)))
    ((Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range a))).map
      (LinearMap.mulRight ℂ (a 0 ^ (k + 1))))
  have h3 := Submodule.finrank_map_le (LinearMap.mulRight ℂ (a 0 ^ k))
    (Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range fun i : Fin l => a i.succ)))
  rw [Subalgebra.finrank_toSubmodule] at h3
  omega

/- English proof (translation)
Introduce `V _ _ _ l a hc x`. Proceed by induction on `x with`. Consider the case `zero`. Establish `hid : LinearMap.mulRight ℂ (a 0 ^ 0) = LinearMap.id` using `LinearMap.ext fun b => by simp`. Rewrite using `[hid, Submodule.map_id, Nat.zero_mul, Nat.zero_add, Subalgebra.finrank_toSubmodule]`.

Consider the case `succ x ih`. Establish `h` using `GlobalTheory.CompanionTheory.CommStep.finrank_map_pow_le a hc x`. Rewrite using `[add_mul, one_mul]`. Use linear arithmetic over natural numbers and integers.
-/
theorem comm_step : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (l : ℕ)
    (a : Fin (l + 1) → Module.End ℂ V), (∀ i j, Commute (a i) (a j)) → ∀ x : ℕ,
    Module.finrank ℂ (Algebra.adjoin ℂ (Set.range a)) ≤
      x * Module.finrank ℂ (Algebra.adjoin ℂ (Set.range fun i : Fin l => a i.succ)) +
        Module.finrank ℂ ((Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range a))).map
          (LinearMap.mulRight ℂ (a 0 ^ x))) := by
  intro V _ _ _ l a hc x
  induction x with
  | zero =>
    have hid : LinearMap.mulRight ℂ (a 0 ^ 0) = LinearMap.id :=
      LinearMap.ext fun b => by simp
    rw [hid, Submodule.map_id, Nat.zero_mul, Nat.zero_add, Subalgebra.finrank_toSubmodule]
  | succ x ih =>
    have h := GlobalTheory.CompanionTheory.CommStep.finrank_map_pow_le a hc x
    rw [add_mul, one_mul]
    omega

end GlobalTheory.CompanionTheory.CommStep
