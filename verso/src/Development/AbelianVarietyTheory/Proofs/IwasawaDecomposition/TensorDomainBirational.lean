import Mathlib
open IsLocalRing TensorProduct

namespace GlobalTheory

/- English proof (translation)
Establish `hinc : Function.Injective (Algebra.TensorProduct.includeRight : R →ₐ[A] TensorProduct A B R)`. Establish `hcomp : ∀ r : R, (Algebra.TensorProduct.includeRight : R →ₐ[A] TensorProduct A B R) r = (LinearMap.rTensor R (Algebra.linearMap A B)) ((TensorProduct.lid A R).symm r)`. Introduce `r`. Simplify using `[Algebra.TensorProduct.includeRight_apply]`. Introduce `r r' h`.

Rewrite `h` using `[hcomp, hcomp]`. Establish `h1` using `Module.Flat.rTensor_preserves_injective_linearMap (M := R) (Algebra.linearMap A B) _hAB h`. Conclude with `(TensorProduct.lid A R).symm.injective h1`. Establish `hmove : ∀ (a : A) (r : R), (algebraMap A B a) ⊗ₜ[A] r = (1 : B) ⊗ₜ[A] (algebraMap A R a * r)`. Introduce `a r`.

Rewrite using `[Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, Algebra.smul_def]`. Establish `hmulInj : ∀ c : B, c ≠ 0 → ∀ x : TensorProduct A B R, (c ⊗ₜ[A] (1 : R)) * x = 0 → x = 0`. Introduce `c hc x hx`. Establish `heq : ∀ y : TensorProduct A B R, (c ⊗ₜ[A] (1 : R)) * y = (LinearMap.rTensor R (LinearMap.mulLeft A c)) y`. Introduce `y`.

Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul b r => simp [Algebra.TensorProduct.tmul_mul_tmul]`. Consider the case `add y z hy hz => rw [mul_add, map_add, hy, hz]`. Establish `hinjc : Function.Injective (LinearMap.mulLeft A c)`.

Introduce `u v huv`. Conclude with `mul_left_cancel₀ hc huv`. Use `Module.Flat.rTensor_preserves_injective_linearMap (M := R) _ hinjc` as an intermediate fact. Apply `this` to reduce the goal to its premises. Rewrite using `[← heq, hx, map_zero]`.

Establish `hden : ∀ x : TensorProduct A B R, ∃ s : A, algebraMap A B s ≠ 0 ∧ ∃ r : R, (algebraMap A B s ⊗ₜ[A] (1 : R)) * x = (1 : B) ⊗ₜ[A] r`. Introduce `x`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => exact ⟨1, by simp, 0, by simp⟩`. Consider the case `tmul b r`.

Take `⟨a, s, hs, hsb⟩` from `hfrac b`. Use `⟨s, hs, algebraMap A R a * r, ?_⟩` and prove the remaining obligations. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, hsb, one_mul, hmove]`. Consider the case `add x y hx hy`. Take `⟨s, hs, r, hr⟩` from `hx`.

Take `⟨s', hs', r', hr'⟩` from `hy`. Use `⟨s * s', by rw [map_mul]; exact mul_ne_zero hs hs', algebraMap A R s' * r + algebraMap A R s * r', ?_⟩` and prove the remaining obligations. Establish `e1 : (algebraMap A B (s * s') ⊗ₜ[A] (1 : R)) = (algebraMap A B s' ⊗ₜ[A] (1 : R)) * (algebraMap A B s ⊗ₜ[A] (1 : R))`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, one_mul, map_mul, mul_comm]`. Establish `e2 : (algebraMap A B (s * s') ⊗ₜ[A] (1 : R)) = (algebraMap A B s ⊗ₜ[A] (1 : R)) * (algebraMap A B s' ⊗ₜ[A] (1 : R))`.

Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, one_mul, map_mul]`. Rewrite using `[mul_add]`. Use `conv_lhs => arg 1`. Rewrite using `[e1, mul_assoc, hr]`. Use `conv_lhs => arg 2`.

Rewrite using `[e2, mul_assoc, hr']`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_one, hmove, hmove, one_mul, one_mul, ← TensorProduct.tmul_add]`. Use `haveI : Nontrivial (TensorProduct A B R) := by`. Use `⟨⟨Algebra.TensorProduct.includeRight (1 : R), Algebra.TensorProduct.includeRight (0 : R), ?_⟩⟩` and prove the remaining obligations. Introduce `h`.

Conclude with `one_ne_zero (hinc h)`. Use `haveI : NoZeroDivisors (TensorProduct A B R) := by`. Use `⟨fun {x y} hxy => ?_⟩` and prove the remaining obligations. Take `⟨s, hs, r, hr⟩` from `hden x`. Take `⟨s', hs', r', hr'⟩` from `hden y`.

Establish `hprod : (1 : B) ⊗ₜ[A] (r * r') = 0`. Establish `: ((algebraMap A B s ⊗ₜ[A] (1 : R)) * x) * ((algebraMap A B s' ⊗ₜ[A] (1 : R)) * y) = 0`. Rewrite using `[mul_mul_mul_comm, hxy, mul_zero]`. Rewrite `this` using `[hr, hr', Algebra.TensorProduct.tmul_mul_tmul, one_mul]`. Conclude with `this`.

Establish `hrr : r * r' = 0`. Apply `hinc` to reduce the goal to its premises. Rewrite using `[map_zero, Algebra.TensorProduct.includeRight_apply]`. Conclude with `hprod`. Break down `mul_eq_zero.mp hrr with h0 | h0` into its components or cases.

Use `left`. Apply `hmulInj _ hs` to reduce the goal to its premises. Rewrite using `[hr, h0, TensorProduct.tmul_zero]`. Use `right`. Apply `hmulInj _ hs'` to reduce the goal to its premises.

Rewrite using `[hr', h0, TensorProduct.tmul_zero]`. Conclude with `⟨NoZeroDivisors.to_isDomain _, hinc⟩`.
-/
theorem flat_baseChange_birational_isDomain_and_includeRight_injective
    (A B R : Type) [CommRing A] [CommRing B] [IsDomain B] [CommRing R] [IsDomain R]
    [Algebra A B] [Algebra A R] [Module.Flat A R]
    (_hAB : Function.Injective (algebraMap A B))
    (hfrac : ∀ b : B, ∃ a s : A, algebraMap A B s ≠ 0 ∧ algebraMap A B s * b = algebraMap A B a) :
    IsDomain (TensorProduct A B R) ∧
      Function.Injective (Algebra.TensorProduct.includeRight : R →ₐ[A] TensorProduct A B R) := by

  have hinc : Function.Injective (Algebra.TensorProduct.includeRight : R →ₐ[A] TensorProduct A B R) := by
    have hcomp : ∀ r : R, (Algebra.TensorProduct.includeRight : R →ₐ[A] TensorProduct A B R) r =
        (LinearMap.rTensor R (Algebra.linearMap A B)) ((TensorProduct.lid A R).symm r) := by
      intro r
      simp [Algebra.TensorProduct.includeRight_apply]
    intro r r' h
    rw [hcomp, hcomp] at h
    have h1 := Module.Flat.rTensor_preserves_injective_linearMap (M := R) (Algebra.linearMap A B) _hAB h
    exact (TensorProduct.lid A R).symm.injective h1

  have hmove : ∀ (a : A) (r : R), (algebraMap A B a) ⊗ₜ[A] r = (1 : B) ⊗ₜ[A] (algebraMap A R a * r) := by
    intro a r
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, Algebra.smul_def]

  have hmulInj : ∀ c : B, c ≠ 0 → ∀ x : TensorProduct A B R, (c ⊗ₜ[A] (1 : R)) * x = 0 → x = 0 := by
    intro c hc x hx
    have heq : ∀ y : TensorProduct A B R, (c ⊗ₜ[A] (1 : R)) * y =
        (LinearMap.rTensor R (LinearMap.mulLeft A c)) y := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul b r => simp [Algebra.TensorProduct.tmul_mul_tmul]
      | add y z hy hz => rw [mul_add, map_add, hy, hz]
    have hinjc : Function.Injective (LinearMap.mulLeft A c) := by
      intro u v huv
      exact mul_left_cancel₀ hc huv
    have := Module.Flat.rTensor_preserves_injective_linearMap (M := R) _ hinjc
    apply this
    rw [← heq, hx, map_zero]

  have hden : ∀ x : TensorProduct A B R, ∃ s : A, algebraMap A B s ≠ 0 ∧
      ∃ r : R, (algebraMap A B s ⊗ₜ[A] (1 : R)) * x = (1 : B) ⊗ₜ[A] r := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨1, by simp, 0, by simp⟩
    | tmul b r =>
      obtain ⟨a, s, hs, hsb⟩ := hfrac b
      refine ⟨s, hs, algebraMap A R a * r, ?_⟩
      rw [Algebra.TensorProduct.tmul_mul_tmul, hsb, one_mul, hmove]
    | add x y hx hy =>
      obtain ⟨s, hs, r, hr⟩ := hx
      obtain ⟨s', hs', r', hr'⟩ := hy
      refine ⟨s * s', by rw [map_mul]; exact mul_ne_zero hs hs',
        algebraMap A R s' * r + algebraMap A R s * r', ?_⟩
      have e1 : (algebraMap A B (s * s') ⊗ₜ[A] (1 : R)) =
          (algebraMap A B s' ⊗ₜ[A] (1 : R)) * (algebraMap A B s ⊗ₜ[A] (1 : R)) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, map_mul, mul_comm]
      have e2 : (algebraMap A B (s * s') ⊗ₜ[A] (1 : R)) =
          (algebraMap A B s ⊗ₜ[A] (1 : R)) * (algebraMap A B s' ⊗ₜ[A] (1 : R)) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, map_mul]
      rw [mul_add]
      conv_lhs => arg 1; rw [e1, mul_assoc, hr]
      conv_lhs => arg 2; rw [e2, mul_assoc, hr']
      rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_one,
        hmove, hmove, one_mul, one_mul, ← TensorProduct.tmul_add]

  haveI : Nontrivial (TensorProduct A B R) := by
    refine ⟨⟨Algebra.TensorProduct.includeRight (1 : R), Algebra.TensorProduct.includeRight (0 : R), ?_⟩⟩
    intro h
    exact one_ne_zero (hinc h)
  haveI : NoZeroDivisors (TensorProduct A B R) := by
    refine ⟨fun {x y} hxy => ?_⟩
    obtain ⟨s, hs, r, hr⟩ := hden x
    obtain ⟨s', hs', r', hr'⟩ := hden y
    have hprod : (1 : B) ⊗ₜ[A] (r * r') = 0 := by
      have : ((algebraMap A B s ⊗ₜ[A] (1 : R)) * x) * ((algebraMap A B s' ⊗ₜ[A] (1 : R)) * y) = 0 := by
        rw [mul_mul_mul_comm, hxy, mul_zero]
      rw [hr, hr', Algebra.TensorProduct.tmul_mul_tmul, one_mul] at this
      exact this
    have hrr : r * r' = 0 := by
      apply hinc
      rw [map_zero, Algebra.TensorProduct.includeRight_apply]
      exact hprod
    rcases mul_eq_zero.mp hrr with h0 | h0
    · left
      apply hmulInj _ hs
      rw [hr, h0, TensorProduct.tmul_zero]
    · right
      apply hmulInj _ hs'
      rw [hr', h0, TensorProduct.tmul_zero]
  exact ⟨NoZeroDivisors.to_isDomain _, hinc⟩

end GlobalTheory
