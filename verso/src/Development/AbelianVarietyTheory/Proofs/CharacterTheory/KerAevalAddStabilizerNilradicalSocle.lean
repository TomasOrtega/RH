import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt

open Polynomial GlobalTheory.CuspGL

namespace GlobalTheory.CuspGL

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => exact ⟨fun x hx => ⟨by simp, by simpa using hx⟩, fun x => by simp⟩`. Consider the case `succ n ih`. Use `⟨fun x hx => ?_, fun x => ?_⟩` and prove the remaining obligations. Take `⟨h1, h2⟩` from `ih.1 x hx`.

Simplify using `only [pow_succ', Module.End.mul_apply, LinearMap.add_apply, h1, hh.2 _ h2, add_zero, true_and]`. Conclude with `hg _ h2`. Establish `h1` using `hg _ (ih.2 x)`. Establish `h2` using `hh.1 (((g + h) ^ n) x)`. Use `A.add_mem h1 h2` as an intermediate fact.

Simplify using `only [pow_succ', Module.End.mul_apply, LinearMap.add_apply]`. Rewrite `this` using `[map_sub]`. Use `this using 1` and compare the differences between its conclusion and the goal. Normalize the expressions using the abelian group laws.
-/
theorem pow_add_nilRad {A : Submodule F V} {g h : Module.End F V} (hg : ∀ x ∈ A, g x ∈ A)
    (hh : h ∈ nilRad A) (n : ℕ) :
    (∀ x ∈ A, ((g + h) ^ n) x = (g ^ n) x ∧ (g ^ n) x ∈ A) ∧ ∀ x, ((g + h) ^ n) x - (g ^ n) x ∈ A := by
  induction n with
  | zero => exact ⟨fun x hx => ⟨by simp, by simpa using hx⟩, fun x => by simp⟩
  | succ n ih =>
    refine ⟨fun x hx => ?_, fun x => ?_⟩
    · obtain ⟨h1, h2⟩ := ih.1 x hx
      simp only [pow_succ', Module.End.mul_apply, LinearMap.add_apply, h1, hh.2 _ h2, add_zero, true_and]
      exact hg _ h2
    · have h1 := hg _ (ih.2 x)
      have h2 := hh.1 (((g + h) ^ n) x)
      have := A.add_mem h1 h2
      simp only [pow_succ', Module.End.mul_apply, LinearMap.add_apply]
      rw [map_sub] at this
      convert this using 1
      abel

/- English proof (translation)
Proceed by induction on `p using Polynomial.induction_on' with`. Consider the case `add p q hp hq`. Use `⟨fun x hx => ?_, fun x => ?_⟩` and prove the remaining obligations. Simplify using `only [map_add, LinearMap.add_apply, hp.1 x hx, hq.1 x hx]`. Use `A.add_mem (hp.2 x) (hq.2 x)` as an intermediate fact.

Simplify using `only [map_add, LinearMap.add_apply]`. Use `this using 1` and compare the differences between its conclusion and the goal. Normalize the expressions using the abelian group laws. Consider the case `monomial n a`. Establish `H` using `pow_add_nilRad hg hh n`.

Use `⟨fun x hx => ?_, fun x => ?_⟩` and prove the remaining obligations. Simplify using `only [aeval_monomial, Module.End.mul_apply, (H.1 x hx).1]`. Simplify using `only [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply, ← smul_sub]`. Conclude with `A.smul_mem _ (H.2 x)`.
-/
theorem aeval_add_nilRad {A : Submodule F V} {g h : Module.End F V} (hg : ∀ x ∈ A, g x ∈ A)
    (hh : h ∈ nilRad A) (p : F[X]) :
    (∀ x ∈ A, aeval (g + h) p x = aeval g p x) ∧ ∀ x, aeval (g + h) p x - aeval g p x ∈ A := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    refine ⟨fun x hx => ?_, fun x => ?_⟩
    · simp only [map_add, LinearMap.add_apply, hp.1 x hx, hq.1 x hx]
    · have := A.add_mem (hp.2 x) (hq.2 x)
      simp only [map_add, LinearMap.add_apply]
      convert this using 1
      abel
  | monomial n a =>
    have H := pow_add_nilRad hg hh n
    refine ⟨fun x hx => ?_, fun x => ?_⟩
    · simp only [aeval_monomial, Module.End.mul_apply, (H.1 x hx).1]
    · simp only [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply, ← smul_sub]
      exact A.smul_mem _ (H.2 x)

/- English proof (translation)
Introduce `F _ V _ _ _ g h f hh`. Establish `hg : ∀ x ∈ LinearMap.ker (aeval g f), g x ∈ LinearMap.ker (aeval g f)`. Introduce `x hx`. Rewrite `hx`, the goal using `[LinearMap.mem_ker]`. Establish `: aeval g f * g = g * aeval g f`.

Establish `h1 : aeval g (f * X) = aeval g (X * f)` using `by rw [mul_comm]`. Simplify using `using h1`. Rewrite using `[← Module.End.mul_apply, this, Module.End.mul_apply, hx, map_zero]`. Use `⟨fun x hx => ?_, fun he j => ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.mem_ker, (aeval_add_nilRad hg hh f).1 x hx]`.

Conclude with `hx`. Establish `: LinearMap.ker (aeval g (f ^ j)) = LinearMap.ker (aeval (g + h) (f ^ j))`. Consider the cases of `j with`. Consider the case `zero`. Use extensionality with `x`.

Simplify using the standard rewrite rules. Consider the case `succ j`. Use extensionality with `x`. Establish `H` using `(aeval_add_nilRad hg hh (f ^ j)).2 x`. Establish `e1 : x ∈ LinearMap.ker (aeval g (f ^ (j + 1))) ↔ aeval g (f ^ j) x ∈ LinearMap.ker (aeval g f)`.

Rewrite using `[pow_succ', map_mul, LinearMap.mem_ker, LinearMap.mem_ker, Module.End.mul_apply]`. Establish `e2 : x ∈ LinearMap.ker (aeval (g + h) (f ^ (j + 1))) ↔ aeval (g + h) (f ^ j) x ∈ LinearMap.ker (aeval (g + h) f)`. Rewrite using `[pow_succ', map_mul, LinearMap.mem_ker, LinearMap.mem_ker, Module.End.mul_apply]`. Rewrite using `[e1, e2, he]`. Prove the components needed by the constructor for the conclusion.

Introduce `a`. Use `Submodule.add_mem _ H a` as an intermediate fact. Rewrite `this` using `[sub_add_cancel]`. Then use the resulting hypothesis. Introduce `a`. Use `Submodule.sub_mem _ a H` as an intermediate fact.

Rewrite `this` using `[sub_sub_cancel]`. Then use the resulting hypothesis. Rewrite using `[this]`.
-/
theorem ker_aeval_add_nilRad :
    ∀ (F : Type) [Field F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (g h : Module.End F V) (f : F[X]), h ∈ nilRad (LinearMap.ker (aeval g f)) → LinearMap.ker (aeval g f) ≤ LinearMap.ker (aeval (g + h) f) ∧ (LinearMap.ker (aeval (g + h) f) = LinearMap.ker (aeval g f) → ∀ j : ℕ, Module.finrank F (LinearMap.ker (aeval g (f ^ j))) = Module.finrank F (LinearMap.ker (aeval (g + h) (f ^ j)))) := by
  intro F _ V _ _ _ g h f hh
  have hg : ∀ x ∈ LinearMap.ker (aeval g f), g x ∈ LinearMap.ker (aeval g f) := by
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    have : aeval g f * g = g * aeval g f := by
      have h1 : aeval g (f * X) = aeval g (X * f) := by rw [mul_comm]
      simpa using h1
    rw [← Module.End.mul_apply, this, Module.End.mul_apply, hx, map_zero]
  refine ⟨fun x hx => ?_, fun he j => ?_⟩
  · rw [LinearMap.mem_ker, (aeval_add_nilRad hg hh f).1 x hx]
    exact hx
  · have : LinearMap.ker (aeval g (f ^ j)) = LinearMap.ker (aeval (g + h) (f ^ j)) := by
      cases j with
      | zero =>
        ext x
        simp
      | succ j =>
        ext x
        have H := (aeval_add_nilRad hg hh (f ^ j)).2 x
        have e1 : x ∈ LinearMap.ker (aeval g (f ^ (j + 1))) ↔
            aeval g (f ^ j) x ∈ LinearMap.ker (aeval g f) := by
          rw [pow_succ', map_mul, LinearMap.mem_ker, LinearMap.mem_ker, Module.End.mul_apply]
        have e2 : x ∈ LinearMap.ker (aeval (g + h) (f ^ (j + 1))) ↔
            aeval (g + h) (f ^ j) x ∈ LinearMap.ker (aeval (g + h) f) := by
          rw [pow_succ', map_mul, LinearMap.mem_ker, LinearMap.mem_ker, Module.End.mul_apply]
        rw [e1, e2, he]
        constructor
        · intro a
          have := Submodule.add_mem _ H a
          rwa [sub_add_cancel] at this
        · intro a
          have := Submodule.sub_mem _ a H
          rwa [sub_sub_cancel] at this
    rw [this]

end GlobalTheory.CuspGL
