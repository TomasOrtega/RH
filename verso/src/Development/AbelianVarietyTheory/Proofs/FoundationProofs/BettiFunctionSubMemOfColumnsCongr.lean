import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ

/- English proof (translation)
Establish `h0` using `Ideal.Quotient.eq.2 (h 0)`. Establish `h1` using `Ideal.Quotient.eq.2 (h 1)`. Rewrite using `[← Ideal.Quotient.eq]`. Simplify using `only [map_mul, map_pow, h0, h1]`.
-/
theorem mono_sub_mem_of_sub_mem {R : Type} [CommRing R] (I : Ideal R) (u v : Fin 2 → R)
    (h : ∀ i, u i - v i ∈ I) (a b : ℕ) : u 0 ^ a * u 1 ^ b - v 0 ^ a * v 1 ^ b ∈ I := by
  have h0 := Ideal.Quotient.eq.2 (h 0)
  have h1 := Ideal.Quotient.eq.2 (h 1)
  rw [← Ideal.Quotient.eq]
  simp only [map_mul, map_pow, h0, h1]

/- English proof (translation)
Proceed by induction on `hb using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨c, -, hc⟩` from `hx.1`. Rewrite using `[hc u, hc v, ← Finset.sum_sub_distrib]`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[← sub_smul]`. Conclude with `Submodule.smul_mem_smul (mono_sub_mem_of_sub_mem _ u v huv _ _) Submodule.mem_top`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy`. Use `Submodule.add_mem _ hx hy` as an intermediate fact.

Simplify using `only [Pi.add_apply]`. Use `this using 1` and compare the differences between its conclusion and the goal. Normalize the expressions using the abelian group laws. Consider the case `smul r x _ hx`. Simplify using `only [Pi.smul_apply, ← smul_sub]`.

Conclude with `Submodule.smul_mem _ r hx`.
-/
theorem Tower.B_sub_mem {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (N l w : ℕ)
    [Fact l.Prime] (b : X.Fn l) (hb : b ∈ X.B N l w) (n : ℕ) (u v : Fin 2 → ℤ_[l])
    (huv : ∀ i, u i - v i ∈ (idl l) ^ n) :
    b u - b v ∈ (idl l) ^ n • (⊤ : Submodule ℤ_[l] (X.Khat l)) := by
  induction hb using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, -, hc⟩ := hx.1
    rw [hc u, hc v, ← Finset.sum_sub_distrib]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [← sub_smul]
    exact Submodule.smul_mem_smul (mono_sub_mem_of_sub_mem _ u v huv _ _) Submodule.mem_top
  | zero => simp
  | add x y _ _ hx hy =>
    have := Submodule.add_mem _ hx hy
    simp only [Pi.add_apply]
    convert this using 1
    abel
  | smul r x _ hx =>
    simp only [Pi.smul_apply, ← smul_sub]
    exact Submodule.smul_mem _ r hx

end GlobalTheory.KZ

/- English proof (translation)
Introduce `X N l w _ b hb n u v h` and use `Tower.B_sub_mem X N l w b hb n u v h`.
-/
example : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (N l w : ℕ) [Fact l.Prime] (b : X.Fn l), b ∈ X.B N l w → ∀ (n : ℕ) (u v : Fin 2 → ℤ_[l]), (∀ i, u i - v i ∈ (idl l) ^ n) → b u - b v ∈ (idl l) ^ n • (⊤ : Submodule ℤ_[l] (X.Khat l)) :=
  fun X N l w _ b hb n u v h => Tower.B_sub_mem X N l w b hb n u v h
