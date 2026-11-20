import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent

namespace GlobalTheory.ClearDenominatorsIntegral

open GlobalTheory.UnitLemma

/- English proof (translation)
Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩`. Consider the case `zero => exact ⟨1, one_ne_zero, by simp⟩`. Consider the case `add y z _ _ hy hz`. Take `⟨d₁, hd₁, h₁⟩` from `hy`.

Take `⟨d₂, hd₂, h₂⟩` from `hz`. Use `⟨d₁ * d₂, mul_ne_zero hd₁ hd₂, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_add]`. Use `M.add_mem ?_ ?_` and prove the remaining obligations. Rewrite using `[mul_comm, mul_smul]`.

Conclude with `M.smul_mem _ h₁`. Rewrite using `[mul_smul]`. Conclude with `M.smul_mem _ h₂`. Consider the case `smul e y _ hy`. Take `⟨d, hd, h⟩` from `hy`.

Take `⟨⟨a, b⟩, hab⟩` from `IsLocalization.surj (nonZeroDivisors (UQ.O K)) e`. Establish `hb : (b : UQ.O K) ≠ 0` using `nonZeroDivisors.coe_ne_zero b`. Use `⟨(b : UQ.O K) * d, mul_ne_zero hb hd, ?_⟩` and prove the remaining obligations. Establish `key : (b : UQ.O K) • (e • y) = a • y`. Rewrite using `[← smul_assoc, Algebra.smul_def, mul_comm, hab, algebraMap_smul]`.

Rewrite using `[mul_comm, mul_smul, key, smul_smul, mul_comm, ← smul_smul]`. Conclude with `M.smul_mem _ h`.
-/
theorem clear_denominators (K : UQ) {V : Type} [AddCommGroup V] [Module (UQ.E K) V] [Module (UQ.O K) V]
    [IsScalarTower (UQ.O K) (UQ.E K) V] (M : Submodule (UQ.O K) V) {x : V}
    (hx : x ∈ Submodule.span (UQ.E K) (↑M : Set V)) :
    ∃ (d : UQ.O K), d ≠ (0 : UQ.O K) ∧ d • x ∈ M := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨d₁, hd₁, h₁⟩ := hy
    obtain ⟨d₂, hd₂, h₂⟩ := hz
    refine ⟨d₁ * d₂, mul_ne_zero hd₁ hd₂, ?_⟩
    rw [smul_add]
    refine M.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact M.smul_mem _ h₁
    · rw [mul_smul]; exact M.smul_mem _ h₂
  | smul e y _ hy =>
    obtain ⟨d, hd, h⟩ := hy
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors (UQ.O K)) e
    have hb : (b : UQ.O K) ≠ 0 := nonZeroDivisors.coe_ne_zero b
    refine ⟨(b : UQ.O K) * d, mul_ne_zero hb hd, ?_⟩
    have key : (b : UQ.O K) • (e • y) = a • y := by
      rw [← smul_assoc, Algebra.smul_def, mul_comm, hab, algebraMap_smul]
    rw [mul_comm, mul_smul, key, smul_smul, mul_comm, ← smul_smul]
    exact M.smul_mem _ h

/- English proof (translation)
Introduce `K _ _ _ _ _ M _ hx` and use `clear_denominators K M hx`.
-/
theorem main : ∀ (K : GlobalTheory.UnitLemma.UQ) {V : Type} [inst : AddCommGroup V] [inst_1 : Module (GlobalTheory.UnitLemma.UQ.E K) V] [inst_2 : Module (GlobalTheory.UnitLemma.UQ.O K) V] [IsScalarTower (GlobalTheory.UnitLemma.UQ.O K) (GlobalTheory.UnitLemma.UQ.E K) V] (M : Submodule (GlobalTheory.UnitLemma.UQ.O K) V) {x : V}, x ∈ Submodule.span (GlobalTheory.UnitLemma.UQ.E K) (↑M : Set V) → ∃ (d : GlobalTheory.UnitLemma.UQ.O K), d ≠ (0 : GlobalTheory.UnitLemma.UQ.O K) ∧ d • x ∈ M :=
  fun K _ _ _ _ _ M _ hx => clear_denominators K M hx

end GlobalTheory.ClearDenominatorsIntegral
