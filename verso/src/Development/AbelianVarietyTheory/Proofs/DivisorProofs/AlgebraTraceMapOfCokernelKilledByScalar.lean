import Mathlib
open IsLocalRing TensorProduct

namespace GlobalTheory

/- English proof (translation)
Use `choose g hg using fun b => (AlgHom.mem_range φ).1 (hr b)`. Set `gl : B →ₗ[S] A` to `{ toFun := g map_add' := by`. Introduce `b c`. Apply `hφ` to reduce the goal to its premises. Rewrite using `[map_add, hg, hg, hg, smul_add]`.

Use the proof step `map_smul' := by`. Introduce `r b`. Apply `hφ` to reduce the goal to its premises. Rewrite using `[hg, RingHom.id_apply, map_smul, hg, smul_comm] }`. Establish `h1 : φ.toLinearMap ∘ₗ gl = s • LinearMap.id`.

Use extensionality with `b`. Simplify using `[gl, hg]`. Establish `h2 : gl ∘ₗ φ.toLinearMap = s • LinearMap.id`. Use extensionality with `a`. Apply `hφ` to reduce the goal to its premises.

Simplify using `[gl, hg]`. Establish `h3 : Algebra.lmul S B (φ x) ∘ₗ φ.toLinearMap = φ.toLinearMap ∘ₗ Algebra.lmul S A x`. Use extensionality with `a`. Simplify using the standard rewrite rules. Establish `key : s * Algebra.trace S B (φ x) = s * Algebra.trace S A x`.

Rewrite using `[Algebra.trace_apply, Algebra.trace_apply]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[h1, LinearMap.comp_smul, LinearMap.comp_id, map_smul, smul_eq_mul]`. Use `_ = LinearMap.trace S B (φ.toLinearMap ∘ₗ (Algebra.lmul S A x ∘ₗ gl)) := by`. Rewrite using `[← LinearMap.comp_assoc, h3, LinearMap.comp_assoc]`.

Use `_ = LinearMap.trace S A ((Algebra.lmul S A x ∘ₗ gl) ∘ₗ φ.toLinearMap) := by`. Rewrite using `[LinearMap.trace_comp_comm']`. Use `_ = s * LinearMap.trace S A (Algebra.lmul S A x) := by`. Rewrite using `[LinearMap.comp_assoc, h2, LinearMap.comp_smul, LinearMap.comp_id, map_smul, smul_eq_mul]`. Conclude with `mul_left_cancel₀ hs key`.
-/
theorem algebraTrace_map_of_cokernel_killed (S A B : Type) [CommRing S] [IsDomain S] [CommRing A]
    [Algebra S A] [Module.Free S A] [Module.Finite S A] [CommRing B] [Algebra S B]
    [Module.Free S B] [Module.Finite S B] (φ : A →ₐ[S] B) (hφ : Function.Injective φ)
    (s : S) (hs : s ≠ 0) (hr : ∀ b : B, s • b ∈ φ.range) (x : A) :
    Algebra.trace S B (φ x) = Algebra.trace S A x := by
  classical
  choose g hg using fun b => (AlgHom.mem_range φ).1 (hr b)
  let gl : B →ₗ[S] A :=
    { toFun := g
      map_add' := by
        intro b c
        apply hφ
        rw [map_add, hg, hg, hg, smul_add]
      map_smul' := by
        intro r b
        apply hφ
        rw [hg, RingHom.id_apply, map_smul, hg, smul_comm] }
  have h1 : φ.toLinearMap ∘ₗ gl = s • LinearMap.id := by
    ext b
    simp [gl, hg]
  have h2 : gl ∘ₗ φ.toLinearMap = s • LinearMap.id := by
    ext a
    apply hφ
    simp [gl, hg]
  have h3 : Algebra.lmul S B (φ x) ∘ₗ φ.toLinearMap = φ.toLinearMap ∘ₗ Algebra.lmul S A x := by
    ext a
    simp
  have key : s * Algebra.trace S B (φ x) = s * Algebra.trace S A x := by
    rw [Algebra.trace_apply, Algebra.trace_apply]
    calc s * LinearMap.trace S B (Algebra.lmul S B (φ x))
        = LinearMap.trace S B (Algebra.lmul S B (φ x) ∘ₗ (φ.toLinearMap ∘ₗ gl)) := by
          rw [h1, LinearMap.comp_smul, LinearMap.comp_id, map_smul, smul_eq_mul]
      _ = LinearMap.trace S B (φ.toLinearMap ∘ₗ (Algebra.lmul S A x ∘ₗ gl)) := by
          rw [← LinearMap.comp_assoc, h3, LinearMap.comp_assoc]
      _ = LinearMap.trace S A ((Algebra.lmul S A x ∘ₗ gl) ∘ₗ φ.toLinearMap) := by
          rw [LinearMap.trace_comp_comm']
      _ = s * LinearMap.trace S A (Algebra.lmul S A x) := by
          rw [LinearMap.comp_assoc, h2, LinearMap.comp_smul, LinearMap.comp_id, map_smul,
            smul_eq_mul]
  exact mul_left_cancel₀ hs key

/- English proof (translation)
The claim follows from `algebraTrace_map_of_cokernel_killed`.
-/
example : ∀ (S A B : Type) [CommRing S] [IsDomain S] [CommRing A] [Algebra S A] [Module.Free S A] [Module.Finite S A] [CommRing B] [Algebra S B] [Module.Free S B] [Module.Finite S B] (φ : A →ₐ[S] B), Function.Injective φ → ∀ s : S, s ≠ 0 → (∀ b : B, s • b ∈ φ.range) → ∀ x : A, Algebra.trace S B (φ x) = Algebra.trace S A x :=
  algebraTrace_map_of_cokernel_killed

end GlobalTheory
