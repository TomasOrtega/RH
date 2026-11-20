import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PowerBoundedIntegrality.Development

namespace PI.PowBddIntWork

open Matrix NumberField

/- English proof (translation)
Introduce `E _ _ k γ N hN hint`. Set `L : (Fin k → Fin k → 𝓞 E) →ₗ[ℤ] Matrix (Fin k) (Fin k) E` to `{ toFun := fun B => Matrix.of fun i j => ((N : E))⁻¹ * algebraMap (𝓞 E) E (B i j) map_add' := fun B C => by ext i j; simp [mul_add] map_smul' := fun c B => by`. Use extensionality with `i j`. Apply the tactic sequence `first | (simp [zsmul_eq_mul]; ring) | simp [zsmul_eq_mul] }`. Establish `hfg : (Submodule.map L ⊤).FG` using `Module.Finite.fg_top.map L`.

Establish `hle : Subalgebra.toSubmodule (Algebra.adjoin ℤ {γ}) ≤ Submodule.map L ⊤`. Rewrite using `[Algebra.adjoin_eq_span, Submodule.span_le]`. Introduce `x hx`. Take `⟨n, rfl⟩` from `Submonoid.mem_closure_singleton.1 hx`. Use `⟨fun i j => IsIntegralClosure.mk' (𝓞 E) ((N : E) * (γ ^ n) i j) (hint n i j), trivial, ?_⟩` and prove the remaining obligations.

Establish `hN' : (N : E) ≠ 0` using `by exact_mod_cast hN.ne'`. Use extensionality with `i j`. Simplify using `[L, IsIntegralClosure.algebraMap_mk', hN']`. Use `haveI := isNoetherian_of_fg_of_noetherian _ hfg`. Conclude with `isIntegral_of_submodule_noetherian (Algebra.adjoin ℤ {γ}) (isNoetherian_of_le hle) γ (Algebra.subset_adjoin (Set.mem_singleton γ))`.
-/
theorem stepA : StepA := by
  intro E _ _ k γ N hN hint
  classical
  let L : (Fin k → Fin k → 𝓞 E) →ₗ[ℤ] Matrix (Fin k) (Fin k) E :=
    { toFun := fun B => Matrix.of fun i j => ((N : E))⁻¹ * algebraMap (𝓞 E) E (B i j)
      map_add' := fun B C => by ext i j; simp [mul_add]
      map_smul' := fun c B => by
        ext i j
        first | (simp [zsmul_eq_mul]; ring) | simp [zsmul_eq_mul] }
  have hfg : (Submodule.map L ⊤).FG := Module.Finite.fg_top.map L
  have hle : Subalgebra.toSubmodule (Algebra.adjoin ℤ {γ}) ≤ Submodule.map L ⊤ := by
    rw [Algebra.adjoin_eq_span, Submodule.span_le]
    intro x hx
    obtain ⟨n, rfl⟩ := Submonoid.mem_closure_singleton.1 hx
    refine ⟨fun i j => IsIntegralClosure.mk' (𝓞 E) ((N : E) * (γ ^ n) i j) (hint n i j), trivial, ?_⟩
    have hN' : (N : E) ≠ 0 := by exact_mod_cast hN.ne'
    ext i j
    simp [L, IsIntegralClosure.algebraMap_mk', hN']
  haveI := isNoetherian_of_fg_of_noetherian _ hfg
  exact isIntegral_of_submodule_noetherian (Algebra.adjoin ℤ {γ}) (isNoetherian_of_le hle) γ
    (Algebra.subset_adjoin (Set.mem_singleton γ))

end PI.PowBddIntWork
