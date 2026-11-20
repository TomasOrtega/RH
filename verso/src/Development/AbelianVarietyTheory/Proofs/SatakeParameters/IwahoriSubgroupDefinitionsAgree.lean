import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IwahoriAdmissibleSet
import GroundTheory.AutomorphicForms.AffineBruhat
open GlobalTheory.IwFn GlobalTheory.SmGL GlobalTheory.TfJl ValuativeRel Matrix

namespace GlobalTheory.IwEq

/- English proof (translation)
Introduce `k _ _ _ _ a`. Use extensionality with `g`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨u, hu, rfl⟩`. Rewrite `hu` using `[SetLike.mem_coe, Subgroup.mem_comap, mem_borel]`.

Use `⟨u, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[SetLike.mem_coe, Subgroup.mem_comap, GroundTheory.Automorphic.mem_borel_iff]`. Introduce `i j hij`. Rewrite using `[GroundTheory.Automorphic.GLnLocal.residueReduction_apply]`. Conclude with `hu i j hij`.

Use extensionality with `i j`. Both sides reduce to the same expression. Introduce and unpack `⟨u, hu, rfl⟩`. Rewrite `hu` using `[SetLike.mem_coe, Subgroup.mem_comap, GroundTheory.Automorphic.mem_borel_iff]`. Use `⟨u, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[SetLike.mem_coe, Subgroup.mem_comap, mem_borel]`. Introduce `i j hij`. Establish `h` using `hu i j hij`. Rewrite `h` using `[GroundTheory.Automorphic.GLnLocal.residueReduction_apply]`. Conclude with `h`.

Use extensionality with `i j`. Both sides reduce to the same expression.
-/
theorem iwahori_eq_glnLocal_iwahori : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (a : ℕ),
    iwahori k (Fin a) = GroundTheory.Automorphic.GLnLocal.iwahori k a := by
  intro k _ _ _ _ a
  ext g
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, mem_borel] at hu
    refine ⟨u, ?_, ?_⟩
    · rw [SetLike.mem_coe, Subgroup.mem_comap, GroundTheory.Automorphic.mem_borel_iff]
      intro i j hij
      rw [GroundTheory.Automorphic.GLnLocal.residueReduction_apply]
      exact hu i j hij
    · ext i j
      rfl
  · rintro ⟨u, hu, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, GroundTheory.Automorphic.mem_borel_iff] at hu
    refine ⟨u, ?_, ?_⟩
    · rw [SetLike.mem_coe, Subgroup.mem_comap, mem_borel]
      intro i j hij
      have h := hu i j hij
      rw [GroundTheory.Automorphic.GLnLocal.residueReduction_apply] at h
      exact h
    · ext i j
      rfl

end GlobalTheory.IwEq
