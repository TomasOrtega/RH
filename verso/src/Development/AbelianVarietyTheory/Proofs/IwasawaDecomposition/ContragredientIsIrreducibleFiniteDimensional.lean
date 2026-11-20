import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IncludeLInjective
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

namespace GlobalTheory

/- English proof (translation)
Introduce `k _ G _ V _ _ _ ρ hρ`. Use `haveI : Nontrivial V := by`. Assume the negation of the conclusion as `hV`. Rewrite `hV` using `[not_nontrivial_iff_subsingleton]`. Conclude with `(bot_ne_top (α := Subrepresentation ρ)) (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))`.

Establish `hdualNT : Nontrivial (Module.Dual k V)` using `inferInstance`. Use `{ toNontrivial := ⟨⊥, ⊤, fun h => ?_⟩, eq_bot_or_eq_top := fun S => ?_ }` and prove the remaining obligations. Establish `h'` using `congrArg Subrepresentation.toSubmodule h`. Take `⟨x, y, hxy⟩` from `hdualNT`. Establish `hx : x ∈ (⊤ : Subrepresentation ρ.dual).toSubmodule` using `Submodule.mem_top`.

Establish `hy : y ∈ (⊤ : Subrepresentation ρ.dual).toSubmodule` using `Submodule.mem_top`. Rewrite `hx`, `hy` using `[← h']`. Conclude with `hxy (((Submodule.mem_bot k).1 hx).trans ((Submodule.mem_bot k).1 hy).symm)`. Set `T : Subrepresentation ρ` to `⟨S.toSubmodule.dualCoannihilator, fun g v hv => by`. Rewrite `hv`, the goal using `[Submodule.mem_dualCoannihilator]`.

Introduce `φ hφ`. Establish `h1` using `hv _ (S.apply_mem_toSubmodule g⁻¹ hφ)`. Simplify `h1⟩` using `[Representation.dual_apply, Module.Dual.transpose_apply]`. Establish `hST : S.toSubmodule = T.toSubmodule.dualAnnihilator` using `(Subspace.dualCoannihilator_dualAnnihilator_eq (W := S.toSubmodule)).symm`. Break down `hρ.eq_bot_or_eq_top T with hT | hT` into its components or cases.

Use `right`. Apply `Subrepresentation.toSubmodule_injective` to reduce the goal to its premises. Rewrite using `[hST, hT]`. Conclude with `Submodule.dualAnnihilator_bot`. Use `left`.

Apply `Subrepresentation.toSubmodule_injective` to reduce the goal to its premises. Rewrite using `[hST, hT]`. Conclude with `Submodule.dualAnnihilator_top`.
-/
theorem contragredient_isIrreducible : ∀ (k : Type) [Field k] (G : Type) [Group G] (V : Type) [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : Representation k G V), ρ.IsIrreducible → ρ.dual.IsIrreducible := by
  intro k _ G _ V _ _ _ ρ hρ
  haveI : Nontrivial V := by
    by_contra hV
    rw [not_nontrivial_iff_subsingleton] at hV
    exact (bot_ne_top (α := Subrepresentation ρ))
      (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))
  have hdualNT : Nontrivial (Module.Dual k V) := inferInstance
  refine { toNontrivial := ⟨⊥, ⊤, fun h => ?_⟩, eq_bot_or_eq_top := fun S => ?_ }
  · have h' := congrArg Subrepresentation.toSubmodule h
    obtain ⟨x, y, hxy⟩ := hdualNT
    have hx : x ∈ (⊤ : Subrepresentation ρ.dual).toSubmodule := Submodule.mem_top
    have hy : y ∈ (⊤ : Subrepresentation ρ.dual).toSubmodule := Submodule.mem_top
    rw [← h'] at hx hy
    exact hxy (((Submodule.mem_bot k).1 hx).trans ((Submodule.mem_bot k).1 hy).symm)
  · let T : Subrepresentation ρ := ⟨S.toSubmodule.dualCoannihilator, fun g v hv => by
      rw [Submodule.mem_dualCoannihilator] at hv ⊢
      intro φ hφ
      have h1 := hv _ (S.apply_mem_toSubmodule g⁻¹ hφ)
      simpa [Representation.dual_apply, Module.Dual.transpose_apply] using h1⟩
    have hST : S.toSubmodule = T.toSubmodule.dualAnnihilator :=
      (Subspace.dualCoannihilator_dualAnnihilator_eq (W := S.toSubmodule)).symm
    rcases hρ.eq_bot_or_eq_top T with hT | hT
    · right
      apply Subrepresentation.toSubmodule_injective
      rw [hST, hT]
      exact Submodule.dualAnnihilator_bot
    · left
      apply Subrepresentation.toSubmodule_injective
      rw [hST, hT]
      exact Submodule.dualAnnihilator_top

end GlobalTheory
