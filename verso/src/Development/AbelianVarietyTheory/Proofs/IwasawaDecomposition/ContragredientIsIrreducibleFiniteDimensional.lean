import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IncludeLInjective
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

namespace GlobalTheory

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Introduce a local definition for the expression. Rewrite the hypotheses and the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.

Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
