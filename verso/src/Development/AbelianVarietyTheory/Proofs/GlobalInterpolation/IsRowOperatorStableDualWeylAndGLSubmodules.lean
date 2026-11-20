import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodTopBot
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.WeylDualWeylLatticesAgreeOfLowestAlcove
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RowPolarizationOperatorsRelationsDivPowBaseChangStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RowPolarizationOperatorsActionOnRowWeightStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RowPolarizationMemOfIsGLSchemeSubmoduleStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeightedHomogeneousComponentMemOfGLSchemeSubmoduStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.GLSchemeSubmoduleStableUnderRowPermStatement

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc

noncomputable section

namespace GlobalTheory.Alc

/- English proof (translation)
Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `v`. Simplify using `[rowAct]`.
-/
theorem rename_rowPerm_eq_rowAct (R : Type) [CommRing R] (r n : ℕ) (σ : Equiv.Perm (Fin r)) :
    (rename (fun v : Fin r × Fin n => (σ v.1, v.2)) : MvPolynomial (Fin r × Fin n) R →ₐ[R] _) =
      rowAct R (n := n) (Matrix.of fun a b : Fin r => if b = σ a then (1 : R) else 0) := by
  apply MvPolynomial.algHom_ext
  intro v
  simp [rowAct]

/- English proof (translation)
Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `a b f hf`. Rewrite using `[(GlobalTheory.T.rowPolarizationOperators_relations_divPow_baseChange k N N).2.1 a b f]`. Conclude with `rowDivStable k N N _ a b 1 f hf`. Introduce `μ f hf`.

Conclude with `dualWeylRowGraded k N N _ μ f hf`. Introduce `σ f hf`. Rewrite using `[rename_rowPerm_eq_rowAct]`. Conclude with `dualWeylRowStable k N N _ _ f hf`.
-/
theorem good_nablaSq (k : Type) [Field k] (N : ℕ) (lam : DomWeight N) : Good (nablaSq k N lam) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b f hf
    rw [(GlobalTheory.T.rowPolarizationOperators_relations_divPow_baseChange k N N).2.1 a b f]
    exact rowDivStable k N N _ a b 1 f hf
  · intro μ f hf
    exact dualWeylRowGraded k N N _ μ f hf
  · intro σ f hf
    rw [rename_rowPerm_eq_rowAct]
    exact dualWeylRowStable k N N _ _ f hf

/- English proof (translation)
Establish `hw : ∀ μ : Fin N → ℕ, ∀ f ∈ M, weightedHomogeneousComponent (rowW N N) μ f ∈ M` using `GlobalTheory.T.weightedHomogeneousComponent_mem_of_GLSchemeSubmodule k N lam M hM`. Use `⟨?_, hw, GlobalTheory.T.GLSchemeSubmodule_stable_under_row_perm k N lam M hM⟩` and prove the remaining obligations. Introduce `a b f hf`. Distinguish the cases in `hab : a = b`. Substitute `hab classical` using the available equality.

Establish `hsum` using `sum_weightedHomogeneousComponent (rowW N N) f`. Rewrite `hsum` using `[finsum_eq_sum _ (weightedHomogeneousComponent_finsupp f)]`. Rewrite using `[← hsum, map_sum]`. Use `Submodule.sum_mem _ fun μ _ => ?_` and prove the remaining obligations. Rewrite using `[((GlobalTheory.T.rowPolarizationOperators_action_on_rowWeight k N N μ _ (weightedHomogeneousComponent_isWeightedHomogeneous μ f)).1 a)]`.

Conclude with `Submodule.smul_mem _ _ (hw μ f hf)`. Conclude with `GlobalTheory.T.rowPolarization_mem_of_isGLSchemeSubmodule k N lam M hM a b hab f hf`.
-/
theorem good_of_isGLSubmodule (k : Type) [Field k] (N : ℕ) (lam : DomWeight N)
    (M : Submodule k (MvPolynomial (Fin N × Fin N) k)) (hM : GlobalTheory.Published.IsGLSubmodule k N lam M) : Good M := by
  have hw : ∀ μ : Fin N → ℕ, ∀ f ∈ M, weightedHomogeneousComponent (rowW N N) μ f ∈ M :=
    GlobalTheory.T.weightedHomogeneousComponent_mem_of_GLSchemeSubmodule k N lam M hM
  refine ⟨?_, hw, GlobalTheory.T.GLSchemeSubmodule_stable_under_row_perm k N lam M hM⟩
  intro a b f hf
  by_cases hab : a = b
  · subst hab
    classical
    have hsum := sum_weightedHomogeneousComponent (rowW N N) f
    rw [finsum_eq_sum _ (weightedHomogeneousComponent_finsupp f)] at hsum
    rw [← hsum, map_sum]
    refine Submodule.sum_mem _ fun μ _ => ?_
    rw [((GlobalTheory.T.rowPolarizationOperators_action_on_rowWeight k N N μ _ (weightedHomogeneousComponent_isWeightedHomogeneous μ f)).1 a)]
    exact Submodule.smul_mem _ _ (hw μ f hf)
  · exact GlobalTheory.T.rowPolarization_mem_of_isGLSchemeSubmodule k N lam M hM a b hab f hf

/- English proof (translation)
Introduce `k _ N lam` and use `⟨good_nablaSq k N lam, good_of_isGLSubmodule k N lam⟩`.
-/
theorem good_nablaSq_and_submodules : ∀ (k : Type) [Field k] (N : ℕ) (lam : DomWeight N), Good (nablaSq k N lam) ∧
    ∀ M : Submodule k (MvPolynomial (Fin N × Fin N) k), GlobalTheory.Published.IsGLSubmodule k N lam M → Good M :=
  fun k _ N lam => ⟨good_nablaSq k N lam, good_of_isGLSubmodule k N lam⟩

end GlobalTheory.Alc
