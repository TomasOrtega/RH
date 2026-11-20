import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ScalarConvolutionTrace.CardUNeZero

noncomputable section

open Classical

namespace PI.GGConvScalarW

open Formalism.L2.SG.GGMirabolic

/- English proof (translation)
Assume the negation of the conclusion and derive a contradiction. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Extract witnesses or component facts from the available result. Reduce the claim to the hypotheses of an applicable result.

Separate the alternatives or extract the components of the hypothesis. Separate the alternatives or extract the components of the hypothesis. Reduce the equality to equality of the corresponding arguments. A detailed English derivation is pending.
-/
theorem nontrivial_of_irreducible {G : Type} [Monoid G] {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ G V) (hπ : π.IsIrreducible) : Nontrivial V := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  have hs : IsSimpleOrder (Subrepresentation π) := hπ
  obtain ⟨a, b, hab⟩ := hs.toNontrivial.exists_pair_ne
  apply hab
  rcases a with ⟨a, ha⟩
  rcases b with ⟨b, hb⟩
  congr 1
  exact Subsingleton.elim a b

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem representation_dimension_pos : DimPos := by
  intro F _ _ k V _ _ _ π hπ
  haveI := nontrivial_of_irreducible π hπ
  exact Module.finrank_pos

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Introduce a local definition for the expression.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Separate the alternatives or extract the components of the hypothesis. It suffices to derive a contradiction. Reduce the claim to the hypotheses of an applicable result.

Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem schur_lemma_complex : SchurC := by
  intro F _ _ k V _ _ _ π hπ f hf
  haveI := nontrivial_of_irreducible π hπ
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue f
  refine ⟨c, ?_⟩
  have hinv : ∀ (g : GL (Fin k) F) ⦃v : V⦄, v ∈ LinearMap.ker (f - c • LinearMap.id) →
      π g v ∈ LinearMap.ker (f - c • LinearMap.id) := by
    intro g v hv
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply] at hv ⊢
    have h1 := congrArg (fun φ : V →ₗ[ℂ] V => φ v) (hf g)
    simp only [LinearMap.comp_apply] at h1
    rw [← h1, ← map_smul, ← map_sub, hv, map_zero]
  let W : Subrepresentation π := ⟨LinearMap.ker (f - c • LinearMap.id), hinv⟩
  have hs : IsSimpleOrder (Subrepresentation π) := hπ
  obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
  rcases hs.eq_bot_or_eq_top W with hW | hW
  · exfalso
    apply hv.2
    have hvW : v ∈ LinearMap.ker (f - c • LinearMap.id) := by
      simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]
      rw [hv.apply_eq_smul, sub_self]
    have h2 := congrArg Subrepresentation.toSubmodule hW
    change LinearMap.ker (f - c • LinearMap.id) = _ at h2
    rw [h2] at hvW
    have h3 : v ∈ (⊥ : Submodule ℂ V) := hvW
    simpa using h3
  · apply LinearMap.ext
    intro x
    have h2 := congrArg Subrepresentation.toSubmodule hW
    change LinearMap.ker (f - c • LinearMap.id) = _ at h2
    have hx : x ∈ LinearMap.ker (f - c • LinearMap.id) := by
      rw [h2]
      exact (show x ∈ (⊤ : Submodule ℂ V) from Submodule.mem_top)
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply] at hx
    simpa [sub_eq_zero] using hx

end PI.GGConvScalarW
