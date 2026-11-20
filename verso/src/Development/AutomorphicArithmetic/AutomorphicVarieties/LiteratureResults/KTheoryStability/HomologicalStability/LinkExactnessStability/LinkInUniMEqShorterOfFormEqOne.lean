import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LinkExactAff
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.SubClosedAndPermAndLinearEquivInvariantUniM
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.ConsMemUniMIffMapSubSmul
open GlobalTheory.SeqCx Matrix

namespace GlobalTheory.SeqCx

/- English proof (translation)
Introduce `R M _ _ _ φ S hS τ hτ v hv hφv`. Establish `hperm` using `(GlobalTheory.T.subClosed_and_perm_and_linearEquiv_invariant_uniM R M).2.1`. Establish `hmod` using `GlobalTheory.T.cons_mem_uniM_iff_map_sub_smul R M φ v hφv`. Establish `hp : τ.Perm (v :: τ.erase v)` using `List.perm_cons_erase hv`. Use `⟨(τ.erase v).map (fun x => x - φ x • v), ?_, ?_, ?_⟩` and prove the remaining obligations.

Conclude with `(hmod _).1 (hperm _ _ hp hτ)`. Simplify using `[List.length_erase_of_mem hv]`. Use `List.length_pos_of_mem hv` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Use extensionality with `w`.

Simplify using `only [linkIn, Set.mem_setOf_eq]`. Use `and_congr_right fun hw => ?_` and prove the remaining obligations. Establish `hpw : (τ ++ w).Perm (v :: (τ.erase v ++ w))` using `hp.append_right w`. Establish `hwfix : w.map (fun x => x - φ x • v) = w` using `by conv_rhs => rw [← List.map_id w]`. Apply `List.map_congr_left` to reduce the goal to its premises.

Introduce `x hx`. Simplify using `[hS x (hw x hx)]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h1` using `(hmod _).1 (hperm _ _ hpw h)`.

Rewrite `h1` using `[List.map_append, hwfix]`. Then use the resulting hypothesis. Introduce `h`. Establish `h1 : (τ.erase v ++ w).map (fun x => x - φ x • v) ∈ uniM R M`. Rewrite using `[List.map_append, hwfix]` and apply the resulting hypothesis. Conclude with `hperm _ _ hpw.symm ((hmod _).2 h1)`.
-/
theorem linkIn_uniM_eq_of_form :
    ∀ (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] (φ : M →ₗ[R] R) (S : Set M),
      (∀ x ∈ S, φ x = 0) → ∀ τ ∈ uniM R M, ∀ v ∈ τ, φ v = 1 →
        ∃ τ' ∈ uniM R M, τ'.length + 1 = τ.length ∧
          linkIn (uniM R M) S τ = linkIn (uniM R M) S τ' := by
  intro R M _ _ _ φ S hS τ hτ v hv hφv
  classical
  have hperm := (GlobalTheory.T.subClosed_and_perm_and_linearEquiv_invariant_uniM R M).2.1
  have hmod := GlobalTheory.T.cons_mem_uniM_iff_map_sub_smul R M φ v hφv
  have hp : τ.Perm (v :: τ.erase v) := List.perm_cons_erase hv
  refine ⟨(τ.erase v).map (fun x => x - φ x • v), ?_, ?_, ?_⟩
  · exact (hmod _).1 (hperm _ _ hp hτ)
  · simp [List.length_erase_of_mem hv]
    have := List.length_pos_of_mem hv
    omega
  · ext w
    simp only [linkIn, Set.mem_setOf_eq]
    refine and_congr_right fun hw => ?_
    have hpw : (τ ++ w).Perm (v :: (τ.erase v ++ w)) := hp.append_right w
    have hwfix : w.map (fun x => x - φ x • v) = w := by
      conv_rhs => rw [← List.map_id w]
      apply List.map_congr_left
      intro x hx
      simp [hS x (hw x hx)]
    constructor
    · intro h
      have h1 := (hmod _).1 (hperm _ _ hpw h)
      rwa [List.map_append, hwfix] at h1
    · intro h
      have h1 : (τ.erase v ++ w).map (fun x => x - φ x • v) ∈ uniM R M := by
        rwa [List.map_append, hwfix]
      exact hperm _ _ hpw.symm ((hmod _).2 h1)

end GlobalTheory.SeqCx

section
open GlobalTheory.SeqCx Matrix
/- English proof (translation)
Use `first`. Consider the case `exact @GlobalTheory.SeqCx.linkIn_uniM_eq_of_form`.
-/
theorem _root_.GlobalTheory.T.linkIn_uniM_eq_shorter_of_form_eq_one : ∀ (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] (φ : M →ₗ[R] R) (S : Set M), (∀ x ∈ S, φ x = 0) → ∀ τ ∈ uniM R M, ∀ v ∈ τ, φ v = 1 → ∃ τ' ∈ uniM R M, τ'.length + 1 = τ.length ∧ linkIn (uniM R M) S τ = linkIn (uniM R M) S τ' := by
  first
  | exact @GlobalTheory.SeqCx.linkIn_uniM_eq_of_form
end
