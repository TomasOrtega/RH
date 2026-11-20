import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformVanishing
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedMissingClosedFibreEmpty

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh

namespace GlobalTheory.CompanionTheory.GE.PSupp

def badSet {X : Scheme.{0}} {P : X.Modules} (S : Subobject P) : Set X :=
  {x | ∀ V : X.affineOpens, secs S (V : X.Opens) = Set.univ → x ∉ (V : X.Opens)}

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Supply the required witnesses or components.

Assume the hypotheses and unpack their components. Supply the required witnesses or components.
-/
lemma badSet_compl_eq {X : Scheme.{0}} {P : X.Modules} (S : Subobject P) :
    (badSet S)ᶜ = ⋃ V ∈ {V : X.affineOpens | secs S (V : X.Opens) = Set.univ}, ((V : X.Opens) : Set X) := by
  ext x
  simp only [badSet, Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall, exists_prop, Set.mem_iUnion]
  constructor
  · rintro ⟨V, hV, hx⟩
    exact ⟨V, hV, not_not.mp hx⟩
  · rintro ⟨V, hV, hx⟩
    exact ⟨V, hV, not_not.mpr hx⟩

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
lemma isClosed_badSet {X : Scheme.{0}} {P : X.Modules} (S : Subobject P) : IsClosed (badSet S) := by
  rw [← isOpen_compl_iff, badSet_compl_eq]
  exact isOpen_biUnion fun V _ => (V : X.Opens).isOpen

/- English proof (translation)
Establish an intermediate fact. Assume the hypotheses and unpack their components. Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem subset_of_closedFibre {A : Type} [CommRing A] (I : Ideal A) (hI : IsAdicComplete I A)
    {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsProper (X ↘ Spec (.of A))] (O : X.Opens) (C : Set X)
    (hC : IsClosed C) (h : ∀ x ∈ C, I ≤ ((X ↘ Spec (.of A)).base x).asIdeal → x ∈ (O : Set X)) :
    C ⊆ O := by

  have hZ := GlobalTheory.CompanionTheory.ClosedFibre.closed_missing_closedFibre_empty A I hI
    (Over.mk (X ↘ Spec (.of A))) (inferInstanceAs (UniversallyClosed (X ↘ Spec (.of A))))
    (C ∩ (O : Set X)ᶜ) (hC.inter O.isOpen.isClosed_compl) (by
      rintro x ⟨hxC, hxO⟩ hIx
      exact hxO (h x hxC hIx))
  intro x hx
  by_contra hxO
  have hx' : x ∈ C ∩ (O : Set X)ᶜ := ⟨hx, hxO⟩
  rw [hZ] at hx'
  exact hx'

end GlobalTheory.CompanionTheory.GE.PSupp
