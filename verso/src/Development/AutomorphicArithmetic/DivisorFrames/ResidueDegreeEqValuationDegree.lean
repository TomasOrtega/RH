import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ValCount
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JGenSpecializes
open CategoryTheory AlgebraicGeometry IsLocalRing GlobalTheory GlobalTheory.ValCount GlobalTheory.TrueGeo
open scoped Classical

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result.

Supply the required witnesses or components.
-/
private theorem exists_stalk_equiv_valuation {X : Scheme.{0}} [IsIntegral X] {W : ValuationSubring X.functionField} {x : X}
    [ValuationRing (X.presheaf.stalk x)] (h : DominatesStalk W x) :
    ∃ e : X.presheaf.stalk x ≃+* W,
      ∀ a, (e a : X.functionField) = algebraMap _ X.functionField a := by
  obtain ⟨ψ, _, hψ⟩ := dominatesStalk_iff_exists_isLocalHom.mp h
  refine ⟨RingEquiv.ofBijective ψ ⟨fun a b e ↦ ?_, fun b ↦ ?_⟩, hψ⟩
  · apply IsFractionRing.injective (X.presheaf.stalk x) X.functionField
    rw [← hψ, ← hψ, e]
  · obtain ⟨a, ha⟩ := h.range_eq_of_valuationRing.ge b.2
    exact ⟨a, Subtype.ext ((hψ a).trans ha)⟩

/- English proof (translation)
Equip the data with the indicated structure. Equip the data with the indicated structure. Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. Extract witnesses or component facts from the available result.

Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.
-/
private theorem finrank_generalized_eigenspace_eq {A B A' B' : Type} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    [IsLocalRing A] [IsLocalRing B] [IsLocalRing A'] [IsLocalRing B']
    (f : A →+* B) (f' : A' →+* B') [IsLocalHom f] [IsLocalHom f'] (i : A ≃+* A') (j : B ≃+* B')
    (h : ∀ a, f' (i a) = j (f a)) :
    (letI := (ResidueField.map f).toAlgebra; Module.finrank (ResidueField A) (ResidueField B)) =
    (letI := (ResidueField.map f').toAlgebra; Module.finrank (ResidueField A') (ResidueField B')) := by
  letI := (ResidueField.map f).toAlgebra
  letI := (ResidueField.map f').toAlgebra
  refine Algebra.finrank_eq_of_equiv_equiv (ResidueField.mapEquiv i) (ResidueField.mapEquiv j) ?_
  ext a
  obtain ⟨a, rfl⟩ := residue_surjective a
  change residue _ (f' (i a)) = residue _ (j (f a))
  rw [h]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem UpperTheory.residueDegree_eq_valuation_degree :
    ∀ (X X' : Scheme.{0}) [IsIntegral X] [IsIntegral X'] (g : X' ⟶ X) (hg : g (genericPoint X') ⤳ genericPoint X) (ζ : X') (V : ValuationSubring X'.functionField), DominatesStalk V ζ → ValuationRing (X'.presheaf.stalk ζ) → ValuationRing (X.presheaf.stalk (g ζ)) → g.residueDegree ζ = vdeg (SmallSec.fnMap g hg) V := by
  intro X X' _ _ g hg ζ V hV h1 h2
  haveI : IsDominant g := ⟨by
    rw [denseRange_iff_closure_range, Set.eq_univ_iff_forall]
    intro x
    exact (hg.trans (genericPoint_specializes x)).mem_closed isClosed_closure
      (subset_closure ⟨_, rfl⟩)⟩
  have e : SmallSec.fnMap g hg = functionFieldMap g := rfl
  rw [e]
  obtain ⟨j, hj⟩ := exists_stalk_equiv_valuation hV
  obtain ⟨i, hi⟩ := exists_stalk_equiv_valuation (hV.comap g)
  exact finrank_generalized_eigenspace_eq (g.stalkMap ζ).hom (vres (functionFieldMap g) V) i j fun a =>
    Subtype.ext (by rw [coe_vres, hi, hj, functionFieldMap_algebraMap])
