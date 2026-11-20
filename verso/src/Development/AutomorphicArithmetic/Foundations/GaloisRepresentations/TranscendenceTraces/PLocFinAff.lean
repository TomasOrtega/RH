import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleFaithfullyFlatRefiningEtaleSurjectionStatement

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces
open scoped TensorProduct

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Introduce a local definition for the expression. Extract witnesses or component facts from the available result. Introduce a local definition for the expression.

Extract witnesses or component facts from the available result. Equip the data with the indicated structure. Introduce a local definition for the expression. Extract witnesses or component facts from the available result. Introduce a local definition for the expression.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations.

Express the relevant assertion in an equivalent form by its definition. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem UpperTheory.Gal.TranscendenceTraces.locFinAff_of :
    Chart → RingSplit → LocFinAff := by
  intro hC hR W V U _ π r _ _ _ x
  let A := Γ(U, ⊤)
  let u : Spec (CommRingCat.of A) ⟶ U := U.isoSpec.inv
  obtain ⟨B, _, _, v, _, hpb⟩ := hC r A u
  haveI : IsIso v := hpb.isIso_fst_of_isIso
  let f : W ⟶ Spec (CommRingCat.of B) := π ≫ inv v
  obtain ⟨C, g, h, hg, hh⟩ := GlobalTheory.T.exists_etaleFaithfullyFlat_refining_etale_surjection (CommRingCat.of B) W f inferInstance inferInstance
  letI : Algebra B C := g.hom.toAlgebra
  haveI : Algebra.Etale B C := hg.1
  haveI : Module.FaithfullyFlat B C := hg.2
  let P : PrimeSpectrum A := U.isoSpec.hom x
  obtain ⟨E, _, _, hE, ⟨Q, hQ⟩, ⟨φ⟩⟩ := hR A B C P
  let gE : Spec (CommRingCat.of E) ⟶ U := Spec.map (CommRingCat.ofHom (algebraMap A E)) ≫ u
  haveI : Etale (Spec.map (CommRingCat.ofHom (algebraMap A E))) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr hE)
  have big := (isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct A B E)).paste_horiz hpb
  have hhπ : h ≫ π = Spec.map g ≫ v := by
    rw [← hh]
    simp [f]
  refine ⟨Spec (CommRingCat.of E), gE, inferInstance, inferInstance, ⟨Q, ?_⟩, ?_⟩
  · change u (Spec.map (CommRingCat.ofHom (algebraMap A E)) Q) = x
    have e : Spec.map (CommRingCat.ofHom (algebraMap A E)) Q = P := hQ
    rw [e]
    show U.isoSpec.inv (U.isoSpec.hom x) = x
    rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id]
    rfl
  · refine ⟨big.lift (pullback.fst r gE) (pullback.snd r gE) pullback.condition ≫
      Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ h, ?_⟩
    have eφ : g ≫ CommRingCat.ofHom φ.toRingHom = CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom := by
      ext b
      exact φ.commutes b
    rw [Category.assoc, Category.assoc, hhπ, ← Category.assoc (Spec.map _) (Spec.map g) v, ← Spec.map_comp, eφ]
    exact big.lift_fst _ _ _
