import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MumfordBundleCechFiniteVanishesOffOriginStatement
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.LengthBallQuotientEqSumMulFdeg
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

namespace GlobalTheory.MumfordAway

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Equip the data with the indicated structure. Rewrite the conclusion using the stated equalities. Assume the negation of the conclusion and derive a contradiction.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

By extensionality, compare the relevant components. A detailed English derivation is pending.
-/
theorem subsingleton_of_points (K : Type) [Field K] [IsAlgClosed K] (R : Type) [CommRing R]
    (s : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType s]
    (H : Type) [AddCommGroup H] [Module R H]
    (h : ∀ χ : R →+* K, Spec.map (CommRingCat.ofHom χ) ≫ s = 𝟙 _ →
      ∃ r : R, χ r ≠ 0 ∧ ∀ z : H, r • z = 0) : Subsingleton H := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective s
  have hφ : φ.hom.FiniteType := (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp inferInstance
  letI : Algebra K R := φ.hom.toAlgebra
  haveI : Algebra.FiniteType K R := hφ
  rw [← Module.annihilator_eq_top_iff (R := R)]
  by_contra hne
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
  obtain ⟨χ, rfl⟩ := GlobalTheory.PointSupport.exists_algHom_ker_eq K R M
  obtain ⟨r, hr, hz⟩ := h χ.toRingHom (by
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext k
    exact χ.commutes k)
  exact hr (hle (Module.mem_annihilator.mpr hz))

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Introduce a local definition for the expression. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem acyclic_away : ∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ P.A.left) (Y : Scheme.{0}) (π : Y ⟶ (P.A ⊗ P.A).left) (f : Y ⟶ Spec (CommRingCat.of R)), IsPullback π f (fst P.A P.A).left t → IsOpenImmersion t → (∀ p q, t p ≠ η[P.A].left q) → ∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → Y.Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → (cechLB f ((translDiff P.A P.L (𝟙 P.A)).pull π) D).Acyclic := by
  intro K _ _ P R _ t Y π f hpb ht hne κ _ _ D hD hcov p
  obtain ⟨-, -, -, h⟩ := GlobalTheory.T.mumfordBundle_cech_finite_vanishes_off_origin K P R t Y π f hpb ht κ D hD hcov
  haveI := P.smoothDim
  haveI : Smooth P.A.hom := SmoothOfRelativeDimension.smooth P.g _
  rw [HomologicalComplex.exactAt_iff_isZero_homology, ModuleCat.isZero_iff_subsingleton]
  refine subsingleton_of_points K R (t ≫ P.A.hom) _ fun χ hχ => h χ (by simpa using hχ) ?_ p
  intro e
  let q : Spec (CommRingCat.of K) := default
  refine hne (Spec.map (CommRingCat.ofHom χ) q) q ?_
  rw [← e]
  rfl

end GlobalTheory.MumfordAway
