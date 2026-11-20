import Mathlib
import Development.EtaleCohomology.EtaleSheaves.H0TwistOverClosedField
import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes

open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Express the relevant assertion in an equivalent form by its definition.

Simplify using the standard rewrite rules. Establish an intermediate fact. Introduce a local definition for the expression. Equip the data with the indicated structure. Reduce the conclusion to the remaining proof obligations.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Equip the data with the indicated structure. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result.

Fix the arbitrary inputs or assume the hypotheses. Express the relevant assertion in an equivalent form by its definition. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
private theorem UpperTheory.affine_opens_same_krullDim (k : Type) [Field k] {Y : Scheme.{0}} [IsIntegral Y]
    (t : Y ⟶ Sp k) [LocallyOfFiniteType t] :
    ∃ c : WithBot ℕ∞, ∀ U : Y.Opens, IsAffineOpen U → Nonempty U → ringKrullDim Γ(Y, U) = c := by
  classical
  let iso : k →+* Γ(Sp k, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
  have hiso : Function.Surjective iso := by
    intro y
    refine ⟨(Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom y, ?_⟩
    change ((Scheme.ΓSpecIso (CommRingCat.of k)).hom ≫ (Scheme.ΓSpecIso (CommRingCat.of k)).inv).hom y = y
    simp
  have eT : (⊤ : Y.Opens) ≤ t ⁻¹ᵁ ⊤ := le_top
  haveI : Nonempty (⊤ : Y.Opens) := ⟨⟨Nonempty.some (inferInstance : Nonempty Y), trivial⟩⟩
  let φ : k →+* Y.functionField := (Y.germToFunctionField ⊤).hom.comp ((t.appLE ⊤ ⊤ eT).hom.comp iso)
  letI : Algebra k Y.functionField := φ.toAlgebra
  refine ⟨((Algebra.trdeg k Y.functionField).toENat : WithBot ℕ∞), ?_⟩
  intro U hU hne
  have eU : U ≤ t ⁻¹ᵁ ⊤ := le_top
  letI : Algebra k Γ(Y, U) := ((t.appLE ⊤ U eU).hom.comp iso).toAlgebra
  haveI : Algebra.FiniteType k Γ(Y, U) := by
    have h1 : (t.appLE ⊤ U eU).hom.FiniteType :=
      t.finiteType_appLE (isAffineOpen_top _) hU eU
    exact h1.comp (RingHom.FiniteType.of_surjective _ hiso)
  haveI : IsFractionRing Γ(Y, U) Y.functionField := functionField_isFractionRing_of_isAffineOpen Y U hU
  haveI : IsScalarTower k Γ(Y, U) Y.functionField := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    change φ x = (Y.germToFunctionField U).hom ((t.appLE ⊤ U eU).hom (iso x))
    simp only [φ, RingHom.comp_apply]
    rw [← Scheme.Hom.appLE_map t eT (homOfLE (le_top : U ≤ ⊤)).op]
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, Scheme.germToFunctionField]
    exact (TopCat.Presheaf.germ_res_apply Y.presheaf (homOfLE (le_top : U ≤ ⊤)) _ _ _).symm
  exact GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_trdeg_fractionRing k Y.functionField

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Supply the required witnesses or components.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem UpperTheory.topologicalKrullDim_le_of_isOpenImmersion_integral :
    ∀ (k : Type) [Field k] {Y D : Scheme.{0}} [IsIntegral Y] (t : Y ⟶ Sp k) [LocallyOfFiniteType t] (j : D ⟶ Y) [IsOpenImmersion j] [Nonempty D], topologicalKrullDim Y ≤ topologicalKrullDim D := by
  intro k _ Y D _ t _ j _ _
  obtain ⟨c, hc⟩ := UpperTheory.affine_opens_same_krullDim k t
  have hdim : ∀ U : Y.Opens, IsAffineOpen U → Nonempty U → topologicalKrullDim U = c := by
    intro U hU hne
    rw [← hc U hU hne, ← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    exact IsHomeomorph.topologicalKrullDim_eq _ hU.isoSpec.hom.homeomorph.isHomeomorph
  have hup : topologicalKrullDim Y ≤ c := by
    apply GlobalTheory.topologicalKrullDim_le_of_forall_exists_isOpen
    intro x
    obtain ⟨_, ⟨A, hA, rfl⟩, hxA, -⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact ⟨A, A.isOpen, hxA, (hdim A hA ⟨⟨x, hxA⟩⟩).le⟩
  have hemb := j.isOpenEmbedding
  obtain ⟨d⟩ := ‹Nonempty D›
  obtain ⟨_, ⟨A, hA, rfl⟩, hyA, hAsub⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_range_self d) hemb.isOpen_range
  have hZ := GlobalTheory.topologicalKrullDim_eq_of_isEmbedding hemb.isEmbedding rfl
  have hAZ := GlobalTheory.topologicalKrullDim_eq_of_isEmbedding (Topology.IsEmbedding.inclusion hAsub) rfl
  have hle := topologicalKrullDim_subspace_le (Set.range _) (Set.range (Set.inclusion hAsub))
  rw [hAZ, hZ] at hle
  exact hup.trans ((hdim A hA ⟨⟨_, hyA⟩⟩).symm.le.trans hle)
