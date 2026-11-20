import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.InvariantsGenerators
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.JSmul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleQuotientKerIffFullLattices
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTopDataOfSlotHyps
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleClassesPropsOfFlatCoefficient
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleOfSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleStd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineSumsTwistsCharactersExpectedJumps
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralCyclotomicChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankDcrisLetterDeRhamComponentEqDim
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvrComplete
open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions
set_option synthInstance.maxHeartbeats 400000
open ReciprocityTheory.Def (Z1 B1 H1)
open TensorProduct

open Formalism.MainNotions.N (twistRep coefRep)

namespace GlobalTheory.AdmLoc

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Substitute using the available equality. Establish an intermediate fact. Split into cases according to the possible forms of the given data. Simplify using the standard rewrite rules. Substitute using the available equality.

Both sides reduce to the same expression. Substitute using the available equality. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction.

Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Both sides reduce to the same expression.

Treat this case separately. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Supply the required witnesses or components.

Introduce a local definition for the expression. Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Rewrite the indicated hypotheses using the stated equalities.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities.

Simplify using the standard rewrite rules. Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Normalize the expressions using the abelian group laws. Rewrite the conclusion using the stated equalities. Normalize the expressions using the abelian group laws. Assume the hypotheses and unpack their components. Introduce a local definition for the expression.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Apply function extensionality and compare values at an arbitrary argument. Express the relevant assertion in an equivalent form by its definition. Simplify using the standard rewrite rules.

Establish an intermediate fact. Simplify using the standard rewrite rules. Normalize the expressions using the abelian group laws. A detailed English derivation is pending.
-/
theorem mk_mem_H1fX_iff_inHfX {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀]
    [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL] {O : Type} [CommRing O] [Algebra O LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] [Module O V]
    [IsScalarTower O LL V] {ρ : Representation LL G V} [TopologicalSpace V] [ContinuousAdd V]
    [ContinuousConstSMul LL V] (L : Lattice (O := O) ρ) (ρ' : Representation LL G V) (L' : Lattice (O := O) ρ')
    (X : Type) [AddCommGroup X] [Module O X] (χ : G →* Oˣ) :
    (∀ g, ρ' g = ((tableLineDegreeTwo.charL (LL := LL) χ g)⁻¹ : LLˣ).val • ρ g) → L'.T = L.T →
    ∀ (z : G → ↥L.T ⊗[O] X) (hz : z ∈ Z1 (twCoef (latRep L) χ X) ⊤),
      (Submodule.Quotient.mk ⟨z, hz⟩ ∈ finiteSelmer PD L χ X ↔ tableLineDegreeTwo.InHfX PD L L' X χ z) := by
  intro hρ hT z hz
  have e1 : ρ' = twistRep ρ (chiLL LL χ⁻¹) := by
    ext g v
    rw [hρ g, twistRep_apply]
    simp [chiLL, tableLineDegreeTwo.charL]
  subst e1
  have e2 : L' = twLattice L χ⁻¹ := by
    cases L'
    simp only at hT
    subst hT
    rfl
  subst e2
  have hact : ∀ g (m : ↥L.T ⊗[O] X), twCoef (latRep L) χ X g m = tableLineDegreeTwo.actTw L X χ g m := by
    intro g m
    induction m using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
      rw [coefRep_tmul, twistRep_apply]
      simp only [tableLineDegreeTwo.actTw, LinearMap.smul_apply, LinearMap.rTensor_tmul, smul_tmul']
      rfl
    | add a b ha hb => rw [map_add, map_add, ha, hb]
  have hA : toAmb (twCoef (latRep L) χ X) (Submodule.Quotient.mk ⟨z, hz⟩) = Submodule.Quotient.mk z := rfl
  rw [finiteSelmer, Submodule.mem_comap, hA, LinearMap.mem_range]
  constructor
  · rintro ⟨u, hu⟩
    obtain ⟨S, rfl⟩ := TensorProduct.exists_finset u
    have hrep : ∀ p : ↥(latticeFiniteCohomology PD (twLattice L χ⁻¹)), ∃ c : ↥(latticeCocycles (twLattice L χ⁻¹)),
        (c : G → V) ∈ latticeFiniteCocycles PD (twLattice L χ⁻¹) ∧ Submodule.Quotient.mk c = (p : LatticeCohomology (twLattice L χ⁻¹)) := by
      rintro ⟨p, hp⟩
      obtain ⟨c, hc, rfl⟩ := Submodule.mem_map.mp hp
      exact ⟨c, hc, rfl⟩
    choose rep hrepf hrepmk using hrep
    let e := S.equivFin
    let cc : Fin S.card → ↥(latticeCocycles (twLattice L χ⁻¹)) := fun j => rep (e.symm j).1.1
    let xx : Fin S.card → X := fun j => (e.symm j).1.2
    have key : (tensAmb L χ X ∘ₗ (latticeFiniteCohomology PD (twLattice L χ⁻¹)).subtype.rTensor X)
        (∑ p ∈ S, p.1 ⊗ₜ[O] p.2) = Submodule.Quotient.mk (∑ j, tensCoc L χ X (cc j) (xx j)) := by
      rw [map_sum, ← Finset.sum_coe_sort S, ← e.symm.sum_comp]
      refine Eq.trans ?_ (map_sum (Submodule.mkQ _) _ _).symm
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [LinearMap.comp_apply, LinearMap.rTensor_tmul, Submodule.subtype_apply, ← hrepmk, tensAmb_tmul]
      rfl
    rw [key] at hu
    obtain ⟨m, -, hm⟩ := (Submodule.Quotient.eq _).mp hu
    refine ⟨S.card, fun j g => evT (twLattice L χ⁻¹) g (cc j), xx, -m, fun j => hrepf _, fun g => ?_⟩
    have h1 : twCoef (latRep L) χ X g m - m = (∑ j, tensCoc L χ X (cc j) (xx j)) g - z g := congrFun hm g
    simp only [Finset.sum_apply] at h1
    rw [hact] at h1
    simp only [map_neg]
    have h2 : ∀ j, tensCoc L χ X (cc j) (xx j) g = evT (twLattice L χ⁻¹) g (cc j) ⊗ₜ[O] xx j := fun j => rfl
    simp only [h2] at h1
    have h3 : z g = ∑ j, evT (twLattice L χ⁻¹) g (cc j) ⊗ₜ[O] xx j - (tableLineDegreeTwo.actTw L X χ g m - m) := by
      rw [h1]; abel
    rw [h3]
    abel
  · rintro ⟨k, c, x, m, hc, hzc⟩
    let cc : Fin k → ↥(latticeCocycles (twLattice L χ⁻¹)) := fun j => ⟨fun g => (c j g : V), (hc j).1⟩
    refine ⟨∑ j, (⟨Submodule.Quotient.mk (cc j), Submodule.mem_map_of_mem (hc j)⟩ :
      ↥(latticeFiniteCohomology PD (twLattice L χ⁻¹))) ⊗ₜ[O] x j, ?_⟩
    rw [map_sum]
    have h1 : ∀ j, (tensAmb L χ X ∘ₗ (latticeFiniteCohomology PD (twLattice L χ⁻¹)).subtype.rTensor X)
        ((⟨Submodule.Quotient.mk (cc j), Submodule.mem_map_of_mem (hc j)⟩ :
          ↥(latticeFiniteCohomology PD (twLattice L χ⁻¹))) ⊗ₜ[O] x j) = Submodule.mkQ _ (tensCoc L χ X (cc j) (x j)) := fun j => rfl
    simp only [h1]
    rw [← map_sum, Submodule.mkQ_apply]
    refine (Submodule.Quotient.eq _).mpr ?_
    refine Submodule.mem_map.mpr ⟨-m, Submodule.mem_top, ?_⟩
    funext g
    change twCoef (latRep L) χ X g (-m) - (-m) = (∑ j, tensCoc L χ X (cc j) (x j)) g - z g
    simp only [Finset.sum_apply, hact, map_neg, hzc g]
    have h2 : ∀ j, tensCoc L χ X (cc j) (x j) g = c j g ⊗ₜ[O] x j := fun j => rfl
    simp only [h2]
    abel

end GlobalTheory.AdmLoc
