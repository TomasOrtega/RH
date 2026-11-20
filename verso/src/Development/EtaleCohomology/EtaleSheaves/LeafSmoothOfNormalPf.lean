import Development.EtaleCohomology.EtaleSheaves.LeafModelCurveCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4

namespace LateralTheory.E.LeafSmoothOfNormalPf

def LeafStalkSmoothClosed : Prop := ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] {C : Scheme.{0}} (c : C ⟶ Sp Ω)
  [IsIntegral C], LocallyOfFiniteType c → (∀ y : C, IsIntegrallyClosed (C.presheaf.stalk y)) →
    topologicalKrullDim C = 1 → ∀ y : C, y ≠ genericPoint C → (c.stalkMap y).hom.FormallySmooth

def LeafRelDimOne : Prop := ∀ (Ω : Type) [Field Ω] {C : Scheme.{0}} (c : C ⟶ Sp Ω),
  IsIntegral C → Smooth c → topologicalKrullDim C = 1 → SmoothOfRelativeDimension 1 c

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem smooth_of_stalks (Ω : Type) [Field Ω] {C : Scheme.{0}} (c : C ⟶ Sp Ω) [LocallyOfFiniteType c]
    (h : ∀ y : C, (c.stalkMap y).hom.FormallySmooth) : Smooth c := by
  rw [← Scheme.Hom.smoothLocus_eq_top_iff]
  exact top_le_iff.mp fun y _ => h y

/- English proof (translation)
Consider separately whether the proposition holds or fails. Substitute using the available equality. A detailed English derivation is pending.
-/
theorem stalk_smooth_all (hA : LeafStalkSmoothClosed) (Ω : Type) [Field Ω] [IsAlgClosed Ω] {C : Scheme.{0}}
    (c : C ⟶ Sp Ω) (hC : IsIntegral C) (hc : LocallyOfFiniteType c)
    (hn : ∀ y : C, IsIntegrallyClosed (C.presheaf.stalk y)) (hd : topologicalKrullDim C = 1) (y : C) :
    (c.stalkMap y).hom.FormallySmooth := by
  by_cases hy : y = genericPoint C
  · subst hy
    exact c.genericPoint_mem_smoothLocus_of_perfectField
  · exact hA Ω c hc hn hd y hy

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem LeafSmoothOfNormal_of (hA : LeafStalkSmoothClosed) (hB : LeafRelDimOne) :
    LateralTheory.E.LeafModelCurveCut.LeafSmoothOfNormal := by
  intro Ω _ _ C c hC hc hn hd
  have hs : Smooth c := smooth_of_stalks Ω c (stalk_smooth_all hA Ω c hC hc hn hd)
  exact hB Ω c hC hs hd

end LateralTheory.E.LeafSmoothOfNormalPf
