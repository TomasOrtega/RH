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

namespace GlobalTheory

/- English proof (translation)
Introduce `G _ _ LL _ O _ _ V _ _ _ _ ρ L X _ _ χ`. Establish `h1 : ∀ g m, tableLineDegreeTwo.actTw L X χ g m = twCoef (latRep L) χ X g m`. Introduce `g m`. Proceed by induction on `m using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `tmul a x`. Simplify using `only [tableLineDegreeTwo.actTw, LinearMap.smul_apply, LinearMap.rTensor_tmul]`. Rewrite using `[coefRep_tmul, twistRep_apply]`. Simplify using `[latRep, smul_tmul', MonoidHom.inv_apply]`. Consider the case `add a b ha hb => rw [map_add, map_add, ha, hb]`.

Use `⟨h1, fun z => ?_⟩` and prove the remaining obligations. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hz, hc⟩`. Use `⟨⟨hz, fun _ => Submodule.mem_top⟩, ?_⟩` and prove the remaining obligations. Use `show (ReciprocityTheory.Def.d1 (twCoef (latRep L) χ X)) z = 0`.

Use function extensionality and compare the values at `x`. Express the relevant statement in the definitionally equal form `twCoef (latRep L) χ X x.1 (z x.2) - z (x.1 * x.2) + z x.1 = 0`. Rewrite using `[hc, ← h1]`. Normalize the expressions using the abelian group laws. Introduce and unpack `⟨⟨hz, -⟩, hk⟩`.

Use `⟨hz, fun g h => ?_⟩` and prove the remaining obligations. Establish `e : twCoef (latRep L) χ X g (z h) - z (g * h) + z g = 0` using `congrFun hk (g, h)`. Rewrite using `[h1, ← sub_eq_zero, ← neg_eq_zero, ← e]`. Normalize the expressions using the abelian group laws.
-/
theorem actTw_eq_twCoef_and_isCoc_iff : ∀ {G : Type} [Group G] [TopologicalSpace G] {LL : Type} [Field LL] {O : Type} [CommRing O]
    [Algebra O LL] {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
    {ρ : Representation LL G V} (L : Lattice (O := O) ρ) (X : Type) [AddCommGroup X] [Module O X]
    (χ : G →* Oˣ),
    (∀ g m, tableLineDegreeTwo.actTw L X χ g m = twCoef (latRep L) χ X g m) ∧
    ∀ z : G → ↥L.T ⊗[O] X, tableLineDegreeTwo.IsCoc L X χ z ↔ z ∈ Z1 (twCoef (latRep L) χ X) ⊤ := by
  intro G _ _ LL _ O _ _ V _ _ _ _ ρ L X _ _ χ
  have h1 : ∀ g m, tableLineDegreeTwo.actTw L X χ g m = twCoef (latRep L) χ X g m := by
    intro g m
    induction m using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
      simp only [tableLineDegreeTwo.actTw, LinearMap.smul_apply, LinearMap.rTensor_tmul]
      rw [coefRep_tmul, twistRep_apply]
      simp [latRep, smul_tmul', MonoidHom.inv_apply]
    | add a b ha hb => rw [map_add, map_add, ha, hb]
  refine ⟨h1, fun z => ?_⟩
  constructor
  · rintro ⟨hz, hc⟩
    refine ⟨⟨hz, fun _ => Submodule.mem_top⟩, ?_⟩
    show (ReciprocityTheory.Def.d1 (twCoef (latRep L) χ X)) z = 0
    funext x
    change twCoef (latRep L) χ X x.1 (z x.2) - z (x.1 * x.2) + z x.1 = 0
    rw [hc, ← h1]; abel
  · rintro ⟨⟨hz, -⟩, hk⟩
    refine ⟨hz, fun g h => ?_⟩
    have e : twCoef (latRep L) χ X g (z h) - z (g * h) + z g = 0 := congrFun hk (g, h)
    rw [h1, ← sub_eq_zero, ← neg_eq_zero, ← e]; abel

end GlobalTheory
