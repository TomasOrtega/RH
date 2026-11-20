import Mathlib
import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.ObstructionLifting.H1StructureDimLe
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsLocalizedModuleResBasicOpenOfQcqs
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsAffineOpenBiInfOfLe
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechLBHomologyFiniteOfAffineCover
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsSmulHomologyEqZeroOfAcyclicFibre
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SubsingletonOfPoints
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MumfordBundleCechFiniteVanishesOffOrigin
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MumfordBundleCechCohomologyFinrank
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProjectiveOverRingByChartsAbelianVariety
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAmpleLBGenericOfSpecial
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FibAc
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.PointSurjectivity

namespace GlobalTheory.CompanionTheory.PointSurjectivity

/- English proof (translation)
Introduce `hac`. Take `⟨t, ht⟩` from `hT`. Set `σ : LB.Sec N` to `⟨fun i => (t.s i).val, fun i j => congrArg Units.val (ht i j)⟩`. Establish `h0` using `hac 0`. Rewrite `h0` using `[cochainComplex_exactAt_zero_iff, cechLB_d _ _ _ 0]`.

Set `x : (secCube f N D).obj ∅` to `SecOnR.of f N _ (GlobalTheory.LB.ofSec σ _)`. Establish `hx : Cube.aug (secCube f N D) x = 0` using `h0 ((Cube.d_aug _ _).trans (map_zero _).symm)`. Take `⟨p⟩` from `‹Nonempty X›`. Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, p ∈ D i := by`. Establish `hp : p ∈ ⨆ i, D i` using `by rw [hc]; trivial`.

Conclude with `TopologicalSpace.Opens.mem_iSup.1 hp`. Choose the witnesses or unpack the hypotheses as in `⟨c, hcp⟩ : ∃ c, p ∈ N.U c := by`. Establish `hp : p ∈ ⨆ i, N.U i` using `by rw [hN.cover]; trivial`. Conclude with `TopologicalSpace.Opens.mem_iSup.1 hp`. Establish `e` using `congrFun hx ⟨{i}, Finset.card_singleton i⟩`.

Establish `e₂` using `congrArg (fun y : SecOnR f N (⨅ j ∈ ({i} : Finset κ), D j) => SecOnR.coord y c) e`. Establish `hpW : p ∈ (⨅ j ∈ ({i} : Finset κ), D j) ⊓ N.U c`. Use `⟨?_, hcp⟩` and prove the remaining obligations. Simplify using `using hi`. Establish `hu : IsUnit (rs X (inf_le_right : (⨅ j ∈ ({i} : Finset κ), D j) ⊓ N.U c ≤ N.U c) (t.s c).val)` using `(t.s c).isUnit.map (rs X inf_le_right)`.

Establish `e₃ : rs X (inf_le_right : (⨅ j ∈ ({i} : Finset κ), D j) ⊓ N.U c ≤ N.U c) (t.s c).val = 0`. Set `y : SecOnR f N (⨅ j ∈ (∅ : Finset κ), D j)` to `x`. Establish `e₄ : rs X (inf_le_inf_right _ (iInf_le_iInf_of_subset D (Finset.empty_subset {i}))) (SecOnR.coord y c) = 0` using `e₂`. Establish `e₅ : SecOnR.coord y c = rs X inf_le_right (t.s c).val` using `GlobalTheory.LB.coord_ofSec _ _ _`. Rewrite `e₄` using `[e₅, rs_rs]`.

Conclude with `e₄`. Rewrite `hu` using `[e₃]`. Establish `hu'` using `hu.map (X.presheaf.germ _ p hpW).hom`. Rewrite `hu'` using `[map_zero]`. Conclude with `not_isUnit_zero hu'`.
-/
theorem not_acyclic_cechLB_of_triv {R : Type} [CommRing R] {X : Scheme.{0}} [Nonempty X]
    (f : X ⟶ Spec (CommRingCat.of R)) (N : LB X)
    (hN : N.IsLB) (hT : Triv N) (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → X.Opens)
    (hc : ⨆ i, D i = ⊤) : ¬ (cechLB f N D).Acyclic := by
  intro hac
  obtain ⟨t, ht⟩ := hT
  let σ : LB.Sec N := ⟨fun i => (t.s i).val, fun i j => congrArg Units.val (ht i j)⟩
  have h0 := hac 0
  rw [cochainComplex_exactAt_zero_iff, cechLB_d _ _ _ 0] at h0
  let x : (secCube f N D).obj ∅ := SecOnR.of f N _ (GlobalTheory.LB.ofSec σ _)
  have hx : Cube.aug (secCube f N D) x = 0 := h0 ((Cube.d_aug _ _).trans (map_zero _).symm)
  obtain ⟨p⟩ := ‹Nonempty X›
  obtain ⟨i, hi⟩ : ∃ i, p ∈ D i := by
    have hp : p ∈ ⨆ i, D i := by rw [hc]; trivial
    exact TopologicalSpace.Opens.mem_iSup.1 hp
  obtain ⟨c, hcp⟩ : ∃ c, p ∈ N.U c := by
    have hp : p ∈ ⨆ i, N.U i := by rw [hN.cover]; trivial
    exact TopologicalSpace.Opens.mem_iSup.1 hp
  have e := congrFun hx ⟨{i}, Finset.card_singleton i⟩
  have e₂ := congrArg (fun y : SecOnR f N (⨅ j ∈ ({i} : Finset κ), D j) => SecOnR.coord y c) e
  have hpW : p ∈ (⨅ j ∈ ({i} : Finset κ), D j) ⊓ N.U c := by
    refine ⟨?_, hcp⟩
    simpa using hi
  have hu : IsUnit (rs X (inf_le_right : (⨅ j ∈ ({i} : Finset κ), D j) ⊓ N.U c ≤ N.U c)
      (t.s c).val) := (t.s c).isUnit.map (rs X inf_le_right)
  have e₃ : rs X (inf_le_right : (⨅ j ∈ ({i} : Finset κ), D j) ⊓ N.U c ≤ N.U c) (t.s c).val = 0 := by
    let y : SecOnR f N (⨅ j ∈ (∅ : Finset κ), D j) := x
    have e₄ : rs X (inf_le_inf_right _ (iInf_le_iInf_of_subset D (Finset.empty_subset {i})))
        (SecOnR.coord y c) = 0 := e₂
    have e₅ : SecOnR.coord y c = rs X inf_le_right (t.s c).val := GlobalTheory.LB.coord_ofSec _ _ _
    rw [e₅, rs_rs] at e₄
    exact e₄
  rw [e₃] at hu
  have hu' := hu.map (X.presheaf.germ _ p hpW).hom
  rw [map_zero] at hu'
  exact not_isUnit_zero hu'

end GlobalTheory.CompanionTheory.PointSurjectivity
