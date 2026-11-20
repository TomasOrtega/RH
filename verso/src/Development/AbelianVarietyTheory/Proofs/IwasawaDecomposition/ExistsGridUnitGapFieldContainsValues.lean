import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SettingsFormsExistList
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyThetaLiftGridDataUnitGapAllStatesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LeastSplitAuxiliaryPrimePosAllStatesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNumberFieldGridCharactersUniformStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEmbeddingFixedFieldOfLeComplexImageStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalSubfieldComplexFinitelyGenerateStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeightCounting.Up

/- English proof (translation)
Introduce `cDep`. Establish `h` using `StepW.and (GlobalTheory.T.nonempty_thetaLiftGridData_unit_gap_all_states cDep) GlobalTheory.T.leastSplitAuxiliaryPrime_pos_allStates`. Use `EvG.imp h (fun K _ _ _ _ hK => ?_)` and prove the remaining obligations. Take `⟨S₁, P₁, A, S₂, a1, a2, hh⟩` from `hK`. Use `choose M hMf hM using GlobalTheory.T.exists_numberField_gridCharacters_uniform cDep K.s.b`.

Use `choose S hSa hS using fun B₀ => GlobalTheory.T.finiteDimensional_subfield_complex_finitelyGenerated (M B₀) (hMf B₀)`. Use `⟨fun B f F => S₁ B f F ∪ S B, P₁, A, S₂, ?_, a2, ?_⟩` and prove the remaining obligations. Introduce `B f F z hz`. Break down `Finset.mem_union.1 hz with hz | hz` into its components or cases. Use `exacts [a1 B f F z hz, hSa B z hz]`.

Introduce `B f T hO hH hP hA hk hF htriv w hw P x`. Establish `hH' : Has₂ B (S₁ B.toPre f B.KsC) (S₂ B.toPre f B.KsC B.fixedCoefficientFieldInComplex (T.set f))` using `⟨fun z hz => hH.1 z (Finset.mem_union_left _ hz), hH.2⟩`. Take `⟨h1, h3⟩` from `hh B f T hO hH' hP hA hk hF htriv w hw`. Take `⟨G⟩` from `h1 P x`. Take `⟨G', hG'⟩` from `hM B.toPre (w.st x.o.Z) rfl (h3 P x) _ x.m.z.R.toRealDat.toLevCh G`.

Establish `hle : M B.toPre ≤ B.fixedCoefficientFieldInComplex` using `hS B.toPre _ (fun z hz => hH.1 z (Finset.mem_union_right _ hz))`. Take `⟨j, hj⟩` from `GlobalTheory.T.exists_ringHom_LL0_of_le_fixedCoefficientField (w.st x.o.Z) (M B.toPre) hle`. Use `⟨G', GlobalTheory.BigTop.Fun.FieldHas.map j ?_⟩` and prove the remaining obligations. Rewrite using `[hj]`. Conclude with `hG'`.
-/
theorem exists_grid_fieldHas : ∀ cDep : ℝ, AllSt fun K _ _ _ _ _ x => ∃ G : GlobalTheory.ChiGrid.GridData x.m.z.R.toRealDat.toLevCh ⟨1, cDep, K.s.b⟩, GlobalTheory.BigTop.Fun.FieldHas G (embLL0 (Dof x)) := by
  intro cDep
  have h := StepW.and (GlobalTheory.T.nonempty_thetaLiftGridData_unit_gap_all_states cDep) GlobalTheory.T.leastSplitAuxiliaryPrime_pos_allStates
  refine EvG.imp h (fun K _ _ _ _ hK => ?_)
  obtain ⟨S₁, P₁, A, S₂, a1, a2, hh⟩ := hK
  choose M hMf hM using GlobalTheory.T.exists_numberField_gridCharacters_uniform cDep K.s.b
  choose S hSa hS using fun B₀ => GlobalTheory.T.finiteDimensional_subfield_complex_finitelyGenerated (M B₀) (hMf B₀)
  refine ⟨fun B f F => S₁ B f F ∪ S B, P₁, A, S₂, ?_, a2, ?_⟩
  · intro B f F z hz
    rcases Finset.mem_union.1 hz with hz | hz
    exacts [a1 B f F z hz, hSa B z hz]
  · intro B f T hO hH hP hA hk hF htriv w hw P x
    have hH' : Has₂ B (S₁ B.toPre f B.KsC) (S₂ B.toPre f B.KsC B.fixedCoefficientFieldInComplex (T.set f)) :=
      ⟨fun z hz => hH.1 z (Finset.mem_union_left _ hz), hH.2⟩
    obtain ⟨h1, h3⟩ := hh B f T hO hH' hP hA hk hF htriv w hw
    obtain ⟨G⟩ := h1 P x
    obtain ⟨G', hG'⟩ := hM B.toPre (w.st x.o.Z) rfl (h3 P x) _ x.m.z.R.toRealDat.toLevCh G
    have hle : M B.toPre ≤ B.fixedCoefficientFieldInComplex := hS B.toPre _ (fun z hz => hH.1 z (Finset.mem_union_right _ hz))
    obtain ⟨j, hj⟩ := GlobalTheory.T.exists_ringHom_LL0_of_le_fixedCoefficientField (w.st x.o.Z) (M B.toPre) hle
    refine ⟨G', GlobalTheory.BigTop.Fun.FieldHas.map j ?_⟩
    rw [hj]; exact hG'

end GlobalTheory.HeightCounting.Up
