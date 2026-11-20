import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.ErrSum
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.IdxFull
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.IdxPsiGood
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.IdxRules
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.LemmaGG
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.Mirabolic
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.UnipotentNumeric
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.OnExport
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.OnLocal
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.OrthogonalityOfMackey
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.RamBasic
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.AbsorbLocalConditions
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.ThreeForms

namespace Formalism.EigenvalueLevelCeiling

/- English proof (translation)
The claim follows from `index_monotone`.
-/
theorem idxMono : IdxMono := index_monotone
/- English proof (translation)
The claim follows from `index_scale_inclusion`.
-/
theorem idxScaleIn : IdxScaleIn := index_scale_inclusion
/- English proof (translation)
The claim follows from `index_truncation_le`.
-/
theorem idxCutLe : IdxCutLe := index_truncation_le
/- English proof (translation)
The claim follows from `index_transport`.
-/
theorem idxTransport : IdxTransport := index_transport
/- English proof (translation)
The claim follows from `lattice_intersection`.
-/
theorem latInter : LatInter := lattice_intersection
/- English proof (translation)
The claim follows from `three_forms`.
-/
theorem threeForms : ThreeForms := three_forms
/- English proof (translation)
The claim follows from `three_forms_sum`.
-/
theorem threeFormsSum : ThreeFormsSum := three_forms_sum
/- English proof (translation)
Unfold `IdxFull`. Introduce `K _ _ _ Z _ _ _ _ _ w M Th ThK hM hTh hThK _ σ hσ hsc E r h`. Take `⟨hL, heq⟩` from `idxScaleIn K Z w ⊤ M ThK hM hThK σ hσ`. Establish `hmono` using `idxMono K Z w ⊤ M Th (sc σ ThK) hM hTh hL hsc`. Rewrite `hmono` using `[heq, finrank_top]`.

Establish `h2 : (lix w M ThK : ℝ) + (Module.finrank K Z : ℝ) * (Formalism.DivisionValues.vw w σ : ℝ) ≤ (lix w M Th : ℝ)`. Conclude with `hmono` after adjusting the coercions. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem idxFull : IdxFull := by
  unfold IdxFull
  intro K _ _ _ Z _ _ _ _ _ w M Th ThK hM hTh hThK _ σ hσ hsc E r h
  obtain ⟨hL, heq⟩ := idxScaleIn K Z w ⊤ M ThK hM hThK σ hσ
  have hmono := idxMono K Z w ⊤ M Th (sc σ ThK) hM hTh hL hsc
  rw [heq, finrank_top] at hmono
  have h2 : (lix w M ThK : ℝ) + (Module.finrank K Z : ℝ) * (Formalism.DivisionValues.vw w σ : ℝ) ≤ (lix w M Th : ℝ) := by
    exact_mod_cast hmono
  nlinarith
/- English proof (translation)
The claim follows from `idxPsiGood_of idxMono idxScaleIn idxCutLe latInter`.
-/
theorem idxPsiGood : IdxPsiGood := idxPsiGood_of idxMono idxScaleIn idxCutLe latInter
/- English proof (translation)
The claim follows from `orthogonality_of_mackey`.
-/
theorem orthOfMackey : OrthOfMackey := orthogonality_of_mackey
/- English proof (translation)
The claim follows from `good_index_GG`.
-/
theorem lemmaGG : LemmaGG := good_index_GG
/- English proof (translation)
The claim follows from `mackey_product`.
-/
theorem mackeyProd : MackeyProd := mackey_product
/- English proof (translation)
The claim follows from `mirabolic_mackey_pair`.
-/
theorem mirabolicMackey : MirabolicMackey := mirabolic_mackey_pair
/- English proof (translation)
The claim follows from `mirabolic_is_mackey`.
-/
theorem mirabolicIsMackey : MirabolicIsMackey := mirabolic_is_mackey
/- English proof (translation)
The claim follows from `data_trace`.
-/
theorem dataTrace : DataTrace := data_trace
/- English proof (translation)
The claim follows from `length_ramified`.
-/
theorem lengthRamified : LengthRamified := length_ramified
/- English proof (translation)
The claim follows from `onLocal_of idxMono idxCutLe idxTransport latInter threeForms idxPsiGood lemmaGG`.
-/
theorem onLocal : OnLocal := onLocal_of idxMono idxCutLe idxTransport latInter threeForms idxPsiGood lemmaGG
/- English proof (translation)
The claim follows from `ramified_basic_bound`.
-/
theorem ramBasic : RamBasic := ramified_basic_bound
/- English proof (translation)
The claim follows from `place_sum`.
-/
theorem placeSum : PlaceSum := place_sum
/- English proof (translation)
The claim follows from `depth_cases`.
-/
theorem depthCases : DepthCases := depth_cases
/- English proof (translation)
The claim follows from `normaliser_pair`.
-/
theorem normaliserPair : NormaliserPair := normaliser_pair
/- English proof (translation)
The claim follows from `level_pair`.
-/
theorem levelPair : LevelPair := level_pair
/- English proof (translation)
The claim follows from `share_numeric`.
-/
theorem shareNum : ShareNum := share_numeric
/- English proof (translation)
The claim follows from `unipotent_numeric`.
-/
theorem unipNum : UnipNum := unipotent_numeric
/- English proof (translation)
The claim follows from `budget_numeric`.
-/
theorem budgetNum : BudgetNum := budget_numeric
/- English proof (translation)
Use `first`. Consider the case `exact error_sum_good_places`. Consider the case `exact errSumGood_of`. Consider the case `exact errSumGood_thm`.
-/
theorem errSumGood : ErrSumGood := by
  first
    | exact error_sum_good_places
    | exact errSumGood_of
    | exact errSumGood_thm
/- English proof (translation)
The claim follows from `onSum_of placeSum ramBasic errSumGood`.
-/
theorem onSum : OnSum := onSum_of placeSum ramBasic errSumGood
/- English proof (translation)
The claim follows from `absorb_local_conditions`.
-/
theorem absorbOn : AbsorbOn := absorb_local_conditions
/- English proof (translation)
The claim follows from `unit_change'`.
-/
theorem unitChange : UnitChange := unit_change'
/- English proof (translation)
Use `first`. Consider the case `exact onExport_of_onExport2 (onExport2_of ramBasic)`. Consider the case `exact onExport_proof'`. Consider the case `exact onExport_of ramBasic`.
-/
theorem onExport : OnExport := by
  first
    | exact onExport_of_onExport2 (onExport2_of ramBasic)
    | exact onExport_proof'
    | exact onExport_of ramBasic

end Formalism.EigenvalueLevelCeiling
