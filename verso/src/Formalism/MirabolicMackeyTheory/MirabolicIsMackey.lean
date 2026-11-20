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
A detailed English derivation is pending.
-/
theorem idxMono : IdxMono := index_monotone
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem idxScaleIn : IdxScaleIn := index_scale_inclusion
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem idxCutLe : IdxCutLe := index_truncation_le
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem idxTransport : IdxTransport := index_transport
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem latInter : LatInter := lattice_intersection
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem threeForms : ThreeForms := three_forms
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem threeFormsSum : ThreeFormsSum := three_forms_sum
/- English proof (translation)
Replace the relevant objects with their definitions. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.
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
A detailed English derivation is pending.
-/
theorem idxPsiGood : IdxPsiGood := idxPsiGood_of idxMono idxScaleIn idxCutLe latInter
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem orthOfMackey : OrthOfMackey := orthogonality_of_mackey
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem lemmaGG : LemmaGG := good_index_GG
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem mackeyProd : MackeyProd := mackey_product
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem mirabolicMackey : MirabolicMackey := mirabolic_mackey_pair
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem mirabolicIsMackey : MirabolicIsMackey := mirabolic_is_mackey
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem dataTrace : DataTrace := data_trace
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem lengthRamified : LengthRamified := length_ramified
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem onLocal : OnLocal := onLocal_of idxMono idxCutLe idxTransport latInter threeForms idxPsiGood lemmaGG
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ramBasic : RamBasic := ramified_basic_bound
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem placeSum : PlaceSum := place_sum
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem depthCases : DepthCases := depth_cases
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem normaliserPair : NormaliserPair := normaliser_pair
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem levelPair : LevelPair := level_pair
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem shareNum : ShareNum := share_numeric
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem unipNum : UnipNum := unipotent_numeric
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem budgetNum : BudgetNum := budget_numeric
/- English proof (translation)
Treat this case separately. Treat this case separately. Treat this case separately. A detailed English derivation is pending.
-/
theorem errSumGood : ErrSumGood := by
  first
    | exact error_sum_good_places
    | exact errSumGood_of
    | exact errSumGood_thm
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem onSum : OnSum := onSum_of placeSum ramBasic errSumGood
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem absorbOn : AbsorbOn := absorb_local_conditions
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem unitChange : UnitChange := unit_change'
/- English proof (translation)
Treat this case separately. Treat this case separately. Treat this case separately. A detailed English derivation is pending.
-/
theorem onExport : OnExport := by
  first
    | exact onExport_of_onExport2 (onExport2_of ramBasic)
    | exact onExport_proof'
    | exact onExport_of ramBasic

end Formalism.EigenvalueLevelCeiling
