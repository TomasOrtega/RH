import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraInducedTypeCharEqProductList
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabelsCharOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalCharacterFormula
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraSeriesLabelExistsUniqueGLn

open Polynomial GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters GlobalTheory.ParamLabel
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHarishChandraInducedTypeCharEqProductList.lean&line=360#L360)
-/
theorem _root_.GlobalTheory.T.harishChandraInducedTypeChar_eq_productList : ∀ (p : ℕ) [Fact p.Prime] (r : ℕ) (s : SSParam p ℂ r), ∃ l : List (Cyc s.1), l.Nodup ∧ (∀ c, c ∈ l) ∧ typeChar s = GlobalTheory.GLq.hcL (l.map fun c => (⟨cycLen s.1 c, cuspOn (s.2 c)⟩ : GlobalTheory.GLq.Pc p)) r := by
  first | exact @GlobalTheory.TypeCharProduct.typeChar_eq_hcL | exact GlobalTheory.TypeCharProduct.typeChar_eq_hcL | (intros; apply GlobalTheory.TypeCharProduct.typeChar_eq_hcL <;> assumption)
