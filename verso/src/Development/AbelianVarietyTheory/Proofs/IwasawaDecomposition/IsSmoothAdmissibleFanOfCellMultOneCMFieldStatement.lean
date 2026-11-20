import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAdmissibleFanOfCellMultOneCMField
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotIsPrimZero
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PolFan.smoothEnd` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FIsSmoothAdmissibleFanOfCellMultOneCMField.lean&line=549#L549)
-/
theorem _root_.GlobalTheory.T.isSmoothAdmissibleFan_of_cellMult_one_CMField : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (φ lab : InvFun (𝓞 E)), (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Dominates H.bar X) → IsPolyFan H.bar q φ → SimpLab H.bar q φ lab → maxMult H.bar q φ ≤ 1 → IsPolFan H.bar q φ ∧ NoSelfInt H.bar q φ := by
  first | exact @GlobalTheory.PolFan.smoothEnd | exact GlobalTheory.PolFan.smoothEnd | (intros; apply GlobalTheory.PolFan.smoothEnd <;> assumption)
