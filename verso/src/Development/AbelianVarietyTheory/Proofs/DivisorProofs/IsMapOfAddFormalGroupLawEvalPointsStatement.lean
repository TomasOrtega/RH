import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMapOfAddFormalGroupLawEvalPoints
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsMapOfAddFormalGroupLawEvalPoints.lean&line=22#L22)
-/
theorem _root_.GlobalTheory.T.isMapOf_add_formalGroupLawEvalPoints : ∀ (p : ℕ) (k : Type) [CommRing k] (d e : ℕ) (G H : PDivGroup p k) (c : Chart G d) (c' : Chart H e), ∀ (ν : Fin e → MvPowerSeries (Fin e ⊕ Fin e) k) (f g : G ⟶ H) (φ ψ : Fin e → MvPowerSeries (Fin d) k), c'.IsLawOf ν → c.IsMapOf c' f φ → c.IsMapOf c' g ψ → c.IsMapOf c' (f + g) (op ν φ ψ) := by
  first | exact @GlobalTheory.Katz.Chart.isMapOf_add | exact GlobalTheory.Katz.Chart.isMapOf_add | (intros; apply GlobalTheory.Katz.Chart.isMapOf_add <;> assumption)
