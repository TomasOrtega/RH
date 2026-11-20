import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NatCardTorsionQuotSpanDvdOfRangeSubset
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultCellsAmong
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBaryStageStart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfToRealRel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAdmissibleFanOfCellMultOneCMField
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FNatCardTorsionQuotSpanDvdOfRangeSubset.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.natCard_torsion_quot_span_dvd_of_range_subset' : ∀ (L : Type) [AddCommGroup L] {m n : ℕ} (δ : Fin m → L) (γ : Fin n → L), LinearIndependent ℤ δ →
    Set.range γ ⊆ Set.range δ →
    Nat.card (Submodule.torsion ℤ (L ⧸ Submodule.span ℤ (Set.range γ))) ∣
      Nat.card (Submodule.torsion ℤ (L ⧸ Submodule.span ℤ (Set.range δ))) := by
  first | exact @GlobalTheory.natCard_torsion_quot_span_dvd_of_range_subset | exact GlobalTheory.natCard_torsion_quot_span_dvd_of_range_subset | (intros; apply GlobalTheory.natCard_torsion_quot_span_dvd_of_range_subset <;> assumption)
