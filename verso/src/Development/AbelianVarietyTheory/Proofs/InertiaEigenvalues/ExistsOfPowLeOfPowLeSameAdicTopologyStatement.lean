import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsOfPowLeOfPowLeSameAdicTopology
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FExistsOfPowLeOfPowLeSameAdicTopology.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.exists_of_pow_le_of_pow_le_same_adicTopology : ∀ (S A : Type) [CommRing S] [CommRing A] (s : S →+* A) (I : Ideal S) (ι : Type) (TB : TopBasis s I ι) (I' : Ideal S) (n m : ℕ), IsHausdorff I S → 0 < n → 0 < m → I ^ n ≤ I' → I' ^ m ≤ I → ∃ TB' : TopBasis s I' ι, TB'.b = TB.b ∧ TB'.c = TB.c := by
  first | exact @GlobalTheory.BSP.TopBasis.exists_of_pow_le_of_pow_le | exact GlobalTheory.BSP.TopBasis.exists_of_pow_le_of_pow_le | (intros; apply GlobalTheory.BSP.TopBasis.exists_of_pow_le_of_pow_le <;> assumption)
