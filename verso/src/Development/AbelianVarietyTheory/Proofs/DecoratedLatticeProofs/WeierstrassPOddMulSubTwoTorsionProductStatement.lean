import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeierstrassPOddMulSubTwoTorsionProduct
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EndOmega
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.TranslateProduct
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.StatementC
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.StatementK
open PowerSeries GlobalTheory.Honda Formalism.L2.Th1.CM
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.OddHalfProduct.wp_odd_mul_sub_half_prod` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FWeierstrassPOddMulSubTwoTorsionProduct.lean&line=161#L161)
-/
theorem _root_.GlobalTheory.T.weierstrassP_odd_mul_sub_twoTorsion_product : ∀ (L : PeriodPair) (n : ℕ) (S : Finset ℂ) (t : ℂ), Odd n → Formalism.L2.Th1.F.IsKerReps L (n : ℂ) S → t ∉ L.lattice → 2 * t ∈ L.lattice → ∀ z, (n : ℂ) * z ∉ L.lattice → (n : ℂ) ^ 2 * (L.weierstrassP (n * z) - L.weierstrassP t) * ∏ P ∈ S, (L.weierstrassP z - L.weierstrassP P) = (L.weierstrassP z - L.weierstrassP t) * ∏ P ∈ S, (L.weierstrassP z - L.weierstrassP (t + P)) := by
  first | exact @GlobalTheory.OddHalfProduct.wp_odd_mul_sub_half_prod | exact GlobalTheory.OddHalfProduct.wp_odd_mul_sub_half_prod | (intros; apply GlobalTheory.OddHalfProduct.wp_odd_mul_sub_half_prod <;> assumption)
