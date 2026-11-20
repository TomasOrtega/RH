import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedCentralizerBlockLeParabolic
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParP
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LeviDesc.twCent_blk_le_parP` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FTwistedCentralizerBlockLeParabolic.lean&line=25#L25)
-/
theorem _root_.GlobalTheory.T.twisted_centralizer_block_le_parabolic : ∀ (E : Type) [Field E] [NumberField E] (n a b : ℕ) (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w), (m.1.val.charpoly * m.2.val.charpoly).Separable → twCent (MonoidHom.id (GLw n w)) (blk h w m 0) ≤ GlobalTheory.LeviDesc.parP a n w := by
  first | exact @GlobalTheory.LeviDesc.twCent_blk_le_parP | exact GlobalTheory.LeviDesc.twCent_blk_le_parP | (intros; apply GlobalTheory.LeviDesc.twCent_blk_le_parP <;> assumption)
