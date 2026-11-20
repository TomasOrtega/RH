import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemTwistedCentralizerBlockIff
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParP
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FMemTwistedCentralizerBlockIff.lean&line=51#L51)
-/
theorem _root_.GlobalTheory.T.mem_twisted_centralizer_block_iff : ∀ (E : Type) [Field E] [NumberField E] (n a b : ℕ) (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w), (m.1.val.charpoly * m.2.val.charpoly).Separable → ∀ (hγ : blk h w m 0 ∈ GlobalTheory.LeviDesc.parP a n w) (p : GlobalTheory.LeviDesc.parP a n w), p ∈ twCent (MonoidHom.id _) (⟨blk h w m 0, hγ⟩ : GlobalTheory.LeviDesc.parP a n w) ↔ ∃ t ∈ twCent (MonoidHom.id _) m, blk h w t 0 = (p : GLw n w) := by
  first | exact @GlobalTheory.LeviDesc.mem_twistedCentralizer_parabolic_iff | exact GlobalTheory.LeviDesc.mem_twistedCentralizer_parabolic_iff | (intros; apply GlobalTheory.LeviDesc.mem_twistedCentralizer_parabolic_iff <;> assumption)
