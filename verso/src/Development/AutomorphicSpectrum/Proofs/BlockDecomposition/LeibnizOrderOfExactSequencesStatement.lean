import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeibnizOrderOfExactSequences
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.PhiPG0
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.LeibOrd.Main.leibnizOrd_of_parts` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FLeibnizOrderOfExactSequences.lean&line=318#L318)
-/
theorem _root_.GlobalTheory.T.leibniz_order_of_exact_sequences : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ResSeq k → PsiGP k → PhiGP k → PsiPG k → PhiPG k → PhiPG0 k → LeibnizOrd k := by
  first | exact @GlobalTheory.CompanionTheory.LeibOrd.Main.leibnizOrd_of_parts | exact GlobalTheory.CompanionTheory.LeibOrd.Main.leibnizOrd_of_parts | (intros; apply GlobalTheory.CompanionTheory.LeibOrd.Main.leibnizOrd_of_parts <;> assumption)
