import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModuleFreeOfRegularOfFreeQuotientLocal
import Mathlib
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.ModDepthGE
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PurityFree
open IsLocalRing
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.AnnRegSeq.free_of_free_quotient_map` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FModuleFreeOfRegularOfFreeQuotientLocal.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.moduleFree_of_regular_of_free_quotient_local : ∀ (R A : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [CommRing A] [Algebra R A] [Module.Finite R A] (f : R), f ∈ maximalIdeal R → IsSMulRegular A f → Module.Free (R ⧸ Ideal.span {f}) (A ⧸ (Ideal.span {f}).map (algebraMap R A)) → Module.Free R A := by
  first | exact @GlobalTheory.AnnRegSeq.free_of_free_quotient_map | exact GlobalTheory.AnnRegSeq.free_of_free_quotient_map | (intros; apply GlobalTheory.AnnRegSeq.free_of_free_quotient_map <;> assumption)
