import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraInductionCuspidalParabolicProduct
import Formalism.PadicSubsetSums.CentralIdempotents.GaloisConjCentralIdempotent
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.CuspidalProductMultiplicity
open CategoryTheory Polynomial Formalism.IrreducibleCountingLemmas.TYPES
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHarishChandraInductionCuspidalParabolicProduct.lean&line=97#L97)
-/
theorem _root_.GlobalTheory.T.harishChandraInduction_cuspidalParabolicProduct : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (r s : ℕ) (b : Fin r → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)), Function.Surjective b → (∀ c, Simple (lam c) ∧ IsCuspidal K (lam c)) → Monotone b → GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.IsCuspProdChar (fun x : GL (Fin r) K => LinearMap.trace ℂ (hcSpace K b lam) (hcRep K b lam x)) := by
  first | exact @GlobalTheory.HCInduction.isCuspProdChar_trace_hcRep | exact GlobalTheory.HCInduction.isCuspProdChar_trace_hcRep | (intros; apply GlobalTheory.HCInduction.isCuspProdChar_trace_hcRep <;> assumption)
