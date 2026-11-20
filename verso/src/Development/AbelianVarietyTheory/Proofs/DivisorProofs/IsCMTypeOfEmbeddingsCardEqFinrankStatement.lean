import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCMTypeOfEmbeddingsCardEqFinrank
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open GlobalTheory.ToricTransport (coordIn)
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CMTypeCard.card_eq_finrank_of_isCMType` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsCMTypeOfEmbeddingsCardEqFinrank.lean&line=28#L28)
-/
theorem _root_.GlobalTheory.T.isCMTypeOfEmbeddings_card_eq_finrank : ∀ {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [IsCMField E] [Algebra K E] {I : Type} [Fintype I] (φ : I → E →+* ℂ) (hφ : IsCMType φ) (h2 : Module.finrank ℚ K = 2), Fintype.card I = Module.finrank K E := by
  first | exact @GlobalTheory.CMTypeCard.card_eq_finrank_of_isCMType | exact GlobalTheory.CMTypeCard.card_eq_finrank_of_isCMType | (intros; apply GlobalTheory.CMTypeCard.card_eq_finrank_of_isCMType <;> assumption)
