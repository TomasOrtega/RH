import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinsumCentralIdempotentOfIrrCharacterEqSimple
import Mathlib
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CanonListLength
open CategoryTheory Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FFinsumCentralIdempotentOfIrrCharacterEqSimple.lean&line=52#L52)
-/
theorem _root_.GlobalTheory.T.finsum_centralIdempotentOfIrrCharacter_eq_simple : ∀ {G : Type} [Group G] [Fintype G] (Q : (G → ℂ) → Prop), ∑ᶠ χ ∈ {χ : G → ℂ | GlobalTheory.GLq.IsIrr χ ∧ Q χ}, GlobalTheory.GLq.zOf χ = ∑ᶠ (z : MonoidAlgebra ℂ G) (_ : ∃ τ : FDRep ℂ G, CategoryTheory.Simple τ ∧ Formalism.IrreducibleCountingLemmas.TYPES.zIdem τ = z ∧ Q τ.character), z := by
  first | exact @GlobalTheory.SerCmp.finsum_zOf_eq_finsum_zIdem | exact GlobalTheory.SerCmp.finsum_zOf_eq_finsum_zIdem | (intros; apply GlobalTheory.SerCmp.finsum_zOf_eq_finsum_zIdem <;> assumption)
