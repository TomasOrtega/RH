import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardClProdFiniteAlgebraWithInvolution
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DltEqZero
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FCardClProdFiniteAlgebraWithInvolution.lean&line=55#L55)
-/
theorem _root_.GlobalTheory.T.card_cl_prod_finiteAlgebraWithInvolution : ∀ (K : UQ) (B₁ B₂ : InvAlg K), Nat.card (B₁.prod B₂).Cl = Nat.card B₁.Cl * Nat.card B₂.Cl := by
  first | exact @GlobalTheory.UnitLemma.InvAlg.ClProd.card_cl_prod | exact GlobalTheory.UnitLemma.InvAlg.ClProd.card_cl_prod | (intros; apply GlobalTheory.UnitLemma.InvAlg.ClProd.card_cl_prod <;> assumption)
