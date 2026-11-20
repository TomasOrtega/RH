import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLatticesIdempotentPositionBounded
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DltEqZero
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FCardLatticesIdempotentPositionBounded.lean&line=84#L84)
-/
theorem _root_.GlobalTheory.T.card_lattices_idempotent_position_bounded : ∀ (K : UQ) (B : InvAlg K) (ι : Type) [Fintype ι] (e π : ι → B.A) (S : Finset ι) (a : K.O), B.P.Separable → K.Small a → IsFrame B e π S → ∀ N : ℕ, ∃ C : ℕ, ∀ p : ι → ℤ, {M : Submodule K.O B.A | Pos B a e N M p}.Finite ∧ {M : Submodule K.O B.A | Pos B a e N M p}.ncard ≤ C := by
  first | exact @GlobalTheory.UnitLemma.Desc.PosCount.card_pos_le | exact GlobalTheory.UnitLemma.Desc.PosCount.card_pos_le | (intros; apply GlobalTheory.UnitLemma.Desc.PosCount.card_pos_le <;> assumption)
