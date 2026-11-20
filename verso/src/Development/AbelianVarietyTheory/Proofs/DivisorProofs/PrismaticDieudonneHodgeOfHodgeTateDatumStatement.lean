import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrismaticDieudonneHodgeOfHodgeTateDatum
import Development.AbelianVarietyTheory.Definitions.Divisors.GhostFrobenius
open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPrismaticDieudonneHodgeOfHodgeTateDatum.lean&line=25#L25)
-/
theorem _root_.GlobalTheory.T.prismaticDieudonneHodge_of_hodgeTateDatum : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), (∀ G : PDivGroup p O, HasDatum hε G) → GlobalTheory.Published.PrismaticDieudonneHodgeAt ε := by
  first | exact @GlobalTheory.PDivLat.prismaticDieudonneHodgeAt_of_hasDatum | exact GlobalTheory.PDivLat.prismaticDieudonneHodgeAt_of_hasDatum | (intros; apply GlobalTheory.PDivLat.prismaticDieudonneHodgeAt_of_hasDatum <;> assumption)
