import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimpleModuleLinkageDualWeylLatticeReduction
import Development.AbelianVarietyTheory.Definitions.Divisors.LiftFrameEmbeddingBase
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSimpleModuleLinkageDualWeylLatticeReduction.lean&line=155#L155)
-/
theorem _root_.GlobalTheory.T.simpleModule_linkage_dualWeylLattice_reduction : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (lam : ι → ℕ → ℕ) (mu : ι → ℕ → ℕ) (l : ℕ) (ϖ : O), l.Prime → Irreducible ϖ → ϖ ∣ (l : O) → (∀ τ, Antitone (res N (lam τ))) → (∀ τ, Antitone (res N (mu τ))) → ∀ (Gm : Type) [AddCommGroup Gm] [Module (alg O N lam) Gm], Nontrivial Gm → SubQ O N lam ϖ Gm → Embeds O N lam mu ϖ Gm → ∀ τ, (∏ a : Fin N, (Polynomial.X + Polynomial.C (((lam τ a : ℤ) - (a : ℕ) : ℤ) : ZMod l))) = ∏ a : Fin N, (Polynomial.X + Polynomial.C (((mu τ a : ℤ) - (a : ℕ) : ℤ) : ZMod l)) := by
  first | exact @GlobalTheory.CapelliLink.linkage | exact GlobalTheory.CapelliLink.linkage | (intros; apply GlobalTheory.CapelliLink.linkage <;> assumption)
