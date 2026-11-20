import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelOperatorsSpanEventually
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KerSCShortExact
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FKernelOperatorsSpanEventually.lean&line=68#L68)
-/
theorem _root_.GlobalTheory.T.kernel_operators_span_eventually : GradedNoeth → ∀ {X : Scheme.{0}} [IsLocallyNoetherian X] {k : ℕ} {M : ℕ → X.Modules} {T : Fin k → ∀ e, M e ⟶ M (e + 1)} {d : ℕ} (h : OpSeq k M T d) (U : X.affineOpens), ∃ dU : ℕ, ∀ e, dU ≤ e → Submodule.span Γ(X, U) (⋃ i, Set.range ((KerSeq.kerOp T h.comm d i e).app U)) = ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.GE.KerSeq.kerSeq_gen_bounded | exact GlobalTheory.CompanionTheory.GE.KerSeq.kerSeq_gen_bounded | (intros; apply GlobalTheory.CompanionTheory.GE.KerSeq.kerSeq_gen_bounded <;> assumption)
