import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnfoldingCharArgMulLeftUnipotent
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsAdmissibleIntegralBasisChangeOne
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Proof.unfoldingCharArg_mul_left_unipotent.chArg_left` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FUnfoldingCharArgMulLeftUnipotent.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.unfoldingCharArg_mul_left_unipotent : ∀ (F : Type) [Field F] (n' c' n c : ℕ), 1 ≤ c → c' = c + 1 → ∀ r ∈ Loc.R1 F n c, ∀ (xj : (Fin n' → F) →ₗ[F] (Fin n → F)) (t : Loc.FC n' c' n c → F), Loc.chArg (r.toLinearMap ∘ₗ Loc.xx1 xj t) = Loc.chArg (Loc.xx1 xj t) + Loc.n1Arg r := by
  first | exact @GlobalTheory.Proof.unfoldingCharArg_mul_left_unipotent.chArg_left | exact GlobalTheory.Proof.unfoldingCharArg_mul_left_unipotent.chArg_left | (intros; apply GlobalTheory.Proof.unfoldingCharArg_mul_left_unipotent.chArg_left <;> assumption)
