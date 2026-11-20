import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemIntegralGLPrincipalCongruenceOfColsCong
import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsMoveRight
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemParahoricOfTrivialReduction
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedK1BlockDecomposition
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FMemIntegralGLPrincipalCongruenceOfColsCong.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.mem_integralGL_principalCongruence_of_cols_cong : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) {n : ℕ} (D : ℕ) (k : Sp E n ≃ₗ[E] Sp E n), 1 ≤ D → (∀ s l, IntAt P (((qOf P : E) ^ D)⁻¹ * (k (Pi.single s (1 : E)) l - (Pi.single s (1 : E) : Sp E n) l))) → ∃ hk : k ∈ GLint E n P, (⟨k, hk⟩ : GLint E n P) ∈ GlobalTheory.TopStep.prinCong n P D := by
  first | exact @GlobalTheory.CongOne.mem_glint_prinCong_of_cols | exact GlobalTheory.CongOne.mem_glint_prinCong_of_cols | (intros; apply GlobalTheory.CongOne.mem_glint_prinCong_of_cols <;> assumption)
