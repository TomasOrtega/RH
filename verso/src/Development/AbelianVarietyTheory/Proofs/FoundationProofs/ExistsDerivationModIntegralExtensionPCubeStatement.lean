import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDerivationModIntegralExtensionPCube
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerTowerQqPowLevelEqQ
open GlobalTheory.K5 GlobalTheory.KumDlog
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.DerExt.exists_ext` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FExistsDerivationModIntegralExtensionPCube.lean&line=192#L192)
-/
theorem _root_.GlobalTheory.T.exists_derivationModIntegral_extension_p_cube : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], ∀ (B C : Subalgebra (O0 p) Ω) (ι : Type) [Fintype ι] (u v : ι → Ω) (tr : Ω → Ω), DualData B C u v tr →
  ∀ d : Ω → Ω, IsDer B d → ∃ D : Ω → Ω, IsDer C D ∧ ∀ b ∈ B, IsInt p (D b - (p : Ω) ^ 3 * d b) := by
  first | exact @GlobalTheory.DerExt.exists_ext | exact GlobalTheory.DerExt.exists_ext | (intros; apply GlobalTheory.DerExt.exists_ext <;> assumption)
