import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemIsotropicUnipotentRadicalIffFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLv
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FMemIsotropicUnipotentRadicalIffFrame.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.mem_isotropicUnipotentRadical_iff_frame : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ u : GAd σ J, u ∈ unipRad σ J C ↔ ((matHom _ σ J u).1 * adMat F C = adMat F C ∧ ∃ b : Matrix (Fin j) (Fin m) (AF F ⊗[F] E), (matHom _ σ J u).1 * adMat F Z = adMat F Z + adMat F C * b) := by
  first | exact @GlobalTheory.SphEis.mem_unipRad_iff_frame | exact GlobalTheory.SphEis.mem_unipRad_iff_frame | (intros; apply GlobalTheory.SphEis.mem_unipRad_iff_frame <;> assumption)
