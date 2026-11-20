import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittFrameEigenvectorColumnForm
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIdTorusEltOne
open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.StdPar GlobalTheory.IdTorus
open Formalism.UG (cT)
open GlobalTheory.Doubling (absE conjUnit)
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FWittFrameEigenvectorColumnForm.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.witt_frame_eigenvector_column_form : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}, IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → ∀ {g : GAd σ J} {k : Fin r} (γ : AF F ⊗[F] E),
    (matHom _ σ J g⁻¹).1 *ᵥ (fun i => adMat F Y i k) = γ • (fun i => adMat F Y i k) → ∀ i,
    (adMat F (cT (σ : E →+* E) Y * J) * (matHom _ σ J g).1) k i =
      (adMat F (cT (σ : E →+* E) Y * J) * (matHom _ σ J g).1 * adMat F X) k k * adMat F (cT (σ : E →+* E) Y * J) k i := by
  first | exact @GlobalTheory.TorusCentRow.row_scalar | exact GlobalTheory.TorusCentRow.row_scalar | (intros; apply GlobalTheory.TorusCentRow.row_scalar <;> assumption)
