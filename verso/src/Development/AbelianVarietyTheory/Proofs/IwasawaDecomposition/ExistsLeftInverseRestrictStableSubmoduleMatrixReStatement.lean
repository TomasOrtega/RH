import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLeftInverseRestrictStableSubmoduleMatrixRe
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SplitRep
open Formalism.ConjugateSelfDual Formalism.MainNotions.N Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FExistsLeftInverseRestrictStableSubmoduleMatrixRe.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.exists_leftInverse_restrict_stable_submodule_matrixRep : ∀ {Γ L : Type} [Group Γ] [Field L] {a : ℕ} (τ : Γ →* GL (Fin a) L) (V : Submodule L (Fin a → L)), IsInv τ V → ∃ (b : ℕ) (E : Matrix (Fin a) (Fin b) L) (D : Matrix (Fin b) (Fin a) L) (σ : Γ →* GL (Fin b) L), D * E = 1 ∧ LinearMap.range E.mulVecLin = V ∧ ∀ g, ((σ g : GL (Fin b) L) : Matrix (Fin b) (Fin b) L) = D * ((τ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) * E ∧ ((τ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) * E = E * ((σ g : GL (Fin b) L) : Matrix (Fin b) (Fin b) L) := by
  first | exact @GlobalTheory.StableSubMat.exists_restrict | exact GlobalTheory.StableSubMat.exists_restrict | (intros; apply GlobalTheory.StableSubMat.exists_restrict <;> assumption)
