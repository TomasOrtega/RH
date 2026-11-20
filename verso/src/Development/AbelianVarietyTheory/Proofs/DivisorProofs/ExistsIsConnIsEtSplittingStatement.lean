import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsConnIsEtSplitting
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PDivGroup.exists_isConn_isEt_splitting` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsIsConnIsEtSplitting.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.exists_connected_etale_splitting_pDivGroup : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k), ∃ (G₀ G₁ : PDivGroup p k) (i₀ : G₀ ⟶ G) (q₀ : G ⟶ G₀) (i₁ : G₁ ⟶ G) (q₁ : G ⟶ G₁), G₀.IsConn ∧ G₁.IsEt ∧ i₀ ≫ q₀ = 𝟙 G₀ ∧ i₁ ≫ q₁ = 𝟙 G₁ ∧ q₀ ≫ i₀ + q₁ ≫ i₁ = 𝟙 G := by
  first | exact @GlobalTheory.PDivGroup.exists_isConn_isEt_splitting | exact GlobalTheory.PDivGroup.exists_isConn_isEt_splitting | (intros; apply GlobalTheory.PDivGroup.exists_isConn_isEt_splitting <;> assumption)
