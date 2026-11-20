import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CentralGroupAlgebraOpPreservesIntegralLevelForms
import Mathlib
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
open NumberField
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FCentralGroupAlgebraOpPreservesIntegralLevelForms.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.centralGroupAlgebraOp_preserves_integralLevelForms : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (v0 : NumberField.InfinitePlace K), Formalism.DivisionValues.IsConjAt v0 →
    ∀ (S : Formalism.L2.DIV.CSD K), (S.H.map v0.embedding).PosDef →
    ∀ (G : Type) [Group G] [Fintype G] (r : Representation K G S.Forms), S.ActGood r →
    ∀ (P : Subgroup G) (ψ : P →* Kˣ) (a : MonoidAlgebra K G), (∀ b, a * b = b * a) → (∀ t : G, ∃ n : ℤ, a.coeff t = n) →
    ∀ x ∈ S.lvlNab r P ψ, (S.lvlOp r P ψ a).mulVec x ∈ S.lvlNab r P ψ := by
  first | exact @GlobalTheory.CentralLevelOp.lvlOp_mem_lvlNab | exact GlobalTheory.CentralLevelOp.lvlOp_mem_lvlNab | (intros; apply GlobalTheory.CentralLevelOp.lvlOp_mem_lvlNab <;> assumption)
