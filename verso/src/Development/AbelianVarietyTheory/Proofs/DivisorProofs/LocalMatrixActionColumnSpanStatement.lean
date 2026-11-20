import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalMatrixActionColumnSpan
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockCentre
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalFieldNormValuation
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability
open scoped TensorProduct
open Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLocalMatrixActionColumnSpan.lean&line=44#L44)
-/
theorem _root_.GlobalTheory.T.local_matrix_action_column_span : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X : Matrix (Fin n) (Fin r) E)
    (v : HeightOneSpectrum (𝓞 F)) (x : GLoc σ J v) (z : Fin n → AF F ⊗[F] E) (I : Set (Fin r)),
    (matHom _ σ J x).1 *ᵥ (fun a => compFin F E v (z a)) - (fun a => compFin F E v (z a)) ∈
      Submodule.span (Fv F v ⊗[F] E) ((fun l a => inclR (F := F) (Fv F v) (X a l)) '' I) →
    (matHom _ σ J (emb σ J v x)).1 *ᵥ z - z ∈ GlobalTheory.StdPar.colSpan F X I := by
  first | exact @GlobalTheory.EmbColSpan.emb_mulVec_sub_mem_colSpan | exact GlobalTheory.EmbColSpan.emb_mulVec_sub_mem_colSpan | (intros; apply GlobalTheory.EmbColSpan.emb_mulVec_sub_mem_colSpan <;> assumption)
