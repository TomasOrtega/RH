import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFiniteAdelicOrthogonalStabilizerEmbedding
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsFinEmb
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FExistsFiniteAdelicOrthogonalStabilizerEmbedding.lean&line=62#L62)
-/
theorem _root_.GlobalTheory.T.exists_finiteAdelic_orthogonal_stabilizer_embedding : ∀ (I : AutInst) (D : Sib I) (s : Bool) (x : Fin I.n → I.E) (A : Matrix (Fin I.n) (Fin D.n) I.E) (xf : I.Gf), IsPerp D s x A xf → ∃ jf : D.inst.Gf →* I.Gf, IsFinEmb D x A jf ∧ ∀ h : I.Gf, I.fmat h *ᵥ afVec I x = afVec I x → h ∈ jf.range := by
  first | exact @GlobalTheory.StabUnfold.exists_finEmb | exact GlobalTheory.StabUnfold.exists_finEmb | (intros; apply GlobalTheory.StabUnfold.exists_finEmb <;> assumption)
