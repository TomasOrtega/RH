import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelEntriesHypOfHeckeCharacterConditions
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.kerEntTied_hyp` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FKernelEntriesHypOfHeckeCharacterConditions.lean&line=24#L24)
-/
theorem _root_.GlobalTheory.T.kernelEntries_hyp_of_heckeCharacterConditions : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), (∀ j, ∃ e, Formalism.L2.Col.IsMu0 t.Ch t.seam.σ₀ e j (t.glob.mu0 j)) → (∀ (j : Fin D.R.m) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 t.X.E)), (∀ i, ((t.Pr.g i : ℕ) : 𝓞 t.X.E) ∉ v.asIdeal) → t.seam.σ₀ (t.Ch.muVal j v : t.X.K) = (((t.glob.mu0 j).val v : ℂˣ) : ℂ)) → (∀ μ k, D.host.g k ∉ Y.Qp μ) → t.TopPinned → t.Hyp := by
  first | exact @GlobalTheory.kerEntTied_hyp | exact GlobalTheory.kerEntTied_hyp | (intros; apply GlobalTheory.kerEntTied_hyp <;> assumption)
