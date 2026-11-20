import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedBasisLocalBlockForm
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsGenericIffIsGenericFor
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittRankLeSkewSignature
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockEmb
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.CuspBlock GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.UnipEmb.emb_mem_unip` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FAdaptedBasisLocalBlockForm.lean&line=76#L76)
-/
theorem _root_.GlobalTheory.T.adapted_basis_local_block_form : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [IsTotallyComplex E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E), IsWittFrame σ J Xf Yf → ∀ (v : HeightOneSpectrum (𝓞 F)) (t : E →ₐ[F] Fv F v) (C : GL (Fin n) E), GlobalTheory.BlockForms.IsAdapted σ J Xf Yf C →
    ∀ (S : Finset (Fin r)) (l d : ℕ), (∀ j : Fin r, l ≤ j.val → j.val + 1 < l + d → j ∉ S) → (∃ k ∈ S, k.val + 1 = l + d) →
      (l = 0 ∨ ∃ p ∈ S, p.val + 1 = l) → ∀ (hld : l + d ≤ n),
      ∀ g ∈ GlobalTheory.SmGL.unipRad (Fv F v) (tripPlace hld), ∀ x : GLoc σ J v,
        IsCompAt σ J t (Matrix.GeneralLinearGroup.map (t : E →+* Fv F v) C) g x → emb σ J v x ∈ GlobalTheory.StdPar.unip σ J Xf S := by
  first | exact @GlobalTheory.UnipEmb.emb_mem_unip | exact GlobalTheory.UnipEmb.emb_mem_unip | (intros; apply GlobalTheory.UnipEmb.emb_mem_unip <;> assumption)
