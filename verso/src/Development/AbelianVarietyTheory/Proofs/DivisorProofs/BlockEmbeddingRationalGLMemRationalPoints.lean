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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormBlockEmbLeftInvariant
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.CuspBlock GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open Matrix
open Formalism.UG (cT)
open scoped TensorProduct

namespace GlobalTheory.CuspBlockRat

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ σ _ n J _ r Xf Yf _ l d h ι hι γ`. Take `⟨Φ, j, -, -, hj, hΦ, hmat⟩` from `hι`. Establish `hΦE : ∀ x : E, Φ (inclR (F` using `F) (AF F) x) = algebraMap E (AdeleRing (𝓞 E) E) x := fun x => by`. Rewrite using `[hΦ]`. Use `Prod.ext ?_ ?_` and prove the remaining obligations.

Use `show j (GlobalTheory.LFun.infTens F E ((1 : AF F) ⊗ₜ[F] x)) = algebraMap E (InfiniteAdeleRing E) x`. Rewrite using `[← hj x]`. Use `congr 1`. Use `show GlobalTheory.LFun.finAdEquiv F E (GlobalTheory.LFun.finTens F E ((1 : AF F) ⊗ₜ[F] x)) = algebraMap E (FiniteAdeleRing (𝓞 E) E) x`. Establish `e : GlobalTheory.LFun.finTens F E ((1 : AF F) ⊗ₜ[F] x) = (1 : Af F) ⊗ₜ[F] x` using `by simp [GlobalTheory.LFun.finTens]`.

Rewrite using `[e, show GlobalTheory.LFun.finAdEquiv F E ((1 : Af F) ⊗ₜ[F] x) = _ from GlobalTheory.LFun.toFinAd_tmul 1 x, map_one, one_mul]`. Establish `hΦs : ∀ x : E, Φ.symm (algebraMap E (AdeleRing (𝓞 E) E) x) = inclR (F` using `F) (AF F) x := fun x => by`. Rewrite using `[RingEquiv.symm_apply_eq, hΦE]`. Establish `hinj : Function.Injective (inclR (F` using `F) (E := E) (AF F)) := by`. Introduce `x y hxy`.

Take `⟨w⟩ : Nonempty (InfinitePlace E)` from `inferInstance`. Use `congrArg (fun z => (Φ z).1 w) hxy` as an intermediate fact. Simplify using `only [hΦE] at this`. Conclude with `(algebraMap E w.Completion).injective this`. Establish `hrat : ∀ δ : GL (Fin d) E, (GlobalTheory.CuspRep.ratGL E d δ).1.map Φ.symm = δ.1.map (inclR (F` using `F) (AF F)) := fun δ => by`.

Use extensionality with `a b`. Conclude with `hΦs (δ.1 a b)`. Use `GlobalTheory.CuspBlockLeft.mem_ratPts_of _ (1 + GlobalTheory.BlockForms.blkCols h Xf * (γ.1 - 1) * (cT (σ : E →+* E) (GlobalTheory.BlockForms.blkCols h Yf) * J) + GlobalTheory.BlockForms.blkCols h Yf * (cT (σ : E →+* E) (γ⁻¹).1 - 1) * (cT (σ : E →+* E) (GlobalTheory.BlockForms.bl …` and prove the remaining obligations. Rewrite using `[hmat, ← map_inv, hrat, hrat, GlobalTheory.CuspBlockLeft.cT_inclR]`. Simplify using `[Matrix.map_add, Matrix.map_sub, Matrix.map_mul, Matrix.map_one]`.
-/
theorem blockEmb_ratGL_mem_ratPts : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [IsTotallyComplex E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E), IsWittFrame σ J Xf Yf →
    ∀ (l d : ℕ) (h : l + d ≤ r) (ι : GlobalTheory.CuspRep.GA E d →* GAd σ J), GlobalTheory.BlockForms.IsBlockEmb σ J Xf Yf h ι →
      ∀ γ : GL (Fin d) E, ι (GlobalTheory.CuspRep.ratGL E d γ) ∈ ratPts σ J := by
  intro F E _ _ _ _ _ _ σ _ n J _ r Xf Yf _ l d h ι hι γ
  obtain ⟨Φ, j, -, -, hj, hΦ, hmat⟩ := hι
  have hΦE : ∀ x : E, Φ (inclR (F := F) (AF F) x) = algebraMap E (AdeleRing (𝓞 E) E) x := fun x => by
    rw [hΦ]
    refine Prod.ext ?_ ?_
    · show j (GlobalTheory.LFun.infTens F E ((1 : AF F) ⊗ₜ[F] x)) = algebraMap E (InfiniteAdeleRing E) x
      rw [← hj x]
      congr 1
    · show GlobalTheory.LFun.finAdEquiv F E (GlobalTheory.LFun.finTens F E ((1 : AF F) ⊗ₜ[F] x)) =
        algebraMap E (FiniteAdeleRing (𝓞 E) E) x
      have e : GlobalTheory.LFun.finTens F E ((1 : AF F) ⊗ₜ[F] x) = (1 : Af F) ⊗ₜ[F] x := by simp [GlobalTheory.LFun.finTens]
      rw [e, show GlobalTheory.LFun.finAdEquiv F E ((1 : Af F) ⊗ₜ[F] x) = _ from GlobalTheory.LFun.toFinAd_tmul 1 x, map_one, one_mul]
  have hΦs : ∀ x : E, Φ.symm (algebraMap E (AdeleRing (𝓞 E) E) x) = inclR (F := F) (AF F) x := fun x => by
    rw [RingEquiv.symm_apply_eq, hΦE]
  have hinj : Function.Injective (inclR (F := F) (E := E) (AF F)) := by
    intro x y hxy
    obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
    have := congrArg (fun z => (Φ z).1 w) hxy
    simp only [hΦE] at this
    exact (algebraMap E w.Completion).injective this
  have hrat : ∀ δ : GL (Fin d) E, (GlobalTheory.CuspRep.ratGL E d δ).1.map Φ.symm = δ.1.map (inclR (F := F) (AF F)) :=
    fun δ => by
      ext a b
      exact hΦs (δ.1 a b)
  refine GlobalTheory.CuspBlockLeft.mem_ratPts_of _ (1 + GlobalTheory.BlockForms.blkCols h Xf * (γ.1 - 1) *
      (cT (σ : E →+* E) (GlobalTheory.BlockForms.blkCols h Yf) * J) +
    GlobalTheory.BlockForms.blkCols h Yf * (cT (σ : E →+* E) (γ⁻¹).1 - 1) *
      (cT (σ : E →+* E) (GlobalTheory.BlockForms.blkCols h Xf) * J)) ?_ hinj
  rw [hmat, ← map_inv, hrat, hrat, GlobalTheory.CuspBlockLeft.cT_inclR]
  simp [Matrix.map_add, Matrix.map_sub, Matrix.map_mul, Matrix.map_one]

end GlobalTheory.CuspBlockRat

end
