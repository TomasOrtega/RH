import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockMatrixMulVecBasis
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar
open GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.LeviHC

namespace GlobalTheory.LeviHC

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hcm n J _hJ τ γ hγ`. Take `⟨w, τ', Z', -, hl⟩` from `hγ`. Use `choose y hy1 hy2 using hl`. Establish `hinj : Function.Injective (GlobalTheory.Orb.archMat σ J τ')` using `fun a b e => by`. Rewrite `e` using `[GlobalTheory.Orb.archMat_eq_archEquiv J hcm, GlobalTheory.Orb.archMat_eq_archEquiv J hcm]`.

Conclude with `(archEquiv J hcm τ').injective (Subtype.ext (Units.ext e))`. Establish `hc : Continuous y`. Rewrite using `[(GlobalTheory.Orb.isEmbedding_archMat J hcm τ').continuous_iff]`. Establish `: (GlobalTheory.Orb.matCoord (GlobalTheory.Orb.archMat σ J τ') ∘ y) = fun t i j => NormedSpace.exp (t • Z') i j`. Use function extensionality and compare the values at `t i j`.

Simplify using `only [Function.comp_apply, GlobalTheory.Orb.matCoord, hy2]`. Rewrite using `[this]`. Establish `hexp : Continuous fun t : ℝ => NormedSpace.exp (t • Z')` using `NormedSpace.exp_continuous.comp (continuous_id.smul continuous_const)`. Conclude with `continuous_pi fun i => continuous_pi fun j => (continuous_apply_apply i j).comp hexp`. Establish `h0 : y 0 = 1` using `hinj (by rw [hy2, map_one, zero_smul, NormedSpace.exp_zero])`.

Establish `hm : ∀ s t, y (s + t) = y s * y t` using `fun s t => hinj (by`. Rewrite using `[hy2, map_mul, hy2, hy2, add_smul]`. Conclude with `NormedSpace.exp_add_of_commute ((Commute.refl Z').smul_left _ |>.smul_right _))`. Take `⟨Z, hZ⟩` from `GlobalTheory.OneParamMatrix.eq_exp_of_continuous_oneParameter (fun t => GlobalTheory.Orb.archMat σ J (τ w) (y t)) ((GlobalTheory.Orb.continuous_archMat σ J (τ w)).comp hc) (by simp only [h0, map_one]) (fun s t => by simp only [hm, map_mul])`. Conclude with `⟨w, Z, fun t => ⟨y t, hy1 t, hZ t⟩⟩`.
-/
theorem isLineOf_of_isRealLine : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (τ : ∀ w : InfinitePlace F, EmbOver E w) (γ : ℝ → GAd σ J), IsRealLine σ J γ →
      ∃ (w : InfinitePlace F) (Z : Matrix (Fin n) (Fin n) ℂ), IsLineOf σ J (τ w) Z γ := by
  intro F E _ _ _ _ _ σ hcm n J _hJ τ γ hγ
  obtain ⟨w, τ', Z', -, hl⟩ := hγ
  choose y hy1 hy2 using hl
  have hinj : Function.Injective (GlobalTheory.Orb.archMat σ J τ') := fun a b e => by
    rw [GlobalTheory.Orb.archMat_eq_archEquiv J hcm, GlobalTheory.Orb.archMat_eq_archEquiv J hcm] at e
    exact (archEquiv J hcm τ').injective (Subtype.ext (Units.ext e))
  have hc : Continuous y := by
    rw [(GlobalTheory.Orb.isEmbedding_archMat J hcm τ').continuous_iff]
    have : (GlobalTheory.Orb.matCoord (GlobalTheory.Orb.archMat σ J τ') ∘ y) = fun t i j => NormedSpace.exp (t • Z') i j := by
      funext t i j
      simp only [Function.comp_apply, GlobalTheory.Orb.matCoord, hy2]
    rw [this]
    have hexp : Continuous fun t : ℝ => NormedSpace.exp (t • Z') :=
      NormedSpace.exp_continuous.comp (continuous_id.smul continuous_const)
    exact continuous_pi fun i => continuous_pi fun j => (continuous_apply_apply i j).comp hexp
  have h0 : y 0 = 1 := hinj (by rw [hy2, map_one, zero_smul, NormedSpace.exp_zero])
  have hm : ∀ s t, y (s + t) = y s * y t := fun s t => hinj (by
    rw [hy2, map_mul, hy2, hy2, add_smul]
    exact NormedSpace.exp_add_of_commute ((Commute.refl Z').smul_left _ |>.smul_right _))
  obtain ⟨Z, hZ⟩ := GlobalTheory.OneParamMatrix.eq_exp_of_continuous_oneParameter
    (fun t => GlobalTheory.Orb.archMat σ J (τ w) (y t)) ((GlobalTheory.Orb.continuous_archMat σ J (τ w)).comp hc)
    (by simp only [h0, map_one]) (fun s t => by simp only [hm, map_mul])
  exact ⟨w, Z, fun t => ⟨y t, hy1 t, hZ t⟩⟩

end GlobalTheory.LeviHC
