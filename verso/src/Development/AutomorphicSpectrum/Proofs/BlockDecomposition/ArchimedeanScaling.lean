import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.UnramifiedSchwartzDensity.SchCut
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsContinuousScale
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdelesLocalRingTotallyReal
noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.HaarScale

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hσ n M μ ν hμ hν`. Establish `hR : IsLocR (Ainf F)` using `GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hσ.1`. Use `haveI : BorelSpace (Ainf F) := ⟨rfl⟩`. Take `⟨A, hA, hAf⟩` from `exists_scale_tuples σ hσ (Ainf F) hR n M μ hμ`. Take `⟨B, hB, hBf⟩` from `exists_scale_herm σ hσ (Ainf F) hR n ν hν`.

Take `⟨hTR, hLC, hSC, hT2, -, -, -, -⟩` from `id hR`. Use `haveI := hTR`. Use `haveI := hLC`. Use `haveI := hSC`. Use `haveI := hT2`.

Take `⟨iTR, iLC, iSC, iT2, hsig, -, -, iB, -, -⟩` from `GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (Ainf F)`. Use `haveI := iB n M`. Use `haveI := iTR`. Use `haveI := iT2`. Take `⟨jLC, jSC, jT2, jB, -⟩` from `GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ hσ (Ainf F) n`.

Use `haveI := jB`. Use `haveI := jT2`. Establish `hs : ∀ x, σ (σ x) = x` using `GlobalTheory.CompanionTheory.SW.HermTop.sigma_sigma hσ`. Use `⟨A, B, hA, hB, fun g hg => ?_⟩` and prove the remaining obligations. Establish `hTc : Continuous fun X : Fin n → Fin M → Ainf F ⊗[F] E => rmul (Ainf F) X g`.

Use `continuous_pi fun a => continuous_pi fun i => ?_` and prove the remaining obligations. Simplify using `only [rmul]`. Conclude with `continuous_finset_sum _ fun c _ => ((continuous_apply_apply c i).mul continuous_const)`. Establish `hTm : Measurable fun X : Fin n → Fin M → Ainf F ⊗[F] E => rmul (Ainf F) X g` using `hTc.measurable`. Set `τ₀ : HermR (Ainf F) σ n → HermR (Ainf F) σ n` to `fun S => ⟨conjT (Ainf F) σ g * (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) * g, conj_mem (Ainf F) hs _ S⟩`.

Establish `hτ₀c : Continuous τ₀`. Use `Continuous.subtype_mk ?_ _` and prove the remaining obligations. Conclude with `(continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const`. Establish `hcT : ∀ S : HermR (Ainf F) σ n, ((τ₀ S : HermR (Ainf F) σ n) : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) = cT (sigR (Ainf F) σ) g * (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) * g` using `fun S => rfl`. Establish `hB0` using `hBf g hg τ₀ (fun S => rfl)`.

Use `⟨?_, ?_, hAf g hg, fun τ hτ => ?_⟩` and prove the remaining obligations. Introduce `h0`. Establish `h1` using `hAf g hg`. Rewrite `h1` using `[h0, zero_smul, Measure.map_eq_zero_iff hTm.aemeasurable]`. Conclude with `(Measure.IsAddHaarMeasure.toIsOpenPosMeasure (μ := μ)).open_pos Set.univ isOpen_univ Set.univ_nonempty (by rw [h1]; simp)`.

Introduce `h0`. Rewrite `hB0` using `[h0, zero_smul, Measure.map_eq_zero_iff hτ₀c.measurable.aemeasurable]`. Conclude with `(Measure.IsAddHaarMeasure.toIsOpenPosMeasure (μ := ν)).open_pos Set.univ isOpen_univ Set.univ_nonempty (by rw [hB0]; simp)`. Establish `: τ = τ₀` using `funext fun S => Subtype.ext ((hτ S).trans (hcT S).symm)`. Rewrite using `[this]`.

Conclude with `hB0`.
-/
theorem scaleInf : PositivityTheory.PfSWUS.SchInf.ScaleInf := by
  intro F E _ _ _ _ _ σ hσ n M μ ν hμ hν
  classical
  have hR : IsLocR (Ainf F) := GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hσ.1
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  obtain ⟨A, hA, hAf⟩ := exists_scale_tuples σ hσ (Ainf F) hR n M μ hμ
  obtain ⟨B, hB, hBf⟩ := exists_scale_herm σ hσ (Ainf F) hR n ν hν
  obtain ⟨hTR, hLC, hSC, hT2, -, -, -, -⟩ := id hR
  haveI := hTR
  haveI := hLC
  haveI := hSC
  haveI := hT2
  obtain ⟨iTR, iLC, iSC, iT2, hsig, -, -, iB, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (Ainf F)
  haveI := iB n M
  haveI := iTR
  haveI := iT2
  obtain ⟨jLC, jSC, jT2, jB, -⟩ := GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ hσ (Ainf F) n
  haveI := jB
  haveI := jT2
  have hs : ∀ x, σ (σ x) = x := GlobalTheory.CompanionTheory.SW.HermTop.sigma_sigma hσ
  refine ⟨A, B, hA, hB, fun g hg => ?_⟩
  have hTc : Continuous fun X : Fin n → Fin M → Ainf F ⊗[F] E => rmul (Ainf F) X g := by
    refine continuous_pi fun a => continuous_pi fun i => ?_
    simp only [rmul]
    exact continuous_finset_sum _ fun c _ => ((continuous_apply_apply c i).mul continuous_const)
  have hTm : Measurable fun X : Fin n → Fin M → Ainf F ⊗[F] E => rmul (Ainf F) X g := hTc.measurable
  let τ₀ : HermR (Ainf F) σ n → HermR (Ainf F) σ n := fun S =>
    ⟨conjT (Ainf F) σ g * (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) * g, conj_mem (Ainf F) hs _ S⟩
  have hτ₀c : Continuous τ₀ := by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const
  have hcT : ∀ S : HermR (Ainf F) σ n, ((τ₀ S : HermR (Ainf F) σ n) : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) =
      cT (sigR (Ainf F) σ) g * (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) * g := fun S => rfl
  have hB0 := hBf g hg τ₀ (fun S => rfl)
  refine ⟨?_, ?_, hAf g hg, fun τ hτ => ?_⟩
  · intro h0
    have h1 := hAf g hg
    rw [h0, zero_smul, Measure.map_eq_zero_iff hTm.aemeasurable] at h1
    exact (Measure.IsAddHaarMeasure.toIsOpenPosMeasure (μ := μ)).open_pos Set.univ isOpen_univ Set.univ_nonempty
      (by rw [h1]; simp)
  · intro h0
    rw [h0, zero_smul, Measure.map_eq_zero_iff hτ₀c.measurable.aemeasurable] at hB0
    exact (Measure.IsAddHaarMeasure.toIsOpenPosMeasure (μ := ν)).open_pos Set.univ isOpen_univ Set.univ_nonempty
      (by rw [hB0]; simp)
  · have : τ = τ₀ := funext fun S => Subtype.ext ((hτ S).trans (hcT S).symm)
    rw [this]
    exact hB0

end GlobalTheory.CompanionTheory.SW.HaarScale
