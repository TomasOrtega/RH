import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaNumberSU
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentHaarRealSUOfMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalVolumeEqLocalFactorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieLatticeIntegralIndexStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialUnitaryTamagawaMeasureStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueInfEmb

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Filter Topology
open scoped TensorProduct ENNReal
open GlobalTheory.TamSU GlobalTheory.SUVol GlobalTheory.UCls GlobalTheory.AdLat GlobalTheory.Published

namespace GlobalTheory.TamUnfoldSU

/- English proof (translation)
Assemble the required witnesses or components as `⟨inferInstance, inferInstance, Algebra.IsQuadraticExtension.finrank_eq_two _ _, fun τ x => IsCMField.complexEmbedding_complexConj E τ x⟩`.
-/
theorem isCMExt_maxReal (E : Type) [Field E] [NumberField E] [IsCMField E] :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt (maximalRealSubfield E) E (IsCMField.complexConj E).toAlgHom :=
  ⟨inferInstance, inferInstance, Algebra.IsQuadraticExtension.finrank_eq_two _ _,
    fun τ x => IsCMField.complexEmbedding_complexConj E τ x⟩

/- English proof (translation)
Introduce `hP E _ _ _ r G Λ Ψ _ _ e J s hr hU hSD hΨ he hli hs`. Establish `hcm` using `isCMExt_maxReal E`. Take `⟨hGc, hGd, hFG, hspan, -⟩` from `id hSD`. Take `⟨hsum, hmain⟩` from `hP (maximalRealSubfield E) E (IsCMField.complexConj E).toAlgHom hcm r Gᵀ hr ⟨fun i j => hGc i j, by rwa [det_transpose]⟩ Λ hFG hspan`. Establish `hlocf : locVol (IsCMField.complexConj E).toAlgHom Gᵀ Λ = locFactor E r`.

Use function extensionality and compare the values at `(GlobalTheory.T.local_volume_eq_local_factor E r G Λ hr hU hSD)`. Take `⟨hlie, hidx, hpos⟩` from `GlobalTheory.T.lie_lattice_integral_index E r G Λ e hSD he hli`. Rewrite `hsum` using `[hlocf]`. Establish `hmul : Multipliable (locFactor E r)`. Establish `e1 : locFactor E r = fun v => 1 + (locFactor E r v - 1)` using `by funext v; ring`.

Rewrite using `[e1]`. Conclude with `Real.multipliable_one_add_of_summable hsum`. Establish `hprod0 : ∏' v, locFactor E r v ≠ 0`. Establish `h` using `tprod_one_add_ne_zero_of_summable (f := fun v => locFactor E r v - 1) (fun v => by have := hpos v; ring_nf; exact this.ne') (by simpa [Real.norm_eq_abs] using hsum.abs)`. Simplify using `using h`.

Establish `hprod : 0 < ∏' v, locFactor E r v` using `lt_of_le_of_ne (tprod_nonneg fun v => (hpos v).le) (Ne.symm hprod0)`. Establish `hD : 0 < |(discr (maximalRealSubfield E) : ℝ)| ^ (-((r : ℝ) ^ 2 - 1) / 2)` using `Real.rpow_pos_of_pos (abs_pos.2 (by exact_mod_cast discr_ne_zero (maximalRealSubfield E))) _`. Establish `hI : (0 : ℝ) < ((Submodule.span (𝓞 (maximalRealSubfield E)) (Set.range e)).toAddSubgroup.relIndex (lieLat G Λ) : ℝ)` using `by exact_mod_cast Nat.pos_of_ne_zero hidx`. Establish `hc0 : ENNReal.ofReal (|(discr (maximalRealSubfield E) : ℝ)| ^ (-((r : ℝ) ^ 2 - 1) / 2) * ((Submodule.span (𝓞 (maximalRealSubfield E)) (Set.range e)).toAddSubgroup.relIndex (lieLat G Λ) : ℝ) * ∏' v, locFactor E r v) ≠ 0` using `(ENNReal.ofReal_pos.2 (mul_pos (mul_pos hD hI) hprod)).ne'`. Use `choose θ hθ using fun ρ : Ψ => (GlobalTheory.Mem.VolEmb.existsUnique_infEmb (maximalRealSubfield E) E (IsCMField.complexConj E).toAlgHom hcm ρ.1).exists`.

Take `⟨hHaar0, hDens⟩` from `GlobalTheory.SUVol.DensOne.tangentHaar_formLie Ψ G hGd e (fun i => ⟨(he i).1, (he i).2.1⟩) hli`. Take `⟨μ, 𝓕, hHaar, hT, hFD, hμ⟩` from `GlobalTheory.T.special_unitary_tamagawa_measure E r G Λ Ψ θ (formLie Ψ e) (tangentHaar (realSU Ψ G) (formLie Ψ e)) J s _ hSD hΨ hθ hHaar0 hDens hs hc0 ENNReal.ofReal_ne_top`. Establish `hTam : IsTamagawa (IsCMField.complexConj E).toAlgHom Gᵀ Λ Ψ θ e μ`. Use `⟨hHaar, ?_⟩` and prove the remaining obligations. Rewrite using `[hlie, hlocf]`.

Conclude with `hT`. Establish `h1` using `hmain Ψ θ e hΨ hθ (fun i => hlie ▸ he i) hli μ hTam 𝓕 hFD`. Conclude with `⟨hmul, hμ.symm.trans h1⟩`.
-/
theorem tamagawaSpecialUnitary : TamagawaNumberSU → TamagawaSpecialUnitary := by
  intro hP E _ _ _ r G Λ Ψ _ _ e J s hr hU hSD hΨ he hli hs
  have hcm := isCMExt_maxReal E
  obtain ⟨hGc, hGd, hFG, hspan, -⟩ := id hSD
  obtain ⟨hsum, hmain⟩ := hP (maximalRealSubfield E) E (IsCMField.complexConj E).toAlgHom hcm r Gᵀ hr
    ⟨fun i j => hGc i j, by rwa [det_transpose]⟩ Λ hFG hspan
  have hlocf : locVol (IsCMField.complexConj E).toAlgHom Gᵀ Λ = locFactor E r :=
    funext (GlobalTheory.T.local_volume_eq_local_factor E r G Λ hr hU hSD)
  obtain ⟨hlie, hidx, hpos⟩ := GlobalTheory.T.lie_lattice_integral_index E r G Λ e hSD he hli
  rw [hlocf] at hsum
  have hmul : Multipliable (locFactor E r) := by
    have e1 : locFactor E r = fun v => 1 + (locFactor E r v - 1) := by funext v; ring
    rw [e1]; exact Real.multipliable_one_add_of_summable hsum
  have hprod0 : ∏' v, locFactor E r v ≠ 0 := by
    have h := tprod_one_add_ne_zero_of_summable (f := fun v => locFactor E r v - 1)
      (fun v => by have := hpos v; ring_nf; exact this.ne') (by simpa [Real.norm_eq_abs] using hsum.abs)
    simpa using h
  have hprod : 0 < ∏' v, locFactor E r v :=
    lt_of_le_of_ne (tprod_nonneg fun v => (hpos v).le) (Ne.symm hprod0)
  have hD : 0 < |(discr (maximalRealSubfield E) : ℝ)| ^ (-((r : ℝ) ^ 2 - 1) / 2) :=
    Real.rpow_pos_of_pos (abs_pos.2 (by exact_mod_cast discr_ne_zero (maximalRealSubfield E))) _
  have hI : (0 : ℝ) < ((Submodule.span (𝓞 (maximalRealSubfield E)) (Set.range e)).toAddSubgroup.relIndex
      (lieLat G Λ) : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hidx
  have hc0 : ENNReal.ofReal (|(discr (maximalRealSubfield E) : ℝ)| ^ (-((r : ℝ) ^ 2 - 1) / 2) *
      ((Submodule.span (𝓞 (maximalRealSubfield E)) (Set.range e)).toAddSubgroup.relIndex (lieLat G Λ) : ℝ) *
        ∏' v, locFactor E r v) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (mul_pos (mul_pos hD hI) hprod)).ne'
  choose θ hθ using fun ρ : Ψ =>
    (GlobalTheory.Mem.VolEmb.existsUnique_infEmb (maximalRealSubfield E) E (IsCMField.complexConj E).toAlgHom hcm ρ.1).exists
  obtain ⟨hHaar0, hDens⟩ := GlobalTheory.SUVol.DensOne.tangentHaar_formLie Ψ G hGd e (fun i => ⟨(he i).1, (he i).2.1⟩) hli
  obtain ⟨μ, 𝓕, hHaar, hT, hFD, hμ⟩ := GlobalTheory.T.special_unitary_tamagawa_measure E r G Λ Ψ θ (formLie Ψ e)
    (tangentHaar (realSU Ψ G) (formLie Ψ e)) J s _ hSD hΨ hθ hHaar0 hDens hs hc0 ENNReal.ofReal_ne_top
  have hTam : IsTamagawa (IsCMField.complexConj E).toAlgHom Gᵀ Λ Ψ θ e μ := by
    refine ⟨hHaar, ?_⟩
    rw [hlie, hlocf]
    exact hT
  have h1 := hmain Ψ θ e hΨ hθ (fun i => hlie ▸ he i) hli μ hTam 𝓕 hFD
  exact ⟨hmul, hμ.symm.trans h1⟩

end GlobalTheory.TamUnfoldSU
