import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeanXMulStarRat
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HermitianSymplecticScalars
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaFunctionsSquareIntegrableHeisenbergUnitary

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CoeffVanish

/- English proof (translation)
Introduce `D V W ψ hψ ν 𝓕 hν h𝓕 G G' hG hG'`. Take `⟨U₁, hU₁, hGfix⟩` from `hG.level`. Take `⟨U₂, hU₂, hG'fix⟩` from `hG'.level`. Use `⟨U₁ ⊓ U₂, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[AddSubgroup.coe_inf]`.

Conclude with `hU₁.inter hU₂`. Introduce `ξ u hu hfin hψu`. Take `⟨hcomp, -, hkeep, hunit, -⟩` from `GlobalTheory.ThetaSquare.heisUnitary (V := V) (W := W) hψ`. Establish `hGu : heisO ψ V W u G = G` using `hGfix u hu.1 hfin`. Establish `hG'u : heisO ψ V W u G' = G'` using `hG'fix u hu.2 hfin`.

Establish `hswap : symplOH V W u ξ = -symplOH V W ξ u` using `GlobalTheory.MixModel.symplOH_skew V W ξ u`. Establish `hmove : heisO ψ V W u (heisO ψ V W ξ G) = ψ (-symplO V W ξ u) • heisO ψ V W ξ G`. Establish `hξG : heisO ψ V W ξ G = ψ (symplOH V W ξ u) • heisO ψ V W (ξ + u) G`. Establish `h` using `hcomp ξ u G`. Rewrite `h` using `[hGu]`. Then use the resulting hypothesis.

Rewrite using `[hcomp u ξ G, add_comm u ξ, hξG, smul_smul, ← AddChar.map_add_eq_mul]`. Use `congr 2`. Rewrite using `[hswap, GlobalTheory.ThetaSquare.symplO_eq]`. Expand and normalize the polynomial expressions, which then agree. Use `set c : ℂ := ψ (-symplO V W ξ u) with hc`.

Establish `hI` using `hunit ν 𝓕 hν h𝓕 u (heisO ψ V W ξ G) G' (hkeep ξ G hG) hG'`. Rewrite `hI` using `[hmove, hG'u]`. Unfold `GlobalTheory.Ker.ipO at hI`. Simplify using `only [Pi.smul_apply, smul_eq_mul, mul_assoc, starRingEnd_apply] at hI`. Rewrite `hI` using `[MeasureTheory.integral_const_mul]`.

Establish `hc1 : c ≠ 1`. Introduce `h1`. Apply `hψu` to reduce the goal to its premises. Establish `hprod : ψ (symplO V W ξ u) * c = 1`. Rewrite using `[hc, ← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]`.

Rewrite `hprod` using `[h1, mul_one]`. Then use the resulting hypothesis. Establish `hsub : (c - 1) * ∫ x in 𝓕, heisO ψ V W ξ G x * star (G' x) ∂ν = 0`. Rewrite using `[sub_mul, one_mul, hI, sub_self]`. Break down `mul_eq_zero.mp hsub with h | h` into its components or cases. Conclude with `absurd (sub_eq_zero.mp h) hc1`.

Conclude with `h`.
-/
theorem matrixCoeff_eq_zero : ∀ (D : D7) (V W : HSp D) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (ν : Measure (WO V W)) (𝓕 : Set (WO V W)), ν.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕 ν →
    ∀ G G' : WO V W → ℂ, IsThetaFunO ψ V W G → IsThetaFunO ψ V W G' →
    ∃ U : AddSubgroup (WO V W), IsOpen (U : Set (WO V W)) ∧ ∀ ξ : WO V W, ∀ u ∈ U, u.map (infPart D) = 0 →
      ψ (symplO V W ξ u) ≠ 1 → ∫ x in 𝓕, heisO ψ V W ξ G x * star (G' x) ∂ν = 0 := by
  intro D V W ψ hψ ν 𝓕 hν h𝓕 G G' hG hG'

  obtain ⟨U₁, hU₁, hGfix⟩ := hG.level
  obtain ⟨U₂, hU₂, hG'fix⟩ := hG'.level
  refine ⟨U₁ ⊓ U₂, ?_, ?_⟩
  · rw [AddSubgroup.coe_inf]
    exact hU₁.inter hU₂
  intro ξ u hu hfin hψu
  obtain ⟨hcomp, -, hkeep, hunit, -⟩ := GlobalTheory.ThetaSquare.heisUnitary (V := V) (W := W) hψ
  have hGu : heisO ψ V W u G = G := hGfix u hu.1 hfin
  have hG'u : heisO ψ V W u G' = G' := hG'fix u hu.2 hfin

  have hswap : symplOH V W u ξ = -symplOH V W ξ u := GlobalTheory.MixModel.symplOH_skew V W ξ u
  have hmove : heisO ψ V W u (heisO ψ V W ξ G) = ψ (-symplO V W ξ u) • heisO ψ V W ξ G := by
    have hξG : heisO ψ V W ξ G = ψ (symplOH V W ξ u) • heisO ψ V W (ξ + u) G := by
      have h := hcomp ξ u G
      rwa [hGu] at h
    rw [hcomp u ξ G, add_comm u ξ, hξG, smul_smul, ← AddChar.map_add_eq_mul]
    congr 2
    rw [hswap, GlobalTheory.ThetaSquare.symplO_eq]
    ring

  set c : ℂ := ψ (-symplO V W ξ u) with hc
  have hI := hunit ν 𝓕 hν h𝓕 u (heisO ψ V W ξ G) G' (hkeep ξ G hG) hG'
  rw [hmove, hG'u] at hI
  unfold GlobalTheory.Ker.ipO at hI
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, starRingEnd_apply] at hI
  rw [MeasureTheory.integral_const_mul] at hI
  have hc1 : c ≠ 1 := by
    intro h1
    apply hψu
    have hprod : ψ (symplO V W ξ u) * c = 1 := by
      rw [hc, ← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
    rwa [h1, mul_one] at hprod
  have hsub : (c - 1) * ∫ x in 𝓕, heisO ψ V W ξ G x * star (G' x) ∂ν = 0 := by
    rw [sub_mul, one_mul, hI, sub_self]
  rcases mul_eq_zero.mp hsub with h | h
  · exact absurd (sub_eq_zero.mp h) hc1
  · exact h

end GlobalTheory.CoeffVanish

end
