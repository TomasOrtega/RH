import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.StatementF
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.SingleLetterBiextensionRelation
import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.CmAll
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.SecondCoeffConsistency

namespace Formalism.L2.Th1.Top

open Formalism.L2.Th1.D
open Formalism.L2.Th1.CM (cm4)

/- English proof (translation)
Introduce `dK L hsq hd4 hcm l _ h5 hd hin ι g2 g3 ε hg hε hth`. Take `⟨s2, hs2, hc2, hN⟩` from `nrcmOfCM4 cm4 dK L hsq hd4 hcm l h5 hd hin ι g2 g3 ε hg hε hth`. Use `⟨s2, hs2, hc2, ?_⟩` and prove the remaining obligations. Introduce `σ hσ F hF d N0 N1 _ hd2 hev ιr _ _ om oms hO hT hζ n _ _ f f' hH Θ γ hγ hK1`. Establish `hInt` using `hK l h5 g2 g3 ε s2 hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF (hN σ hσ) n Θ γ hγ hK1`.

Take `⟨U0, Φ, hU, hΦ, hsim, hΘ⟩` from `hS l h5 g2 g3 ε s2 hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF (hN σ hσ) N0 N1 ιr n f f' hH Θ hInt`. Rewrite using `[hΘ]`. Conclude with `theorem_a_entry_all l h5 g2 g3 ε hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF s2 (hN σ hσ) d N0 N1 hd2 hev ιr om oms hO hT hζ U0 Φ hU hΦ hsim`.
-/
theorem matrixEntriesCM_of_uniformGaussModels_of_hypShape (hK : uniformGaussModelConditionReformulated) (hS : HypShape) : MatrixEntriesCM := by
  intro dK L hsq hd4 hcm l _ h5 hd hin ι g2 g3 ε hg hε hth
  obtain ⟨s2, hs2, hc2, hN⟩ :=
    nrcmOfCM4 cm4 dK L hsq hd4 hcm l h5 hd hin ι g2 g3 ε hg hε hth
  refine ⟨s2, hs2, hc2, ?_⟩
  intro σ hσ F hF d N0 N1 _ hd2 hev ιr _ _ om oms hO hT hζ n _ _ f f' hH Θ γ hγ hK1
  have hInt := hK l h5 g2 g3 ε s2 hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF (hN σ hσ) n Θ γ hγ hK1
  obtain ⟨U0, Φ, hU, hΦ, hsim, hΘ⟩ := hS l h5 g2 g3 ε s2 hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF (hN σ hσ)
    N0 N1 ιr n f f' hH Θ hInt
  rw [hΘ]
  exact theorem_a_entry_all l h5 g2 g3 ε hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF s2 (hN σ hσ) d N0 N1 hd2 hev ιr om oms hO hT hζ
    U0 Φ hU hΦ hsim

/- English proof (translation)
Introduce `dK L hsq hd4 hcm l _ h5 hd hin ι g2 g3 ε hg hε hth`. Take `⟨s2, hs2, hc2, hN⟩` from `nrcmOfCM4 cm4 dK L hsq hd4 hcm l h5 hd hin ι g2 g3 ε hg hε hth`. Use `⟨s2, hs2, hc2, ?_⟩` and prove the remaining obligations. Introduce `σ hσ F hF d N0 N1 _ hd2 hev ιr _ _ om oms hO hT hζ n _ _ f f' hH Θ γ hγ hK1`. Establish `hInt` using `hK l h5 g2 g3 ε s2 hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF (hN σ hσ) n Θ γ hγ hK1`.

Take `⟨U0, Φ, hU, hΦ, hsim, hΘ⟩` from `hS l h5 g2 g3 ε s2 hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF (hN σ hσ) N0 N1 ιr n f f' hH Θ hInt`. Rewrite using `[hΘ]`. Conclude with `theorem_a_gauss_all l h5 g2 g3 ε hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF s2 (hN σ hσ) d N0 N1 hd2 hev ιr om oms hO hT hζ U0 Φ hU hΦ hsim`.
-/
theorem gaussFormCM_of_uniformGaussModels_of_hypShape (hK : uniformGaussModelConditionReformulated) (hS : HypShape) : GaussFormCM := by
  intro dK L hsq hd4 hcm l _ h5 hd hin ι g2 g3 ε hg hε hth
  obtain ⟨s2, hs2, hc2, hN⟩ :=
    nrcmOfCM4 cm4 dK L hsq hd4 hcm l h5 hd hin ι g2 g3 ε hg hε hth
  refine ⟨s2, hs2, hc2, ?_⟩
  intro σ hσ F hF d N0 N1 _ hd2 hev ιr _ _ om oms hO hT hζ n _ _ f f' hH Θ γ hγ hK1
  have hInt := hK l h5 g2 g3 ε s2 hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF (hN σ hσ) n Θ γ hγ hK1
  obtain ⟨U0, Φ, hU, hΦ, hsim, hΘ⟩ := hS l h5 g2 g3 ε s2 hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF (hN σ hσ)
    N0 N1 ιr n f f' hH Θ hInt
  rw [hΘ]
  exact theorem_a_gauss_all l h5 g2 g3 ε hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF s2 (hN σ hσ) d N0 N1 hd2 hev ιr om oms hO hT hζ
    U0 Φ hU hΦ hsim

/- English proof (translation)
Introduce `dK L hsq hd4 hcm l _ h5 hd hin ι g2 g3 ε hg hε hth`. Take `⟨s2, hs2, hc2, hN⟩` from `nrcmOfCM4 cm4 dK L hsq hd4 hcm l h5 hd hin ι g2 g3 ε hg hε hth`. Use `⟨s2, hs2, hc2, ?_⟩` and prove the remaining obligations. Introduce `σ hσ F hF ν r0 r1 _ om oms hO hT n _ _ f f' hH Θ γ hγ hK1`. Establish `hInt` using `hK l h5 g2 g3 ε s2 hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF (hN σ hσ) n Θ γ hγ hK1`.

Take `⟨U0, Φ, hU, hΦ, hsim, hΘ⟩` from `hS l h5 g2 g3 ε s2 hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF (hN σ hσ) r0 r1 (Fin ν) n f f' hH Θ hInt`. Rewrite using `[hΘ]`. Conclude with `kernel_all l h5 g2 g3 ε hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF s2 (hN σ hσ) ν r0 r1 om oms hO hT U0 Φ hU hΦ hsim`.
-/
theorem threeBoundsCM_of_uniformGaussModels_of_hypShape (hK : uniformGaussModelConditionReformulated) (hS : HypShape) : ThreeBoundsCM := by
  intro dK L hsq hd4 hcm l _ h5 hd hin ι g2 g3 ε hg hε hth
  obtain ⟨s2, hs2, hc2, hN⟩ :=
    nrcmOfCM4 cm4 dK L hsq hd4 hcm l h5 hd hin ι g2 g3 ε hg hε hth
  refine ⟨s2, hs2, hc2, ?_⟩
  intro σ hσ F hF ν r0 r1 _ om oms hO hT n _ _ f f' hH Θ γ hγ hK1
  have hInt := hK l h5 g2 g3 ε s2 hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF (hN σ hσ) n Θ γ hγ hK1
  obtain ⟨U0, Φ, hU, hΦ, hsim, hΘ⟩ := hS l h5 g2 g3 ε s2 hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF (hN σ hσ)
    r0 r1 (Fin ν) n f f' hH Θ hInt
  rw [hΘ]
  exact kernel_all l h5 g2 g3 ε hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF s2 (hN σ hσ) ν r0 r1 om oms hO hT
    U0 Φ hU hΦ hsim

/- English proof (translation)
Introduce `dK L hsq hd4 hcm l _ h5 hd hin ι g2 g3 ε hg hε hth`. Take `⟨s2, hs2, hc2, hN⟩` from `nrcmOfCM4 cm4 dK L hsq hd4 hcm l h5 hd hin ι g2 g3 ε hg hε hth`. Use `⟨s2, hs2, hc2, ?_⟩` and prove the remaining obligations. Introduce `σ hσ F hF N0 N1 C Θ γ hγ hK1`. Establish `hInt` using `hK l h5 g2 g3 ε s2 hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF (hN σ hσ) (Fin N0 × Fin N1) Θ γ hγ hK1`.

Establish `h0 : MvPowerSeries.constantCoeff (Formalism.L2.Th1.E.phSum (phL l g2 g3 s2 ε) : MvPowerSeries (Fin N0 × Fin N1) ℂ_[l]) = 0`. Unfold `Formalism.L2.Th1.E.phSum`. Rewrite using `[map_sum]`. Use `Finset.sum_eq_zero fun x _ => ?_` and prove the remaining obligations. Use `Pair.constantCoeff_inVar_eq_zero x ?_` and prove the remaining obligations.

Unfold `phL`. Rewrite using `[← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply, FAux.cc_phFF (by omega), map_zero]`. Establish `hΘ : Θ = Formalism.DworkPowerSeriesWeights.mvExp (-(Formalism.L2.Th1.E.phSum (phL l g2 g3 s2 ε) : MvPowerSeries (Fin N0 × Fin N1) ℂ_[l])) * (Formalism.DworkPowerSeriesWeights.mvExp (Formalism.L2.Th1.E.phSum (phL l g2 g3 s2 ε)) * Θ)`. Take `⟨e0, -, eadd, -⟩` from `Formalism.L2.Th1.C.mvExpLaws ℂ_[l] (Fin N0 × Fin N1)`. Establish `h1` using `eadd (-(Formalism.L2.Th1.E.phSum (phL l g2 g3 s2 ε))) (Formalism.L2.Th1.E.phSum (phL l g2 g3 s2 ε)) (by rw [map_neg, h0, neg_zero]) h0`.

Rewrite `h1` using `[neg_add_cancel, e0]`. Rewrite using `[← mul_assoc]`. Express the relevant statement in the definitionally equal form `Θ = (Formalism.L2.Th1.C.mvExp _ * Formalism.L2.Th1.C.mvExp _) * Θ`. Rewrite using `[← h1, one_mul]`. Rewrite using `[hΘ]`.

Conclude with `one_letter_gauss_all l h5 g2 g3 ε hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF s2 (hN σ hσ) N0 N1 C _ _ hInt h0 (InverseCommuting.sim_refl _)`.
-/
theorem oneLetterGaussCMReformulated_of_uniformGaussModels (hK : uniformGaussModelConditionReformulated) : OneLetterGaussCMReformulated := by
  intro dK L hsq hd4 hcm l _ h5 hd hin ι g2 g3 ε hg hε hth
  obtain ⟨s2, hs2, hc2, hN⟩ :=
    nrcmOfCM4 cm4 dK L hsq hd4 hcm l h5 hd hin ι g2 g3 ε hg hε hth
  refine ⟨s2, hs2, hc2, ?_⟩
  intro σ hσ F hF N0 N1 C Θ γ hγ hK1
  have hInt := hK l h5 g2 g3 ε s2 hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF (hN σ hσ) (Fin N0 × Fin N1) Θ γ hγ hK1
  have h0 : MvPowerSeries.constantCoeff
      (Formalism.L2.Th1.E.phSum (phL l g2 g3 s2 ε) : MvPowerSeries (Fin N0 × Fin N1) ℂ_[l]) = 0 := by
    unfold Formalism.L2.Th1.E.phSum
    rw [map_sum]
    refine Finset.sum_eq_zero fun x _ => ?_
    refine Pair.constantCoeff_inVar_eq_zero x ?_
    unfold phL
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, FAux.cc_phFF (by omega), map_zero]
  have hΘ : Θ = Formalism.DworkPowerSeriesWeights.mvExp (-(Formalism.L2.Th1.E.phSum (phL l g2 g3 s2 ε) :
      MvPowerSeries (Fin N0 × Fin N1) ℂ_[l])) *
      (Formalism.DworkPowerSeriesWeights.mvExp (Formalism.L2.Th1.E.phSum (phL l g2 g3 s2 ε)) * Θ) := by
    obtain ⟨e0, -, eadd, -⟩ := Formalism.L2.Th1.C.mvExpLaws ℂ_[l] (Fin N0 × Fin N1)
    have h1 := eadd (-(Formalism.L2.Th1.E.phSum (phL l g2 g3 s2 ε))) (Formalism.L2.Th1.E.phSum (phL l g2 g3 s2 ε))
      (by rw [map_neg, h0, neg_zero]) h0
    rw [neg_add_cancel, e0] at h1
    rw [← mul_assoc]
    change Θ = (Formalism.L2.Th1.C.mvExp _ * Formalism.L2.Th1.C.mvExp _) * Θ
    rw [← h1, one_mul]
  rw [hΘ]
  exact one_letter_gauss_all l h5 g2 g3 ε hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF s2 (hN σ hσ) N0 N1 C
    _ _ hInt h0 (InverseCommuting.sim_refl _)

end Formalism.L2.Th1.Top
