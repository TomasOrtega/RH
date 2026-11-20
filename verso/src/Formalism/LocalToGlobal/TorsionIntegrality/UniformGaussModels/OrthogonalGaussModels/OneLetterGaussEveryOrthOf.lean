import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.StatementB
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthShapeOne
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.SingleLetterBiextensionRelation
import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.CmAll

namespace Formalism.L2.Th1.Top

open Formalism.L2.Th1.D
open Formalism.L2.Th1.CM (cm2 cm3 cm4)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem ThmAEntryEveryOrth_of (hS : OrthShape) : ThmAEntryEveryOrth := by
  intro dK L hsq hd4 hcm l _ h5 hd hin ι g2 g3 ε hg hε hth
  obtain ⟨s2, hs2, ⟨c, hc, e2, e3, es⟩, hN⟩ :=
    nrcmOfCM4 cm4 dK L hsq hd4 hcm l h5 hd hin ι g2 g3 ε hg hε hth
  refine ⟨s2, c, hc, hs2, e2, e3, es, ?_⟩
  intro σ hσ F hF d N0 N1 _ hd2 hev ιr _ _ om oms hO hT hζ n _ f f' hH ω₀ hω hω2 κ _ r s N hr hN0 hlN hs
  obtain ⟨U0, Φ, hU, hΦ, hsim, hΘ⟩ := hS l h5 (Formalism.L2.Th1.F.scalePair L c hc) ι g2 g3 ε s2 e2 e3 es
    hg.2.2.1 hg.2.2.2.1 hg.2.2.2.2.1 hε hth σ hσ F hF (hN σ hσ) N0 N1 ιr n f f' hH ω₀ hω hω2 κ r s N
    hr hN0 hlN hs
  rw [hΘ]
  exact theorem_a_entry_all l h5 g2 g3 ε hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF s2 (hN σ hσ) d N0 N1 hd2 hev ιr om oms hO hT hζ
    U0 Φ hU hΦ hsim

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem ThmAGaussEveryOrth_of (hS : OrthShape) : ThmAGaussEveryOrth := by
  intro dK L hsq hd4 hcm l _ h5 hd hin ι g2 g3 ε hg hε hth
  obtain ⟨s2, hs2, ⟨c, hc, e2, e3, es⟩, hN⟩ :=
    nrcmOfCM4 cm4 dK L hsq hd4 hcm l h5 hd hin ι g2 g3 ε hg hε hth
  refine ⟨s2, c, hc, hs2, e2, e3, es, ?_⟩
  intro σ hσ F hF d N0 N1 _ hd2 hev ιr _ _ om oms hO hT hζ n _ f f' hH ω₀ hω hω2 κ _ r s N hr hN0 hlN hs
  obtain ⟨U0, Φ, hU, hΦ, hsim, hΘ⟩ := hS l h5 (Formalism.L2.Th1.F.scalePair L c hc) ι g2 g3 ε s2 e2 e3 es
    hg.2.2.1 hg.2.2.2.1 hg.2.2.2.2.1 hε hth σ hσ F hF (hN σ hσ) N0 N1 ιr n f f' hH ω₀ hω hω2 κ r s N
    hr hN0 hlN hs
  rw [hΘ]
  exact theorem_a_gauss_all l h5 g2 g3 ε hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF s2 (hN σ hσ) d N0 N1 hd2 hev ιr om oms hO hT hζ
    U0 Φ hU hΦ hsim

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem KernelEveryOrth_of (hS : OrthShape) : KernelEveryOrth := by
  intro dK L hsq hd4 hcm l _ h5 hd hin ι g2 g3 ε hg hε hth
  obtain ⟨s2, hs2, ⟨c, hc, e2, e3, es⟩, hN⟩ :=
    nrcmOfCM4 cm4 dK L hsq hd4 hcm l h5 hd hin ι g2 g3 ε hg hε hth
  refine ⟨s2, c, hc, hs2, e2, e3, es, ?_⟩
  intro σ hσ F hF ν r0 r1 _ om oms hO hT n _ f f' hH ω₀ hω hω2 κ _ r s N hr hN0 hlN hs
  obtain ⟨U0, Φ, hU, hΦ, hsim, hΘ⟩ := hS l h5 (Formalism.L2.Th1.F.scalePair L c hc) ι g2 g3 ε s2 e2 e3 es
    hg.2.2.1 hg.2.2.2.1 hg.2.2.2.2.1 hε hth σ hσ F hF (hN σ hσ) r0 r1 (Fin ν) n f f' hH ω₀ hω hω2 κ r s N
    hr hN0 hlN hs
  rw [hΘ]
  exact kernel_all l h5 g2 g3 ε hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF s2 (hN σ hσ) ν r0 r1 om oms hO hT
    U0 Φ hU hΦ hsim

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities.
-/
theorem OneLetterGaussEveryOrth_of (hS : OrthShapeOne) : OneLetterGaussEveryOrth := by
  intro dK L hsq hd4 hcm l _ h5 hd hin ι g2 g3 ε hg hε hth
  obtain ⟨s2, hs2, ⟨c, hc, e2, e3, es⟩, hN⟩ :=
    nrcmOfCM4 cm4 dK L hsq hd4 hcm l h5 hd hin ι g2 g3 ε hg hε hth
  refine ⟨s2, c, hc, hs2, e2, e3, es, ?_⟩
  intro σ hσ F hF N0 N1 C ω₀ hω hω2 κ _ r s N hr hN0 hlN hs
  obtain ⟨U0, hU, hΘ⟩ := hS l h5 (Formalism.L2.Th1.F.scalePair L c hc) ι g2 g3 ε s2 e2 e3 es
    hg.2.2.1 hg.2.2.2.1 hg.2.2.2.2.1 hε hth (Fin N0 × Fin N1) ω₀ hω hω2 κ r s N hr hN0 hlN hs
  rw [hΘ]
  refine one_letter_gauss_all l h5 g2 g3 ε hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF s2 (hN σ hσ) N0 N1 C
    U0 _ hU ?_ (InverseCommuting.sim_refl _)
  rw [map_sum]
  refine Finset.sum_eq_zero fun x _ => ?_
  refine Pair.constantCoeff_inVar_eq_zero x ?_
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, FAux.cc_phFF (by omega), map_zero]

variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in
/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem ThmAEntryOrth_of (h : ThmAEntryEveryOrth) : ThmAEntryOrth := by
  intro dK L hsq hd4 hcm l _ h5 hd hin ι
  obtain ⟨g2, g3, ε, hg, hε, hth⟩ := FAux.model l cm2 cm3 dK L hsq hd4 hcm h5 hd hin ι
  obtain ⟨s2, c, hc, hs2, e2, e3, es, tail⟩ := h dK L hsq hd4 hcm l h5 hd hin ι g2 g3 ε hg hε hth
  exact ⟨g2, g3, ε, s2, c, hc, hg, hε, hth, hs2, e2, e3, es, tail⟩

variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in
/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem ThmAGaussOrth_of (h : ThmAGaussEveryOrth) : ThmAGaussOrth := by
  intro dK L hsq hd4 hcm l _ h5 hd hin ι
  obtain ⟨g2, g3, ε, hg, hε, hth⟩ := FAux.model l cm2 cm3 dK L hsq hd4 hcm h5 hd hin ι
  obtain ⟨s2, c, hc, hs2, e2, e3, es, tail⟩ := h dK L hsq hd4 hcm l h5 hd hin ι g2 g3 ε hg hε hth
  exact ⟨g2, g3, ε, s2, c, hc, hg, hε, hth, hs2, e2, e3, es, tail⟩

variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in
/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem OneLetterGaussOrth_of (h : OneLetterGaussEveryOrth) : OneLetterGaussOrth := by
  intro dK L hsq hd4 hcm l _ h5 hd hin ι
  obtain ⟨g2, g3, ε, hg, hε, hth⟩ := FAux.model l cm2 cm3 dK L hsq hd4 hcm h5 hd hin ι
  obtain ⟨s2, c, hc, hs2, e2, e3, es, tail⟩ := h dK L hsq hd4 hcm l h5 hd hin ι g2 g3 ε hg hε hth
  exact ⟨g2, g3, ε, s2, c, hc, hg, hε, hth, hs2, e2, e3, es, tail⟩

variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in
/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem KernelOrth_of (h : KernelEveryOrth) : KernelOrth := by
  intro dK L hsq hd4 hcm l _ h5 hd hin ι
  obtain ⟨g2, g3, ε, hg, hε, hth⟩ := FAux.model l cm2 cm3 dK L hsq hd4 hcm h5 hd hin ι
  obtain ⟨s2, c, hc, hs2, e2, e3, es, tail⟩ := h dK L hsq hd4 hcm l h5 hd hin ι g2 g3 ε hg hε hth
  exact ⟨g2, g3, ε, s2, c, hc, hg, hε, hth, hs2, e2, e3, es, tail⟩

end Formalism.L2.Th1.Top
