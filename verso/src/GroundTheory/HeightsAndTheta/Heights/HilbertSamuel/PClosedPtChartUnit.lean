import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsClosedPtChartUnit
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinVertDivIff
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.IsVerticalDivOfIsVerticalDivisorAlt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

/- English proof (translation)
Introduce `S _ K _ ι _ P hP I hI hX f a hf hfP`. Establish `: P.IsPrime` using `hP.1.1`. Establish `hTP : KH.cellMon S I ≤ P.primeCompl` using `Submonoid.closure_le.mpr (by rintro _ ⟨k, i, hi, rfl⟩; exact hX k i hi)`. Establish `hPh : NumbersDVR.IsMultiHomogIdeal P` using `(NumbersDVR.Objects.isMultiHomogIdeal_iff P).mpr hP.1.2.1`. Choose the witnesses or unpack the hypotheses as in `⟨t, htT, htJ⟩ : ∃ t ∈ KH.cellMon S I, t ∈ P ⊔ Ideal.span {f} := by`.

Assume the negation of the conclusion as `hno`. Use `push Not at hno`. Take `⟨p, hp, hJp, hdisj⟩` from `Ideal.exists_le_prime_disjoint (P ⊔ Ideal.span {f}) (KH.cellMon S I) (Set.disjoint_left.mpr fun x hxJ hxT => hno x hxT hxJ)`. Take `⟨W, hW, hWh, hWp, hWJ, hWf⟩` from `NumbersDVR.exists_multiHomog_core hp`. Establish `hPW : P ≤ W` using `hWJ P hPh (le_sup_left.trans hJp)`.

Establish `hfW : f ∈ W` using `hWf f a ((NumbersDVR.Objects.isMultiHomog_iff f a).mpr hf) (hJp (Ideal.mem_sup_right (Ideal.mem_span_singleton_self f)))`. Establish `hrel : IsRelevant W`. Introduce `k`. Take `⟨i, hi⟩` from `hI k`. Use `⟨i, fun hXW => Set.disjoint_left.mp hdisj (hWp hXW) ?_⟩` and prove the remaining obligations.

Conclude with `Submonoid.subset_closure ⟨k, i, hi, rfl⟩`. Establish `hWP : W = P` using `hP.2 W ⟨hW, (NumbersDVR.Objects.isMultiHomogIdeal_iff W).mp hWh, hrel⟩ hPW`. Conclude with `hfP (hWP ▸ hfW)`. Take `⟨e, hte'⟩ : ∃ e, NumbersDVR.IsMultiHomog t e` from `by clear htJ`. Proceed by induction on `htT using Submonoid.closure_induction with`.

Consider the case `mem x hx`. Take `⟨k, i, -, rfl⟩` from `hx`. Conclude with `⟨_, isWeightedHomogeneous_X S (NumbersDVR.blockWeight ι) ⟨k, i⟩⟩`. Consider the case `one => exact ⟨0, isWeightedHomogeneous_one S (NumbersDVR.blockWeight ι)⟩`. Consider the case `mul x y _ _ hx hy`.

Take `⟨c, hc⟩` from `hx`. Take `⟨d, hd⟩` from `hy`. Conclude with `⟨c + d, IsWeightedHomogeneous.mul hc hd⟩`. Establish `hf' : NumbersDVR.IsMultiHomog f a` using `(NumbersDVR.Objects.isMultiHomog_iff f a).mpr hf`. Take `⟨p, hpP, r, hr, hpr⟩` from `Submodule.mem_sup.mp htJ`.

Take `⟨g₀, rfl⟩` from `Ideal.mem_span_singleton'.mp hr`. Establish `hcomp : weightedHomogeneousComponent (NumbersDVR.blockWeight ι) e t = weightedHomogeneousComponent (NumbersDVR.blockWeight ι) e p + weightedHomogeneousComponent (NumbersDVR.blockWeight ι) e (g₀ * f)`. Rewrite using `[← hpr, map_add]`. Establish `htself : weightedHomogeneousComponent (NumbersDVR.blockWeight ι) e t = t`. Rewrite using `[weightedHomogeneousComponent_of_mem ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr hte'), if_pos rfl]`.

Rewrite `hcomp` using `[htself]`. Establish `hpe : weightedHomogeneousComponent (NumbersDVR.blockWeight ι) e p ∈ P` using `hPh p hpP e`. Distinguish the cases in `hae : a ≤ e`. Use `⟨t, htT, weightedHomogeneousComponent (NumbersDVR.blockWeight ι) (e - a) g₀, e - a, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[add_tsub_cancel_of_le hae]`.

Conclude with `(NumbersDVR.Objects.isMultiHomog_iff t e).mp hte'`. Conclude with `(NumbersDVR.Objects.isMultiHomog_iff _ _).mp (weightedHomogeneousComponent_isWeightedHomogeneous _ _)`. Rewrite `hcomp` using `[NumbersDVR.component_mul_form_of_le hf' hae]`. Rewrite using `[hcomp, add_sub_cancel_right]`. Conclude with `hpe`.

Rewrite `hcomp` using `[NumbersDVR.component_mul_form_of_not_le hf' hae, add_zero]`. Conclude with `absurd (hcomp ▸ hpe) (hTP htT)`.
-/
theorem ClosedPtChartUnit.proof : ClosedPtChartUnit.Statement := by
  classical
  intro S _ K _ ι _ P hP I hI hX f a hf hfP
  have : P.IsPrime := hP.1.1

  have hTP : KH.cellMon S I ≤ P.primeCompl :=
    Submonoid.closure_le.mpr (by rintro _ ⟨k, i, hi, rfl⟩; exact hX k i hi)
  have hPh : NumbersDVR.IsMultiHomogIdeal P := (NumbersDVR.Objects.isMultiHomogIdeal_iff P).mpr hP.1.2.1

  obtain ⟨t, htT, htJ⟩ : ∃ t ∈ KH.cellMon S I, t ∈ P ⊔ Ideal.span {f} := by
    by_contra hno
    push Not at hno
    obtain ⟨p, hp, hJp, hdisj⟩ := Ideal.exists_le_prime_disjoint (P ⊔ Ideal.span {f}) (KH.cellMon S I)
      (Set.disjoint_left.mpr fun x hxJ hxT => hno x hxT hxJ)
    obtain ⟨W, hW, hWh, hWp, hWJ, hWf⟩ := NumbersDVR.exists_multiHomog_core hp
    have hPW : P ≤ W := hWJ P hPh (le_sup_left.trans hJp)
    have hfW : f ∈ W :=
      hWf f a ((NumbersDVR.Objects.isMultiHomog_iff f a).mpr hf)
        (hJp (Ideal.mem_sup_right (Ideal.mem_span_singleton_self f)))
    have hrel : IsRelevant W := by
      intro k
      obtain ⟨i, hi⟩ := hI k
      refine ⟨i, fun hXW => Set.disjoint_left.mp hdisj (hWp hXW) ?_⟩
      exact Submonoid.subset_closure ⟨k, i, hi, rfl⟩
    have hWP : W = P := hP.2 W ⟨hW, (NumbersDVR.Objects.isMultiHomogIdeal_iff W).mp hWh, hrel⟩ hPW
    exact hfP (hWP ▸ hfW)

  obtain ⟨e, hte'⟩ : ∃ e, NumbersDVR.IsMultiHomog t e := by
    clear htJ
    induction htT using Submonoid.closure_induction with
    | mem x hx =>
      obtain ⟨k, i, -, rfl⟩ := hx
      exact ⟨_, isWeightedHomogeneous_X S (NumbersDVR.blockWeight ι) ⟨k, i⟩⟩
    | one => exact ⟨0, isWeightedHomogeneous_one S (NumbersDVR.blockWeight ι)⟩
    | mul x y _ _ hx hy =>
      obtain ⟨c, hc⟩ := hx
      obtain ⟨d, hd⟩ := hy
      exact ⟨c + d, IsWeightedHomogeneous.mul hc hd⟩
  have hf' : NumbersDVR.IsMultiHomog f a := (NumbersDVR.Objects.isMultiHomog_iff f a).mpr hf
  obtain ⟨p, hpP, r, hr, hpr⟩ := Submodule.mem_sup.mp htJ
  obtain ⟨g₀, rfl⟩ := Ideal.mem_span_singleton'.mp hr
  have hcomp : weightedHomogeneousComponent (NumbersDVR.blockWeight ι) e t =
      weightedHomogeneousComponent (NumbersDVR.blockWeight ι) e p +
        weightedHomogeneousComponent (NumbersDVR.blockWeight ι) e (g₀ * f) := by
    rw [← hpr, map_add]
  have htself : weightedHomogeneousComponent (NumbersDVR.blockWeight ι) e t = t := by
    rw [weightedHomogeneousComponent_of_mem ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr hte'), if_pos rfl]
  rw [htself] at hcomp
  have hpe : weightedHomogeneousComponent (NumbersDVR.blockWeight ι) e p ∈ P := hPh p hpP e
  by_cases hae : a ≤ e
  · refine ⟨t, htT, weightedHomogeneousComponent (NumbersDVR.blockWeight ι) (e - a) g₀, e - a, ?_, ?_, ?_⟩
    · rw [add_tsub_cancel_of_le hae]
      exact (NumbersDVR.Objects.isMultiHomog_iff t e).mp hte'
    · exact (NumbersDVR.Objects.isMultiHomog_iff _ _).mp (weightedHomogeneousComponent_isWeightedHomogeneous _ _)
    · rw [NumbersDVR.component_mul_form_of_le hf' hae] at hcomp
      rw [hcomp, add_sub_cancel_right]
      exact hpe
  · rw [NumbersDVR.component_mul_form_of_not_le hf' hae, add_zero] at hcomp
    exact absurd (hcomp ▸ hpe) (hTP htT)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
