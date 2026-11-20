import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddCharConductorAndHaarIntegersExist
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierTransformInversionLocalFieldPi
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSchwartzBruhatConvolutionLocalFieldPower

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi
open scoped Topology

noncomputable section
namespace GlobalTheory.SplitWeil.FourierPi

/- English proof (translation)
Introduce `k _ _ _ _ _ _ ν hν n _ r R S hS hrep F hF hF0`. Establish `: ν.IsAddHaarMeasure` using `hν`. Establish `: SecondCountableTopology k` using `secondCountable k`. Establish `: SigmaFinite ν` using `inferInstance`. Establish `: (Measure.pi fun _ : n => ν).IsAddHaarMeasure` using `inferInstance`.

Use `set μ : Measure (n → k) := Measure.pi fun _ => ν`. Establish `hmeas : MeasurableSet (box n r)` using `MeasurableSet.univ_pi fun _ => (isOpen_cball r).measurableSet`. Establish `hfin : μ (box n r) < ⊤` using `(isCompact_box r).measure_lt_top`. Establish `key : ∀ y, F y = ∑ b ∈ S, (box n r).indicator (fun _ => F b) (y - b)`. Introduce `y`.

Distinguish the cases in `hy : y ∈ box n R`. Take `⟨b, ⟨hbS, hb⟩, huniq⟩` from `hrep y hy`. Rewrite using `[Finset.sum_eq_single b]`. Rewrite using `[Set.indicator_of_mem hb]`. Establish `h` using `hF (y - b) hb b`.

Rewrite `h` using `[add_sub_cancel]`. Then use the resulting hypothesis. Introduce `b' hb'S hne`. Establish `hnot : y - b' ∉ box n r` using `fun hmem => hne (huniq b' ⟨hb'S, hmem⟩)`. Conclude with `Set.indicator_of_notMem hnot _`. Introduce `hbn`.

Conclude with `absurd hbS hbn`. Rewrite using `[hF0 y hy]`. Use `symm`. Use `Finset.sum_eq_zero fun b _ => ?_` and prove the remaining obligations. Distinguish the cases in `hmem : y - b ∈ box n r`.

Rewrite using `[Set.indicator_of_mem hmem]`. Establish `h` using `hF (y - b) hmem b`. Rewrite `h` using `[add_sub_cancel]`. Rewrite using `[← h, hF0 y hy]`. Conclude with `Set.indicator_of_notMem hmem _`.

Establish `hint : ∀ b ∈ S, Integrable (fun y => (box n r).indicator (fun _ => F b) (y - b)) μ`. Introduce `b _`. Establish `h1 : Integrable ((box n r).indicator fun _ : n → k => F b) μ`. Use `(integrable_indicator_iff hmeas).2 ?_` and prove the remaining obligations. Conclude with `integrableOn_const hfin.ne`.

Conclude with `h1.comp_sub_right b`. Combine the equalities or inequalities in the displayed calculation. Use `congr 1`. Use function extensionality and compare the values at `y`. Conclude with `key y`.

Use `_ = ∑ b ∈ S, ∫ y, (box n r).indicator (fun _ => F b) (y - b) ∂μ := integral_finsetSum S hint`. Use `_ = ∑ b ∈ S, (μ.real (box n r) : ℂ) * F b := by`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[integral_sub_right_eq_self (fun y => (box n r).indicator (fun _ => F b) y) b, integral_indicator_const _ hmeas, Complex.real_smul]`. Use `_ = _ := by rw [Finset.mul_sum]`.
-/
theorem integral_eq_measureReal_box_mul_sum : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), ν.IsAddHaarMeasure → ∀ (n : Type) [Fintype n] (r R : kˣ) (S : Finset (n → k)), (∀ b ∈ S, b ∈ box n R) → (∀ a ∈ box n R, ∃! b, b ∈ S ∧ a - b ∈ box n r) → ∀ F : (n → k) → ℂ, (∀ t ∈ box n r, ∀ y, F (y + t) = F y) → (∀ y ∉ box n R, F y = 0) → ∫ y, F y ∂(Measure.pi fun _ => ν) = ((Measure.pi fun _ : n => ν).real (box n r) : ℂ) * ∑ b ∈ S, F b := by
  intro k _ _ _ _ _ _ ν hν n _ r R S hS hrep F hF hF0
  classical
  have : ν.IsAddHaarMeasure := hν
  have : SecondCountableTopology k := secondCountable k
  have : SigmaFinite ν := inferInstance
  have : (Measure.pi fun _ : n => ν).IsAddHaarMeasure := inferInstance
  set μ : Measure (n → k) := Measure.pi fun _ => ν
  have hmeas : MeasurableSet (box n r) :=
    MeasurableSet.univ_pi fun _ => (isOpen_cball r).measurableSet
  have hfin : μ (box n r) < ⊤ := (isCompact_box r).measure_lt_top

  have key : ∀ y, F y = ∑ b ∈ S, (box n r).indicator (fun _ => F b) (y - b) := by
    intro y
    by_cases hy : y ∈ box n R
    · obtain ⟨b, ⟨hbS, hb⟩, huniq⟩ := hrep y hy
      rw [Finset.sum_eq_single b]
      · rw [Set.indicator_of_mem hb]
        have h := hF (y - b) hb b
        rwa [add_sub_cancel] at h
      · intro b' hb'S hne
        have hnot : y - b' ∉ box n r := fun hmem => hne (huniq b' ⟨hb'S, hmem⟩)
        exact Set.indicator_of_notMem hnot _
      · intro hbn
        exact absurd hbS hbn
    · rw [hF0 y hy]
      symm
      refine Finset.sum_eq_zero fun b _ => ?_
      by_cases hmem : y - b ∈ box n r
      · rw [Set.indicator_of_mem hmem]
        have h := hF (y - b) hmem b
        rw [add_sub_cancel] at h
        rw [← h, hF0 y hy]
      · exact Set.indicator_of_notMem hmem _
  have hint : ∀ b ∈ S, Integrable (fun y => (box n r).indicator (fun _ => F b) (y - b)) μ := by
    intro b _
    have h1 : Integrable ((box n r).indicator fun _ : n → k => F b) μ := by
      refine (integrable_indicator_iff hmeas).2 ?_
      exact integrableOn_const hfin.ne
    exact h1.comp_sub_right b
  calc ∫ y, F y ∂μ = ∫ y, ∑ b ∈ S, (box n r).indicator (fun _ => F b) (y - b) ∂μ := by
        congr 1
        funext y
        exact key y
    _ = ∑ b ∈ S, ∫ y, (box n r).indicator (fun _ => F b) (y - b) ∂μ := integral_finsetSum S hint
    _ = ∑ b ∈ S, (μ.real (box n r) : ℂ) * F b := by
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [integral_sub_right_eq_self (fun y => (box n r).indicator (fun _ => F b) y) b,
          integral_indicator_const _ hmeas, Complex.real_smul]
    _ = _ := by rw [Finset.mul_sum]

end GlobalTheory.SplitWeil.FourierPi
