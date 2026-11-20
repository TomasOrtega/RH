import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ModelDdcForms

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms MeasureTheory
open scoped ContDiff Topology

namespace GlobalTheory

/- English proof (translation)
Take `⟨j, hj⟩` from `A.cover (ψ.symm z)`. Establish `h2 : ContDiffAt ℝ ∞ (A.chart j ∘ ψ.symm) z` using `(((hψ j).2 z ⟨hz, hj⟩).contDiffAt (n := ∞)).restrict_scalars ℝ`. Establish `hopen : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (P.U (ψ.symm z) ∩ O))` using `(A.chart j).isOpen_inter_preimage_symm ((P.isOpen_U _).inter hO)`. Establish `hmem : (A.chart j ∘ ψ.symm) z ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' (P.U (ψ.symm z) ∩ O)`. Use `⟨(A.chart j).map_source hj, ?_⟩` and prove the remaining obligations.

Simplify using `only [Function.comp_apply, Set.mem_preimage, (A.chart j).left_inv hj]`. Conclude with `⟨P.mem_U _, hzO⟩`. Establish `h1 : ContDiffAt ℝ ∞ (P.φ (ψ.symm z) ∘ (A.chart j).symm) ((A.chart j ∘ ψ.symm) z)` using `(hP.1 (ψ.symm z) j).contDiffAt (hopen.mem_nhds hmem)`. Use `(h1.comp z h2).congr_of_eventuallyEq ?_` and prove the remaining obligations. Establish `hev : ∀ᶠ y in 𝓝 z, ψ.symm y ∈ (A.chart j).source` using `(ψ.continuousAt_symm hz).eventually ((A.chart j).open_source.mem_nhds hj)`.

Use `filter_upwards [hev] with y hy`. Simplify using `only [Function.comp_apply, (A.chart j).left_inv hy]`.
-/
theorem isPotentialOn_contDiffAt_top_compatChart {e : ℕ} {X : Type} [TopologicalSpace X]
    (A : FinHolAtlas e X) (P : LocPot X) (O : Set X)
    (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (z : Fin e → ℂ) (hO : IsOpen O)
    (hP : IsPotentialOn A O P) (hψ : IsCompatChart A ψ)
    (hz : z ∈ ψ.target) (hzO : ψ.symm z ∈ O) :
    ContDiffAt ℝ ∞ (P.φ (ψ.symm z) ∘ ψ.symm) z := by
  obtain ⟨j, hj⟩ := A.cover (ψ.symm z)
  have h2 : ContDiffAt ℝ ∞ (A.chart j ∘ ψ.symm) z :=
    (((hψ j).2 z ⟨hz, hj⟩).contDiffAt (n := ∞)).restrict_scalars ℝ
  have hopen : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (P.U (ψ.symm z) ∩ O)) :=
    (A.chart j).isOpen_inter_preimage_symm ((P.isOpen_U _).inter hO)
  have hmem : (A.chart j ∘ ψ.symm) z ∈
      (A.chart j).target ∩ (A.chart j).symm ⁻¹' (P.U (ψ.symm z) ∩ O) := by
    refine ⟨(A.chart j).map_source hj, ?_⟩
    simp only [Function.comp_apply, Set.mem_preimage, (A.chart j).left_inv hj]
    exact ⟨P.mem_U _, hzO⟩
  have h1 : ContDiffAt ℝ ∞ (P.φ (ψ.symm z) ∘ (A.chart j).symm) ((A.chart j ∘ ψ.symm) z) :=
    (hP.1 (ψ.symm z) j).contDiffAt (hopen.mem_nhds hmem)
  refine (h1.comp z h2).congr_of_eventuallyEq ?_
  have hev : ∀ᶠ y in 𝓝 z, ψ.symm y ∈ (A.chart j).source :=
    (ψ.continuousAt_symm hz).eventually ((A.chart j).open_source.mem_nhds hj)
  filter_upwards [hev] with y hy
  simp only [Function.comp_apply, (A.chart j).left_inv hy]

/- English proof (translation)
The claim follows from `(isPotentialOn_contDiffAt_top_compatChart A P O ψ z hO hP hψ hz hzO).of_le (show (2 : WithTop ℕ∞) ≤ ∞ by norm_cast)`.
-/
theorem isPotentialOn_contDiffAt_two_compatChart {e : ℕ} {X : Type} [TopologicalSpace X]
    (A : FinHolAtlas e X) (P : LocPot X) (O : Set X)
    (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (z : Fin e → ℂ) (hO : IsOpen O)
    (hP : IsPotentialOn A O P) (hψ : IsCompatChart A ψ)
    (hz : z ∈ ψ.target) (hzO : ψ.symm z ∈ O) :
    ContDiffAt ℝ 2 (P.φ (ψ.symm z) ∘ ψ.symm) z :=
  (isPotentialOn_contDiffAt_top_compatChart A P O ψ z hO hP hψ hz hzO).of_le
    (show (2 : WithTop ℕ∞) ≤ ∞ by norm_cast)

end GlobalTheory
