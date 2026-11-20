import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnimodularity.KCountable
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularIndex.PairwiseDisjointCosets

noncomputable section

namespace PI.WAU

open Formalism.MainNotions.S MeasureTheory Matrix Pointwise

/- English proof (translation)
Use extensionality with `x`. Use `⟨fun h => h.1, fun h => ⟨h, fun y hy => ⟨(I.fmat x - 1) *ᵥ y, ?_, by simp⟩⟩⟩` and prove the remaining obligations. Establish `h' : ∀ y, y ∈ I.Lf ↔ I.fmat x *ᵥ y ∈ I.Lf` using `h`. Rewrite using `[Matrix.sub_mulVec, Matrix.one_mulVec]`. Conclude with `I.Lf.sub_mem ((h' y).1 hy) hy`.
-/
theorem kg_one_eq (I : AutInst) : I.Kg 1 = I.Kset := by
  ext x
  refine ⟨fun h => h.1, fun h => ⟨h, fun y hy => ⟨(I.fmat x - 1) *ᵥ y, ?_, by simp⟩⟩⟩
  have h' : ∀ y, y ∈ I.Lf ↔ I.fmat x *ᵥ y ∈ I.Lf := h
  rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  exact I.Lf.sub_mem ((h' y).1 hy) hy

/- English proof (translation)
Rewrite using `[← kg_one_eq]`. Conclude with `I.topf_open 1 le_rfl`.
-/
theorem kset_open (I : AutInst) : IsOpen I.Kset := by
  rw [← kg_one_eq]
  exact I.topf_open 1 le_rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem ksub_coe (I : AutInst) : ((Ksub I : Subgroup I.Gf) : Set I.Gf) = I.Kset := rfl

/- English proof (translation)
Use `haveI := hμ`. Take `⟨s, hs, hcov⟩` from `hQ`. Use `Measure.sigmaFinite_of_countable (S := (fun y => (fun x => y * x) '' I.Kset) '' s) (hs.image _) ?_ ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨y, -, rfl⟩ show μ ((fun x => y * x) '' I.Kset) < ⊤`. Rewrite using `[Set.image_mul_left, measure_preimage_mul]`.

Conclude with `hKc.measure_lt_top`. Rewrite using `[Set.sUnion_image, Set.eq_univ_iff_forall]`. Introduce `x`. Take `⟨y, hy, hyx⟩` from `hcov x`. Conclude with `Set.mem_biUnion hy ⟨y⁻¹ * x, hyx, mul_inv_cancel_left y x⟩`.
-/
theorem sigmaFinite_of_K (I : AutInst) (μ : Measure I.Gf) (hμ : μ.IsHaarMeasure)
    (hKc : IsCompact I.Kset) (hQ : ∃ s : Set I.Gf, s.Countable ∧ ∀ x : I.Gf, ∃ y ∈ s, y⁻¹ * x ∈ I.Kset) :
    SigmaFinite μ := by
  haveI := hμ
  obtain ⟨s, hs, hcov⟩ := hQ
  refine Measure.sigmaFinite_of_countable (S := (fun y => (fun x => y * x) '' I.Kset) '' s)
    (hs.image _) ?_ ?_
  · rintro _ ⟨y, -, rfl⟩
    show μ ((fun x => y * x) '' I.Kset) < ⊤
    rw [Set.image_mul_left, measure_preimage_mul]
    exact hKc.measure_lt_top
  · rw [Set.sUnion_image, Set.eq_univ_iff_forall]
    intro x
    obtain ⟨y, hy, hyx⟩ := hcov x
    exact Set.mem_biUnion hy ⟨y⁻¹ * x, hyx, mul_inv_cancel_left y x⟩

/- English proof (translation)
Introduce `I μ hμ`. Use `haveI := sigmaFinite_of_K I μ hμ (hC I) (hQ I)`. Use `choose U hU using fun n : ℕ => hA I (n + 1) (by omega)`. Use `PI.UnimodIdxWork.unimodIdx_main I.Gf μ hμ U (fun n => ?_) (fun V hV => ?_) (Ksub I) ?_ ?_ (hI I)` and prove the remaining obligations. Rewrite using `[hU n]`.

Conclude with `I.topf_open (n + 1) (by omega)`. Take `⟨g, hg1, hgV⟩` from `I.topf_basis V hV`. Use `⟨g - 1, ?_⟩` and prove the remaining obligations. Rewrite using `[hU (g - 1), show g - 1 + 1 = g by omega]`. Conclude with `hgV`.

Rewrite using `[ksub_coe]`. Conclude with `kset_open I`. Rewrite using `[ksub_coe]`. Conclude with `hC I`.
-/
theorem adUnimod_of (hA : KgSubgroup) (hC : KCompact) (hQ : KCountable) (hI : IndexEq) :
    PI.AdUnimod := by
  intro I μ hμ
  haveI := sigmaFinite_of_K I μ hμ (hC I) (hQ I)
  choose U hU using fun n : ℕ => hA I (n + 1) (by omega)
  refine PI.UnimodIdxWork.unimodIdx_main I.Gf μ hμ U (fun n => ?_) (fun V hV => ?_) (Ksub I) ?_ ?_ (hI I)
  · rw [hU n]
    exact I.topf_open (n + 1) (by omega)
  · obtain ⟨g, hg1, hgV⟩ := I.topf_basis V hV
    refine ⟨g - 1, ?_⟩
    rw [hU (g - 1), show g - 1 + 1 = g by omega]
    exact hgV
  · rw [ksub_coe]
    exact kset_open I
  · rw [ksub_coe]
    exact hC I

end PI.WAU
