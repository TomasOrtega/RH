import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.LiftFactorization

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace UpperTheory.Gal.InertialTypesAlt.L

/- English proof (translation)
Use `haveI : Fintype (C' ⧸ H'.subgroupOf C') := Fintype.ofFinite _`. Set `r : (C' ⧸ H'.subgroupOf C') → T` to `fun q => ((Quotient.out q : C') : T)`. Establish `hr : ∀ q, r q ∈ C'` using `fun q => (Quotient.out q).2`. Establish `hcov : (C' : Set T) = ⋃ q, (fun y => (r q)⁻¹ * y) ⁻¹' (H' : Set T)`. Use extensionality with `x`.

Simplify using `only [Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe]`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Use `⟨QuotientGroup.mk ⟨x, hx⟩, ?_⟩` and prove the remaining obligations. Establish `h1` using `QuotientGroup.eq.mp (QuotientGroup.out_eq' (QuotientGroup.mk ⟨x, hx⟩ : C' ⧸ H'.subgroupOf C'))`.

Rewrite `h1` using `[Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]`. Conclude with `h1`. Introduce and unpack `⟨q, hq⟩`. Establish `h2` using `C'.mul_mem (hr q) (hHC hq)`. Rewrite `h2` using `[mul_inv_cancel_left]`. Then use the resulting hypothesis.

Establish `hdisj : Pairwise (Function.onFun Disjoint fun q => (fun y => (r q)⁻¹ * y) ⁻¹' (H' : Set T))`. Introduce `q q' hqq'`. Rewrite using `[Function.onFun, Set.disjoint_left]`. Introduce `x hx hx'`. Simplify using `only [Set.mem_preimage, SetLike.mem_coe] at hx hx'`.

Apply `hqq'` to reduce the goal to its premises. Rewrite using `[← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q', QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]`. Express the relevant statement in the definitionally equal form `(r q)⁻¹ * r q' ∈ H'`. Establish `e : (r q)⁻¹ * r q' = ((r q)⁻¹ * x) * ((r q')⁻¹ * x)⁻¹` using `by group`. Rewrite using `[e]`.

Conclude with `H'.mul_mem hx (H'.inv_mem hx')`. Rewrite using `[hcov, measure_iUnion hdisj (fun q => (hH'.preimage (continuous_const_mul _)).measurableSet), tsum_fintype]`. Simplify using `only [measure_preimage_mul]`. Rewrite using `[Finset.sum_const, Finset.card_univ, nsmul_eq_mul]`. Use `congr 1`.

Simplify using `[Subgroup.relIndex, Subgroup.index, Nat.card_eq_fintype_card]`.
-/
private lemma haar_measure_open_subgroup_index {T : Type} [Group T] [TopologicalSpace T] [IsTopologicalGroup T]
    [MeasurableSpace T] [BorelSpace T] (ν : Measure T) [ν.IsMulLeftInvariant]
    (C' H' : Subgroup T) (hH' : IsOpen (H' : Set T)) (hHC : H' ≤ C')
    [Finite (C' ⧸ H'.subgroupOf C')] :
    ν (C' : Set T) = (H'.relIndex C' : ℝ≥0∞) * ν (H' : Set T) := by
  classical
  haveI : Fintype (C' ⧸ H'.subgroupOf C') := Fintype.ofFinite _
  let r : (C' ⧸ H'.subgroupOf C') → T := fun q => ((Quotient.out q : C') : T)
  have hr : ∀ q, r q ∈ C' := fun q => (Quotient.out q).2
  have hcov : (C' : Set T) = ⋃ q, (fun y => (r q)⁻¹ * y) ⁻¹' (H' : Set T) := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe]
    constructor
    · intro hx
      refine ⟨QuotientGroup.mk ⟨x, hx⟩, ?_⟩
      have h1 := QuotientGroup.eq.mp (QuotientGroup.out_eq' (QuotientGroup.mk ⟨x, hx⟩ : C' ⧸ H'.subgroupOf C'))
      rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] at h1
      exact h1
    · rintro ⟨q, hq⟩
      have h2 := C'.mul_mem (hr q) (hHC hq)
      rwa [mul_inv_cancel_left] at h2
  have hdisj : Pairwise (Function.onFun Disjoint fun q => (fun y => (r q)⁻¹ * y) ⁻¹' (H' : Set T)) := by
    intro q q' hqq'
    rw [Function.onFun, Set.disjoint_left]
    intro x hx hx'
    simp only [Set.mem_preimage, SetLike.mem_coe] at hx hx'
    apply hqq'
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q', QuotientGroup.eq, Subgroup.mem_subgroupOf,
      Subgroup.coe_mul, Subgroup.coe_inv]
    change (r q)⁻¹ * r q' ∈ H'
    have e : (r q)⁻¹ * r q' = ((r q)⁻¹ * x) * ((r q')⁻¹ * x)⁻¹ := by group
    rw [e]
    exact H'.mul_mem hx (H'.inv_mem hx')
  rw [hcov, measure_iUnion hdisj (fun q => (hH'.preimage (continuous_const_mul _)).measurableSet), tsum_fintype]
  simp only [measure_preimage_mul]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  congr 1
  simp [Subgroup.relIndex, Subgroup.index, Nat.card_eq_fintype_card]

/- English proof (translation)
Introduce `G _ _ _ _ _ _ T C H hT ν hν hCT hC hHC hH`. Use `haveI := hν`. Establish `eH : {t : T | (t : G) ∈ H} = ((H.subgroupOf T : Subgroup T) : Set T)` using `rfl`. Establish `eC : {t : T | (t : G) ∈ C} = ((C.subgroupOf T : Subgroup T) : Set T)` using `rfl`. Establish `hHo : IsOpen ((H.subgroupOf T : Subgroup T) : Set T)`.

Rewrite using `[← eH]`. Conclude with `hH`. Establish `hCc : IsCompact ((C.subgroupOf T : Subgroup T) : Set T)`. Rewrite using `[← eC]`. Conclude with `hT.isClosedEmbedding_subtypeVal.isCompact_preimage hC`.

Establish `hle : H.subgroupOf T ≤ C.subgroupOf T` using `fun x hx => hHC hx`. Use `haveI : CompactSpace (C.subgroupOf T) := isCompact_iff_compactSpace.mp hCc`. Use `haveI : Finite ((C.subgroupOf T) ⧸ (H.subgroupOf T).subgroupOf (C.subgroupOf T)) := Subgroup.quotient_finite_of_isOpen _ (by`. Rewrite using `[Subgroup.coe_subgroupOf]`. Conclude with `hHo.preimage continuous_subtype_val)`.

Establish `key` using `haar_measure_open_subgroup_index ν (C.subgroupOf T) (H.subgroupOf T) hHo hle`. Rewrite `key` using `[Subgroup.relIndex_subgroupOf hCT]`. Establish `hpos : ν ((H.subgroupOf T : Subgroup T) : Set T) ≠ 0` using `(hHo.measure_pos ν ⟨1, (H.subgroupOf T).one_mem⟩).ne'`. Establish `hfinH : ν ((H.subgroupOf T : Subgroup T) : Set T) ≠ ∞` using `((measure_mono (fun x hx => hle hx)).trans_lt hCc.measure_lt_top).ne`. Rewrite using `[eH, eC]`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[measureReal_def, ENNReal.toReal_ne_zero]`. Conclude with `⟨hpos, hfinH⟩`. Simplify using `only [measureReal_def, key, ENNReal.toReal_mul, ENNReal.toReal_natCast]`.
-/
theorem volIdx :
    UpperTheory.Gal.InertialTypesAlt.L.VolIdx := by
  intro G _ _ _ _ _ _ T C H hT ν hν hCT hC hHC hH
  haveI := hν
  have eH : {t : T | (t : G) ∈ H} = ((H.subgroupOf T : Subgroup T) : Set T) := rfl
  have eC : {t : T | (t : G) ∈ C} = ((C.subgroupOf T : Subgroup T) : Set T) := rfl
  have hHo : IsOpen ((H.subgroupOf T : Subgroup T) : Set T) := by
    rw [← eH]
    exact hH
  have hCc : IsCompact ((C.subgroupOf T : Subgroup T) : Set T) := by
    rw [← eC]
    exact hT.isClosedEmbedding_subtypeVal.isCompact_preimage hC
  have hle : H.subgroupOf T ≤ C.subgroupOf T := fun x hx => hHC hx
  haveI : CompactSpace (C.subgroupOf T) := isCompact_iff_compactSpace.mp hCc
  haveI : Finite ((C.subgroupOf T) ⧸ (H.subgroupOf T).subgroupOf (C.subgroupOf T)) :=
    Subgroup.quotient_finite_of_isOpen _ (by
      rw [Subgroup.coe_subgroupOf]
      exact hHo.preimage continuous_subtype_val)
  have key := haar_measure_open_subgroup_index ν (C.subgroupOf T) (H.subgroupOf T) hHo hle
  rw [Subgroup.relIndex_subgroupOf hCT] at key
  have hpos : ν ((H.subgroupOf T : Subgroup T) : Set T) ≠ 0 :=
    (hHo.measure_pos ν ⟨1, (H.subgroupOf T).one_mem⟩).ne'
  have hfinH : ν ((H.subgroupOf T : Subgroup T) : Set T) ≠ ∞ :=
    ((measure_mono (fun x hx => hle hx)).trans_lt hCc.measure_lt_top).ne
  rw [eH, eC]
  refine ⟨?_, ?_⟩
  · rw [measureReal_def, ENNReal.toReal_ne_zero]
    exact ⟨hpos, hfinH⟩
  · simp only [measureReal_def, key, ENNReal.toReal_mul, ENNReal.toReal_natCast]

end UpperTheory.Gal.InertialTypesAlt.L
