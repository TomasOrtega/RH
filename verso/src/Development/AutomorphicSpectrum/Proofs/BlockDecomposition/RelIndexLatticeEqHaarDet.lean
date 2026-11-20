import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantAddChar
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RelIndexMulMeasure

open MeasureTheory Matrix
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.IndexDet

/- English proof (translation)
Use `haveI : CompactSpace L := isCompact_iff_compactSpace.mp hL`. Establish `ho : IsOpen ((H.addSubgroupOf L : AddSubgroup L) : Set L)` using `hH.preimage continuous_subtype_val`. Use `haveI : Finite (L ⧸ H.addSubgroupOf L) := AddSubgroup.quotient_finite_of_isOpen _ ho`. Use `haveI : (H.addSubgroupOf L).FiniteIndex := AddSubgroup.finiteIndex_of_finite_quotient`. Conclude with `GlobalTheory.BaseModule.addRelIndex_mul_measure H L hHL hH.measurableSet μ`.
-/
theorem relIndex_mul_measure_of_isCompact {G : Type*} [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
    [μ.IsAddLeftInvariant] {H L : AddSubgroup G} (hL : IsCompact (L : Set G))
    (hH : IsOpen (H : Set G)) (hHL : H ≤ L) :
    (H.relIndex L : ℝ≥0∞) * μ H = μ L := by
  haveI : CompactSpace L := isCompact_iff_compactSpace.mp hL
  have ho : IsOpen ((H.addSubgroupOf L : AddSubgroup L) : Set L) := hH.preimage continuous_subtype_val
  haveI : Finite (L ⧸ H.addSubgroupOf L) := AddSubgroup.quotient_finite_of_isOpen _ ho
  haveI : (H.addSubgroupOf L).FiniteIndex := AddSubgroup.finiteIndex_of_finite_quotient
  exact GlobalTheory.BaseModule.addRelIndex_mul_measure H L hHL hH.measurableSet μ

/- English proof (translation)
Use `borelize k`. Use `haveI := GlobalTheory.SplitWeil.secondCountable k`. Use `haveI := GlobalTheory.SplitWeil.t2Space k`. Use `set B := A.comap (Matrix.mulVecLin (g : Matrix (Fin n) (Fin n) k)).toAddMonoidHom with hB`. Set `μ : Measure (Fin n → k)` to `Measure.pi fun _ : Fin n => (Measure.addHaar : Measure k)`.

Establish `hBset : (B : Set (Fin n → k)) = (fun x => (g⁻¹).val *ᵥ x) '' (A : Set (Fin n → k))`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Use `⟨g.val *ᵥ x, hx, ?_⟩` and prove the remaining obligations.

Simplify using `only [mulVec_mulVec, Units.inv_mul, one_mulVec]`. Introduce and unpack `⟨y, hy, rfl⟩`. Express the relevant statement in the definitionally equal form `g.val *ᵥ ((g⁻¹).val *ᵥ y) ∈ A`. Simplify `hy` using `only [mulVec_mulVec, Units.mul_inv, one_mulVec, SetLike.mem_coe]`. Establish `hBc : IsCompact (B : Set (Fin n → k))`.

Rewrite using `[hBset]`. Conclude with `hA.image (by fun_prop)`. Establish `hAm : MeasurableSet (A : Set (Fin n → k))` using `hA.measurableSet`. Establish `hm : Measurable (g.val.mulVec)` using `(continuous_const.matrix_mulVec continuous_id).measurable`. Establish `hscale : μ A = (distribHaarChar k (Matrix.GeneralLinearGroup.det g) : ℝ≥0∞) * μ B`.

Establish `h` using `GlobalTheory.WeilM.smul_map_mulVec_pi (Measure.addHaar : Measure k) g.val (Matrix.GeneralLinearGroup.det g) rfl`. Establish `h2` using `congrArg (fun m : Measure (Fin n → k) => m (A : Set (Fin n → k))) h`. Simplify using `only [Measure.smul_apply, smul_eq_mul, Measure.map_apply hm hAm] at h2`. Conclude with `h2.symm`. Establish `i1` using `relIndex_mul_measure_of_isCompact μ hA hA₀ h₀`.

Establish `i2` using `relIndex_mul_measure_of_isCompact μ hBc hA₀ h₁`. Establish `hpos : μ A₀ ≠ 0` using `(hA₀.measure_pos μ ⟨0, A₀.zero_mem⟩).ne'`. Establish `htop : μ A₀ ≠ ∞` using `((measure_mono h₀).trans_lt hA.measure_lt_top).ne`. Establish `key : ((A₀.relIndex A : ℕ) : ℝ≥0∞) = (distribHaarChar k (Matrix.GeneralLinearGroup.det g) : ℝ≥0∞) * ((A₀.relIndex B : ℕ) : ℝ≥0∞)`. Use `(ENNReal.mul_left_inj hpos htop).mp ?_` and prove the remaining obligations.

Rewrite using `[i1, hscale, ← i2, mul_assoc]`. Use `congrArg ENNReal.toReal key` as an intermediate fact. Simplify using `using this`.
-/
theorem relIndex_eq_distribHaarChar_det_mul (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (g : GL (Fin n) k)
    (A₀ A : AddSubgroup (Fin n → k)) (hA : IsCompact (A : Set (Fin n → k)))
    (hA₀ : IsOpen (A₀ : Set (Fin n → k))) (h₀ : A₀ ≤ A)
    (h₁ : A₀ ≤ A.comap (Matrix.mulVecLin (g : Matrix (Fin n) (Fin n) k)).toAddMonoidHom) :
    ((A₀.relIndex A : ℕ) : ℝ) = (distribHaarChar k (Matrix.GeneralLinearGroup.det g) : ℝ) *
      ((A₀.relIndex (A.comap (Matrix.mulVecLin (g : Matrix (Fin n) (Fin n) k)).toAddMonoidHom) : ℕ) : ℝ) := by
  borelize k
  haveI := GlobalTheory.SplitWeil.secondCountable k
  haveI := GlobalTheory.SplitWeil.t2Space k
  set B := A.comap (Matrix.mulVecLin (g : Matrix (Fin n) (Fin n) k)).toAddMonoidHom with hB
  let μ : Measure (Fin n → k) := Measure.pi fun _ : Fin n => (Measure.addHaar : Measure k)
  have hBset : (B : Set (Fin n → k)) = (fun x => (g⁻¹).val *ᵥ x) '' (A : Set (Fin n → k)) := by
    ext x
    constructor
    · intro hx
      refine ⟨g.val *ᵥ x, hx, ?_⟩
      simp only [mulVec_mulVec, Units.inv_mul, one_mulVec]
    · rintro ⟨y, hy, rfl⟩
      change g.val *ᵥ ((g⁻¹).val *ᵥ y) ∈ A
      simpa only [mulVec_mulVec, Units.mul_inv, one_mulVec, SetLike.mem_coe] using hy
  have hBc : IsCompact (B : Set (Fin n → k)) := by
    rw [hBset]
    exact hA.image (by fun_prop)
  have hAm : MeasurableSet (A : Set (Fin n → k)) := hA.measurableSet
  have hm : Measurable (g.val.mulVec) := (continuous_const.matrix_mulVec continuous_id).measurable
  have hscale : μ A = (distribHaarChar k (Matrix.GeneralLinearGroup.det g) : ℝ≥0∞) * μ B := by
    have h := GlobalTheory.WeilM.smul_map_mulVec_pi (Measure.addHaar : Measure k) g.val
      (Matrix.GeneralLinearGroup.det g) rfl
    have h2 := congrArg (fun m : Measure (Fin n → k) => m (A : Set (Fin n → k))) h
    simp only [Measure.smul_apply, smul_eq_mul, Measure.map_apply hm hAm] at h2
    exact h2.symm
  have i1 := relIndex_mul_measure_of_isCompact μ hA hA₀ h₀
  have i2 := relIndex_mul_measure_of_isCompact μ hBc hA₀ h₁
  have hpos : μ A₀ ≠ 0 := (hA₀.measure_pos μ ⟨0, A₀.zero_mem⟩).ne'
  have htop : μ A₀ ≠ ∞ := ((measure_mono h₀).trans_lt hA.measure_lt_top).ne
  have key : ((A₀.relIndex A : ℕ) : ℝ≥0∞) =
      (distribHaarChar k (Matrix.GeneralLinearGroup.det g) : ℝ≥0∞) * ((A₀.relIndex B : ℕ) : ℝ≥0∞) := by
    refine (ENNReal.mul_left_inj hpos htop).mp ?_
    rw [i1, hscale, ← i2, mul_assoc]
  have := congrArg ENNReal.toReal key
  simpa using this

end GlobalTheory.CompanionTheory.IndexDet
