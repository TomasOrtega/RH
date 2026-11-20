import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.UPartBot
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAdmOnOfFiniteDimensional

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.OpTrace GlobalTheory.LeviFactor
open GlobalTheory.AutomorphicL2Unitary (IsTopIrreducible IsIrredSubrep)
open scoped InnerProductSpace
open scoped Pointwise

namespace GlobalTheory.CompactRight

/- English proof (translation)
Use `set c := Measure.haarScalarFactor (Measure.map (· * k) μ) μ with hc`. Establish `hmapEq : Measure.map (· * k) μ = c • μ` using `Measure.isMulLeftInvariant_eq_smul _ μ`. Take `⟨V, hVc, hV1⟩` from `exists_compact_mem_nhds (1 : G)`. Use `set S : Set G := V * (K : Set G) with hS`. Establish `hScpt : IsCompact S` using `hVc.mul hK`.

Establish `hVsubS : V ⊆ S`. Introduce `v hv`. Conclude with `Set.mem_mul.2 ⟨v, hv, 1, K.one_mem, mul_one v⟩`. Establish `hSpre : (· * k) ⁻¹' S = S`. Use extensionality with `x`.

Simplify using `only [Set.mem_preimage, hS, Set.mem_mul, SetLike.mem_coe]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨v, hv, a, ha, hva⟩`. Use `⟨v, hv, a * k⁻¹, K.mul_mem ha (K.inv_mem hk), ?_⟩` and prove the remaining obligations. Rewrite using `[← mul_assoc, hva, mul_inv_cancel_right]`.

Introduce and unpack `⟨v, hv, a, ha, hva⟩`. Conclude with `⟨v, hv, a * k, K.mul_mem ha hk, by rw [← mul_assoc, hva]⟩`. Establish `hSpos : μ S ≠ 0` using `(lt_of_lt_of_le (Measure.measure_pos_of_mem_nhds (μ := μ) hV1) (measure_mono hVsubS)).ne'`. Establish `hSfin : μ S ≠ ⊤` using `hScpt.measure_lt_top.ne`. Establish `hmapS : Measure.map (· * k) μ S = μ S`.

Rewrite using `[show (· * k) = (MeasurableEquiv.mulRight k : G → G) from rfl, MeasurableEquiv.map_apply]`. Conclude with `congrArg μ hSpre`. Establish `hcOne : c = 1`. Establish `hcEq : (c : ENNReal) * μ S = 1 * μ S`. Establish `hcS` using `hmapS`.

Rewrite `hcS` using `[hmapEq, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]`. Rewrite using `[one_mul]`. Conclude with `hcS`. Conclude with `(ENNReal.mul_left_inj hSpos hSfin).1 hcEq` after adjusting the coercions. Rewrite using `[hmapEq, hcOne, one_smul]`.
-/
theorem map_mul_right_eq_of_mem_compact {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (K : Subgroup G)
    (hK : IsCompact (K : Set G)) (k : G) (hk : k ∈ K) : Measure.map (· * k) μ = μ := by
  set c := Measure.haarScalarFactor (Measure.map (· * k) μ) μ with hc
  have hmapEq : Measure.map (· * k) μ = c • μ := Measure.isMulLeftInvariant_eq_smul _ μ
  obtain ⟨V, hVc, hV1⟩ := exists_compact_mem_nhds (1 : G)
  set S : Set G := V * (K : Set G) with hS
  have hScpt : IsCompact S := hVc.mul hK
  have hVsubS : V ⊆ S := by
    intro v hv
    exact Set.mem_mul.2 ⟨v, hv, 1, K.one_mem, mul_one v⟩
  have hSpre : (· * k) ⁻¹' S = S := by
    ext x
    simp only [Set.mem_preimage, hS, Set.mem_mul, SetLike.mem_coe]
    constructor
    · rintro ⟨v, hv, a, ha, hva⟩
      refine ⟨v, hv, a * k⁻¹, K.mul_mem ha (K.inv_mem hk), ?_⟩
      rw [← mul_assoc, hva, mul_inv_cancel_right]
    · rintro ⟨v, hv, a, ha, hva⟩
      exact ⟨v, hv, a * k, K.mul_mem ha hk, by rw [← mul_assoc, hva]⟩
  have hSpos : μ S ≠ 0 := (lt_of_lt_of_le (Measure.measure_pos_of_mem_nhds (μ := μ) hV1) (measure_mono hVsubS)).ne'
  have hSfin : μ S ≠ ⊤ := hScpt.measure_lt_top.ne
  have hmapS : Measure.map (· * k) μ S = μ S := by
    rw [show (· * k) = (MeasurableEquiv.mulRight k : G → G) from rfl, MeasurableEquiv.map_apply]
    exact congrArg μ hSpre
  have hcOne : c = 1 := by
    have hcEq : (c : ENNReal) * μ S = 1 * μ S := by
      have hcS := hmapS
      rw [hmapEq, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at hcS
      rw [one_mul]
      exact hcS
    exact_mod_cast (ENNReal.mul_left_inj hSpos hSfin).1 hcEq
  rw [hmapEq, hcOne, one_smul]

end GlobalTheory.CompactRight
