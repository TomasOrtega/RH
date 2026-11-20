import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleHermitianPairStructureFactsStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

open scoped Pointwise NNReal ENNReal

namespace GlobalTheory.JR.Et
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  [Unram F E] (A : Et F E)

/- English proof (translation)
Use `haveI : LocallyCompactSpace F := Unram.lcF (E := E)`. Use `haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F`. Set `e : A.K ≃ₗ[F] (Fin (Module.finrank F A.K) → F)` to `(Module.finBasis F A.K).equivFun`. Establish `h1 : Continuous e` using `IsModuleTopology.continuous_of_linearMap e.toLinearMap`. Establish `h2 : Continuous e.symm` using `IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap`.

Set `h : A.K ≃ₜ (Fin (Module.finrank F A.K) → F)` to `⟨e.toEquiv, h1, h2⟩`. Conclude with `h.isEmbedding.secondCountableTopology`.
-/
theorem secondCountable_K : SecondCountableTopology A.K := by
  haveI : LocallyCompactSpace F := Unram.lcF (E := E)
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  let e : A.K ≃ₗ[F] (Fin (Module.finrank F A.K) → F) := (Module.finBasis F A.K).equivFun
  have h1 : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have h2 : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  let h : A.K ≃ₜ (Fin (Module.finrank F A.K) → F) := ⟨e.toEquiv, h1, h2⟩
  exact h.isEmbedding.secondCountableTopology

/- English proof (translation)
Unfold `absK`. Rewrite using `[dif_pos x.isUnit]`. Use `congr 2`. Use `ext`. Both sides reduce to the same expression.
-/
theorem absK_unit (x : A.Kˣ) : A.absK (x : A.K) = (distribHaarChar A.K x : ℝ) := by
  unfold absK
  rw [dif_pos x.isUnit]
  congr 2
  ext; rfl

/- English proof (translation)
Distinguish the cases in `hs : IsUnit s`. Distinguish the cases in `ht : IsUnit t`. Establish `e1` using `A.absK_unit (hs.unit * ht.unit)`. Establish `e2` using `A.absK_unit hs.unit`. Establish `e3` using `A.absK_unit ht.unit`.

Simplify using `only [Units.val_mul, IsUnit.unit_spec] at e1 e2 e3`. Rewrite using `[e1, e2, e3, map_mul, NNReal.coe_mul]`. Establish `: ¬ IsUnit (s * t)` using `fun h => ht (IsUnit.mul_iff.1 h).2`. Simplify using `[absK, this, ht]`. Establish `: ¬ IsUnit (s * t)` using `fun h => hs (IsUnit.mul_iff.1 h).1`.

Simplify using `[absK, this, hs]`.
-/
theorem absK_mul (s t : A.K) : A.absK (s * t) = A.absK s * A.absK t := by
  by_cases hs : IsUnit s
  · by_cases ht : IsUnit t
    · have e1 := A.absK_unit (hs.unit * ht.unit)
      have e2 := A.absK_unit hs.unit
      have e3 := A.absK_unit ht.unit
      simp only [Units.val_mul, IsUnit.unit_spec] at e1 e2 e3
      rw [e1, e2, e3, map_mul, NNReal.coe_mul]
    · have : ¬ IsUnit (s * t) := fun h => ht (IsUnit.mul_iff.1 h).2
      simp [absK, this, ht]
  · have : ¬ IsUnit (s * t) := fun h => hs (IsUnit.mul_iff.1 h).1
    simp [absK, this, hs]

/- English proof (translation)
Use `haveI := A.secondCountable_K`. Take `⟨-, -, -, -, -, -, -, -, -, hO, hC, R, hR⟩` from `GlobalTheory.T.etaleHermitianPair_structure_facts F E A`. Set `μ : Measure A.K` to `Measure.addHaar`. Establish `h0 : (0 : A.K) ∈ A.OK` using `by rw [← hR]; exact R.zero_mem`. Establish `hm0 : μ A.OK ≠ 0` using `hO.measure_ne_zero μ ⟨0, h0⟩`.

Establish `hmt : μ A.OK ≠ ⊤` using `hC.measure_lt_top.ne`. Establish `hsub : u • A.OK ⊆ A.OK`. Introduce and unpack `_ ⟨z, hz, rfl⟩`. Rewrite `hz`, `hu`, the goal using `[← hR]`. Conclude with `R.mul_mem hu hz`.

Establish `hle : (distribHaarChar A.K u : ℝ≥0∞) * μ A.OK ≤ 1 * μ A.OK`. Rewrite using `[distribHaarChar_mul μ u A.OK, one_mul]`. Conclude with `measure_mono hsub`. Use `(ENNReal.mul_le_mul_iff_left hm0 hmt).1 hle` as an intermediate fact. Conclude with `this` after adjusting the coercions.
-/
theorem distribHaarChar_le_one_of_mem_OK (u : A.Kˣ) (hu : (u : A.K) ∈ A.OK) : distribHaarChar A.K u ≤ 1 := by
  haveI := A.secondCountable_K
  obtain ⟨-, -, -, -, -, -, -, -, -, hO, hC, R, hR⟩ := GlobalTheory.T.etaleHermitianPair_structure_facts F E A
  let μ : Measure A.K := Measure.addHaar
  have h0 : (0 : A.K) ∈ A.OK := by rw [← hR]; exact R.zero_mem
  have hm0 : μ A.OK ≠ 0 := hO.measure_ne_zero μ ⟨0, h0⟩
  have hmt : μ A.OK ≠ ⊤ := hC.measure_lt_top.ne
  have hsub : u • A.OK ⊆ A.OK := by
    rintro _ ⟨z, hz, rfl⟩
    rw [← hR] at hz hu ⊢
    exact R.mul_mem hu hz
  have hle : (distribHaarChar A.K u : ℝ≥0∞) * μ A.OK ≤ 1 * μ A.OK := by
    rw [distribHaarChar_mul μ u A.OK, one_mul]; exact measure_mono hsub
  have := (ENNReal.mul_le_mul_iff_left hm0 hmt).1 hle
  exact_mod_cast this

/- English proof (translation)
Introduce `F E _ _ _ _ _ A`. Use `⟨A.absK_mul, ?_, ?_⟩` and prove the remaining obligations. Introduce `s s' hs hs' h`. Set `u : A.Kˣ` to `⟨s, s', h, by rw [mul_comm]; exact h⟩`. Establish `h1` using `A.distribHaarChar_le_one_of_mem_OK u hs`.

Establish `h2` using `A.distribHaarChar_le_one_of_mem_OK u⁻¹ hs'`. Establish `hprod : distribHaarChar A.K u * distribHaarChar A.K u⁻¹ = 1`. Rewrite using `[← map_mul, mul_inv_cancel, map_one]`. Establish `: distribHaarChar A.K u = 1`. Use `le_antisymm h1 ?_` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation. Establish `e` using `A.absK_unit u`. Express the relevant statement in the definitionally equal form `A.absK s = 1`. Rewrite using `[show s = (u : A.K) from rfl, e, this, NNReal.coe_one]`. Introduce `μ hμ x a S _ haveI := A.secondCountable_K`.

Establish `hset : {a' : A.K | (x : A.K) * a' - a ∈ S} = x⁻¹ • ((fun z => z + -a) ⁻¹' S)`. Use extensionality with `a'`. Rewrite using `[Set.mem_smul_set_iff_inv_smul_mem, inv_inv]`. Simplify using `[Units.smul_def, sub_eq_add_neg]`. Rewrite using `[hset, ← distribHaarChar_mul μ x⁻¹, measure_preimage_add_right, A.absK_unit, map_inv, ← NNReal.coe_inv, ENNReal.ofReal_coe_nnreal]`.
-/
theorem absK_facts : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), ((∀ s t : A.K, A.absK (s * t) = A.absK s * A.absK t) ∧ (∀ s s' : A.K, s ∈ A.OK → s' ∈ A.OK → s * s' = 1 → A.absK s = 1) ∧ (∀ (μ : Measure A.K), μ.IsAddHaarMeasure → ∀ (x : A.Kˣ) (a : A.K) (S : Set A.K), MeasurableSet S → μ {a' : A.K | (x : A.K) * a' - a ∈ S} = ENNReal.ofReal (A.absK (x : A.K))⁻¹ * μ S)) := by
  intro F E _ _ _ _ _ A
  refine ⟨A.absK_mul, ?_, ?_⟩
  · intro s s' hs hs' h
    let u : A.Kˣ := ⟨s, s', h, by rw [mul_comm]; exact h⟩
    have h1 := A.distribHaarChar_le_one_of_mem_OK u hs
    have h2 := A.distribHaarChar_le_one_of_mem_OK u⁻¹ hs'
    have hprod : distribHaarChar A.K u * distribHaarChar A.K u⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel, map_one]
    have : distribHaarChar A.K u = 1 := by
      refine le_antisymm h1 ?_
      calc (1 : ℝ≥0) = distribHaarChar A.K u * distribHaarChar A.K u⁻¹ := hprod.symm
        _ ≤ distribHaarChar A.K u * 1 := mul_le_mul_of_nonneg_left h2 zero_le'
        _ = distribHaarChar A.K u := mul_one _
    have e := A.absK_unit u
    change A.absK s = 1
    rw [show s = (u : A.K) from rfl, e, this, NNReal.coe_one]
  · intro μ hμ x a S _
    haveI := A.secondCountable_K
    have hset : {a' : A.K | (x : A.K) * a' - a ∈ S} = x⁻¹ • ((fun z => z + -a) ⁻¹' S) := by
      ext a'
      rw [Set.mem_smul_set_iff_inv_smul_mem, inv_inv]
      simp [Units.smul_def, sub_eq_add_neg]
    rw [hset, ← distribHaarChar_mul μ x⁻¹, measure_preimage_add_right, A.absK_unit, map_inv,
      ← NNReal.coe_inv, ENNReal.ofReal_coe_nnreal]

end GlobalTheory.JR.Et
