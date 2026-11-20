import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsGaugeAll
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactHaarRightInvariantInst
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsRiemannianHaarUnitaryJSubgroupOfAlgebraStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsNilpotentAlgebraIsotropicFlagUnipotentRadiStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAlgebraIsotropicFlagSelfAdjointLeviStatement

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.FlagMeas

/- English proof (translation)
Establish `hg : (uMat g)ᴴ * Formalism.REAL.Jm ε * uMat g = Formalism.REAL.Jm ε` using `g.2`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h1 : (uMat g)ᴴ * uMat g = 1` using `h`. Establish `h2 : uMat g * (uMat g)ᴴ = 1` using `mul_eq_one_comm.mp h1`.

Use `⟨Matrix.mem_unitaryGroup_iff'.mpr h1, ?_⟩` and prove the remaining obligations. Use `show uMat g * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * uMat g`. Combine the equalities or inequalities in the displayed calculation. Introduce `h`. Conclude with `Matrix.mem_unitaryGroup_iff'.mp h.1`.
-/
theorem gaugeSubEx_mem_maxK_iff {n : ℕ} (ε : Fin n → Bool) (g : Formalism.REAL.UJ ε) :
    g ∈ maxK ε ↔ g ∈ Formalism.REAL.KG ε := by
  have hg : (uMat g)ᴴ * Formalism.REAL.Jm ε * uMat g = Formalism.REAL.Jm ε := g.2
  constructor
  · intro h
    have h1 : (uMat g)ᴴ * uMat g = 1 := h
    have h2 : uMat g * (uMat g)ᴴ = 1 := mul_eq_one_comm.mp h1
    refine ⟨Matrix.mem_unitaryGroup_iff'.mpr h1, ?_⟩
    show uMat g * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * uMat g
    calc uMat g * Formalism.REAL.Jm ε = uMat g * ((uMat g)ᴴ * Formalism.REAL.Jm ε * uMat g) := by rw [hg]
      _ = (uMat g * (uMat g)ᴴ) * Formalism.REAL.Jm ε * uMat g := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h2, Matrix.one_mul]
  · intro h
    exact Matrix.mem_unitaryGroup_iff'.mp h.1

/- English proof (translation)
Establish `hK : maxK ε = (Formalism.REAL.KG ε : Set (Formalism.REAL.UJ ε))` using `Set.ext fun g => gaugeSubEx_mem_maxK_iff ε g`. Establish `hc : IsCompact (Formalism.REAL.KG ε : Set (Formalism.REAL.UJ ε))` using `isCompact_iff_compactSpace.mpr (Formalism.REAL.instCompactKG n ε)`. Establish `hm : MeasurableSet (maxK ε)` using `hK ▸ hc.isClosed.measurableSet`. Establish `hv : Measurable (Subtype.val : Formalism.REAL.KG ε → Formalism.REAL.UJ ε)` using `measurable_subtype_coe`. Use `Formalism.REAL.compact_haar_probability n ε` as an intermediate fact.

Use `⟨(Formalism.REAL.muK ε).map Subtype.val, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Measure.map_apply hv hm.compl]`. Establish `: (Subtype.val : Formalism.REAL.KG ε → Formalism.REAL.UJ ε) ⁻¹' (maxK ε)ᶜ = ∅`. Use extensionality with `k`. Simplify using `[hK]`.

Rewrite using `[this, measure_empty]`. Rewrite using `[Measure.map_apply hv MeasurableSet.univ, Set.preimage_univ, measure_univ]`. Introduce `k hk`. Establish `hk' : k ∈ Formalism.REAL.KG ε` using `(gaugeSubEx_mem_maxK_iff ε k).mp hk`. Establish `h` using `map_mul_left_eq_self (Formalism.REAL.muK ε) ⟨k, hk'⟩`.

Rewrite using `[Measure.map_map (measurable_const_mul k) hv]`. Use `conv_rhs => rw [← h]`. Rewrite using `[Measure.map_map hv (measurable_const_mul _)]`. Both sides reduce to the same expression.
-/
theorem gaugeSubEx_haarK (n : ℕ) (ε : Fin n → Bool) :
    ∃ μ : Measure (Formalism.REAL.UJ ε), μ (maxK ε)ᶜ = 0 ∧ μ Set.univ = 1 ∧
      ∀ k ∈ maxK ε, μ.map (fun g => k * g) = μ := by
  have hK : maxK ε = (Formalism.REAL.KG ε : Set (Formalism.REAL.UJ ε)) :=
    Set.ext fun g => gaugeSubEx_mem_maxK_iff ε g
  have hc : IsCompact (Formalism.REAL.KG ε : Set (Formalism.REAL.UJ ε)) :=
    isCompact_iff_compactSpace.mpr (Formalism.REAL.instCompactKG n ε)
  have hm : MeasurableSet (maxK ε) := hK ▸ hc.isClosed.measurableSet
  have hv : Measurable (Subtype.val : Formalism.REAL.KG ε → Formalism.REAL.UJ ε) := measurable_subtype_coe
  have := Formalism.REAL.compact_haar_probability n ε
  refine ⟨(Formalism.REAL.muK ε).map Subtype.val, ?_, ?_, ?_⟩
  · rw [Measure.map_apply hv hm.compl]
    have : (Subtype.val : Formalism.REAL.KG ε → Formalism.REAL.UJ ε) ⁻¹' (maxK ε)ᶜ = ∅ := by
      ext k
      simp [hK]
    rw [this, measure_empty]
  · rw [Measure.map_apply hv MeasurableSet.univ, Set.preimage_univ, measure_univ]
  · intro k hk
    have hk' : k ∈ Formalism.REAL.KG ε := (gaugeSubEx_mem_maxK_iff ε k).mp hk
    have h := map_mul_left_eq_self (Formalism.REAL.muK ε) ⟨k, hk'⟩
    rw [Measure.map_map (measurable_const_mul k) hv]
    conv_rhs => rw [← h]
    rw [Measure.map_map hv (measurable_const_mul _)]
    rfl

/- English proof (translation)
Introduce `n ε a j W _ hW`. Use `⟨?_, ?_, gaugeSubEx_haarK n ε⟩` and prove the remaining obligations. Take `⟨A, E, h1, h2, h3, h4⟩` from `GlobalTheory.T.exists_nilpotentAlgebra_isotropicFlagUnipotentRadical n ε a j W hW`. Rewrite using `[h4]`. Conclude with `GlobalTheory.T.exists_riemannianHaar_unitaryJSubgroupOfAlgebra n ε A _ E h1 h2 h3`.

Take `⟨A, E, h1, h2, h3, h4⟩` from `GlobalTheory.T.exists_algebra_isotropicFlagSelfAdjointLevi n ε a j W hW`. Rewrite using `[h4]`. Conclude with `GlobalTheory.T.exists_riemannianHaar_unitaryJSubgroupOfAlgebra n ε A _ E h1 h2 h3`.
-/
theorem gaugeSubEx : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), (∀ i, 1 ≤ j i) → IsIsoFlag ε j W → (∃ μ, SigmaFinite μ ∧ IsGaugeSub (flagN ε W) (dimN n j) μ) ∧ (∃ μ, SigmaFinite μ ∧ IsGaugeSub (flagM ε W) ((n - 2 * ∑ i, j i) ^ 2 + 2 * ∑ i, j i ^ 2) μ) ∧ ∃ μ : Measure (Formalism.REAL.UJ ε), μ (maxK ε)ᶜ = 0 ∧ μ Set.univ = 1 ∧ ∀ k ∈ maxK ε, μ.map (fun g => k * g) = μ := by
  intro n ε a j W _ hW
  refine ⟨?_, ?_, gaugeSubEx_haarK n ε⟩
  · obtain ⟨A, E, h1, h2, h3, h4⟩ := GlobalTheory.T.exists_nilpotentAlgebra_isotropicFlagUnipotentRadical n ε a j W hW
    rw [h4]
    exact GlobalTheory.T.exists_riemannianHaar_unitaryJSubgroupOfAlgebra n ε A _ E h1 h2 h3
  · obtain ⟨A, E, h1, h2, h3, h4⟩ := GlobalTheory.T.exists_algebra_isotropicFlagSelfAdjointLevi n ε a j W hW
    rw [h4]
    exact GlobalTheory.T.exists_riemannianHaar_unitaryJSubgroupOfAlgebra n ε A _ E h1 h2 h3

end GlobalTheory.FlagMeas
