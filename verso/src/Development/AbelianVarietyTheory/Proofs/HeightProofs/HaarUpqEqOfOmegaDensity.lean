import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedSmooth
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactExponentialSurjective
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.IsotypicSignedParameters
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsBlockOrd
import Development.AbelianVarietyTheory.Proofs.HeightProofs.HaarUpqIsMulRightInvariant

open Formalism.BasicNotions Matrix MeasureTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace GlobalTheory.CompactDualUnique

/- English proof (translation)
Use `haveI : BorelSpace (lieU P Q) := ⟨rfl⟩`. Use `haveI : LocallyCompactSpace (Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) := inferInstanceAs (LocallyCompactSpace ((Fin P ⊕ Fin Q) → (Fin P ⊕ Fin Q) → ℂ))`. Use `haveI : SecondCountableTopology (Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) := inferInstanceAs (SecondCountableTopology ((Fin P ⊕ Fin Q) → (Fin P ⊕ Fin Q) → ℂ))`. Use `haveI : LocallyCompactSpace (lieU P Q) := (Submodule.closed_of_finiteDimensional (lieU P Q)).isClosedEmbedding_subtypeVal.locallyCompactSpace`. Use `haveI : SecondCountableTopology (lieU P Q) := TopologicalSpace.Subtype.secondCountableTopology _`.

Take `⟨h1, h2⟩` from `h`. Take `⟨h1', h2'⟩` from `h'`. Take `⟨t, ht⟩ : ∃ t : ℝ≥0, lam = t • lam'` from `⟨_, Measure.isAddLeftInvariant_eq_smul lam lam'⟩`. Establish `hp : lam.prod lam = (t * t) • lam'.prod lam'`. Rewrite using `[ht, Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]`.

Rewrite `h2` using `[hp, Measure.map_smul, h2']`. Establish `h3` using `congrArg (fun m : Measure ((Fin P ⊕ Fin Q) × (Fin P ⊕ Fin Q) → ℂ) => m (Metric.ball 0 1)) h2`. Simplify using `only [Measure.smul_apply] at h3`. Establish `hpos : (volume : Measure ((Fin P ⊕ Fin Q) × (Fin P ⊕ Fin Q) → ℂ)) (Metric.ball 0 1) ≠ 0` using `(Metric.measure_ball_pos _ _ one_pos).ne'`. Establish `hfin : (volume : Measure ((Fin P ⊕ Fin Q) × (Fin P ⊕ Fin Q) → ℂ)) (Metric.ball 0 1) ≠ ⊤` using `measure_ball_lt_top.ne`.

Establish `h4 : ((t * t : ℝ≥0) : ℝ≥0∞) = 1`. Rewrite `h3` using `[ENNReal.smul_def, smul_eq_mul]`. Conclude with `(ENNReal.mul_left_inj hpos hfin).1 (h3.trans (one_mul _).symm)`. Establish `h5 : t * t = 1` using `by exact_mod_cast h4`. Establish `h6 : t = 1`.

Establish `h7 : (t : ℝ) * t = 1` using `by exact_mod_cast h5`. Establish `h8 : (0 : ℝ) ≤ t` using `t.2`. Establish `: (t : ℝ) = 1` using `by nlinarith`. Conclude with `this` after adjusting the coercions. Rewrite using `[ht, h6, one_smul]`.
-/
theorem isOmegaLeb_unique {P Q : ℕ} {lam lam' : Measure (lieU P Q)}
    (h : IsOmegaLeb lam) (h' : IsOmegaLeb lam') : lam = lam' := by
  haveI : BorelSpace (lieU P Q) := ⟨rfl⟩
  haveI : LocallyCompactSpace (Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) :=
    inferInstanceAs (LocallyCompactSpace ((Fin P ⊕ Fin Q) → (Fin P ⊕ Fin Q) → ℂ))
  haveI : SecondCountableTopology (Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) :=
    inferInstanceAs (SecondCountableTopology ((Fin P ⊕ Fin Q) → (Fin P ⊕ Fin Q) → ℂ))
  haveI : LocallyCompactSpace (lieU P Q) :=
    (Submodule.closed_of_finiteDimensional (lieU P Q)).isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (lieU P Q) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  obtain ⟨h1, h2⟩ := h
  obtain ⟨h1', h2'⟩ := h'
  obtain ⟨t, ht⟩ : ∃ t : ℝ≥0, lam = t • lam' := ⟨_, Measure.isAddLeftInvariant_eq_smul lam lam'⟩
  have hp : lam.prod lam = (t * t) • lam'.prod lam' := by
    rw [ht, Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]
  rw [hp, Measure.map_smul, h2'] at h2
  have h3 := congrArg (fun m : Measure ((Fin P ⊕ Fin Q) × (Fin P ⊕ Fin Q) → ℂ) =>
    m (Metric.ball 0 1)) h2
  simp only [Measure.smul_apply] at h3
  have hpos : (volume : Measure ((Fin P ⊕ Fin Q) × (Fin P ⊕ Fin Q) → ℂ)) (Metric.ball 0 1) ≠ 0 :=
    (Metric.measure_ball_pos _ _ one_pos).ne'
  have hfin : (volume : Measure ((Fin P ⊕ Fin Q) × (Fin P ⊕ Fin Q) → ℂ)) (Metric.ball 0 1) ≠ ⊤ :=
    measure_ball_lt_top.ne
  have h4 : ((t * t : ℝ≥0) : ℝ≥0∞) = 1 := by
    rw [ENNReal.smul_def, smul_eq_mul] at h3
    exact (ENNReal.mul_left_inj hpos hfin).1 (h3.trans (one_mul _).symm)
  have h5 : t * t = 1 := by exact_mod_cast h4
  have h6 : t = 1 := by
    have h7 : (t : ℝ) * t = 1 := by exact_mod_cast h5
    have h8 : (0 : ℝ) ≤ t := t.2
    have : (t : ℝ) = 1 := by nlinarith
    exact_mod_cast this
  rw [ht, h6, one_smul]

/- English proof (translation)
Take `⟨lam, h1, h2⟩` from `h`. Take `⟨lam', h1', h2'⟩` from `h'`. Take `rfl` from `isOmegaLeb_unique h1 h1'`. Conclude with `tendsto_nhds_unique h2 h2'`.
-/
theorem omegaDensity_unique {P Q : ℕ} {μ : Measure (UpqT P Q)} {c c' : ℝ≥0∞}
    (h : OmegaDensity μ c) (h' : OmegaDensity μ c') : c = c' := by
  obtain ⟨lam, h1, h2⟩ := h
  obtain ⟨lam', h1', h2'⟩ := h'
  obtain rfl := isOmegaLeb_unique h1 h1'
  exact tendsto_nhds_unique h2 h2'

/- English proof (translation)
Take `⟨lam, h1, h2⟩` from `h`. Use `⟨lam, h1, ?_⟩` and prove the remaining obligations. Use `ENNReal.Tendsto.const_mul (a := (t : ℝ≥0∞)) h2 (Or.inr ENNReal.coe_ne_top)` as an intermediate fact. Use `this.congr fun r => ?_` and prove the remaining obligations. Rewrite using `[Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, mul_div_assoc]`.
-/
theorem omegaDensity_smul {P Q : ℕ} {μ : Measure (UpqT P Q)} {c : ℝ≥0∞} (t : ℝ≥0)
    (h : OmegaDensity μ c) : OmegaDensity (t • μ) (t * c) := by
  obtain ⟨lam, h1, h2⟩ := h
  refine ⟨lam, h1, ?_⟩
  have := ENNReal.Tendsto.const_mul (a := (t : ℝ≥0∞)) h2 (Or.inr ENNReal.coe_ne_top)
  refine this.congr fun r => ?_
  rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, mul_div_assoc]

/- English proof (translation)
Use `haveI : IsTopologicalGroup (UpqT P Q) := inferInstanceAs (IsTopologicalGroup (Formalism.UG.Upq P Q))`. Use `haveI : BorelSpace (UpqT P Q) := ⟨rfl⟩`. Use `haveI : LocallyCompactSpace (UpqT P Q) := (UpqUnimodular.modelEquiv P Q).toHomeomorph.isClosedEmbedding.locallyCompactSpace`. Use `haveI : SecondCountableTopology (UpqT P Q) := (UpqUnimodular.modelEquiv P Q).toHomeomorph.secondCountableTopology`. Conclude with `⟨_, Measure.isMulLeftInvariant_eq_smul μ ν⟩`.
-/
theorem exists_eq_smul {P Q : ℕ} (μ ν : Measure (UpqT P Q)) [μ.IsHaarMeasure] [ν.IsHaarMeasure] :
    ∃ t : ℝ≥0, μ = t • ν := by
  haveI : IsTopologicalGroup (UpqT P Q) := inferInstanceAs (IsTopologicalGroup (Formalism.UG.Upq P Q))
  haveI : BorelSpace (UpqT P Q) := ⟨rfl⟩
  haveI : LocallyCompactSpace (UpqT P Q) :=
    (UpqUnimodular.modelEquiv P Q).toHomeomorph.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (UpqT P Q) :=
    (UpqUnimodular.modelEquiv P Q).toHomeomorph.secondCountableTopology
  exact ⟨_, Measure.isMulLeftInvariant_eq_smul μ ν⟩

/- English proof (translation)
Use `haveI := cd.haar P Q`. Use `haveI := cd.haar (P + Q) 0`. Use `haveI := cd.prob (P + Q)`. Take `⟨c', h0', ht', h1', h2'⟩` from `cd.trick P Q`. Take `⟨s, hs⟩` from `exists_eq_smul νc (cd.cd (P + Q) 0)`.

Establish `hs1 : s = 1`. Use `congrArg (fun m : Measure (UpqT (P + Q) 0) => m Set.univ) hs` as an intermediate fact. Simplify using `only [Measure.smul_apply, measure_univ, ENNReal.smul_def, smul_eq_mul, mul_one] at this`. Conclude with `this.symm` after adjusting the coercions. Rewrite `hs` using `[hs1, one_smul]`.

Rewrite `h2` using `[hs]`. Take `rfl` from `omegaDensity_unique h2 h2'`. Take `⟨t, ht⟩` from `exists_eq_smul ν (cd.cd P Q)`. Establish `h3` using `omegaDensity_smul t h1'`. Rewrite `h3` using `[← ht]`.

Establish `h4` using `omegaDensity_unique h3 h1`. Establish `h5 : (t : ℝ≥0∞) = 1` using `(ENNReal.mul_left_inj h0' ht').1 (h4.trans (one_mul _).symm)`. Establish `h6 : t = 1` using `by exact_mod_cast h5`. Rewrite using `[ht, h6, one_smul]`.
-/
theorem eq_cd (cd : CDHaar) (P Q : ℕ) (ν : Measure (UpqT P Q)) (νc : Measure (UpqT (P + Q) 0))
    (c : ENNReal) (hν : ν.IsHaarMeasure) (hνc : νc.IsHaarMeasure) (hp : IsProbabilityMeasure νc)
    (_h0 : c ≠ 0) (_ht : c ≠ ⊤) (h1 : OmegaDensity ν c) (h2 : OmegaDensity νc c) :
    ν = cd.cd P Q := by
  haveI := cd.haar P Q
  haveI := cd.haar (P + Q) 0
  haveI := cd.prob (P + Q)
  obtain ⟨c', h0', ht', h1', h2'⟩ := cd.trick P Q
  obtain ⟨s, hs⟩ := exists_eq_smul νc (cd.cd (P + Q) 0)
  have hs1 : s = 1 := by
    have := congrArg (fun m : Measure (UpqT (P + Q) 0) => m Set.univ) hs
    simp only [Measure.smul_apply, measure_univ, ENNReal.smul_def, smul_eq_mul, mul_one] at this
    exact_mod_cast this.symm
  rw [hs1, one_smul] at hs
  rw [hs] at h2
  obtain rfl := omegaDensity_unique h2 h2'
  obtain ⟨t, ht⟩ := exists_eq_smul ν (cd.cd P Q)
  have h3 := omegaDensity_smul t h1'
  rw [← ht] at h3
  have h4 := omegaDensity_unique h3 h1
  have h5 : (t : ℝ≥0∞) = 1 := (ENNReal.mul_left_inj h0' ht').1 (h4.trans (one_mul _).symm)
  have h6 : t = 1 := by exact_mod_cast h5
  rw [ht, h6, one_smul]

end GlobalTheory.CompactDualUnique
