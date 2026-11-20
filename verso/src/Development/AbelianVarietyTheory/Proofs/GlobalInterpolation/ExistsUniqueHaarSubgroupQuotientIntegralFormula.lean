import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.InvariantRadonFibre
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsUniqueHaarOfInvariantRadonOnCosetsStatement
open MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre
open scoped ENNReal NNReal

namespace GlobalTheory.Proof.existsUnique_haar_subgroup_quotient_integral_formula

section

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] (H : Subgroup G)

/- English proof (translation)
Use function extensionality and compare the values at `q`. Take `⟨g, rfl⟩` from `QuotientGroup.mk_surjective q`. Rewrite using `[fibreIntegral_mk, fibreIntegral_mk, lintegral_smul_measure]`. Both sides reduce to the same expression.
-/
theorem fibreIntegral_smul (c : ℝ≥0) (ν : Measure H) [ν.IsMulLeftInvariant]
    [(c • ν).IsMulLeftInvariant] (f : G → ℝ≥0∞) :
    fibreIntegral H (c • ν) f = fun q => (c : ℝ≥0∞) * fibreIntegral H ν f q := by
  funext q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  rw [fibreIntegral_mk, fibreIntegral_mk, lintegral_smul_measure]
  rfl

/- English proof (translation)
Introduce `f hf`. Take `⟨h1, h2⟩` from `h f hf`. Rewrite using `[fibreIntegral_smul]`. Use `⟨h1.const_mul _, ?_⟩` and prove the remaining obligations. Rewrite using `[lintegral_const_mul _ h1, lintegral_smul_measure, h2]`.

Both sides reduce to the same expression.
-/
theorem quotientFormula_smul [MeasurableSpace (G ⧸ H)] (c : ℝ≥0) (dg : Measure G)
    (ν : Measure H) [ν.IsMulLeftInvariant] [(c • ν).IsMulLeftInvariant] (μ : Measure (G ⧸ H))
    (h : QuotientFormula H dg ν μ) : QuotientFormula H (c • dg) (c • ν) μ := by
  intro f hf
  obtain ⟨h1, h2⟩ := h f hf
  rw [fibreIntegral_smul]
  refine ⟨h1.const_mul _, ?_⟩
  rw [lintegral_const_mul _ h1, lintegral_smul_measure, h2]
  rfl

/- English proof (translation)
Use extensionality with `s hs`. Establish `hm : Measurable (s.indicator (1 : G → ℝ≥0∞))` using `measurable_one.indicator hs`. Rewrite using `[← lintegral_indicator_one hs, ← lintegral_indicator_one hs, (h _ hm).2, (h' _ hm).2]`.
-/
theorem eq_of_quotientFormula [MeasurableSpace (G ⧸ H)] {dg dg' : Measure G}
    (ν : Measure H) [ν.IsMulLeftInvariant] (μ : Measure (G ⧸ H))
    (h : QuotientFormula H dg ν μ) (h' : QuotientFormula H dg' ν μ) : dg = dg' := by
  ext s hs
  have hm : Measurable (s.indicator (1 : G → ℝ≥0∞)) := measurable_one.indicator hs
  rw [← lintegral_indicator_one hs, ← lintegral_indicator_one hs, (h _ hm).2, (h' _ hm).2]

end

/- English proof (translation)
Introduce `G _ _ _ _ _ _ _ _ H _ _ hH _ _ dg _ μ hμ`. Use `haveI : LocallyCompactSpace H := hH.locallyCompactSpace`. Use `haveI : SecondCountableTopology H := inferInstanceAs (SecondCountableTopology (H : Set G))`. Establish `key : ∀ (ν ν' : Measure H) [ν.IsHaarMeasure] [ν'.IsHaarMeasure], QuotientFormula H dg ν μ → QuotientFormula H dg ν' μ → ν' = ν`. Introduce `ν ν' _ _ h h'`.

Take `⟨c, hc⟩ : ∃ c : ℝ≥0, ν' = c • ν` from `⟨_, Measure.isMulLeftInvariant_eq_smul ν' ν⟩`. Substitute `hc` using the available equality. Establish `h1` using `eq_of_quotientFormula H _ μ (quotientFormula_smul H c dg ν μ h) h'`. Take `⟨K⟩ : Nonempty (TopologicalSpace.PositiveCompacts G)` from `inferInstance`. Establish `hK0 : dg K ≠ 0` using `(Measure.measure_pos_of_nonempty_interior dg K.interior_nonempty).ne'`.

Establish `hKt : dg K ≠ ∞` using `K.isCompact.measure_lt_top.ne`. Establish `h2 : (c : ℝ≥0∞) * dg K = 1 * dg K`. Rewrite using `[one_mul]`. Use `congrArg (fun m : Measure G => m K) h1` as an intermediate fact. Simplify using `using this`.

Establish `h3 : (c : ℝ≥0∞) = 1` using `(ENNReal.mul_left_inj hK0 hKt).mp h2`. Establish `h4 : c = 1` using `by exact_mod_cast h3`. Rewrite using `[h4, one_smul]`. Take `⟨dg₀, ⟨_, h₀⟩, -⟩` from `GlobalTheory.T.existsUnique_haar_of_invariantRadonOnCosets G H hH (Measure.haar : Measure H) μ hμ`. Establish `hc : dg = Measure.haarScalarFactor dg dg₀ • dg₀` using `Measure.isMulLeftInvariant_eq_smul dg dg₀`.

Establish `hpos : Measure.haarScalarFactor dg dg₀ ≠ 0` using `(Measure.haarScalarFactor_pos_of_isHaarMeasure dg dg₀).ne'`. Use `haveI hν : (Measure.haarScalarFactor dg dg₀ • (Measure.haar : Measure H)).IsHaarMeasure := Measure.IsHaarMeasure.nnreal_smul _ hpos`. Establish `h₁ : QuotientFormula H dg (Measure.haarScalarFactor dg dg₀ • (Measure.haar : Measure H)) μ`. Use `quotientFormula_smul H (Measure.haarScalarFactor dg dg₀) dg₀ _ μ h₀` as an intermediate fact. Rewrite `this` using `[← hc]`. Then use the resulting hypothesis.

Use `⟨_, ⟨hν, h₁⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `ν ⟨_, h⟩`. Conclude with `key _ _ h₁ h`.
-/
theorem normaliseSubgroupClause : NormaliseSubgroupClause := by
  intro G _ _ _ _ _ _ _ _ H _ _ hH _ _ dg _ μ hμ
  haveI : LocallyCompactSpace H := hH.locallyCompactSpace
  haveI : SecondCountableTopology H :=
    inferInstanceAs (SecondCountableTopology (H : Set G))
  have key : ∀ (ν ν' : Measure H) [ν.IsHaarMeasure] [ν'.IsHaarMeasure],
      QuotientFormula H dg ν μ → QuotientFormula H dg ν' μ → ν' = ν := by
    intro ν ν' _ _ h h'
    obtain ⟨c, hc⟩ : ∃ c : ℝ≥0, ν' = c • ν := ⟨_, Measure.isMulLeftInvariant_eq_smul ν' ν⟩
    subst hc
    have h1 := eq_of_quotientFormula H _ μ (quotientFormula_smul H c dg ν μ h) h'
    obtain ⟨K⟩ : Nonempty (TopologicalSpace.PositiveCompacts G) := inferInstance
    have hK0 : dg K ≠ 0 :=
      (Measure.measure_pos_of_nonempty_interior dg K.interior_nonempty).ne'
    have hKt : dg K ≠ ∞ := K.isCompact.measure_lt_top.ne
    have h2 : (c : ℝ≥0∞) * dg K = 1 * dg K := by
      rw [one_mul]
      have := congrArg (fun m : Measure G => m K) h1
      simpa using this
    have h3 : (c : ℝ≥0∞) = 1 := (ENNReal.mul_left_inj hK0 hKt).mp h2
    have h4 : c = 1 := by exact_mod_cast h3
    rw [h4, one_smul]
  obtain ⟨dg₀, ⟨_, h₀⟩, -⟩ := GlobalTheory.T.existsUnique_haar_of_invariantRadonOnCosets G H hH (Measure.haar : Measure H) μ hμ
  have hc : dg = Measure.haarScalarFactor dg dg₀ • dg₀ :=
    Measure.isMulLeftInvariant_eq_smul dg dg₀
  have hpos : Measure.haarScalarFactor dg dg₀ ≠ 0 :=
    (Measure.haarScalarFactor_pos_of_isHaarMeasure dg dg₀).ne'
  haveI hν : (Measure.haarScalarFactor dg dg₀ • (Measure.haar : Measure H)).IsHaarMeasure :=
    Measure.IsHaarMeasure.nnreal_smul _ hpos
  have h₁ : QuotientFormula H dg
      (Measure.haarScalarFactor dg dg₀ • (Measure.haar : Measure H)) μ := by
    have := quotientFormula_smul H (Measure.haarScalarFactor dg dg₀) dg₀ _ μ h₀
    rwa [← hc] at this
  refine ⟨_, ⟨hν, h₁⟩, ?_⟩
  rintro ν ⟨_, h⟩
  exact key _ _ h₁ h

end GlobalTheory.Proof.existsUnique_haar_subgroup_quotient_integral_formula
