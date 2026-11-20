import Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.BernsteinTheoremA.FrobeniusReciprocity.SupportedInIffOfFrob
open MeasureTheory MeasureTheory.Measure GlobalTheory.SplitWeil PositivityTheory.PfBern.Frob

namespace GlobalTheory.CompanionTheory.HaarUnimod

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]

/- English proof (translation)
The claim follows from `hG g`.
-/
theorem modularCharacterFun_eq_one (hG : IsUnimod G) (g : G) : modularCharacterFun g = 1 :=
  hG g

/- English proof (translation)
Introduce `G _ _ _ _ _ _ _ hG μ _`. Use `⟨fun g => ?_⟩` and prove the remaining obligations. Rewrite using `[isMulLeftInvariant_eq_smul (map (· * g) μ) μ, ← modularCharacterFun_eq_haarScalarFactor, modularCharacterFun_eq_one hG g, one_smul]`.
-/
theorem isMulRightInvariant_of_isUnimod :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
      [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G], IsUnimod G →
      ∀ (μ : Measure G) [μ.IsHaarMeasure], μ.IsMulRightInvariant := by
  intro G _ _ _ _ _ _ _ hG μ _
  refine ⟨fun g => ?_⟩
  rw [isMulLeftInvariant_eq_smul (map (· * g) μ) μ,
    ← modularCharacterFun_eq_haarScalarFactor, modularCharacterFun_eq_one hG g, one_smul]

end GlobalTheory.CompanionTheory.HaarUnimod
