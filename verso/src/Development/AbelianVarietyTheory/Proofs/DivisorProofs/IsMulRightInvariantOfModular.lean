import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedStabX
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup

noncomputable section

open GlobalTheory.WeilM GlobalTheory.KSTransfer GlobalTheory.ParAvg MeasureTheory MeasureTheory.Measure
open scoped Matrix NNReal

namespace GlobalTheory.ParAvg

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem isMulRightInvariant_of_modular {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] [μ.InnerRegular]
    (h : ∀ g : G, modularCharacterFun g = 1) : μ.IsMulRightInvariant :=
  ⟨fun g => by rw [map_right_mul_eq_modularCharacterFun_smul μ g, h g, one_smul]⟩

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Express the relevant assertion in an equivalent form by its definition. Establish an intermediate fact. Rewrite the hypotheses and the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem modularCharacterFun_GL {r : ℕ} {E : Type} [Field E] [TopologicalSpace E] [IsTopologicalRing E]
    [LocallyCompactSpace (GL (Fin r) E)] (a : GL (Fin r) E) : modularCharacterFun a = 1 := by
  borelize (GL (Fin r) E)
  refine GlobalTheory.SplitFlip.hom_eq_one_of_center (modularCharacter : GL (Fin r) E →* ℝ≥0) (fun z hz => ?_) a
  change modularCharacterFun z = 1
  have e : map (fun x : GL (Fin r) E => x * z) (haar : Measure (GL (Fin r) E)) = haar := by
    rw [show (fun x : GL (Fin r) E => x * z) = fun x => z * x from funext fun x => (hz x).symm,
      map_mul_left_eq_self]
  rw [modularCharacterFun_eq_haarScalarFactor (haar : Measure (GL (Fin r) E)) z]
  simp only [e, haarScalarFactor_self]

end GlobalTheory.ParAvg
