import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.SquareIntegrable.SSmooth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TemperedBoundGL2
import GroundTheory.LocalFields.QuadraticAbelian.WeilRepQuadratic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSmoothCharCompNorm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WcEqZero
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.DualHol
open GlobalTheory.CompanionTheory.WcB
open scoped Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.WcB.NormOpen

/- English proof (translation)
Introduce `F _ _ _ _ _ _ E _ _ _ _ _ _ _ _ _ _ _`. Establish `hO : IsOpen ((GroundTheory.LocalField.normUnits F E).range : Set Fˣ)` using `GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.isOpen_range_normUnits (K := F) (E := E)`. Establish `hemb : Topology.IsOpenEmbedding (Units.val : Fˣ → F)` using `GroundTheory.LocalField.isOpenEmbedding_units_val`. Establish `hC : IsClosed ((GroundTheory.LocalField.normUnits F E).range : Set Fˣ)` using `Subgroup.isClosed_of_isOpen _ hO`. Prove the components needed by the constructor for the conclusion.

Establish `h` using `hemb.isOpenMap _ hO`. Use `h using 1` and compare the differences between its conclusion and the goal. Use extensionality with `a`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨t, rfl⟩`.

Conclude with `⟨GroundTheory.LocalField.normUnits F E t, ⟨t, rfl⟩, rfl⟩`. Introduce and unpack `⟨_, ⟨t, rfl⟩, rfl⟩`. Conclude with `⟨t, rfl⟩`. Establish `h` using `hemb.isOpenMap _ hC.isOpen_compl`. Use `h using 1` and compare the differences between its conclusion and the goal.

Use extensionality with `a`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨ha, hn⟩`. Use `⟨Units.mk0 a ha, ?_, rfl⟩` and prove the remaining obligations. Introduce and unpack `⟨t, ht⟩`.

Conclude with `hn ⟨t, by simpa using congrArg Units.val ht⟩`. Introduce and unpack `⟨u, hu, rfl⟩`. Use `⟨u.ne_zero, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨t, ht⟩`. Conclude with `hu ⟨t, Units.ext ht⟩`.
-/
theorem isOpen_norms_and_nonnorms : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E] [Algebra.IsSeparable F E] [Fact (Module.finrank F E = 2)], IsOpen {a : F | ∃ t : Eˣ, Algebra.norm F (t : E) = a} ∧ IsOpen {a : F | a ≠ 0 ∧ ¬ ∃ t : Eˣ, Algebra.norm F (t : E) = a} := by
  intro F _ _ _ _ _ _ E _ _ _ _ _ _ _ _ _ _ _
  have hO : IsOpen ((GroundTheory.LocalField.normUnits F E).range : Set Fˣ) :=
    GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.isOpen_range_normUnits (K := F) (E := E)
  have hemb : Topology.IsOpenEmbedding (Units.val : Fˣ → F) := GroundTheory.LocalField.isOpenEmbedding_units_val
  have hC : IsClosed ((GroundTheory.LocalField.normUnits F E).range : Set Fˣ) :=
    Subgroup.isClosed_of_isOpen _ hO
  constructor
  · have h := hemb.isOpenMap _ hO
    convert h using 1
    ext a
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨GroundTheory.LocalField.normUnits F E t, ⟨t, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
      exact ⟨t, rfl⟩
  · have h := hemb.isOpenMap _ hC.isOpen_compl
    convert h using 1
    ext a
    constructor
    · rintro ⟨ha, hn⟩
      refine ⟨Units.mk0 a ha, ?_, rfl⟩
      rintro ⟨t, ht⟩
      exact hn ⟨t, by simpa using congrArg Units.val ht⟩
    · rintro ⟨u, hu, rfl⟩
      refine ⟨u.ne_zero, ?_⟩
      rintro ⟨t, ht⟩
      exact hu ⟨t, Units.ext ht⟩

end GlobalTheory.CompanionTheory.WcB.NormOpen
