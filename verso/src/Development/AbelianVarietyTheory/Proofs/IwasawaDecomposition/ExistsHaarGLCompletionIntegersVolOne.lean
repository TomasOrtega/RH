import Formalism.LocalToGlobal.Divisibility.QLocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HostPins
import Formalism.DoubleCosetMeasures.LatticeCoset
import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.IsClosedLowUni
import ReciprocityTheory.GeneralLinearIntegers.AlgebraMapIntMemOint
open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD

namespace GlobalTheory

/- English proof (translation)
Introduce `L _ _ P r`. Establish `hc : IsCompact ((GLint (OP P) r : Subgroup (GL (Fin r) (P.adicCompletion L))) : Set (GL (Fin r) (P.adicCompletion L)))` using `Formalism.DoubleCosetMeasures.P.GeneralLinearIntegersOpenCompact.glR_compact (OP P) (ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isCompact_integers P) r`. Establish `ho : IsOpen ((GLint (OP P) r : Subgroup (GL (Fin r) (P.adicCompletion L))) : Set (GL (Fin r) (P.adicCompletion L)))` using `Formalism.DoubleCosetMeasures.P.GeneralLinearIntegersOpenCompact.glR_open (OP P) (ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isOpen_integers P) r`. Set `K₀ : TopologicalSpace.PositiveCompacts (GL (Fin r) (P.adicCompletion L))` to `⟨⟨_, hc⟩, by`. Rewrite using `[ho.interior_eq]`.

Conclude with `⟨1, (GLint (OP P) r).one_mem⟩⟩`. Use `⟨Measure.haarMeasure K₀, Measure.isMulLeftInvariant_haarMeasure K₀, ?_⟩` and prove the remaining obligations. Conclude with `Measure.haarMeasure_self`.
-/
theorem haar_glInt_one : ∀ (L : Type) [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L)) (r : ℕ), ∃ μ : Measure (GL (Fin r) (P.adicCompletion L)), μ.IsMulLeftInvariant ∧ μ ((GLint (OP P) r : Subgroup (GL (Fin r) (P.adicCompletion L))) : Set (GL (Fin r) (P.adicCompletion L))) = 1 := by
  intro L _ _ P r
  have hc : IsCompact ((GLint (OP P) r : Subgroup (GL (Fin r) (P.adicCompletion L))) : Set (GL (Fin r) (P.adicCompletion L))) :=
    Formalism.DoubleCosetMeasures.P.GeneralLinearIntegersOpenCompact.glR_compact (OP P) (ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isCompact_integers P) r
  have ho : IsOpen ((GLint (OP P) r : Subgroup (GL (Fin r) (P.adicCompletion L))) : Set (GL (Fin r) (P.adicCompletion L))) :=
    Formalism.DoubleCosetMeasures.P.GeneralLinearIntegersOpenCompact.glR_open (OP P) (ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isOpen_integers P) r
  let K₀ : TopologicalSpace.PositiveCompacts (GL (Fin r) (P.adicCompletion L)) :=
    ⟨⟨_, hc⟩, by
      rw [ho.interior_eq]; exact ⟨1, (GLint (OP P) r).one_mem⟩⟩
  refine ⟨Measure.haarMeasure K₀, Measure.isMulLeftInvariant_haarMeasure K₀, ?_⟩
  exact Measure.haarMeasure_self

end GlobalTheory
