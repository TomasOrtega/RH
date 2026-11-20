import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.LocalQuotientIntegrals.OneVanish
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.T2SpaceAdelicGLCmField

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB

namespace PositivityTheory.Rg.BcB.CV.AdelicTopology

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

/- English proof (translation)
Introduce and unpack `_ ⟨g, -, rfl⟩`. Conclude with `⟨g, rfl⟩`.
-/
theorem ratCent_subset_range (d : GL (Fin n) E) :
    (ratCent d : Set (GA E n)) ⊆ ((ratGL E n).range : Set (GA E n)) := by
  rintro _ ⟨g, -, rfl⟩
  exact ⟨g, rfl⟩

/- English proof (translation)
The claim follows from `DiscreteTopology.of_subset (s := ((ratGL E n).range : Set (GA E n))) GlobalTheory.CompanionTheory.KerTwFin.discreteTopology_range (ratCent_subset_range d)`.
-/
theorem discrete_ratCent (d : GL (Fin n) E) : DiscreteTopology (ratCent d) :=
  DiscreteTopology.of_subset (s := ((ratGL E n).range : Set (GA E n)))
    GlobalTheory.CompanionTheory.KerTwFin.discreteTopology_range (ratCent_subset_range d)

/- English proof (translation)
Use `GlobalTheory.CompanionTheory.UnfoldCut.countable_GL (E := E) (n := n)` as an intermediate fact. Establish `h : (ratCent d : Set (GA E n)).Countable` using `(Set.countable_range (ratGL E n)).mono fun _ hx => by`. Take `⟨g, hg⟩` from `ratCent_subset_range d hx`. Conclude with `⟨g, hg⟩`. Conclude with `h.to_subtype`.
-/
theorem countable_ratCent (d : GL (Fin n) E) : Countable (ratCent d) := by
  have := GlobalTheory.CompanionTheory.UnfoldCut.countable_GL (E := E) (n := n)
  have h : (ratCent d : Set (GA E n)).Countable :=
    (Set.countable_range (ratGL E n)).mono fun _ hx => by
      obtain ⟨g, hg⟩ := ratCent_subset_range d hx
      exact ⟨g, hg⟩
  exact h.to_subtype

end PositivityTheory.Rg.BcB.CV.AdelicTopology

/- English proof (translation)
Introduce `hD _ E _ _ _ n`. Use `GlobalTheory.CompanionTheory.UnfoldCut.t2Space_adelicGL_cmField (E := E) (n := n)` as an intermediate fact. Use `⟨GlobalTheory.CompanionTheory.UnfoldCut.locallyCompact_GA, inferInstance, GlobalTheory.CompanionTheory.UnfoldCut.secondCountable_GA, GlobalTheory.CompanionTheory.KerTwFin.continuous_thetaA, fun W => ?_, fun d => ?_⟩` and prove the remaining obligations. Set `_ : MeasurableSpace (GA E n)` to `borel _`. Establish `: BorelSpace (GA E n)` using `⟨rfl⟩`.

Conclude with `((hD E n).2 W).measurable`. Use `PositivityTheory.Rg.BcB.CV.AdelicTopology.discrete_ratCent d` as an intermediate fact. Conclude with `⟨Subgroup.isClosed_of_discrete, inferInstance, PositivityTheory.Rg.BcB.CV.AdelicTopology.countable_ratCent d⟩`.
-/
theorem PositivityTheory.Rg.BcB.CV.pf_AdTop : PositivityTheory.Rg.BcB.DegBdd → PositivityTheory.Rg.BcB.D4.RatDisc → PositivityTheory.Rg.BcB.CV.AdTop := by
  intro hD _ E _ _ _ n
  have := GlobalTheory.CompanionTheory.UnfoldCut.t2Space_adelicGL_cmField (E := E) (n := n)
  refine ⟨GlobalTheory.CompanionTheory.UnfoldCut.locallyCompact_GA, inferInstance, GlobalTheory.CompanionTheory.UnfoldCut.secondCountable_GA,
    GlobalTheory.CompanionTheory.KerTwFin.continuous_thetaA, fun W => ?_, fun d => ?_⟩
  · let _ : MeasurableSpace (GA E n) := borel _
    have : BorelSpace (GA E n) := ⟨rfl⟩
    exact ((hD E n).2 W).measurable
  · have := PositivityTheory.Rg.BcB.CV.AdelicTopology.discrete_ratCent d
    exact ⟨Subgroup.isClosed_of_discrete, inferInstance, PositivityTheory.Rg.BcB.CV.AdelicTopology.countable_ratCent d⟩
