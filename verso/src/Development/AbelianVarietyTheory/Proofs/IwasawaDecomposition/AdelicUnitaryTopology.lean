import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DiscreteTopologyRationalPointsHermitianSpace

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.AdelicGroupTop

/- English proof (translation)
Use `Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.isTopRing (F := F) (E := E)` as an intermediate fact. Conclude with `inferInstanceAs (IsTopologicalGroup (HR (AF F) σ J))`.
-/
theorem isTopologicalGroup_HA {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) : IsTopologicalGroup (HA (AF F) σ J) := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.isTopRing (F := F) (E := E)
  exact inferInstanceAs (IsTopologicalGroup (HR (AF F) σ J))

/- English proof (translation)
Introduce `D V`. Take `⟨h1, h2, h3⟩` from `GlobalTheory.AdelicUnitaryTop.lcsc_adelicUnitary D.host.F D.host.E D.sp.cm.sig V.rank V.gram`. Establish `hd : DiscreteTopology (GQ V)` using `GlobalTheory.RationalDiscrete.discreteTopology_GQ D V`. Establish `h2' : SecondCountableTopology (GA D V)` using `h2`. Conclude with `⟨h1, h2, h3, ⟨rfl⟩, isTopologicalGroup_HA D.sp.cm.sig V.gram, hd, TopologicalSpace.separableSpace_iff_countable.1 inferInstance⟩`.
-/
theorem adelic_unitary_topology : ∀ (D : D7) (V : HSp D), LocallyCompactSpace (GA D V) ∧ SecondCountableTopology (GA D V) ∧ T2Space (GA D V) ∧ BorelSpace (GA D V) ∧ IsTopologicalGroup (GA D V) ∧ DiscreteTopology (GQ V) ∧ Countable (GQ V) := by
  intro D V
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.AdelicUnitaryTop.lcsc_adelicUnitary D.host.F D.host.E D.sp.cm.sig V.rank V.gram
  have hd : DiscreteTopology (GQ V) := GlobalTheory.RationalDiscrete.discreteTopology_GQ D V
  have h2' : SecondCountableTopology (GA D V) := h2
  exact ⟨h1, h2, h3, ⟨rfl⟩, isTopologicalGroup_HA D.sp.cm.sig V.gram, hd,
    TopologicalSpace.separableSpace_iff_countable.1 inferInstance⟩

end GlobalTheory.Mem.AdelicGroupTop
