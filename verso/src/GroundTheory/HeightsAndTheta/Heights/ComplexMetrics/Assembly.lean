import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexPointsBase
import GroundTheory.HeightsAndTheta.Heights.ComplexMetrics.PProjPointContinuous
import GroundTheory.HeightsAndTheta.Heights.ComplexMetrics.PFractionContinuous
import GroundTheory.HeightsAndTheta.Heights.ComplexMetrics.PGermFraction
import GroundTheory.HeightsAndTheta.Heights.ComplexMetrics.PLocalLift
import GroundTheory.HeightsAndTheta.Heights.ComplexMetrics.PRegularContinuous
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open AlgebraicGeometry CategoryTheory MonoidalCategory

universe u

noncomputable section

namespace ComplexMetric

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ProjPointContinuous.full : ProjPointContinuous.Statement.{u} :=
  ProjPointContinuous.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem FractionContinuous.full : FractionContinuous.Statement.{u} :=
  FractionContinuous.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem GermFraction.full : GermFraction.Statement.{u} :=
  GermFraction.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem LocalLift.full : LocalLift.Statement.{u} :=
  LocalLift.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem RegularContinuous.full : RegularContinuous.Statement.{u} :=
  RegularContinuous.proof ProjPointContinuous.full FractionContinuous.full GermFraction.full
    LocalLift.full

end ComplexMetric

namespace ProjScheme

variable {A : Type u} [CommRing A] {N : ℕ}

def standardMetricOf (X : ProjScheme A N) : X.ContinuousMetric (𝟙_ X.X.Modules) :=
  X.standardMetric ComplexMetric.RegularContinuous.full

def trivialBundleOf (X : ProjScheme A N) : X.HermitianLineBundle :=
  X.trivialBundle ComplexMetric.RegularContinuous.full

def standardMetricSelf (A : Type u) [CommRing A] (N : ℕ) :
    (ProjScheme.self A N).ContinuousMetric (𝟙_ (ProjScheme.self A N).X.Modules) :=
  (ProjScheme.self A N).standardMetricOf

def trivialBundleSelf (A : Type u) [CommRing A] (N : ℕ) : (ProjScheme.self A N).HermitianLineBundle :=
  (ProjScheme.self A N).trivialBundleOf

def standardMetricBase (A : Type u) [CommRing A] (N : ℕ) :
    (ProjScheme.base A N).ContinuousMetric (𝟙_ (ProjScheme.base A N).X.Modules) :=
  (ProjScheme.base A N).standardMetricOf

def trivialBundleBase (A : Type u) [CommRing A] (N : ℕ) : (ProjScheme.base A N).HermitianLineBundle :=
  (ProjScheme.base A N).trivialBundleOf

/- English proof (translation)
Both sides reduce to the same expression.
-/
example (x : (ProjScheme.self ℤ 1).complexPoints (Int.castRingHom ℂ))
    (s : (ProjScheme.self ℤ 1).Fibre (𝟙_ (ProjScheme.self ℤ 1).X.Modules) x) :
    (standardMetricSelf ℤ 1).norm _ x s = ‖(ProjScheme.self ℤ 1).unitFibreEquiv x s‖ := rfl

end ProjScheme

end

end GroundTheory.Heights₂.Heights
