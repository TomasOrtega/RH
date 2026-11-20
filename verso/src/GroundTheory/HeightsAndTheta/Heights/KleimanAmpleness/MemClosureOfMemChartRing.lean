import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsGraphGenTwistBundleZero
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsExtraTer
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTerAlt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsRestAlt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsExtraTail
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsLastRest
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsMoreTer
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ObjectsAlt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsLastTer
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsLastSide
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver)

noncomputable section

section Points

variable {S : Type} [CommRing S] {Ω : Type} [Field Ω] [Algebra S Ω] {N : ℕ}

/- English proof (translation)
Rewrite using `[← TranslateEq.chartRing.equiv S x hi]`. Unfold `chartRingOver ReciprocityTheory.ChartRestriction.G.Geo.chartRing`. Use `congr 1`. Use extensionality with `z`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨⟨⟨⟩, a⟩, rfl⟩`. Conclude with `⟨a, rfl⟩`. Introduce and unpack `⟨a, rfl⟩`. Conclude with `⟨⟨(), a⟩, rfl⟩`.
-/
theorem chartRingOver_oneBlock (x : Fin (N + 1) → Ω) (c : Unit → Fin (N + 1)) (hi : x (c ()) ≠ 0) :
    chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) c = Kleiman.chartRing S x (Kleiman.singleChart hi) := by
  rw [← TranslateEq.chartRing.equiv S x hi]
  unfold chartRingOver ReciprocityTheory.ChartRestriction.G.Geo.chartRing
  congr 1
  ext z
  constructor
  · rintro ⟨⟨⟨⟩, a⟩, rfl⟩
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨⟨(), a⟩, rfl⟩

end Points

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
