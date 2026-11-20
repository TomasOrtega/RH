import Formalism.TameInertiaTowers.FinalGroup
import Formalism.TameInertiaTowers.CentralOrderTwo.Galois
import Formalism.TameInertiaTowers.CentralOrderTwo.ConjEqInvOfPowEqOne
import Formalism.TameInertiaTowers.CentralOrderTwo.DecompositionSubgroupIndex
import Formalism.TameInertiaTowers.CentralOrderTwo.OddEqOneOfSubOneMem

namespace Formalism.TwoAdicCyclotomicDecomposition

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem layerConj : LayerConj := layerConj_of layerGalois
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem layerReal : LayerReal := layerReal_of layerGalois layerConj
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem layerDecompTwo : LayerDecompTwo := layerDecompTwo_of layerGalois
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem layerInertiaTwo : LayerInertiaTwo := layerInertiaTwo_of layerGalois
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem layerEFGTwo : LayerEFGTwo := layerEFGTwo_of layerGalois layerReal
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem layerInertiaTame : LayerInertiaTame := layerInertiaTame_of layerGalois
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem layerFrob : LayerFrob := layerFrob_of layerGalois

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem tower_field_foundations :
    LayerExists ∧ LayerGalois ∧ LayerConj ∧ LayerReal ∧ LayerDecompTwo ∧ LayerInertiaTwo ∧
    LayerEFGTwo ∧ LayerInertiaTame ∧ LayerFrob :=
  ⟨layerExists, layerGalois, layerConj, layerReal, layerDecompTwo, layerInertiaTwo, layerEFGTwo,
    layerInertiaTame, layerFrob⟩

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem towerProperties :
    (UnitsTwoPow ∧ QuotCyclic ∧ TwoAdicOrder ∧ TwoAdicVal ∧ DecompModel ∧ GmRank ∧ GensModel ∧
      GamEModel ∧ GGModel ∧ CentralExtAbelian ∧ CommGen ∧ RankBound ∧
      NormalOrderTwoCentral ∧ TwistVal ∧ CoinvLength ∧ PGroupGen ∧ GenusModel ∧ GenusAbelian) ∧
    InvLength ∧
    (LayerExists ∧ LayerGalois ∧ LayerConj ∧ LayerReal ∧ LayerDecompTwo ∧ LayerInertiaTwo ∧
      LayerEFGTwo ∧ LayerInertiaTame ∧ LayerFrob) :=
  ⟨⟨unitsTwoPow, quotCyclic, twoAdicOrder, twoAdicVal, decompModel, gmRank, gensModel, gamEModel,
      ggModel, centralExtAbelian, commGen, rankBound,
      normalOrderTwoCentral, twistVal, coinvLength, pGroupGen, genusModel, genusAbelian⟩,
    invLength, tower_field_foundations⟩

end Formalism.TwoAdicCyclotomicDecomposition
