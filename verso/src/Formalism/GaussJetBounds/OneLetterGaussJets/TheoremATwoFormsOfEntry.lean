import Formalism.GaussJetBounds.OneLetterGaussJets.OneLetterGaussProofs.CapLeOddShiftBound
import Formalism.GaussJetBounds.GaussJetProofs.WeightsAddOverOrbitsLogLoss
import Formalism.GaussJetBounds.OneLetterGaussJets.OneLetterGaussProofs.TheoremAMonomialOfLemmas
import Formalism.GaussJetBounds.OneLetterGaussJets.OneLetterGaussProofs.ThmAGen7Of
import Formalism.GaussJetBounds.OneLetterGaussJets.OneLetterGaussProofs.ThmAGeneric7Of
import Formalism.GaussJetBounds.OneLetterGaussJets.OneLetterGaussProofs.TwoFormsOfTheoremA
import Formalism.GaussJetBounds.OneLetterGaussJets.MinWeightSumAddCostAbsBound
import Formalism.GaussJetBounds.GaussJetProofs.IntegralOperatorsOnJets

universe u v w

namespace Formalism.DworkPowerSeriesWeights.OddLevelGainBounds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem thmAAssembly7 : ThmAAssembly7 := gauss_jet_bound_of_parts
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem thmAJet7 : ThmAJet7.{u} := thmAJet7_of thmAAssembly7
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem thmAOp7 : ThmAOp7.{u} := thmAOp7_of thmAJet7
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem thmAGen7 : ThmAGen7.{u} := thmAGen7_of thmAOp7
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem thmAFrame7 : ThmAFrame7.{u} := thmAFrame7_of thmAGen7
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem thmAGeneric7 : ThmAGeneric7.{u} := thmAGeneric7_of thmAFrame7
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem thmAGauss7 : ThmAGauss7 := thmAGauss7_of thmAGeneric7
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem thmAWeyl7 : ThmAWeyl7 := thmAWeyl7_of thmAGauss7
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem thmAEntry7 : ThmAEntry7 := thmAEntry7_of thmAWeyl7

end Formalism.DworkPowerSeriesWeights.OddLevelGainBounds
