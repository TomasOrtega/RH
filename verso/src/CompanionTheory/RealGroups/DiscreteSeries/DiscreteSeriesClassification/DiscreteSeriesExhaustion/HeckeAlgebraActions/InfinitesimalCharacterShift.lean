import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.HeckeAlgebraActions.HeckeDuality.DualModuleFacts
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.HeckeAlgebraActions.HeckeUnits.Unitarity
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.HeckeAlgebraActions.TensorReflections.PiIsoTensVd
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.HeckeAlgebraActions.SimpleBackwardTransfer.FwdSimpleOfb
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.HeckeAlgebraActions.ScalarCharacters.ScalCharOfSimple
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.QuantumDeterminantEqualityStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.QuantumDeterminantTensorStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CayleyHamiltonStatementStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.InfinitesimalCharacterStatementStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HeckeNonVanishingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HeckeNonScalarStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HeckeBackwardStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HeckeBackwardStableStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.OmegaScalarStatement

namespace CompanionTheory.RgExh.Hk

/- English proof (translation)
The claim follows from `UnitB.unit_of_dualFacts dual_module_facts`.
-/
theorem unitarity : Unit := UnitB.unit_of_dualFacts dual_module_facts

/- English proof (translation)
The claim follows from `reflect_of' GlobalTheory.T.QuantumDeterminantTensor GlobalTheory.T.OmegaScalar GlobalTheory.T.HeckeBackwardStable dual_module_facts unitarity`.
-/
theorem reflection_symmetry : Reflect :=
  reflect_of' GlobalTheory.T.QuantumDeterminantTensor GlobalTheory.T.OmegaScalar GlobalTheory.T.HeckeBackwardStable dual_module_facts unitarity

/- English proof (translation)
The claim follows from `forward_simple_of_tensor_facts GlobalTheory.T.QuantumDeterminantTensor GlobalTheory.T.HeckeBackwardStable dual_module_facts unitarity`.
-/
theorem forward_simple_module : FwdSimple :=
  forward_simple_of_tensor_facts GlobalTheory.T.QuantumDeterminantTensor GlobalTheory.T.HeckeBackwardStable dual_module_facts unitarity

/- English proof (translation)
The claim follows from `GlobalTheory.T.InfinitesimalCharacterStatement`.
-/
theorem infinitesimal_character_shift : CompanionTheory.RgExh.StepChar := GlobalTheory.T.InfinitesimalCharacterStatement

/- English proof (translation)
The claim follows from `hecke_of' GlobalTheory.T.QuantumDeterminantEquality GlobalTheory.T.InfinitesimalCharacterStatement GlobalTheory.T.CayleyHamiltonHk GlobalTheory.T.HeckeNonVanishing GlobalTheory.T.HeckeNonScalar GlobalTheory.T.HeckeBackward GlobalTheory.T.OmegaScalar forward_simple_module reflecti …`.
-/
theorem hecke_algebra_exhaustion : CompanionTheory.RgExh.Hecke :=
  hecke_of' GlobalTheory.T.QuantumDeterminantEquality GlobalTheory.T.InfinitesimalCharacterStatement GlobalTheory.T.CayleyHamiltonHk GlobalTheory.T.HeckeNonVanishing GlobalTheory.T.HeckeNonScalar GlobalTheory.T.HeckeBackward GlobalTheory.T.OmegaScalar
    forward_simple_module reflection_symmetry

end CompanionTheory.RgExh.Hk
