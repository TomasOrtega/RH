import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.WtProj
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistsPowEqZero
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.InNOfMem
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.RhoSurj
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistsAdFam
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CompactFiniteAdelesAwayPBoundedDenominators
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.OrthCycCycStable
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.FilterAll
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.CreAnnApply
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.KoszulDifferentialAnticommutator
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.GeneralizedVermaModulePolynomial
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.CycDense
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter

namespace CompanionTheory.D.LK

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hGenCO : GenCO := genCO_of koszul_differential_sq_zero (cover2_of (acycAbs_of koszul_differential_sq_zero))

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hInj : Inj :=
  inj_of (vanK_of (cok_of hGenCO) GlobalTheory.CompanionTheory.LKWtProj.wtProj (GlobalTheory.CompanionTheory.KWeightMajor.wtMajor_of DSIC.hLowSpan)) GlobalTheory.CompanionTheory.LKWtProj.wtProj koszul_differential_sq_zero

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hMultAlg : MultAlg :=
  multAlg_of DSIC.hLowSpan DSIC.hHWMap GlobalTheory.CompanionTheory.LKDens.dens GlobalTheory.CompanionTheory.LKInvLift.invLift GlobalTheory.CompanionTheory.HCdecomp.hcdec hGenCO top_degree_cycle hInj

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hKModExists : KModExists :=
  GlobalTheory.CompanionTheory.KModExists.kModExists DSIC.hSmMod CompanionTheory.D.gk.admitted.kFin_mem_smoothVecs DSIC.hKFinStab DSIC.hStabLink DSIC.hHWofType
    DSIC.hTypeOfHW

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hOrthCyc : OrthCyc := GlobalTheory.CompanionTheory.LowKType.orthCyc

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem low_K_type_multiplicity_one_unconditional : LowKMultOneP := lowKMultOneP_of hMultAlg hKModExists cyclic_vectors_dense hOrthCyc

end CompanionTheory.D.LK
