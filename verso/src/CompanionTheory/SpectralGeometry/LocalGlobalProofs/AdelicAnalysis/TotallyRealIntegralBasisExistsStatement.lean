import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TotallyRealIntegralBasisExists
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SumRhoEqTrace
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.ThW
open scoped ENNReal NNReal MatrixGroups Kronecker
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FAdelicAnalysis%2FTotallyRealIntegralBasisExists.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.totally_real_integral_basis_exists : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → Nonempty (Module.Basis (InfinitePlace F) ℤ (𝓞 F)) := by
  first | exact @GlobalTheory.CompanionTheory.SW.ThW.exists_integralBasis_infinitePlace | exact GlobalTheory.CompanionTheory.SW.ThW.exists_integralBasis_infinitePlace | (intros; apply GlobalTheory.CompanionTheory.SW.ThW.exists_integralBasis_infinitePlace <;> assumption)
