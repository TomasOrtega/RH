import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormMemNormGroup
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CTUnitsLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonsplitCentraliserNormElement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetGramRatOneNeZero
import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLemmas.ToComplBijective
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField PositivityTheory.BCUSide.HermitianLocalForms
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FNormMemNormGroup.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.norm_mem_norm_group : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (k : Type) [Field k] [Algebra (maximalRealSubfield E) k] (r : ℕ) (Q : SelfRecip E r) (x : (k ⊗[(maximalRealSubfield E)] plus Q)ˣ), x ∈ norms Q k → Units.map (Algebra.norm k : k ⊗[(maximalRealSubfield E)] plus Q →* k) x ∈ GlobalTheory.QuadSymbol.normGroup (maximalRealSubfield E) E k := by
  first | exact @GlobalTheory.CompanionTheory.NormClassNorm.norm_mem_normGroup | exact GlobalTheory.CompanionTheory.NormClassNorm.norm_mem_normGroup | (intros; apply GlobalTheory.CompanionTheory.NormClassNorm.norm_mem_normGroup <;> assumption)
