import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteUnitaryTorusNormClassesAtAllPlaces
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHasCls
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FFiniteUnitaryTorusNormClassesAtAllPlaces.lean&line=216#L216)
-/
theorem _root_.GlobalTheory.T.finite_unitaryTorusNormClasses_at_all_places : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (r : ℕ) (P : PPol σ r), (∀ v : HeightOneSpectrum (𝓞 F), Finite (Cls P (Fv F v))) ∧ ∀ w : InfinitePlace F, Finite (Cls P w.Completion) := by
  first | exact @GlobalTheory.SqCls.finite_cls | exact GlobalTheory.SqCls.finite_cls | (intros; apply GlobalTheory.SqCls.finite_cls <;> assumption)
