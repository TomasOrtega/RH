import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DecompositionGroupMulEquivLocalGaloisCyclotomic
import Mathlib
import Formalism.GaloisCohomology.LocalTateDualityK
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.DecLocal.exists_mulEquiv_cyc` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FDecompositionGroupMulEquivLocalGaloisCyclotomic.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.decompositionGroup_mulEquiv_localGalois_cyclotomic : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (v : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω), ((l : ℕ) : 𝓞 F) ∈ v.asIdeal → IsPlaceOver A v → ∃ (K : IntermediateField ℚ_[l] (PadicAlgCl l)) (_ : FiniteDimensional ℚ_[l] K) (e : Dec (F := F) A ≃* GK l K), Continuous e ∧ Continuous e.symm ∧ ∀ (r : ℕ) (g : Dec (F := F) A), cycK l K r (e g) = cycMod F Ω l r (g : G F Ω) := by
  first | exact @GlobalTheory.DecLocal.exists_mulEquiv_cyc | exact GlobalTheory.DecLocal.exists_mulEquiv_cyc | (intros; apply GlobalTheory.DecLocal.exists_mulEquiv_cyc <;> assumption)
