import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AfIsoEqZeroIff
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TrueColumnChoicesHeckeCharReferenceEqOne
open NumberField IsDedekindDomain Formalism.L2.DIV
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FAfIsoEqZeroIff.lean&line=104#L104)
-/
theorem _root_.GlobalTheory.T.afIso_ringEquiv_eq_zero_iff : ∀ (F E F' E' : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [Field F'] [NumberField F'] [Field E'] [NumberField E'] [Algebra F' E'] (s : E ≃+* E') (φ : AfE F E ≃+* AfE F' E'), (∀ x : E, φ (x ⊗ₜ[F] 1) = s x ⊗ₜ[F'] 1) → (∀ y, φ y ∈ RInt F' E' ↔ y ∈ RInt F E) → ∀ y ∈ RInt F E, ∀ P : HeightOneSpectrum (𝓞 E), (GlobalTheory.Mem.Col2.afIso F' E' (φ y) (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv s) P) = 0 ↔ GlobalTheory.Mem.Col2.afIso F E y P = 0) := by
  first | exact @GlobalTheory.AfeLocTr.afIso_eq_zero_iff | exact GlobalTheory.AfeLocTr.afIso_eq_zero_iff | (intros; apply GlobalTheory.AfeLocTr.afIso_eq_zero_iff <;> assumption)
