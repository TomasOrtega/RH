import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFiniteGaloisContainsRootsOfUnits
import Mathlib
open NumberField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.KummerUnits.exists_finite_galois_mem_of_pow_eq_unit` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FExistsFiniteGaloisContainsRootsOfUnits.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.exists_finite_galois_contains_roots_of_units : ∀ (E F Ω : Type) [Field E] [NumberField E] [Field F] [Field Ω] [IsAlgClosed Ω]
    [Algebra E F] [Algebra E Ω] [Algebra F Ω] [IsScalarTower E F Ω] (M : ℕ), 0 < M →
    (∃ ζ : F, IsPrimitiveRoot ζ M) → ∃ L : IntermediateField F Ω, FiniteDimensional F L ∧ IsGalois F L ∧
      ∀ (u : (𝓞 E)ˣ) (w : Ω), w ^ M = algebraMap E Ω ((u : 𝓞 E) : E) → w ∈ L := by
  first | exact @GlobalTheory.KummerUnits.exists_finite_galois_mem_of_pow_eq_unit | exact GlobalTheory.KummerUnits.exists_finite_galois_mem_of_pow_eq_unit | (intros; apply GlobalTheory.KummerUnits.exists_finite_galois_mem_of_pow_eq_unit <;> assumption)
