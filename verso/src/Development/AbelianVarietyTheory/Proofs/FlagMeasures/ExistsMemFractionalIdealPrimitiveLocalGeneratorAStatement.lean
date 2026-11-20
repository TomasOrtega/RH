import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsMemFractionalIdealPrimitiveLocalGeneratorA
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FExistsMemFractionalIdealPrimitiveLocalGeneratorA.lean&line=150#L150)
-/
theorem _root_.GlobalTheory.T.exists_mem_fractionalIdeal_primitive_local_generator' : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], Module.finrank F E = 2 → ∀ (c : FractionalIdeal (nonZeroDivisors (𝓞 E)) E), c ≠ 0 → ∀ N : 𝓞 E, N ≠ 0 → ∃ a : E, a ∈ c ∧ (∀ Q : Ideal (𝓞 E), Q.IsMaximal → N ∈ Q → a ∉ (Q : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) * c) ∧ ∀ p : Ideal (𝓞 F), p.IsMaximal → a ∉ ((Ideal.map (algebraMap (𝓞 F) (𝓞 E)) p : Ideal (𝓞 E)) : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) * c := by
  first | exact @GlobalTheory.exists_mem_fractionalIdeal_primitive_local_generator | exact GlobalTheory.exists_mem_fractionalIdeal_primitive_local_generator | (intros; apply GlobalTheory.exists_mem_fractionalIdeal_primitive_local_generator <;> assumption)
