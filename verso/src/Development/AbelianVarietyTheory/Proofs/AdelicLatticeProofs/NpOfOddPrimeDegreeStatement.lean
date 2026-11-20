import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.NpOfOddPrimeDegree
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FAdelicLatticeProofs%2FNpOfOddPrimeDegree.lean&line=42#L42)
-/
theorem _root_.GlobalTheory.T.np_of_odd_prime_degree' : ∀ (p : ℕ) (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E], p.Prime → p ≠ 2 → Module.finrank F E = p → NP F E := by
  first | exact @GlobalTheory.CNorm.np_of_odd_prime_degree | exact GlobalTheory.CNorm.np_of_odd_prime_degree | (intros; apply GlobalTheory.CNorm.np_of_odd_prime_degree <;> assumption)
