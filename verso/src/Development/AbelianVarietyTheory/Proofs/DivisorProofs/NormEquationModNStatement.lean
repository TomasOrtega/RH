import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormEquationModN
import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.NormSurjMod.exists_mul_bar_sub_eq_nsmul` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FNormEquationModN.lean&line=123#L123)
-/
theorem _root_.GlobalTheory.T.norm_equation_mod_n : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (N : ℕ), 0 < N → ∀ u : 𝓞 E, (∃ b : 𝓞 E, H.bar u - u = N • b) → (∃ v b : 𝓞 E, u * v - 1 = N • b) → ∃ x b : 𝓞 E, x * H.bar x - u = N • b := by
  first | exact @GlobalTheory.NormSurjMod.exists_mul_bar_sub_eq_nsmul | exact GlobalTheory.NormSurjMod.exists_mul_bar_sub_eq_nsmul | (intros; apply GlobalTheory.NormSurjMod.exists_mul_bar_sub_eq_nsmul <;> assumption)
