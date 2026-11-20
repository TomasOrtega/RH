import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLaurentSeriesSumCongruentModPPow
import Development.AbelianVarietyTheory.Definitions.Foundations.ApplyEqOfMemAdjoin
import Development.AbelianVarietyTheory.Definitions.Foundations.IsTopWTopWOfExists
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AlgebraMapZpInjective
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois GlobalTheory.GeoFix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.GeoFix.exists_cong_lau` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FExistsLaurentSeriesSumCongruentModPPow.lean&line=35#L35)
-/
theorem _root_.GlobalTheory.T.exists_laurentSeries_sum_congruent_mod_p_pow : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω] (T : Tower p Ω) (n : ℕ) (ψ : O0 p →+* Ω), IsReb T n ψ → ∀ (d : ℕ) (e : Fin d → Ω) (b : Fin d → O0 p), (∀ t, IsInt p (e t)) → ∀ K : ℕ, ∃ a : Fin d → Lau p, Cong p K (∑ t, e t * ψ (b t)) (∑ t, e t * ψ (algebraMap (Lau p) (O0 p) (a t))) := by
  first | exact @GlobalTheory.GeoFix.exists_cong_lau | exact GlobalTheory.GeoFix.exists_cong_lau | (intros; apply GlobalTheory.GeoFix.exists_cong_lau <;> assumption)
