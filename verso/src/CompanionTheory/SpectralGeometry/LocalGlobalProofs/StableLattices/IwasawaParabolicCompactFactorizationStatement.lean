import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IwasawaParabolicCompactFactorization
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HsConjTranspose
open Matrix
open CompanionTheory.RgExh.Dec CompanionTheory.RgExh.Dec.L ReciprocityTheory.ChartRestriction.DS GlobalTheory.CompanionTheory.PSubFlag GlobalTheory.CompanionTheory.UGeo
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.UGeo.iwasawa_psub` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FStableLattices%2FIwasawaParabolicCompactFactorization.lean&line=33#L33)
-/
theorem _root_.GlobalTheory.T.iwasawa_parabolic_compact_factorization : ∀ (n : ℕ) (ε : Fin n → Bool) (A : Matrix (Fin n) (Fin n) ℂ), IsGrad ε A → ∀ g : S7.UJ ε, ∃ (x : PSub ε A) (k : S7.KG ε), g = (x : S7.UJ ε) * (k : S7.UJ ε) := by
  first | exact @GlobalTheory.CompanionTheory.UGeo.iwasawa_psub | exact GlobalTheory.CompanionTheory.UGeo.iwasawa_psub | (intros; apply GlobalTheory.CompanionTheory.UGeo.iwasawa_psub <;> assumption)
