import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TemperedWeightSpaceBound
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RestrictHomApply
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.WeilDeligne.PrimDecomp GlobalTheory.LocLanglands
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.WeilDeligne.PrimDecomp.exists_top_weight` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FTemperedWeightSpaceBound.lean&line=29#L29)
-/
theorem _root_.GlobalTheory.T.tempered_weight_space_bound : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (a : WDRep h V), a.Tempered → Nontrivial V → ∃ m : ℕ, wtSpace a (-(m : ℤ)) ≠ ⊥ ∧ ∀ k : ℤ, (m : ℤ) < k → wtSpace a k = ⊥ := by
  first | exact @GlobalTheory.WeilDeligne.PrimDecomp.exists_top_weight | exact GlobalTheory.WeilDeligne.PrimDecomp.exists_top_weight | (intros; apply GlobalTheory.WeilDeligne.PrimDecomp.exists_top_weight <;> assumption)
