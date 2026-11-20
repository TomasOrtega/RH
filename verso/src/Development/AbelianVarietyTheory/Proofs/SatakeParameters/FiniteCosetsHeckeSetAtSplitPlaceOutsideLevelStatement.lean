import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteCosetsHeckeSetAtSplitPlaceOutsideLevel
import Mathlib
import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TSetFin.finite_image_tSet` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FFiniteCosetsHeckeSetAtSplitPlaceOutsideLevel.lean&line=123#L123)
-/
theorem _root_.GlobalTheory.T.finite_cosets_heckeSet_at_splitPlace_outside_level : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (J : Subgroup (Formalism.AUTREP.GAf L n)) (χ : J →* ℂˣ) (B : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))), Formalism.L2.NG.HypOutside J χ B → ∀ (s : ReciprocityTheory.Aut.SplitPlace L) (ϖ : s.v.adicCompletion (maximalRealSubfield L)) (k : ℕ), s.v ∉ B → Formalism.AUTREP.IsUnif L s.v ϖ → ((fun x : Formalism.AUTREP.GAf L n => (x : Formalism.AUTREP.GAf L n ⧸ J)) '' Formalism.AUTREP.tSet L n s ϖ k).Finite := by
  first | exact @GlobalTheory.TSetFin.finite_image_tSet | exact GlobalTheory.TSetFin.finite_image_tSet | (intros; apply GlobalTheory.TSetFin.finite_image_tSet <;> assumption)
