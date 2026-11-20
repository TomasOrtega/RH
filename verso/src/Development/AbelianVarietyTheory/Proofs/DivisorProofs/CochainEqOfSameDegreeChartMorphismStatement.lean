import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CochainEqOfSameDegreeChartMorphism
import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
import Development.AbelianVarietyTheory.Definitions.Divisors.FstTszeSec
open CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts TopologicalSpace
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.AnPer.Charts.cochain_eq_ptHom` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCochainEqOfSameDegreeChartMorphism.lean&line=36#L36)
-/
theorem _root_.GlobalTheory.T.cochain_eq_of_same_degree_chartMorphism : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F) (h : C1 K.Oc) (l : Λ), (∀ (k : K.K) (T : K.Obj) (χ : K.jet k ⟶ T), χ.deg = l → h _ _ (jet0 k ≫ χ) = h _ _ (jet1 k ≫ χ)) → ∀ (k : K.K) (T : K.Obj) (f : K.triv k ⟶ T), f.deg = l → h _ _ f = h _ _ (ptHom T (Charts.Hom.le f)) := by
  first | exact @GlobalTheory.AnPer.Charts.cochain_eq_ptHom | exact GlobalTheory.AnPer.Charts.cochain_eq_ptHom | (intros; apply GlobalTheory.AnPer.Charts.cochain_eq_ptHom <;> assumption)
