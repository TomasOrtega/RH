import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
import Formalism.SharpRestriction.GlobalTheoremInputs
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.JointConditionTameBound
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CrysOnCond
import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BaseSizes
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GlobalCore
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CentralIdemCoeff
import Formalism.SharpRestriction.LevelLetterCocycles.IdempotentChoiceDepthZero
import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
import Formalism.SharpRestriction.LevelLetterCocycles.AdmissibleParameterJ
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CoefficientCompatibilityOf
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ResidualIrreducibilityFormsEquivalent
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanRepMatrixEqTopOfAbsIrreducible
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink GlobalTheory.Pass GlobalTheory.Cut

noncomputable section

namespace GlobalTheory.AdmGThreeRest

/- English proof (translation)
Introduce `l _ a ρ h`. Break down `Nat.eq_zero_or_pos a with ha | ha` into its components or cases. Substitute `ha` using the available equality. Conclude with `Subsingleton.elim _ _`. Apply `GlobalTheory.BurnsideField.span_mat_eq_top_of_isIrrSub ρ` to reduce the goal to its premises.

Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `hb`. Establish `: (Pi.single (⟨0, ha⟩ : Fin a) (1 : CyclotomicNorms.Fbar l) : Fin a → CyclotomicNorms.Fbar l) ∈ (⊤ : Submodule (CyclotomicNorms.Fbar l) (Fin a → CyclotomicNorms.Fbar l))` using `trivial`. Rewrite `this` using `[hb, Submodule.mem_bot]`. Establish `h1` using `congrFun this ⟨0, ha⟩`.

Simplify using `at h1`. Introduce `g x _`. Discharge the goal by the elementary cases of `trivial`. Introduce `W' _ hW'`. Conclude with `h W' (fun g _ x hx => hW' g x hx)`.
-/
theorem litBurnside_host (D : D7) : LitBurnside (G D.host.E D.nd.Om) := by
  intro l _ a ρ h
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha
    exact Subsingleton.elim _ _
  · apply GlobalTheory.BurnsideField.span_mat_eq_top_of_isIrrSub ρ
    refine ⟨?_, ?_, ?_⟩
    · intro hb
      have : (Pi.single (⟨0, ha⟩ : Fin a) (1 : CyclotomicNorms.Fbar l) : Fin a → CyclotomicNorms.Fbar l) ∈ (⊤ : Submodule (CyclotomicNorms.Fbar l) (Fin a → CyclotomicNorms.Fbar l)) := trivial
      rw [hb, Submodule.mem_bot] at this
      have h1 := congrFun this ⟨0, ha⟩
      simp at h1
    · intro g x _; trivial
    · intro W' _ hW'
      exact h W' (fun g _ x hx => hW' g x hx)

/- English proof (translation)
Introduce `D L nch i r π ρ fa _ _ hHG hr _ hρ`. Take `⟨hcont, e, he⟩` from `hρ`. Establish `hdec : TruncatedSeriesCountingIdentities.SemisimpleDecomposition (D` using `D) i r (fun _ => ρ) π := ⟨e, fun g u => he g u⟩`. Conclude with `galois_condition_three_of D i r (fun _ => ρ) π fa.Conclusion1.1 hr hdec hcont hHG fa.rhoBar (litBurnside_host D) (fa.duties.2.1 i r hr)`.
-/
theorem main : ∀ (D : D7) (L : SizeData₂ D) (nch : NChoice D) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i) (ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O i)), GlobalTheory.NFacts.Facts D nch → LevelStarExponents.lStar L < (D.nd.l i : ℝ) → (∀ k, D.nd.l i ≠ D.host.g k) → HG D.nd D.naut i → GoodR D.nd i r → π ∈ D.nd.Z i → GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.IsRankRPart D i (r π) ρ → TruncatedSeriesCountingIdentities.admG3 i r (fun _ => ρ) π := by
  intro D L nch i r π ρ fa _ _ hHG hr _ hρ
  obtain ⟨hcont, e, he⟩ := hρ
  have hdec : TruncatedSeriesCountingIdentities.SemisimpleDecomposition (D := D) i r (fun _ => ρ) π := ⟨e, fun g u => he g u⟩
  exact galois_condition_three_of D i r (fun _ => ρ) π fa.Conclusion1.1 hr hdec hcont hHG fa.rhoBar (litBurnside_host D)
    (fa.duties.2.1 i r hr)

end GlobalTheory.AdmGThreeRest
