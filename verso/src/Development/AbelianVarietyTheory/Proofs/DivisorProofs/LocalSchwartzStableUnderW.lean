import Mathlib
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogAbsEEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSpaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatLocalApproximationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterAtUniformizerNotRootOfUnityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalThetaGoodPlaceLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedPairThetaLatticeSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearBarFunctionalGoodPlace
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearBarLocalThetaFactorStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

/- English proof (translation)
Introduce `hP F E _ _ _ _ _ σ B a a' G X om om' hT v _ t h hh φ hφ φ₁ hφ₁ hA`. Take `⟨hφSB, ι, hι, hsupp⟩` from `hφ`. Use `⟨hφ₁, ι, hι, fun Y hY => ?_⟩` and prove the remaining obligations. Establish `h1 : (1 : UA σ G.V'.J) ∈ UAt σ G.V' (evFin F v)`. Introduce `u _`.

Simplify using `[mat]`. Take `⟨c, P, Q, hPQ⟩` from `GlobalTheory.T.linear_bar_local_theta_factor hP F E σ B a a' G X om om' hT v t ι hι 1 h1 h hh φ hφSB φ₁ hφ₁ hA`. Establish `hr : (P.1 * Y * Q.1).rank = Y.rank`. Rewrite using `[Matrix.rank_mul_eq_left_of_isUnit_det _ _ ((Matrix.isUnit_iff_isUnit_det _).1 Q.isUnit), Matrix.rank_mul_eq_right_of_isUnit_det _ _ ((Matrix.isUnit_iff_isUnit_det _).1 P.isUnit)]`. Rewrite using `[hPQ, hsupp _ (by rw [hr]; exact hY), mul_zero]`.
-/
theorem _root_.GlobalTheory.T.local_schwartz_stable_under_W : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ v, X.Good v → ∀ t : E →ₐ[F] Fv F v, ∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ G.M'.SoLoc B.ψ t, ∀ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v), Acts (evFin F v) (om' (1, h)) φ φ₁ → φ₁ ∈ G.M'.SoLoc B.ψ t := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hT v _ t h hh φ hφ φ₁ hφ₁ hA
  obtain ⟨hφSB, ι, hι, hsupp⟩ := hφ
  refine ⟨hφ₁, ι, hι, fun Y hY => ?_⟩
  have h1 : (1 : UA σ G.V'.J) ∈ UAt σ G.V' (evFin F v) := by
    intro u _
    simp [mat]
  obtain ⟨c, P, Q, hPQ⟩ := GlobalTheory.T.linear_bar_local_theta_factor hP F E σ B a a' G X om om' hT v t ι hι 1 h1 h hh φ hφSB φ₁ hφ₁ hA
  have hr : (P.1 * Y * Q.1).rank = Y.rank := by
    rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ ((Matrix.isUnit_iff_isUnit_det _).1 Q.isUnit),
      Matrix.rank_mul_eq_right_of_isUnit_det _ _ ((Matrix.isUnit_iff_isUnit_det _).1 P.isUnit)]
  rw [hPQ, hsupp _ (by rw [hr]; exact hY), mul_zero]
