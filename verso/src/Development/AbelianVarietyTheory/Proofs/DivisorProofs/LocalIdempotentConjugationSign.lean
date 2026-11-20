import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinPartIdemMulMemIff
import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.SwapAtSplit

open scoped TensorProduct
open GlobalTheory.EmbChart (atPlace tensAt compFin_tensAt tensAt_mul_right sigR_tensAt)

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ h v t`. Use `set y : Fv F v ⊗[F] E := (splitAlgEquiv h t).symm (1, -1) with hy`. Establish `hQ : algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1) = tensAt E v 1` using `rfl`. Establish `hpi : ∀ τ : E →ₐ[F] Fv F v, piW τ (tensAt E v y) = splitProj τ y` using `fun τ => by`. Express the relevant statement in the definitionally equal form `splitProj τ (compFin F E v (tensAt E v y)) = _`.

Rewrite using `[compFin_tensAt]`. Use `⟨tensAt E v y, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Algebra.smul_def, mul_comm, tensAt_mul_right]`. Establish `e : compFin F E v (algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1)) = 1`. Express the relevant statement in the definitionally equal form `GlobalTheory.AdelicU.evFin F v (GlobalTheory.LatVac.liftV v 1) ⊗ₜ[F] (1 : E) = 1`.

Rewrite using `[GlobalTheory.LatVac.evFin_liftV]`. Both sides reduce to the same expression. Rewrite using `[e, mul_one]`. Rewrite using `[hQ, tensAt_mul_right, compFin_tensAt]`. Use `congr 1`.

Conclude with `split_ext h t (by simp [hy]) (by simp [hy])`. Establish `hc : cA σ (tensAt E v y) = tensAt E v (sigR (Fv F v) σ y)` using `sigR_tensAt v σ y`. Rewrite using `[hc, hQ, tensAt_mul_right, compFin_tensAt, ← map_neg]`. Use `congr 1`. Use `split_ext h t ?_ ?_` and prove the remaining obligations.

Rewrite using `[map_mul, ← splitProj_comp, map_neg, map_one]`. Simplify using `[hy]`. Rewrite using `[map_mul, splitProj_comp_sigR h, map_neg, map_one]`. Simplify using `[hy]`. Rewrite using `[hpi]`.

Simplify using `[hy]`. Rewrite using `[hpi]`. Simplify using `[hy]`.
-/
theorem exists_swap_elt : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (v : Pl F) (t : E →ₐ[F] Fv F v), ∃ f : AE F E,
      GlobalTheory.LatVac.liftV v (1 : Fv F v) • f = f ∧ f * f = algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1) ∧
      f * cA σ f = -algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1) ∧ piW t f = 1 ∧ piW (t.comp σ) f = -1 := by
  intro F E _ _ _ _ _ σ h v t
  set y : Fv F v ⊗[F] E := (splitAlgEquiv h t).symm (1, -1) with hy
  have hQ : algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1) = tensAt E v 1 := rfl
  have hpi : ∀ τ : E →ₐ[F] Fv F v, piW τ (tensAt E v y) = splitProj τ y := fun τ => by
    change splitProj τ (compFin F E v (tensAt E v y)) = _
    rw [compFin_tensAt]
  refine ⟨tensAt E v y, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Algebra.smul_def, mul_comm, tensAt_mul_right]
    have e : compFin F E v (algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1)) = 1 := by
      change GlobalTheory.AdelicU.evFin F v (GlobalTheory.LatVac.liftV v 1) ⊗ₜ[F] (1 : E) = 1
      rw [GlobalTheory.LatVac.evFin_liftV]; rfl
    rw [e, mul_one]
  · rw [hQ, tensAt_mul_right, compFin_tensAt]
    congr 1
    exact split_ext h t (by simp [hy]) (by simp [hy])
  · have hc : cA σ (tensAt E v y) = tensAt E v (sigR (Fv F v) σ y) := sigR_tensAt v σ y
    rw [hc, hQ, tensAt_mul_right, compFin_tensAt, ← map_neg]
    congr 1
    refine split_ext h t ?_ ?_
    · rw [map_mul, ← splitProj_comp, map_neg, map_one]; simp [hy]
    · rw [map_mul, splitProj_comp_sigR h, map_neg, map_one]; simp [hy]
  · rw [hpi]; simp [hy]
  · rw [hpi]; simp [hy]

end GlobalTheory.SwapAtSplit
