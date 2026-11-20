import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RatVInjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZeroMemBoxF
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov GlobalTheory.CompanionTheory.RedCov.Simple
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.RedCov.Simple.BoxCpt

/- English proof (translation)
Establish `hi` using `NumberField.InfinitePlace.Completion.isometry_extensionEmbedding w`. Establish `hce` using `hi.isClosedEmbedding`. Use `⟨fun x r => ?_⟩` and prove the remaining obligations. Establish `e : Metric.closedBall x r = NumberField.InfinitePlace.Completion.extensionEmbedding w ⁻¹' Metric.closedBall (NumberField.InfinitePlace.Completion.extensionEmbedding w x) r`. Use extensionality with `y`.

Simplify using `[Metric.mem_closedBall, hi.dist_eq]`. Rewrite using `[e]`. Conclude with `hce.isCompact_preimage (isCompact_closedBall _ _)`.
-/
theorem properSpace_completion (F : Type) [Field F] [NumberField F] (w : InfinitePlace F) :
    ProperSpace w.Completion := by
  have hi := NumberField.InfinitePlace.Completion.isometry_extensionEmbedding w
  have hce := hi.isClosedEmbedding
  refine ⟨fun x r => ?_⟩
  have e : Metric.closedBall x r = NumberField.InfinitePlace.Completion.extensionEmbedding w ⁻¹'
      Metric.closedBall (NumberField.InfinitePlace.Completion.extensionEmbedding w x) r := by
    ext y
    simp [Metric.mem_closedBall, hi.dist_eq]
  rw [e]
  exact hce.isCompact_preimage (isCompact_closedBall _ _)

/- English proof (translation)
Establish `h1 : IsCompact (Set.univ.pi fun w : InfinitePlace F => Metric.closedBall (0 : w.Completion) 1)` using `by haveI : ∀ w : InfinitePlace F, ProperSpace w.Completion := fun w => properSpace_completion F w`. Conclude with `isCompact_univ_pi fun w => isCompact_closedBall 0 1`. Establish `h2` using `GroundTheory.Global.isCompact_integralFiniteAdeles F`. Establish `e : boxF F 1 = (Set.univ.pi fun w : InfinitePlace F => Metric.closedBall (0 : w.Completion) 1) ×ˢ (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F))`. Use extensionality with `a`.

Simplify using `only [boxF, Set.mem_setOf_eq]`. Express the relevant statement in the definitionally equal form `_ ↔ (a.1 ∈ (Set.univ.pi fun w : InfinitePlace F => Metric.closedBall (0 : w.Completion) 1) ∧ a.2 ∈ (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)))`. Use `and_congr ⟨fun h => Set.mem_univ_pi.mpr fun w => ?_, fun h w => ?_⟩ Iff.rfl` and prove the remaining obligations. Simplify `h w` using `[Metric.mem_closedBall, dist_zero_right]`. Simplify `Set.mem_univ_pi.mp h w` using `[Metric.mem_closedBall, dist_zero_right]`.

Rewrite using `[e]`. Conclude with `h1.prod h2`.
-/
theorem isCompact_boxF_one (F : Type) [Field F] [NumberField F] : IsCompact (boxF F 1) := by
  have h1 : IsCompact (Set.univ.pi fun w : InfinitePlace F => Metric.closedBall (0 : w.Completion) 1) := by
    haveI : ∀ w : InfinitePlace F, ProperSpace w.Completion := fun w => properSpace_completion F w
    exact isCompact_univ_pi fun w => isCompact_closedBall 0 1
  have h2 := GroundTheory.Global.isCompact_integralFiniteAdeles F
  have e : boxF F 1 = (Set.univ.pi fun w : InfinitePlace F => Metric.closedBall (0 : w.Completion) 1) ×ˢ
      (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) := by
    ext a
    simp only [boxF, Set.mem_setOf_eq]
    change _ ↔ (a.1 ∈ (Set.univ.pi fun w : InfinitePlace F => Metric.closedBall (0 : w.Completion) 1) ∧
      a.2 ∈ (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)))
    refine and_congr ⟨fun h => Set.mem_univ_pi.mpr fun w => ?_, fun h w => ?_⟩ Iff.rfl
    · simpa [Metric.mem_closedBall, dist_zero_right] using h w
    · simpa [Metric.mem_closedBall, dist_zero_right] using Set.mem_univ_pi.mp h w
  rw [e]
  exact h1.prod h2

/- English proof (translation)
Use `set b := Algebra.TensorProduct.basis (AF F) (Module.finBasis F E) with hb`. Use `haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩`. Use `haveI : ContinuousAdd (AF F ⊗[F] E) := IsModuleTopology.toContinuousAdd (AF F) _`. Use `haveI : ContinuousSMul (AF F) (AF F ⊗[F] E) := inferInstance`. Establish `hK : IsCompact (Set.univ.pi fun _ : Fin (Module.finrank F E) => boxF F 1)` using `isCompact_univ_pi fun _ => isCompact_boxF_one F`.

Establish `hc : Continuous ((b.equivFun.symm : (Fin (Module.finrank F E) → AF F) →ₗ[AF F] AF F ⊗[F] E))` using `IsModuleTopology.continuous_of_linearMap _`. Establish `e : boxE F E 1 = b.equivFun.symm '' (Set.univ.pi fun _ => boxF F 1)`. Use extensionality with `x`. Simplify using `only [boxE, Set.mem_setOf_eq, Set.mem_image, Set.mem_univ_pi, ← hb]`. Prove the components needed by the constructor for the conclusion.

Introduce `hx`. Conclude with `⟨b.equivFun x, fun k => by rw [Module.Basis.equivFun_apply]; exact hx k, b.equivFun.symm_apply_apply x⟩`. Introduce and unpack `⟨y, hy, rfl⟩ k`. Establish `h : b.repr (b.equivFun.symm y) k = y k`. Rewrite using `[← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]`.

Rewrite using `[h]`. Conclude with `hy k`. Rewrite using `[e]`. Conclude with `hK.image hc`.
-/
theorem isCompact_boxE_one (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    IsCompact (boxE F E 1) := by
  set b := Algebra.TensorProduct.basis (AF F) (Module.finBasis F E) with hb
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (AF F ⊗[F] E) := IsModuleTopology.toContinuousAdd (AF F) _
  haveI : ContinuousSMul (AF F) (AF F ⊗[F] E) := inferInstance
  have hK : IsCompact (Set.univ.pi fun _ : Fin (Module.finrank F E) => boxF F 1) :=
    isCompact_univ_pi fun _ => isCompact_boxF_one F
  have hc : Continuous
      ((b.equivFun.symm : (Fin (Module.finrank F E) → AF F) →ₗ[AF F] AF F ⊗[F] E)) :=
    IsModuleTopology.continuous_of_linearMap _
  have e : boxE F E 1 = b.equivFun.symm '' (Set.univ.pi fun _ => boxF F 1) := by
    ext x
    simp only [boxE, Set.mem_setOf_eq, Set.mem_image, Set.mem_univ_pi, ← hb]
    constructor
    · intro hx
      exact ⟨b.equivFun x, fun k => by rw [Module.Basis.equivFun_apply]; exact hx k,
        b.equivFun.symm_apply_apply x⟩
    · rintro ⟨y, hy, rfl⟩ k
      have h : b.repr (b.equivFun.symm y) k = y k := by
        rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
      rw [h]
      exact hy k
  rw [e]
  exact hK.image hc

/- English proof (translation)
Introduce `F E _ _ _ _ _`. Conclude with `⟨isCompact_boxF_one F, isCompact_boxE_one F E⟩`.
-/
theorem main : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E],
    IsCompact (boxF F 1) ∧ IsCompact (boxE F E 1) := by
  intro F E _ _ _ _ _
  exact ⟨isCompact_boxF_one F, isCompact_boxE_one F E⟩

end GlobalTheory.CompanionTheory.RedCov.Simple.BoxCpt

end
