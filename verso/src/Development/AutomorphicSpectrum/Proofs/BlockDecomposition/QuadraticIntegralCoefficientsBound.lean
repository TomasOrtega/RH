import Mathlib
import Development.WeilBound.ThetaLifts.LatticeBasics.HypothesesE
import Development.WeilBound.ThetaLifts.LatticeBasics.UnfoldC
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EmbBar
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
open GlobalTheory.CompanionTheory.GodementH

namespace GlobalTheory.CompanionTheory.GodementH

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hCM x`. Take `⟨_, hEc, hfin2, hconj⟩` from `hCM`. Take `⟨τ0⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Establish `hσσ : ∀ z, σ (σ z) = z` using `fun z => τ0.injective (by rw [hconj, hconj, star_star])`. Establish `hσne : ∃ w, σ w ≠ w`.

Assume the negation of the conclusion as `hcon`. Simplify using `only [not_exists, not_not] at hcon`. Establish `hreal : NumberField.ComplexEmbedding.IsReal τ0`. Rewrite using `[NumberField.ComplexEmbedding.isReal_iff]`. Use `RingHom.ext fun w => ?_` and prove the remaining obligations.

Rewrite using `[NumberField.ComplexEmbedding.conjugate_coe_eq]`. Establish `h1` using `hconj τ0 w`. Rewrite `h1` using `[hcon w]`. Conclude with `h1.symm`. Conclude with `InfinitePlace.not_isReal_iff_isComplex.2 (hEc.isComplex (InfinitePlace.mk τ0)) ⟨τ0, hreal, rfl⟩`.

Use `haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)`. Establish `hfix : ∀ z : E, σ z = z → ∃ y : F, algebraMap F E y = z`. Introduce `z hz`. Establish `hSle : Submodule.span F {(1 : E)} ≤ LinearMap.ker (σ.toLinearMap - LinearMap.id)`. Rewrite using `[Submodule.span_le, Set.singleton_subset_iff]`.

Simplify using the standard rewrite rules. Establish `hker : LinearMap.ker (σ.toLinearMap - LinearMap.id) ≠ ⊤`. Introduce `htop`. Take `⟨w, hw⟩` from `hσne`. Establish `hw' : w ∈ LinearMap.ker (σ.toLinearMap - LinearMap.id)` using `htop ▸ Submodule.mem_top`.

Rewrite `hw'` using `[LinearMap.mem_ker]`. Conclude with `hw (sub_eq_zero.1 hw')`. Establish `h1 : Module.finrank F (Submodule.span F {(1 : E)}) = 1` using `finrank_span_singleton one_ne_zero`. Establish `hlt` using `Submodule.finrank_lt hker`. Establish `hge` using `Submodule.finrank_mono hSle`.

Establish `heq` using `Submodule.eq_of_le_of_finrank_eq hSle (by omega)`. Establish `hzk : z ∈ LinearMap.ker (σ.toLinearMap - LinearMap.id)`. Rewrite using `[LinearMap.mem_ker]`. Simplify using `[hz]`. Rewrite `hzk` using `[← heq]`.

Take `⟨c, hc⟩` from `Submodule.mem_span_singleton.1 hzk`. Conclude with `⟨c, by rw [Algebra.algebraMap_eq_smul_one]; exact hc⟩`. Take `⟨y₁, hy₁⟩` from `hfix (x + σ x) (by rw [map_add, hσσ, add_comm])`. Take `⟨y₂, hy₂⟩` from `hfix (x * σ x) (by rw [map_mul, hσσ, mul_comm])`. Use `⟨y₁, y₂, by rw [hy₁, hy₂]; ring, fun v τ => ?_⟩` and prove the remaining obligations.

Establish `key : ∀ y : F, τ (algebraMap F E y) = algebraMap (Fv F v) (FvBar F v) (algebraMap F (Fv F v) y)` using `fun y => by`. Rewrite using `[τ.commutes]`. Conclude with `IsScalarTower.algebraMap_apply F (Fv F v) (FvBar F v) y`. Prove the components needed by the constructor for the conclusion. Rewrite using `[← absBar_algebraMap F v, ← key, hy₁, map_add]`.

Conclude with `absBar_add_le F v _ _`. Rewrite using `[← absBar_algebraMap F v, ← key, hy₂, map_mul]`. Conclude with `absBar_mul F v _ _`.
-/
theorem trace_norm_local_sizes : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ x : E, ∃ y₁ y₂ : F,
    x ^ 2 - algebraMap F E y₁ * x + algebraMap F E y₂ = 0 ∧ ∀ (v : Pl F) (τ : E →ₐ[F] FvBar F v),
      ‖algebraMap F (Fv F v) y₁‖₊ ≤ max (absBar F v (τ x)) (absBar F v (τ (σ x))) ∧
      ‖algebraMap F (Fv F v) y₂‖₊ = absBar F v (τ x) * absBar F v (τ (σ x)) := by
  intro F E _ _ _ _ _ σ hCM x
  obtain ⟨_, hEc, hfin2, hconj⟩ := hCM
  obtain ⟨τ0⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hσσ : ∀ z, σ (σ z) = z := fun z => τ0.injective (by rw [hconj, hconj, star_star])
  have hσne : ∃ w, σ w ≠ w := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    have hreal : NumberField.ComplexEmbedding.IsReal τ0 := by
      rw [NumberField.ComplexEmbedding.isReal_iff]
      refine RingHom.ext fun w => ?_
      rw [NumberField.ComplexEmbedding.conjugate_coe_eq]
      have h1 := hconj τ0 w
      rw [hcon w] at h1
      exact h1.symm
    exact InfinitePlace.not_isReal_iff_isComplex.2 (hEc.isComplex (InfinitePlace.mk τ0)) ⟨τ0, hreal, rfl⟩
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  have hfix : ∀ z : E, σ z = z → ∃ y : F, algebraMap F E y = z := by
    intro z hz
    have hSle : Submodule.span F {(1 : E)} ≤ LinearMap.ker (σ.toLinearMap - LinearMap.id) := by
      rw [Submodule.span_le, Set.singleton_subset_iff]
      simp
    have hker : LinearMap.ker (σ.toLinearMap - LinearMap.id) ≠ ⊤ := by
      intro htop
      obtain ⟨w, hw⟩ := hσne
      have hw' : w ∈ LinearMap.ker (σ.toLinearMap - LinearMap.id) := htop ▸ Submodule.mem_top
      rw [LinearMap.mem_ker] at hw'
      exact hw (sub_eq_zero.1 hw')
    have h1 : Module.finrank F (Submodule.span F {(1 : E)}) = 1 := finrank_span_singleton one_ne_zero
    have hlt := Submodule.finrank_lt hker
    have hge := Submodule.finrank_mono hSle
    have heq := Submodule.eq_of_le_of_finrank_eq hSle (by omega)
    have hzk : z ∈ LinearMap.ker (σ.toLinearMap - LinearMap.id) := by
      rw [LinearMap.mem_ker]
      simp [hz]
    rw [← heq] at hzk
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hzk
    exact ⟨c, by rw [Algebra.algebraMap_eq_smul_one]; exact hc⟩
  obtain ⟨y₁, hy₁⟩ := hfix (x + σ x) (by rw [map_add, hσσ, add_comm])
  obtain ⟨y₂, hy₂⟩ := hfix (x * σ x) (by rw [map_mul, hσσ, mul_comm])
  refine ⟨y₁, y₂, by rw [hy₁, hy₂]; ring, fun v τ => ?_⟩
  have key : ∀ y : F, τ (algebraMap F E y) =
      algebraMap (Fv F v) (FvBar F v) (algebraMap F (Fv F v) y) := fun y => by
    rw [τ.commutes]
    exact IsScalarTower.algebraMap_apply F (Fv F v) (FvBar F v) y
  constructor
  · rw [← absBar_algebraMap F v, ← key, hy₁, map_add]
    exact absBar_add_le F v _ _
  · rw [← absBar_algebraMap F v, ← key, hy₂, map_mul]
    exact absBar_mul F v _ _

end GlobalTheory.CompanionTheory.GodementH
