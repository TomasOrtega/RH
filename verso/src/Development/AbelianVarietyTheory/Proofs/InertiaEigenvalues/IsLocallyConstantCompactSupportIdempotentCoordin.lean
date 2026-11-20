import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WHyp
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.Hyp

/- English proof (translation)
Introduce `F E _ _ _ _ _ A e h1 h2`. Set `ι : A.K →ₗ[F] A.L` to `(Algebra.linearMap A.K A.L).restrictScalars F`. Set `f : (A.K × A.K) →ₗ[F] A.L` to `LinearMap.mulRight F e ∘ₗ ι ∘ₗ LinearMap.fst F A.K A.K + LinearMap.mulRight F (1 - e) ∘ₗ ι ∘ₗ LinearMap.snd F A.K A.K`. Set `tr : A.L →ₗ[F] A.K` to `(Algebra.trace A.K A.L).restrictScalars F`. Set `g : A.L →ₗ[F] A.K × A.K` to `LinearMap.prod (tr ∘ₗ LinearMap.mulRight F e) (tr ∘ₗ LinearMap.mulRight F (1 - e))`.

Use `haveI : ContinuousAdd A.L := IsModuleTopology.toContinuousAdd F A.L`. Establish `hf : ∀ p, f p = cc A e p` using `fun p => rfl`. Establish `hg : ∀ y, g y = ci A e y` using `fun y => rfl`. Establish `cf : Continuous (cc A e)`. Use `IsModuleTopology.continuous_of_linearMap f` as an intermediate fact.

Simplify `this` using `[funext hf]`. Establish `cg : Continuous (ci A e)`. Use `IsModuleTopology.continuous_of_linearMap g` as an intermediate fact. Simplify `this` using `[funext hg]`. Set `H : (A.K × A.K) ≃ₜ A.L` to `{ toFun := cc A e, invFun := ci A e, left_inv := h1, right_inv := h2, continuous_toFun := cf, continuous_invFun := cg }`.

Use `⟨fun φ hφ => ⟨hφ.1.comp_continuous cf, hφ.2.comp_homeomorph H⟩, fun Φ hΦ => ⟨hΦ.1.comp_continuous cg, hΦ.2.comp_homeomorph H.symm⟩⟩` and prove the remaining obligations.
-/
theorem isTest_coord : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (e : A.L), (∀ p, Hyp.ci A e (Hyp.cc A e p) = p) → (∀ y, Hyp.cc A e (Hyp.ci A e y) = y) → (∀ φ : A.L → ℂ, IsTest φ → IsTest (fun p => φ (Hyp.cc A e p))) ∧ ∀ Φ : A.K × A.K → ℂ, IsTest Φ → IsTest (fun y => Φ (Hyp.ci A e y)) := by
  intro F E _ _ _ _ _ A e h1 h2
  let ι : A.K →ₗ[F] A.L := (Algebra.linearMap A.K A.L).restrictScalars F
  let f : (A.K × A.K) →ₗ[F] A.L :=
    LinearMap.mulRight F e ∘ₗ ι ∘ₗ LinearMap.fst F A.K A.K +
      LinearMap.mulRight F (1 - e) ∘ₗ ι ∘ₗ LinearMap.snd F A.K A.K
  let tr : A.L →ₗ[F] A.K := (Algebra.trace A.K A.L).restrictScalars F
  let g : A.L →ₗ[F] A.K × A.K :=
    LinearMap.prod (tr ∘ₗ LinearMap.mulRight F e) (tr ∘ₗ LinearMap.mulRight F (1 - e))
  haveI : ContinuousAdd A.L := IsModuleTopology.toContinuousAdd F A.L
  have hf : ∀ p, f p = cc A e p := fun p => rfl
  have hg : ∀ y, g y = ci A e y := fun y => rfl
  have cf : Continuous (cc A e) := by
    have := IsModuleTopology.continuous_of_linearMap f
    simpa [funext hf] using this
  have cg : Continuous (ci A e) := by
    have := IsModuleTopology.continuous_of_linearMap g
    simpa [funext hg] using this
  let H : (A.K × A.K) ≃ₜ A.L :=
    { toFun := cc A e, invFun := ci A e, left_inv := h1, right_inv := h2,
      continuous_toFun := cf, continuous_invFun := cg }
  refine ⟨fun φ hφ => ⟨hφ.1.comp_continuous cf, hφ.2.comp_homeomorph H⟩,
    fun Φ hΦ => ⟨hΦ.1.comp_continuous cg, hΦ.2.comp_homeomorph H.symm⟩⟩

end GlobalTheory.JR.Hyp
