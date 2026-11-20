import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.HighestVectorsRegularLine
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WtRInjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDimensionalOfHom
open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG

namespace GlobalTheory.CompanionTheory.HomTrace

/- English proof (translation)
Establish `h : (LinearMap.pi fun i => S i ∘ₗ LinearMap.proj i) = ∑ i, (LinearMap.single ℂ P i) ∘ₗ (S i ∘ₗ LinearMap.proj i)`. Use `LinearMap.ext fun x => funext fun j => ?_` and prove the remaining obligations. Simplify using `only [LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.sum_apply, Finset.sum_apply]`. Rewrite using `[Finset.sum_eq_single j]`. Simplify using the standard rewrite rules.

Introduce `i _ hij`. Simplify using `[Pi.single_eq_of_ne hij.symm]`. Simplify using the standard rewrite rules. Rewrite using `[h, map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[LinearMap.trace_comp_comm']`. Establish `h2 : (S i ∘ₗ LinearMap.proj i) ∘ₗ LinearMap.single ℂ P i = S i`. Use `LinearMap.ext fun x => ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Rewrite using `[h2]`.
-/
theorem trace_pi_blocks {ι : Type} [Fintype ι] [DecidableEq ι] (P : ι → Type)
    [∀ i, AddCommGroup (P i)] [∀ i, Module ℂ (P i)] [∀ i, FiniteDimensional ℂ (P i)]
    (S : ∀ i, P i →ₗ[ℂ] P i) :
    LinearMap.trace ℂ (∀ i, P i) (LinearMap.pi fun i => S i ∘ₗ LinearMap.proj i) =
      ∑ i, LinearMap.trace ℂ (P i) (S i) := by
  have h : (LinearMap.pi fun i => S i ∘ₗ LinearMap.proj i) =
      ∑ i, (LinearMap.single ℂ P i) ∘ₗ (S i ∘ₗ LinearMap.proj i) := by
    refine LinearMap.ext fun x => funext fun j => ?_
    simp only [LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply,
      LinearMap.sum_apply, Finset.sum_apply]
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij
      simp [Pi.single_eq_of_ne hij.symm]
    · simp
  rw [h, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.trace_comp_comm']
  have h2 : (S i ∘ₗ LinearMap.proj i) ∘ₗ LinearMap.single ℂ P i = S i := by
    refine LinearMap.ext fun x => ?_
    simp
  rw [h2]

/- English proof (translation)
Introduce `ι _ _ I W H _ _ _ _ _ _ _ _ _ R F a b hF`. Use `haveI hP : FiniteDimensional ℂ (∀ i, W i →ₗ[ℂ] H i) := LinearEquiv.finiteDimensional R`. Use `haveI hHom : ∀ i, FiniteDimensional ℂ (W i →ₗ[ℂ] H i) := fun i => Module.Finite.of_surjective (LinearMap.proj (R := ℂ) (φ := fun i => W i →ₗ[ℂ] H i) i) (fun y => ⟨Pi.single i y, by simp⟩)`. Use `haveI hH : ∀ i, FiniteDimensional ℂ (H i) := fun i => finiteDimensional_of_hom (W i) (H i)`. Use `⟨hH, ?_⟩` and prove the remaining obligations.

Establish `hconj : R.conj F = LinearMap.pi fun i => sandwich (a i) (b i) ∘ₗ LinearMap.proj i`. Rewrite using `[LinearEquiv.conj_apply]`. Use `LinearMap.ext fun f => funext fun i => ?_` and prove the remaining obligations. Use `hF (R.symm f) i` as an intermediate fact. Simplify using `using this`.

Rewrite using `[← LinearMap.trace_conj' F R, hconj, trace_pi_blocks]`. Conclude with `Finset.sum_congr rfl fun i _ => trace_sandwich (a i) (b i)`.
-/
theorem trace_of_block_sandwich : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (I : Type) (W H : ι → Type) [AddCommGroup I] [Module ℂ I] [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)] [∀ i, AddCommGroup (H i)] [∀ i, Module ℂ (H i)] [FiniteDimensional ℂ I] [∀ i, FiniteDimensional ℂ (W i)] [∀ i, Nontrivial (W i)] (R : I ≃ₗ[ℂ] ∀ i, W i →ₗ[ℂ] H i) (F : I →ₗ[ℂ] I) (a : ∀ i, H i →ₗ[ℂ] H i) (b : ∀ i, W i →ₗ[ℂ] W i), (∀ x i, R (F x) i = a i ∘ₗ R x i ∘ₗ b i) → (∀ i, FiniteDimensional ℂ (H i)) ∧ LinearMap.trace ℂ I F = ∑ i, LinearMap.trace ℂ (W i) (b i) * LinearMap.trace ℂ (H i) (a i) := by
  intro ι _ _ I W H _ _ _ _ _ _ _ _ _ R F a b hF
  haveI hP : FiniteDimensional ℂ (∀ i, W i →ₗ[ℂ] H i) := LinearEquiv.finiteDimensional R
  haveI hHom : ∀ i, FiniteDimensional ℂ (W i →ₗ[ℂ] H i) := fun i =>
    Module.Finite.of_surjective (LinearMap.proj (R := ℂ) (φ := fun i => W i →ₗ[ℂ] H i) i)
      (fun y => ⟨Pi.single i y, by simp⟩)
  haveI hH : ∀ i, FiniteDimensional ℂ (H i) := fun i => finiteDimensional_of_hom (W i) (H i)
  refine ⟨hH, ?_⟩
  have hconj : R.conj F =
      LinearMap.pi fun i => sandwich (a i) (b i) ∘ₗ LinearMap.proj i := by
    rw [LinearEquiv.conj_apply]
    refine LinearMap.ext fun f => funext fun i => ?_
    have := hF (R.symm f) i
    simpa using this
  rw [← LinearMap.trace_conj' F R, hconj, trace_pi_blocks]
  exact Finset.sum_congr rfl fun i _ => trace_sandwich (a i) (b i)

end GlobalTheory.CompanionTheory.HomTrace
