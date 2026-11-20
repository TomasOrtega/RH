import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.CuspidalMultiplicityOneTotallyComplex
import GroundTheory.AutomorphicForms.CompactSelfAdjoint
import Mathlib.Analysis.InnerProductSpace.Spectrum

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C

/- English proof (translation)
Introduce `H _ _ _ W A hW hA hAW hC η hη`. Establish `hWc : W.topologicalClosure = W` using `hW.submodule_topologicalClosure_eq`. Establish `hPW : ∀ v, prj W v ∈ W`. Introduce `v`. Establish `: prj W v ∈ W.topologicalClosure` using `Submodule.starProjection_apply_mem _ v`.

Rewrite `this` using `[hWc]`. Then use the resulting hypothesis. Establish `hperp : ∀ v, ∀ w ∈ W, inner ℂ w (v - prj W v) = 0`. Introduce `v w hw`. Establish `: v - prj W v ∈ W.topologicalClosureᗮ` using `Submodule.sub_starProjection_mem_orthogonal v`. Conclude with `this w (W.le_topologicalClosure hw)`.

Establish `hfix : ∀ w ∈ W, prj W w = w`. Introduce `w hw`. Use `Submodule.eq_starProjection_of_mem_orthogonal (W.le_topologicalClosure hw) ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Establish `hmem : ∀ x : ℝ, ∀ w, w ∈ eigIn W A x ↔ w ∈ W ∧ A w = (x : ℂ) • w`.

Introduce `x w`. Simplify using `[eigIn, Module.End.mem_eigenspace_iff]`. Establish `hB : IsSelfAdjoint (A ∘L prj W)`. Rewrite using `[ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]`. Introduce `u v`.

Express the relevant statement in the definitionally equal form `inner ℂ (A (prj W u)) v = inner ℂ u (A (prj W v))`. Establish `h1 : inner ℂ (A (prj W u)) v = inner ℂ (A (prj W u)) (prj W v)`. Use `hperp v _ (hAW _ (hPW u))` as an intermediate fact. Rewrite `this` using `[inner_sub_right, sub_eq_zero]`. Conclude with `this`.

Establish `h2 : inner ℂ u (A (prj W v)) = inner ℂ (prj W u) (A (prj W v))`. Use `hperp u _ (hAW _ (hPW v))` as an intermediate fact. Rewrite `this` using `[inner_sub_right, sub_eq_zero]`. Rewrite using `[← inner_conj_symm, this, inner_conj_symm]`. Rewrite using `[h1, h2]`.

Conclude with `hA.isSymmetric _ _`. Establish `hle : ∀ x : ℝ, eigIn W A x ≤ Module.End.eigenspace ((A ∘L prj W : H →L[ℂ] H) : H →ₗ[ℂ] H) (x : ℂ)`. Introduce `x w hw`. Take `⟨hwW, hwA⟩` from `(hmem x w).1 hw`. Rewrite using `[Module.End.mem_eigenspace_iff]`.

Express the relevant statement in the definitionally equal form `A (prj W w) = _`. Rewrite using `[hfix w hwW, hwA]`. Establish `hfin` using `GroundTheory.Automorphic.CompactSelfAdjoint.finite_eigenvalues_norm_ge hC hB hη`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `Set.Finite.of_finite_image (f := fun x : ℝ => (x : ℂ)) (hfin.subset ?_) (Complex.ofReal_injective.injOn)` and prove the remaining obligations.

Introduce and unpack `_ ⟨x, ⟨hx, hne⟩, rfl⟩`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Take `⟨w, hw, hw0⟩` from `(Submodule.ne_bot_iff _).1 hne`. Conclude with `Module.End.hasEigenvalue_of_hasEigenvector ⟨hle x hw, hw0⟩`. Establish `: η ≤ |x|` using `hx.le.trans (le_abs_self x)`.

Simplify using `using this`. Introduce `x hx`. Establish `hx0 : (x : ℂ) ≠ 0`. Establish `: x ≠ 0` using `(hη.trans hx).ne'`. Conclude with `this` after adjusting the coercions.

Use `haveI : FiniteDimensional ℂ (Module.End.eigenspace ((A ∘L prj W : H →L[ℂ] H) : H →ₗ[ℂ] H) (x : ℂ)) := ContinuousLinearMap.finite_dimensional_eigenspace hC _ hx0`. Conclude with `Submodule.finiteDimensional_of_le (hle x)`.
-/
theorem UpperTheory.eigIn_finite_above_of_isCompactOperator :
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (W : Submodule ℂ H) (A : H →L[ℂ] H), IsClosed (W : Set H) → IsSelfAdjoint A → (∀ v ∈ W, A v ∈ W) → IsCompactOperator (A ∘L prj W) → ∀ η : ℝ, 0 < η → {x : ℝ | η < x ∧ eigIn W A x ≠ ⊥}.Finite ∧ ∀ x : ℝ, η < x → FiniteDimensional ℂ (eigIn W A x) := by
  intro H _ _ _ W A hW hA hAW hC η hη
  have hWc : W.topologicalClosure = W := hW.submodule_topologicalClosure_eq
  have hPW : ∀ v, prj W v ∈ W := by
    intro v
    have : prj W v ∈ W.topologicalClosure := Submodule.starProjection_apply_mem _ v
    rwa [hWc] at this
  have hperp : ∀ v, ∀ w ∈ W, inner ℂ w (v - prj W v) = 0 := by
    intro v w hw
    have : v - prj W v ∈ W.topologicalClosureᗮ := Submodule.sub_starProjection_mem_orthogonal v
    exact this w (W.le_topologicalClosure hw)
  have hfix : ∀ w ∈ W, prj W w = w := by
    intro w hw
    refine Submodule.eq_starProjection_of_mem_orthogonal
      (W.le_topologicalClosure hw) ?_
    simp
  have hmem : ∀ x : ℝ, ∀ w, w ∈ eigIn W A x ↔ w ∈ W ∧ A w = (x : ℂ) • w := by
    intro x w
    simp [eigIn, Module.End.mem_eigenspace_iff]
  have hB : IsSelfAdjoint (A ∘L prj W) := by
    rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
    intro u v
    change inner ℂ (A (prj W u)) v = inner ℂ u (A (prj W v))
    have h1 : inner ℂ (A (prj W u)) v = inner ℂ (A (prj W u)) (prj W v) := by
      have := hperp v _ (hAW _ (hPW u))
      rw [inner_sub_right, sub_eq_zero] at this
      exact this
    have h2 : inner ℂ u (A (prj W v)) = inner ℂ (prj W u) (A (prj W v)) := by
      have := hperp u _ (hAW _ (hPW v))
      rw [inner_sub_right, sub_eq_zero] at this
      rw [← inner_conj_symm, this, inner_conj_symm]
    rw [h1, h2]
    exact hA.isSymmetric _ _
  have hle : ∀ x : ℝ, eigIn W A x ≤
      Module.End.eigenspace ((A ∘L prj W : H →L[ℂ] H) : H →ₗ[ℂ] H) (x : ℂ) := by
    intro x w hw
    obtain ⟨hwW, hwA⟩ := (hmem x w).1 hw
    rw [Module.End.mem_eigenspace_iff]
    change A (prj W w) = _
    rw [hfix w hwW, hwA]
  have hfin := GroundTheory.Automorphic.CompactSelfAdjoint.finite_eigenvalues_norm_ge hC hB hη
  refine ⟨?_, ?_⟩
  · refine Set.Finite.of_finite_image (f := fun x : ℝ => (x : ℂ)) (hfin.subset ?_)
      (Complex.ofReal_injective.injOn)
    rintro _ ⟨x, ⟨hx, hne⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff _).1 hne
      exact Module.End.hasEigenvalue_of_hasEigenvector ⟨hle x hw, hw0⟩
    · have : η ≤ |x| := hx.le.trans (le_abs_self x)
      simpa using this
  · intro x hx
    have hx0 : (x : ℂ) ≠ 0 := by
      have : x ≠ 0 := (hη.trans hx).ne'
      exact_mod_cast this
    haveI : FiniteDimensional ℂ (Module.End.eigenspace ((A ∘L prj W : H →L[ℂ] H) : H →ₗ[ℂ] H) (x : ℂ)) :=
      ContinuousLinearMap.finite_dimensional_eigenspace hC _ hx0
    exact Submodule.finiteDimensional_of_le (hle x)
