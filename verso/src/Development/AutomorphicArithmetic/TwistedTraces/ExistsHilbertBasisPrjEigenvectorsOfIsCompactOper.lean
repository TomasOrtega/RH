import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.CuspidalMultiplicityOneTotallyComplex
import GroundTheory.AutomorphicForms.CompactSelfAdjoint

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C

/- English proof (translation)
Introduce `H _ _ _ W A hW hsa hinv hK`. Establish `hcl : W.topologicalClosure = W` using `hW.submodule_topologicalClosure_eq`. Establish `hmem : ∀ u, prj W u ∈ W` using `fun u => hcl.le (Submodule.starProjection_apply_mem W.topologicalClosure u)`. Establish `hfix : ∀ w ∈ W, prj W w = w` using `fun w hw => Submodule.starProjection_eq_self_iff.mpr (W.le_topologicalClosure hw)`. Establish `hPsym : ∀ x y : H, inner ℂ (prj W x) y = inner ℂ x (prj W y)` using `fun x y => Submodule.inner_starProjection_left_eq_right W.topologicalClosure x y`.

Establish `hAsym : ∀ x y : H, inner ℂ (A x) y = inner ℂ x (A y)` using `ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hsa`. Establish `hBsa : IsSelfAdjoint (A ∘L prj W)`. Use `ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr fun u v => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `inner ℂ (A (prj W u)) v = inner ℂ u (A (prj W v))`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[hfix _ (hinv _ (hmem u))]`. Use `_ = inner ℂ (A (prj W u)) (prj W v) := hPsym _ _`. Use `_ = inner ℂ (prj W u) (A (prj W v)) := hAsym _ _`. Use `_ = inner ℂ u (prj W (A (prj W v))) := hPsym _ _`. Use `_ = inner ℂ u (A (prj W v)) := by rw [hfix _ (hinv _ (hmem v))]`.

Take `⟨s, b, hb, hev⟩` from `GroundTheory.Automorphic.CompactSelfAdjoint.exists_hilbertBasis_eigenvectors hK hBsa`. Use `⟨s, b, fun i => ?_⟩` and prove the remaining obligations. Establish `hbi : b i ∈ s`. Rewrite using `[hb]`. Conclude with `i.2`.

Take `⟨μ, hμ⟩` from `hev (b i) hbi`. Establish `hμ' : A (prj W (b i)) = (μ : ℂ) • b i` using `hμ`. Use `⟨μ, ?_⟩` and prove the remaining obligations. Establish `h2 : prj W (A (prj W (b i))) = (μ : ℂ) • prj W (b i)`. Rewrite using `[hμ', map_smul]`.

Rewrite using `[← h2, hfix _ (hinv _ (hmem _))]`.
-/
theorem UpperTheory.exists_hilbertBasis_prj_eigenvectors_of_isCompactOperator :
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (W : Submodule ℂ H) (A : H →L[ℂ] H), IsClosed (W : Set H) → IsSelfAdjoint A → (∀ v ∈ W, A v ∈ W) → IsCompactOperator (A ∘L prj W) → ∃ (s : Set H) (b : HilbertBasis s ℂ H), ∀ i, ∃ μ : ℝ, A (prj W (b i)) = (μ : ℂ) • prj W (b i) := by
  intro H _ _ _ W A hW hsa hinv hK
  have hcl : W.topologicalClosure = W := hW.submodule_topologicalClosure_eq
  have hmem : ∀ u, prj W u ∈ W := fun u =>
    hcl.le (Submodule.starProjection_apply_mem W.topologicalClosure u)
  have hfix : ∀ w ∈ W, prj W w = w := fun w hw =>
    Submodule.starProjection_eq_self_iff.mpr (W.le_topologicalClosure hw)
  have hPsym : ∀ x y : H, inner ℂ (prj W x) y = inner ℂ x (prj W y) := fun x y =>
    Submodule.inner_starProjection_left_eq_right W.topologicalClosure x y
  have hAsym : ∀ x y : H, inner ℂ (A x) y = inner ℂ x (A y) :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hsa
  have hBsa : IsSelfAdjoint (A ∘L prj W) := by
    refine ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr fun u v => ?_
    change inner ℂ (A (prj W u)) v = inner ℂ u (A (prj W v))
    calc inner ℂ (A (prj W u)) v = inner ℂ (prj W (A (prj W u))) v := by
          rw [hfix _ (hinv _ (hmem u))]
      _ = inner ℂ (A (prj W u)) (prj W v) := hPsym _ _
      _ = inner ℂ (prj W u) (A (prj W v)) := hAsym _ _
      _ = inner ℂ u (prj W (A (prj W v))) := hPsym _ _
      _ = inner ℂ u (A (prj W v)) := by rw [hfix _ (hinv _ (hmem v))]
  obtain ⟨s, b, hb, hev⟩ :=
    GroundTheory.Automorphic.CompactSelfAdjoint.exists_hilbertBasis_eigenvectors hK hBsa
  refine ⟨s, b, fun i => ?_⟩
  have hbi : b i ∈ s := by
    rw [hb]
    exact i.2
  obtain ⟨μ, hμ⟩ := hev (b i) hbi
  have hμ' : A (prj W (b i)) = (μ : ℂ) • b i := hμ
  refine ⟨μ, ?_⟩
  have h2 : prj W (A (prj W (b i))) = (μ : ℂ) • prj W (b i) := by
    rw [hμ', map_smul]
  rw [← h2, hfix _ (hinv _ (hmem _))]
