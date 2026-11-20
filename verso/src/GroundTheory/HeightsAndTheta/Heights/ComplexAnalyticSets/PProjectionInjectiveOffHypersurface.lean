import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StProjectionInjectiveOffHypersurface
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PFrameJacobianGeneric
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PFrameImplicitGraph
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial

/- English proof (translation)
Introduce `σ _ I k hI hk`. Use `set n := Fintype.card σ`. Set `e : σ ≃ Fin n` to `Fintype.equivFin σ`. Set `φ : MvPolynomial σ ℂ ≃ₐ[ℂ] MvPolynomial (Fin n) ℂ` to `renameEquiv ℂ e`. Set `J : Ideal (MvPolynomial (Fin n) ℂ)` to `I.map φ`.

Establish `hJ : J.IsPrime` using `Ideal.map_isPrime_of_equiv φ`. Establish `hJk : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (k : ℕ)`. Rewrite using `[← hk]`. Conclude with `(ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv I J φ rfl).symm)`. Set `b` to `EuclideanSpace.basisFun (Fin n) ℂ`.

Take `⟨I₀, f, -, hcard, hfJ, -, hdet, -⟩` from `hF n k J hJ hJk b`. Set `T : (σ → ℂ) → EuclideanSpace ℂ (Fin n)` to `fun x => WithLp.toLp 2 (x ∘ e.symm)`. Establish `hT : ∀ (x : σ → ℂ) (p : MvPolynomial (Fin n) ℂ), eval (fun i => T x i) p = eval x (φ.symm p)`. Introduce `x p`. Establish `: φ.symm p = rename e.symm p` using `rfl`.

Rewrite using `[this, eval_rename]`. Establish `hTinj : Function.Injective T`. Introduce `x y hxy`. Use function extensionality and compare the values at `s`. Use `congrArg (fun v : EuclideanSpace ℂ (Fin n) => v (e s)) hxy` as an intermediate fact.

Simplify `this` using `[T]`. Establish `hTc : Continuous T` using `(PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => continuous_apply _)`. Use `⟨φ.symm (frameJacobianDet b I₀ f), ?_, ?_⟩` and prove the remaining obligations. Introduce `hmem`. Apply `hdet` to reduce the goal to its premises.

Conclude with `(Ideal.mem_map_of_equiv φ _).2 ⟨_, hmem, by simp⟩`. Introduce `z hz hzh`. Establish `hf0 : ∀ x ∈ zeroSetIn I, ∀ j, eval (fun i => T x i) (f j) = 0`. Introduce `x hx j`. Take `⟨q, hq, hqf⟩` from `(Ideal.mem_map_of_equiv φ (f j)).1 (hfJ j)`.

Rewrite using `[hT, ← hqf, AlgEquiv.symm_apply_apply]`. Conclude with `hx q hq`. Establish `hz' : eval (fun i => T z i) (frameJacobianDet b I₀ f) ≠ 0` using `by rwa [hT]`. Take `⟨Ω, V, g, -, hV, hzV, -, -, hpg, hgraph⟩` from `FrameImplicitGraph.proof n b I₀ f (T z) (hf0 z hz) hz' Set.univ isOpen_univ (Set.mem_univ _)`. Set `c : Fin k ≃ I₀` to `(Fintype.equivFinOfCardEq (by simpa using hcard)).symm`.

Set `A : (σ → ℂ) →L[ℂ] (Fin k → ℂ)` to `ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj (e.symm (c j : Fin n))`. Use `⟨T ⁻¹' V, hV.preimage hTc, hzV, A, ?_⟩` and prove the remaining obligations. Establish `hback : ∀ x ∈ zeroSetIn I ∩ T ⁻¹' V, g (frameProj b I₀ (T x)) = T x`. Introduce and unpack `x ⟨hx, hxV⟩`. Establish `hmem : T x ∈ {y : EuclideanSpace ℂ (Fin n) | ∀ j, eval (fun i => y i) (f j) = 0} ∩ V` using `⟨hf0 x hx, hxV⟩`.

Rewrite `hmem` using `[hgraph]`. Take `⟨w, hw, hwx⟩` from `hmem`. Rewrite using `[← hwx, hpg w hw]`. Introduce `x hx y hy hAxy`. Apply `hTinj` to reduce the goal to its premises.

Establish `hproj : frameProj b I₀ (T x) = frameProj b I₀ (T y)`. Use function extensionality and compare the values at `i`. Use `congrFun hAxy (c.symm i)` as an intermediate fact. Use `show inner ℂ (b i) (T x) = inner ℂ (b i) (T y)`. Rewrite using `[EuclideanSpace.basisFun_inner, EuclideanSpace.basisFun_inner]`.

Simplify `this` using `[A, T]`. Rewrite using `[← hback x hx, ← hback y hy, hproj]`.
-/
theorem ProjectionInjectiveOffHypersurface.proof (hF : FrameJacobianGeneric.Statement) :
    ProjectionInjectiveOffHypersurface.Statement := by
  classical
  intro σ _ I k hI hk
  set n := Fintype.card σ
  let e : σ ≃ Fin n := Fintype.equivFin σ
  let φ : MvPolynomial σ ℂ ≃ₐ[ℂ] MvPolynomial (Fin n) ℂ := renameEquiv ℂ e
  let J : Ideal (MvPolynomial (Fin n) ℂ) := I.map φ
  have hJ : J.IsPrime := Ideal.map_isPrime_of_equiv φ
  have hJk : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (k : ℕ) := by
    rw [← hk]
    exact (ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv I J φ rfl).symm)
  let b := EuclideanSpace.basisFun (Fin n) ℂ
  obtain ⟨I₀, f, -, hcard, hfJ, -, hdet, -⟩ := hF n k J hJ hJk b

  let T : (σ → ℂ) → EuclideanSpace ℂ (Fin n) := fun x => WithLp.toLp 2 (x ∘ e.symm)
  have hT : ∀ (x : σ → ℂ) (p : MvPolynomial (Fin n) ℂ),
      eval (fun i => T x i) p = eval x (φ.symm p) := by
    intro x p
    have : φ.symm p = rename e.symm p := rfl
    rw [this, eval_rename]
  have hTinj : Function.Injective T := by
    intro x y hxy
    funext s
    have := congrArg (fun v : EuclideanSpace ℂ (Fin n) => v (e s)) hxy
    simpa [T] using this
  have hTc : Continuous T :=
    (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => continuous_apply _)
  refine ⟨φ.symm (frameJacobianDet b I₀ f), ?_, ?_⟩
  · intro hmem
    apply hdet
    exact (Ideal.mem_map_of_equiv φ _).2 ⟨_, hmem, by simp⟩
  intro z hz hzh
  have hf0 : ∀ x ∈ zeroSetIn I, ∀ j, eval (fun i => T x i) (f j) = 0 := by
    intro x hx j
    obtain ⟨q, hq, hqf⟩ := (Ideal.mem_map_of_equiv φ (f j)).1 (hfJ j)
    rw [hT, ← hqf, AlgEquiv.symm_apply_apply]
    exact hx q hq
  have hz' : eval (fun i => T z i) (frameJacobianDet b I₀ f) ≠ 0 := by rwa [hT]
  obtain ⟨Ω, V, g, -, hV, hzV, -, -, hpg, hgraph⟩ :=
    FrameImplicitGraph.proof n b I₀ f (T z) (hf0 z hz) hz' Set.univ isOpen_univ (Set.mem_univ _)
  let c : Fin k ≃ I₀ := (Fintype.equivFinOfCardEq (by simpa using hcard)).symm
  let A : (σ → ℂ) →L[ℂ] (Fin k → ℂ) :=
    ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj (e.symm (c j : Fin n))
  refine ⟨T ⁻¹' V, hV.preimage hTc, hzV, A, ?_⟩

  have hback : ∀ x ∈ zeroSetIn I ∩ T ⁻¹' V, g (frameProj b I₀ (T x)) = T x := by
    rintro x ⟨hx, hxV⟩
    have hmem : T x ∈ {y : EuclideanSpace ℂ (Fin n) | ∀ j, eval (fun i => y i) (f j) = 0} ∩ V :=
      ⟨hf0 x hx, hxV⟩
    rw [hgraph] at hmem
    obtain ⟨w, hw, hwx⟩ := hmem
    rw [← hwx, hpg w hw]
  intro x hx y hy hAxy
  apply hTinj
  have hproj : frameProj b I₀ (T x) = frameProj b I₀ (T y) := by
    funext i
    have := congrFun hAxy (c.symm i)
    show inner ℂ (b i) (T x) = inner ℂ (b i) (T y)
    rw [EuclideanSpace.basisFun_inner, EuclideanSpace.basisFun_inner]
    simpa [A, T] using this
  rw [← hback x hx, ← hback y hy, hproj]

/- English proof (translation)
The claim follows from `ProjectionInjectiveOffHypersurface.proof (FrameJacobianGeneric.proof hR hC)`.
-/
theorem ProjectionInjectiveOffHypersurface.proof_of_rank (hR : JacobianRankGeneric.Statement)
    (hC : ConormalGenerationGeneric.Statement) : ProjectionInjectiveOffHypersurface.Statement :=
  ProjectionInjectiveOffHypersurface.proof (FrameJacobianGeneric.proof hR hC)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
