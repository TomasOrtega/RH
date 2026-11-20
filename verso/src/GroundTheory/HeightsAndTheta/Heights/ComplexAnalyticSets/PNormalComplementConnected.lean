import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalComplementConnected
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalGermIrreducible
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StIrreducibleGermComplementConnected
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StVanishNearPoint
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalLocallyIrreducible
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology Filter

/- English proof (translation)
Take `⟨s, hs⟩` from `(IsNoetherian.noetherian I : I.FG)`. Use `⟨Set.univ, s.card, fun i z => eval z (s.equivFin.symm i : MvPolynomial σ ℂ), isOpen_univ, trivial, fun i => AnalyticOnNhd.eval_mvPolynomial _, ?_⟩` and prove the remaining obligations. Use extensionality with `z`. Simplify using `only [Set.mem_inter_iff, Set.mem_univ, and_true, Set.mem_ofPred_eq, true_and]`. Prove the components needed by the constructor for the conclusion.

Introduce `hz i`. Apply `hz` to reduce the goal to its premises. Rewrite using `[← hs]`. Conclude with `Submodule.subset_span (s.equivFin.symm i).2`. Introduce `hz q hq`.

Establish `hle : Ideal.span (s : Set (MvPolynomial σ ℂ)) ≤ RingHom.ker (MvPolynomial.eval z)`. Rewrite using `[Ideal.span_le]`. Introduce `p hp`. Rewrite using `[SetLike.mem_coe, RingHom.mem_ker]`. Simplify using `using hz (s.equivFin ⟨p, hp⟩)`.

Rewrite `hq` using `[← hs]`. Conclude with `hle hq`.
-/
theorem zeroSetIn_isAnalyticNear {σ : Type} [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) :
    IsAnalyticNear (zeroSetIn I) w := by
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian I : I.FG)
  refine ⟨Set.univ, s.card, fun i z => eval z (s.equivFin.symm i : MvPolynomial σ ℂ), isOpen_univ, trivial,
    fun i => AnalyticOnNhd.eval_mvPolynomial _, ?_⟩
  ext z
  simp only [Set.mem_inter_iff, Set.mem_univ, and_true, Set.mem_ofPred_eq, true_and]
  constructor
  · intro hz i
    apply hz
    rw [← hs]
    exact Submodule.subset_span (s.equivFin.symm i).2
  · intro hz q hq
    have hle : Ideal.span (s : Set (MvPolynomial σ ℂ)) ≤ RingHom.ker (MvPolynomial.eval z) := by
      rw [Ideal.span_le]
      intro p hp
      rw [SetLike.mem_coe, RingHom.mem_ker]
      simpa using hz (s.equivFin ⟨p, hp⟩)
    rw [← hs] at hq
    exact hle hq

/- English proof (translation)
Introduce `σ _ I h w hI hnorm hh hw U hU`. Establish `hne : ¬ ∀ᶠ z in 𝓝 w, z ∈ zeroSetIn I → eval z h = 0`. Introduce `hev`. Establish `hcl` using `zeroSetIn_subset_closure_diff hvan I h hI hh hw`. Rewrite `hcl` using `[mem_closure_iff_nhds]`.

Take `⟨z, hzt, hzZ, hzh⟩` from `hcl _ hev`. Conclude with `hzh (hzt hzZ)`. Conclude with `hconn σ (zeroSetIn I) w (fun z => eval z h) (zeroSetIn_isAnalyticNear I w) (hgerm σ I w hI hnorm hw) (AnalyticOnNhd.eval_mvPolynomial h w trivial) hne U hU`.
-/
theorem NormalComplementConnected.proof (hvan : VanishNearPoint.Statement)
    (hgerm : NormalGermIrreducible.Statement) (hconn : IrreducibleGermComplementConnected.Statement) :
    NormalComplementConnected.Statement := by
  intro σ _ I h w hI hnorm hh hw U hU
  have hne : ¬ ∀ᶠ z in 𝓝 w, z ∈ zeroSetIn I → eval z h = 0 := by
    intro hev
    have hcl := zeroSetIn_subset_closure_diff hvan I h hI hh hw
    rw [mem_closure_iff_nhds] at hcl
    obtain ⟨z, hzt, hzZ, hzh⟩ := hcl _ hev
    exact hzh (hzt hzZ)
  exact hconn σ (zeroSetIn I) w (fun z => eval z h) (zeroSetIn_isAnalyticNear I w)
    (hgerm σ I w hI hnorm hw) (AnalyticOnNhd.eval_mvPolynomial h w trivial) hne U hU

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
