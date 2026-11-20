import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.CuspInvariantsFinite.CuspInvFin
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl

namespace GlobalTheory.CompanionTheory.CompactFix

/- English proof (translation)
Use `set K : Submodule ℂ X := LinearMap.ker ((T : X →ₗ[ℂ] X) - LinearMap.id) with hK`. Establish `hfix : ∀ x ∈ K, T x = x`. Introduce `x hx`. Establish `: (T : X →ₗ[ℂ] X) x - x = 0` using `by simpa [hK] using hx`. Simplify `this` using `[sub_eq_zero]`.

Establish `hclosed : IsClosed (K : Set X)`. Establish `: (K : Set X) = {x | T x = x}`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Conclude with `hfix x`.

Introduce `h`. Establish `h' : T x = x` using `h`. Simplify using `[hK, h']`. Rewrite using `[this]`. Conclude with `isClosed_eq T.continuous continuous_id`.

Take `⟨C, hC, hCsub⟩` from `hT`. Establish `hpre : (T ⁻¹' C) ∈ nhds (0 : X)` using `hCsub`. Take `⟨r, hr, hball⟩` from `Metric.nhds_basis_closedBall.mem_iff.1 hpre`. Establish `hcomp : IsCompact (Metric.closedBall (0 : K) r)`. Establish `hemb : Topology.IsClosedEmbedding (Subtype.val : K → X)` using `hclosed.isClosedEmbedding_subtypeVal`.

Rewrite using `[hemb.isCompact_iff]`. Use `hC.of_isClosed_subset ?_ ?_` and prove the remaining obligations. Establish `: (Subtype.val '' Metric.closedBall (0 : K) r) = (K : Set X) ∩ Metric.closedBall 0 r`. Use extensionality with `x`. Simplify using `[Metric.mem_closedBall, dist_eq_norm, and_comm]`.

Rewrite using `[this]`. Conclude with `hclosed.inter Metric.isClosed_closedBall`. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Establish `hx' : (x : X) ∈ Metric.closedBall (0 : X) r`. Simplify `hx` using `[Metric.mem_closedBall, dist_eq_norm]`.

Use `hball hx'` as an intermediate fact. Simplify `this` using `[hfix x x.2]`. Conclude with `FiniteDimensional.of_isCompact_closedBall ℂ hr hcomp`.
-/
theorem finiteDimensional_ker_sub_id {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (T : X →L[ℂ] X) (hT : IsCompactOperator T) :
    FiniteDimensional ℂ (LinearMap.ker ((T : X →ₗ[ℂ] X) - LinearMap.id)) := by
  set K : Submodule ℂ X := LinearMap.ker ((T : X →ₗ[ℂ] X) - LinearMap.id) with hK
  have hfix : ∀ x ∈ K, T x = x := by
    intro x hx
    have : (T : X →ₗ[ℂ] X) x - x = 0 := by simpa [hK] using hx
    simpa [sub_eq_zero] using this
  have hclosed : IsClosed (K : Set X) := by
    have : (K : Set X) = {x | T x = x} := by
      ext x
      constructor
      · exact hfix x
      · intro h
        have h' : T x = x := h
        simp [hK, h']
    rw [this]
    exact isClosed_eq T.continuous continuous_id
  obtain ⟨C, hC, hCsub⟩ := hT
  have hpre : (T ⁻¹' C) ∈ nhds (0 : X) := hCsub
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.1 hpre
  have hcomp : IsCompact (Metric.closedBall (0 : K) r) := by
    have hemb : Topology.IsClosedEmbedding (Subtype.val : K → X) := hclosed.isClosedEmbedding_subtypeVal
    rw [hemb.isCompact_iff]
    refine hC.of_isClosed_subset ?_ ?_
    · have : (Subtype.val '' Metric.closedBall (0 : K) r) = (K : Set X) ∩ Metric.closedBall 0 r := by
        ext x
        simp [Metric.mem_closedBall, dist_eq_norm, and_comm]
      rw [this]
      exact hclosed.inter Metric.isClosed_closedBall
    · rintro _ ⟨x, hx, rfl⟩
      have hx' : (x : X) ∈ Metric.closedBall (0 : X) r := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hx
      have := hball hx'
      simpa [hfix x x.2] using this
  exact FiniteDimensional.of_isCompact_closedBall ℂ hr hcomp

end GlobalTheory.CompanionTheory.CompactFix
