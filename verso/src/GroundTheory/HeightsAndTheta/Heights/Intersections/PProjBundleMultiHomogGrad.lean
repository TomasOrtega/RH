import Mathlib
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial

section Graded

variable {σ τ R M : Type*} [CommRing R] [AddCommMonoid M]

/- English proof (translation)
Proceed by induction. Treat this case separately. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Consider separately whether the proposition holds or fails. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Treat this case separately. A detailed English derivation is pending.
-/
theorem aeval_weightedHomogeneousComponent_of_weights (w : σ → M) (ω : τ → M)
    (e : σ → MvPolynomial τ R) (he : ∀ v, IsWeightedHomogeneous ω (e v) (w v)) (m : M)
    (p : MvPolynomial σ R) :
    aeval e (weightedHomogeneousComponent w m p) = weightedHomogeneousComponent ω m (aeval e p) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial d c =>
    have hmon : IsWeightedHomogeneous ω (aeval e (monomial d c)) (Finsupp.weight w d) := by
      rw [aeval_monomial, Finsupp.weight_apply, algebraMap_eq]
      have := (isWeightedHomogeneous_C ω c).mul (IsWeightedHomogeneous.prod d.support
        (fun v => e v ^ d v) (fun v => d v • w v) (fun v _ => (he v).pow (d v)))
      rw [zero_add] at this
      exact this
    by_cases hdm : Finsupp.weight w d = m
    · have hmon' : IsWeightedHomogeneous ω (aeval e (monomial d c)) m := hdm ▸ hmon
      rw [(isWeightedHomogeneous_monomial _ d c hdm).weightedHomogeneousComponent_same,
        hmon'.weightedHomogeneousComponent_same]
    · rw [(isWeightedHomogeneous_monomial w d c
        (m := Finsupp.weight w d) rfl).weightedHomogeneousComponent_ne m
        (Ne.symm hdm), hmon.weightedHomogeneousComponent_ne m (Ne.symm hdm), map_zero]
  | add p q hp hq => simp only [map_add, hp, hq]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem isWeightedHomogeneous_aeval_of_weights {w : σ → M} {ω : τ → M} {e : σ → MvPolynomial τ R}
    (he : ∀ v, IsWeightedHomogeneous ω (e v) (w v)) {p : MvPolynomial σ R} {a : M}
    (hp : IsWeightedHomogeneous w p a) : IsWeightedHomogeneous ω (aeval e p) a := by
  rw [← hp.weightedHomogeneousComponent_same, aeval_weightedHomogeneousComponent_of_weights w ω e he]
  exact weightedHomogeneousComponent_isWeightedHomogeneous _ _

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem weightedHomogeneousComponent_mem_map_aeval [DecidableEq M] {w : σ → M} {ω : τ → M}
    {e : σ → MvPolynomial τ R} (he : ∀ v, IsWeightedHomogeneous ω (e v) (w v))
    (G : Set (MvPolynomial σ R)) (hG : ∀ f ∈ G, ∃ a, IsWeightedHomogeneous w f a)
    {f : MvPolynomial τ R} (hf : f ∈ Ideal.map (aeval e) (Ideal.span G)) (m : M) :
    weightedHomogeneousComponent ω m f ∈ Ideal.map (aeval e) (Ideal.span G) := by
  let _ := weightedGradedAlgebra R ω
  have hom : (Ideal.map (aeval e) (Ideal.span G)).IsHomogeneous (weightedHomogeneousSubmodule R ω) := by
    rw [Ideal.map_span]
    refine Ideal.homogeneous_span _ _ fun x hx => ?_
    obtain ⟨f, hfG, rfl⟩ := hx
    obtain ⟨a, ha⟩ := hG f hfG
    exact ⟨a, (mem_weightedHomogeneousSubmodule R ω a _).mpr (isWeightedHomogeneous_aeval_of_weights he ha)⟩
  exact weightedHomogeneousComponent_mem_of_mem R ω hom hf m

/- English proof (translation)
Proceed by induction. Treat this case separately. Establish an intermediate fact. Establish an intermediate fact. Consider separately whether the proposition holds or fails.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the indicated hypotheses using the stated equalities.

Treat this case separately. A detailed English derivation is pending.
-/
theorem weightedHomogeneousComponent_mul_of_left {M : Type*} [AddCancelCommMonoid M] {w : σ → M}
    {c : MvPolynomial σ R} {m : M} (hc : IsWeightedHomogeneous w c m) (γ : M) (L : MvPolynomial σ R) :
    weightedHomogeneousComponent w (γ + m) (c * L) = c * weightedHomogeneousComponent w γ L := by
  classical
  induction L using MvPolynomial.induction_on' with
  | monomial d r =>
    have hd := isWeightedHomogeneous_monomial w d r (m := Finsupp.weight w d) rfl
    have hcd := hc.mul hd
    by_cases hdm : Finsupp.weight w d = γ
    · rw [(hdm ▸ hd : IsWeightedHomogeneous w (monomial d r) γ).weightedHomogeneousComponent_same]
      rw [show γ + m = m + Finsupp.weight w d by rw [hdm, add_comm]]
      exact hcd.weightedHomogeneousComponent_same
    · rw [hd.weightedHomogeneousComponent_ne γ (Ne.symm hdm), mul_zero]
      refine hcd.weightedHomogeneousComponent_ne _ fun h => hdm ?_
      rw [add_comm m] at h
      exact (add_right_cancel h).symm
  | add p q hp hq => simp only [mul_add, map_add, hp, hq]

end Graded

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
