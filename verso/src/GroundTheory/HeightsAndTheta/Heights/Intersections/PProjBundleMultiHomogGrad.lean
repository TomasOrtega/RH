import Mathlib
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial

section Graded

variable {σ τ R M : Type*} [CommRing R] [AddCommMonoid M]

/- English proof (translation)
Proceed by induction on `p using MvPolynomial.induction_on' with`. Consider the case `monomial d c`. Establish `hmon : IsWeightedHomogeneous ω (aeval e (monomial d c)) (Finsupp.weight w d)`. Rewrite using `[aeval_monomial, Finsupp.weight_apply, algebraMap_eq]`. Use `(isWeightedHomogeneous_C ω c).mul (IsWeightedHomogeneous.prod d.support (fun v => e v ^ d v) (fun v => d v • w v) (fun v _ => (he v).pow (d v)))` as an intermediate fact.

Rewrite `this` using `[zero_add]`. Conclude with `this`. Distinguish the cases in `hdm : Finsupp.weight w d = m`. Establish `hmon' : IsWeightedHomogeneous ω (aeval e (monomial d c)) m` using `hdm ▸ hmon`. Rewrite using `[(isWeightedHomogeneous_monomial _ d c hdm).weightedHomogeneousComponent_same, hmon'.weightedHomogeneousComponent_same]`.

Rewrite using `[(isWeightedHomogeneous_monomial w d c (m := Finsupp.weight w d) rfl).weightedHomogeneousComponent_ne m (Ne.symm hdm), hmon.weightedHomogeneousComponent_ne m (Ne.symm hdm), map_zero]`. Consider the case `add p q hp hq => simp only [map_add, hp, hq]`.
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
Rewrite using `[← hp.weightedHomogeneousComponent_same, aeval_weightedHomogeneousComponent_of_weights w ω e he]`. Conclude with `weightedHomogeneousComponent_isWeightedHomogeneous _ _`.
-/
theorem isWeightedHomogeneous_aeval_of_weights {w : σ → M} {ω : τ → M} {e : σ → MvPolynomial τ R}
    (he : ∀ v, IsWeightedHomogeneous ω (e v) (w v)) {p : MvPolynomial σ R} {a : M}
    (hp : IsWeightedHomogeneous w p a) : IsWeightedHomogeneous ω (aeval e p) a := by
  rw [← hp.weightedHomogeneousComponent_same, aeval_weightedHomogeneousComponent_of_weights w ω e he]
  exact weightedHomogeneousComponent_isWeightedHomogeneous _ _

/- English proof (translation)
Set `_` to `weightedGradedAlgebra R ω`. Establish `hom : (Ideal.map (aeval e) (Ideal.span G)).IsHomogeneous (weightedHomogeneousSubmodule R ω)`. Rewrite using `[Ideal.map_span]`. Use `Ideal.homogeneous_span _ _ fun x hx => ?_` and prove the remaining obligations. Take `⟨f, hfG, rfl⟩` from `hx`.

Take `⟨a, ha⟩` from `hG f hfG`. Conclude with `⟨a, (mem_weightedHomogeneousSubmodule R ω a _).mpr (isWeightedHomogeneous_aeval_of_weights he ha)⟩`. Conclude with `weightedHomogeneousComponent_mem_of_mem R ω hom hf m`.
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
Proceed by induction on `L using MvPolynomial.induction_on' with`. Consider the case `monomial d r`. Establish `hd` using `isWeightedHomogeneous_monomial w d r (m := Finsupp.weight w d) rfl`. Establish `hcd` using `hc.mul hd`. Distinguish the cases in `hdm : Finsupp.weight w d = γ`.

Rewrite using `[(hdm ▸ hd : IsWeightedHomogeneous w (monomial d r) γ).weightedHomogeneousComponent_same]`. Rewrite using `[show γ + m = m + Finsupp.weight w d by rw [hdm, add_comm]]`. Conclude with `hcd.weightedHomogeneousComponent_same`. Rewrite using `[hd.weightedHomogeneousComponent_ne γ (Ne.symm hdm), mul_zero]`. Use `hcd.weightedHomogeneousComponent_ne _ fun h => hdm ?_` and prove the remaining obligations.

Rewrite `h` using `[add_comm m]`. Conclude with `(add_right_cancel h).symm`. Consider the case `add p q hp hq => simp only [mul_add, map_add, hp, hq]`.
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
