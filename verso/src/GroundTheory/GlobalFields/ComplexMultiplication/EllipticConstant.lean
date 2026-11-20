import Mathlib
import GroundTheory.GlobalFields.ComplexMultiplication.EllipticFunctions

open Complex Filter Topology Set

noncomputable section

namespace GroundTheory.Global
namespace Elliptic

variable {E : Type*} [NormedAddCommGroup E]

def limPunctured (f : ℂ → E) (z : ℂ) : E := limUnder (𝓝[≠] z) f

/- English proof (translation)
A detailed English derivation is pending.
-/
lemma limPunctured_eq_of_continuousAt {f : ℂ → E} {z : ℂ} (h : ContinuousAt f z) :
    limPunctured f z = f z :=
  (tendsto_nhdsWithin_of_tendsto_nhds h.tendsto).limUnder_eq

/- English proof (translation)
Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Use the resulting assumption.
-/
lemma tendsto_limPunctured [NormedSpace ℂ E] {f : ℂ → E} {z : ℂ} (hf : MeromorphicAt f z)
    (ho : 0 ≤ meromorphicOrderAt f z) :
    Tendsto f (𝓝[≠] z) (𝓝 (limPunctured f z)) := by
  obtain ⟨c, hc⟩ := tendsto_nhds_of_meromorphicOrderAt_nonneg hf ho
  rwa [limPunctured, hc.limUnder_eq]

/- English proof (translation)
A detailed English derivation is pending.
-/
lemma limPunctured_eventuallyEq_of_analyticAt [NormedSpace ℂ E] [CompleteSpace E] {f : ℂ → E} {w : ℂ} (hw : AnalyticAt ℂ f w) :
    limPunctured f =ᶠ[𝓝 w] f := by
  filter_upwards [(isOpen_analyticAt ℂ f).mem_nhds hw] with u hu
  exact limPunctured_eq_of_continuousAt hu.continuousAt

variable [NormedSpace ℂ E]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
lemma analyticAt_limPunctured [CompleteSpace E] {f : ℂ → E} {z : ℂ} (hf : MeromorphicAt f z)
    (ho : 0 ≤ meromorphicOrderAt f z) : AnalyticAt ℂ (limPunctured f) z := by
  have hev : ∀ᶠ w in 𝓝[≠] z, AnalyticAt ℂ f w := hf.eventually_analyticAt
  have heq : limPunctured f =ᶠ[𝓝[≠] z] f :=
    hev.mono fun w hw ↦ (limPunctured_eventuallyEq_of_analyticAt hw).eq_of_nhds
  apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
  · exact hev.mono fun w hw ↦
      hw.differentiableAt.congr_of_eventuallyEq (limPunctured_eventuallyEq_of_analyticAt hw)
  · rw [← continuousWithinAt_compl_self]
    exact (tendsto_limPunctured hf ho).congr' heq.symm

variable {L : PeriodPair}

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Fix the arbitrary inputs or assume the hypotheses.

Reduce the claim to the hypotheses of an applicable result. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
lemma IsPeriodic.limPunctured_add {f : ℂ → E} (hp : IsPeriodic L f) {z l : ℂ}
    (hl : l ∈ L.lattice) (hf : MeromorphicAt f z) (ho : 0 ≤ meromorphicOrderAt f z) :
    limPunctured f (z + l) = limPunctured f z := by
  have h1 : Tendsto (fun w ↦ w - l) (𝓝[≠] (z + l)) (𝓝[≠] z) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun w ↦ w - l) (𝓝 (z + l)) (𝓝 (z + l - l)) :=
        (continuous_id.sub continuous_const).tendsto _
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with w hw
      intro h
      apply hw
      simp only [mem_singleton_iff] at h ⊢
      rw [← h]; ring
  have h2 := (tendsto_limPunctured hf ho).comp h1
  have e : (f ∘ fun w ↦ w - l) = f := funext fun w ↦ hp.sub w hl
  rw [e] at h2
  exact h2.limUnder_eq

variable (L) in

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem exists_const_of_meromorphicOrderAt_nonneg [CompleteSpace E] {f : ℂ → E} (hf : Meromorphic f)
    (hp : IsPeriodic L f) (ho : ∀ z, 0 ≤ meromorphicOrderAt f z) :
    ∃ c : E, ∀ z, AnalyticAt ℂ f z → f z = c := by
  have hd : Differentiable ℂ (limPunctured f) := fun z ↦
    (analyticAt_limPunctured (hf z) (ho z)).differentiableAt
  have hFp : IsPeriodic L (limPunctured f) := fun z l hl ↦
    hp.limPunctured_add hl (hf z) (ho z)
  refine ⟨limPunctured f 0, fun z hz ↦ ?_⟩
  rw [← limPunctured_eq_of_continuousAt hz.continuousAt]
  exact eq_of_differentiable_of_isPeriodic L hd hFp z 0

variable (L) in

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem exists_eventuallyEq_const_of_meromorphicOrderAt_nonneg [CompleteSpace E] {f : ℂ → E} (hf : Meromorphic f)
    (hp : IsPeriodic L f) (ho : ∀ z, 0 ≤ meromorphicOrderAt f z) :
    ∃ c : E, f =ᶠ[codiscrete ℂ] fun _ ↦ c := by
  obtain ⟨c, hc⟩ := exists_const_of_meromorphicOrderAt_nonneg L hf hp ho
  refine ⟨c, ?_⟩
  filter_upwards [(hf.meromorphicOn (s := univ)).analyticAt_mem_codiscreteWithin] with z hz
  exact hc z hz

end Elliptic
end GroundTheory.Global
