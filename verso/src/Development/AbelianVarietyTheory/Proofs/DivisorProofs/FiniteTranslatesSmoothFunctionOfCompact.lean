import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfMemSpanK
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

namespace GlobalTheory

/- English proof (translation)
Establish `hn : ∀ f ∈ Kf, {g | finRep E a g φ = finRep E a f φ} ∈ nhds f`. Introduce `f _`. Establish `hc : Continuous (fun g : GL (Fin a) (Af E) => f⁻¹ * g)` using `continuous_const.mul continuous_id`. Establish `ho` using `h.preimage hc`. Use `Filter.mem_of_superset (ho.mem_nhds ?_) ?_` and prove the remaining obligations.

Simplify using the standard rewrite rules. Introduce `g hg`. Establish `hg' : finRep E a (f⁻¹ * g) φ = φ` using `hg`. Establish `e : g = f * (f⁻¹ * g)` using `by simp`. Use `show finRep E a g φ = finRep E a f φ`.

Combine the equalities or inequalities in the displayed calculation. Take `⟨t, -, ht⟩` from `hK.elim_nhds_subcover (fun f => {g | finRep E a g φ = finRep E a f φ}) hn`. Use `⟨t, fun f hf => ?_⟩` and prove the remaining obligations. Use `ht hf` as an intermediate fact. Simplify using `only [Set.mem_iUnion] at this`.

Take `⟨f', hf', h'⟩` from `this`. Conclude with `⟨f', hf', h'⟩`.
-/
theorem finite_translates_of_isCompact (E : Type) [Field E] [NumberField E] [IsTotallyComplex E]
    (a : ℕ) (φ : Sm E a) (h : IsOpen {k | finRep E a k φ = φ})
    (Kf : Set (GL (Fin a) (Af E))) (hK : IsCompact Kf) :
    ∃ S : Finset (GL (Fin a) (Af E)), ∀ f ∈ Kf, ∃ f' ∈ S,
      finRep E a f φ = finRep E a f' φ := by
  have hn : ∀ f ∈ Kf, {g | finRep E a g φ = finRep E a f φ} ∈ nhds f := by
    intro f _
    have hc : Continuous (fun g : GL (Fin a) (Af E) => f⁻¹ * g) :=
      continuous_const.mul continuous_id
    have ho := h.preimage hc
    refine Filter.mem_of_superset (ho.mem_nhds ?_) ?_
    · simp
    · intro g hg
      have hg' : finRep E a (f⁻¹ * g) φ = φ := hg
      have e : g = f * (f⁻¹ * g) := by simp
      show finRep E a g φ = finRep E a f φ
      calc finRep E a g φ = finRep E a (f * (f⁻¹ * g)) φ := by rw [← e]
        _ = finRep E a f (finRep E a (f⁻¹ * g) φ) := by rw [map_mul]; rfl
        _ = finRep E a f φ := by rw [hg']
  obtain ⟨t, -, ht⟩ := hK.elim_nhds_subcover (fun f => {g | finRep E a g φ = finRep E a f φ}) hn
  refine ⟨t, fun f hf => ?_⟩
  have := ht hf
  simp only [Set.mem_iUnion] at this
  obtain ⟨f', hf', h'⟩ := this
  exact ⟨f', hf', h'⟩

end GlobalTheory
