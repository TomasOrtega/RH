import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumEquiv
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsCharFnAndIsPseudoCoeffOfCompact

noncomputable section

open MeasureTheory
open Formalism.REAL (KG toMK muK)
open scoped ComplexConjugate

namespace GlobalTheory.PsCo.PcEF

/- English proof (translation)
Introduce `n ε γ W _ _ _ T hT`. Take `⟨hnt, hU, hK⟩` from `hT`. Establish `hemb : Topology.IsEmbedding (fun k : KG ε => toMK k)` using `(Formalism.REAL.isClosedEmbeddingMatrix n ε).1.isEmbedding.comp Topology.IsEmbedding.subtypeVal`. Set `π : KG ε →* (W →L[ℂ] W)` to `{ toFun := fun k => T (toMK k) map_one' := hU.1.1 map_mul' := fun a b => hU.1.2 _ a.2 _ b.2 }`. Establish `hπU : GlobalTheory.OpTrace.IsUnitaryRep π` using `⟨fun k v => hU.2.1 _ k.2 v, fun v => (hU.2.2 v).comp_continuous hemb.continuous fun k => k.2⟩`.

Establish `hπI : GlobalTheory.AutomorphicL2Unitary.IsTopIrreducible π`. Use `⟨hnt, fun S hS => ?_⟩` and prove the remaining obligations. Use `hK.2.2.1 S le_top fun g hg v hv => ?_` and prove the remaining obligations. Establish `: g ∈ Set.range (fun k : KG ε => toMK k)` using `by rw [Formalism.REAL.range_toMK]; exact hg`. Take `⟨k, rfl⟩` from `this`.

Conclude with `hS.2 k v hv`. Establish `h` using `GlobalTheory.Orb.integral_conj_trace_mul_trace (μ := muK ε) hπU hπI`. Establish `h1 : (muK ε).real Set.univ = 1`. Rewrite using `[Measure.real, Formalism.REAL.muK, ← TopologicalSpace.PositiveCompacts.coe_top, Measure.haarMeasure_self]`. Both sides reduce to the same expression.

Rewrite `h` using `[h1]`. Conclude with `h` after adjusting the coercions.
-/
theorem norm_irreducibleCharacter_unitaryMaxCompact_eq_one : SchurOne := by
  intro n ε γ W _ _ _ T hT
  obtain ⟨hnt, hU, hK⟩ := hT
  have hemb : Topology.IsEmbedding (fun k : KG ε => toMK k) :=
    (Formalism.REAL.isClosedEmbeddingMatrix n ε).1.isEmbedding.comp Topology.IsEmbedding.subtypeVal
  let π : KG ε →* (W →L[ℂ] W) :=
    { toFun := fun k => T (toMK k)
      map_one' := hU.1.1
      map_mul' := fun a b => hU.1.2 _ a.2 _ b.2 }
  have hπU : GlobalTheory.OpTrace.IsUnitaryRep π :=
    ⟨fun k v => hU.2.1 _ k.2 v, fun v => (hU.2.2 v).comp_continuous hemb.continuous fun k => k.2⟩
  have hπI : GlobalTheory.AutomorphicL2Unitary.IsTopIrreducible π := by
    refine ⟨hnt, fun S hS => ?_⟩
    refine hK.2.2.1 S le_top fun g hg v hv => ?_
    have : g ∈ Set.range (fun k : KG ε => toMK k) := by rw [Formalism.REAL.range_toMK]; exact hg
    obtain ⟨k, rfl⟩ := this
    exact hS.2 k v hv
  have h := GlobalTheory.Orb.integral_conj_trace_mul_trace (μ := muK ε) hπU hπI
  have h1 : (muK ε).real Set.univ = 1 := by
    rw [Measure.real, Formalism.REAL.muK, ← TopologicalSpace.PositiveCompacts.coe_top, Measure.haarMeasure_self]
    rfl
  rw [h1] at h
  exact_mod_cast h

end GlobalTheory.PsCo.PcEF
