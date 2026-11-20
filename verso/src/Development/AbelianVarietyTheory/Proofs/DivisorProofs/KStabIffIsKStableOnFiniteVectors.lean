import Mathlib
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HolomorphicDiscreteSeries
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealFormSpans
open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace

namespace GlobalTheory.KFinStab

/- English proof (translation)
Introduce `n ε H _ _ σ D E hc hσ hirr hK U hU`. Take `⟨S, E', hS⟩` from `CompanionTheory.D.DSIC.hSmMod n ε H σ hσ`. Establish `hDS : D ≤ S` using `fun v hv => (hS.mem v).2 (CompanionTheory.D.gk.admitted.kFin_mem_smoothVecs n ε H σ hσ hirr v ((hK.mem v).1 hv))`. Use `set ι := Submodule.inclusion hDS with hι`. Establish `hιinj : Function.Injective ι` using `Submodule.inclusion_injective hDS`.

Establish `hE : ∀ a b (v : D), E' a b (ι v) = ι (E a b v)`. Introduce `a b v`. Establish `key` using `GlobalTheory.realForm_spans n ε H (fun a b => (E a b v : H) - (E' a b (ι v) : H)) ?_ a b`. Apply `Subtype.ext` to reduce the goal to its premises. Conclude with `(sub_eq_zero.1 key).symm`.

Introduce `X hX`. Establish `h1` using `hK.real X hX v`. Establish `h2` using `hS.real X hX (ι v)`. Establish `h3 : ((ι v : S) : H) = (v : H)` using `rfl`. Rewrite `h2` using `[h3]`.

Establish `h4` using `h1.unique h2`. Simplify using `only [smul_sub, Finset.sum_sub_distrib, h4, sub_self]`. Establish `hmap : (U.map ι).map S.subtype = U.map D.subtype`. Rewrite using `[← Submodule.map_comp]`. Both sides reduce to the same expression.

Establish `: FiniteDimensional ℂ (U.map ι)` using `inferInstance`. Establish `hL` using `CompanionTheory.D.DSIC.hStabLink n ε H σ S E' hσ hS (U.map ι) inferInstance`. Rewrite `hL` using `[hmap]`. Use `Iff.trans ?_ hL` and prove the remaining obligations. Prove the components needed by the constructor for the conclusion.

Introduce `h a b hab w hw`. Take `⟨v, hv, rfl⟩` from `Submodule.mem_map.1 hw`. Rewrite using `[hE]`. Conclude with `Submodule.mem_map_of_mem (h a b hab v hv)`. Introduce `h a b hab v hv`.

Use `h a b hab (ι v) (Submodule.mem_map_of_mem hv)` as an intermediate fact. Rewrite `this` using `[hE]`. Take `⟨x, hx, hxe⟩` from `Submodule.mem_map.1 this`. Rewrite using `[← hιinj hxe]` and apply the resulting hypothesis.
-/
theorem kStab_iff_kStableOn : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D), CompleteSpace H → IsURepOn (UJset ε) σ → IsIrredOn (UJset ε) σ → IsKMod ε σ D E → ∀ U : Submodule ℂ D, FiniteDimensional ℂ U → (KStab ε E U ↔ IsKStableOn ε σ (U.map D.subtype)) := by
  intro n ε H _ _ σ D E hc hσ hirr hK U hU
  obtain ⟨S, E', hS⟩ := CompanionTheory.D.DSIC.hSmMod n ε H σ hσ
  have hDS : D ≤ S := fun v hv =>
    (hS.mem v).2 (CompanionTheory.D.gk.admitted.kFin_mem_smoothVecs n ε H σ hσ hirr v ((hK.mem v).1 hv))
  set ι := Submodule.inclusion hDS with hι
  have hιinj : Function.Injective ι := Submodule.inclusion_injective hDS
  have hE : ∀ a b (v : D), E' a b (ι v) = ι (E a b v) := by
    intro a b v
    have key := GlobalTheory.realForm_spans n ε H (fun a b => (E a b v : H) - (E' a b (ι v) : H)) ?_ a b
    · apply Subtype.ext
      exact (sub_eq_zero.1 key).symm
    intro X hX
    have h1 := hK.real X hX v
    have h2 := hS.real X hX (ι v)
    have h3 : ((ι v : S) : H) = (v : H) := rfl
    rw [h3] at h2
    have h4 := h1.unique h2
    simp only [smul_sub, Finset.sum_sub_distrib, h4, sub_self]
  have hmap : (U.map ι).map S.subtype = U.map D.subtype := by
    rw [← Submodule.map_comp]
    rfl
  have : FiniteDimensional ℂ (U.map ι) := inferInstance
  have hL := CompanionTheory.D.DSIC.hStabLink n ε H σ S E' hσ hS (U.map ι) inferInstance
  rw [hmap] at hL
  refine Iff.trans ?_ hL
  constructor
  · intro h a b hab w hw
    obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.1 hw
    rw [hE]
    exact Submodule.mem_map_of_mem (h a b hab v hv)
  · intro h a b hab v hv
    have := h a b hab (ι v) (Submodule.mem_map_of_mem hv)
    rw [hE] at this
    obtain ⟨x, hx, hxe⟩ := Submodule.mem_map.1 this
    rwa [← hιinj hxe]

end GlobalTheory.KFinStab
