import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsFactorisationCuspidal
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.FlathTensorProduct
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnitaryIrreducibleAdmissible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryIrreducibleSmoothAdmissibleStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyExistsDoubleCosetAntiInvolutionUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GelfandPairSphericalVectorUniqueStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonarchimedeanGroupOfIsCompactIsOpen
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsOpenIsCompactLevelOffFinEmpty
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField Filter GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.AdelicU GlobalTheory.AutMult
open GlobalTheory.PRep (IsAdmissible fixed)

namespace GlobalTheory

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hc n J hJ H _ _ π hπ`. Take `⟨R, ξ, B, hf⟩` from `h1 F E σ hc n J hJ H π hπ`. Establish `hirr : ∀ v, (smRep (Flath.finFactor R v)).IsIrreducible ∧ IsAdmissible (smRep (Flath.finFactor R v))`. Introduce `v`. Use `haveI := GlobalTheory.Doubling.nonarchimedeanGroup_GLoc σ J v`.

Conclude with `GlobalTheory.T.unitary_irreducible_smooth_admissible (GLoc σ J v) (R (.inr v)).H (Flath.finFactor R v) (R (.inr v)).isIrr (fun K hK hK' => h2 F E σ hc n J hJ v (R (.inr v)).H (Flath.finFactor R v) (R (.inr v)).isIrr K hK hK')`. Use `⟨R, ξ, B, hf, hirr, fun L hL => ?_⟩` and prove the remaining obligations. Use `haveI := hL`. Establish `hu : ∀ᶠ v in cofinite, ‖ξ (.inr v)‖ = 1` using `Sum.inr_injective.tendsto_cofinite.eventually hf.unit`. Use `filter_upwards [hu, hf.eventually_fixed L, GlobalTheory.T.eventually_exists_doubleCoset_antiInvolution_unitary F E σ hc n J hJ L hL] with v hv hfix hθ`.

Take `⟨θ, hθ1, hθ2, hθ3⟩` from `hθ`. Establish `hKo : IsOpen (stabLoc σ J L v : Set (GLoc σ J v))` using `isOpen_stabLoc σ J L v`. Establish `hKc : IsCompact (stabLoc σ J L v : Set (GLoc σ J v))` using `isCompact_stabLoc σ J L v`. Establish `sm : ∀ y, y ∈ fixed (toRep (Flath.finFactor R v)) (stabLoc σ J L v) → y ∈ GlobalTheory.PRep.smoothPart (toRep (Flath.finFactor R v))`. Introduce `y hy`.

Set `S : Subgroup (GLoc σ J v)` to `{ carrier := {g | toRep (Flath.finFactor R v) g y = y} mul_mem' := by`. Introduce `a b ha hb`. Simplify using `only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *`. Rewrite using `[hb, ha]`. Use the proof step `one_mem' := by simp`.

Use the proof step `inv_mem' := by`. Introduce `a ha`. Simplify using `only [Set.mem_setOf_eq] at *`. Use `conv_lhs => rw [← ha]`. Rewrite using `[← Module.End.mul_apply, ← map_mul]`.

Simplify using `}`. Establish `hle : stabLoc σ J L v ≤ S` using `fun k hk => GlobalTheory.LGrp.mem_fixed.1 hy k hk`. Conclude with `Subgroup.isOpen_mono hle hKo`. Establish `hξ : ξ (.inr v) ∈ fixed (toRep (Flath.finFactor R v)) (stabLoc σ J L v)` using `GlobalTheory.LGrp.mem_fixed.2 fun k hk => hfix k hk`. Set `x : GlobalTheory.PRep.smoothPart (toRep (Flath.finFactor R v))` to `⟨ξ (.inr v), sm _ hξ⟩`.

Establish `hx : x ∈ fixed (smRep (Flath.finFactor R v)) (stabLoc σ J L v)` using `GlobalTheory.LGrp.mem_fixed.2 fun k hk => Subtype.ext (GlobalTheory.LGrp.mem_fixed.1 hξ k hk)`. Establish `hx0 : x ≠ 0` using `fun e => by`. Establish `: ξ (.inr v) = 0` using `congrArg Subtype.val e`. Rewrite `hv` using `[this, norm_zero]`. Conclude with `zero_ne_one hv`.

Establish `hline` using `GlobalTheory.T.gelfand_pair_spherical_vector_unique (GLoc σ J v) (stabLoc σ J L v) hKo hKc θ hθ1 hθ2 hθ3 _ (smRep (Flath.finFactor R v)) (hirr v).1 (hirr v).2 x hx hx0`. Use `le_antisymm (fun y hy => ?_) ((Submodule.span_singleton_le_iff_mem _ _).2 hξ)` and prove the remaining obligations. Establish `hy' : (⟨y, sm y hy⟩ : GlobalTheory.PRep.smoothPart (toRep (Flath.finFactor R v))) ∈ fixed (smRep (Flath.finFactor R v)) (stabLoc σ J L v)` using `GlobalTheory.LGrp.mem_fixed.2 fun k hk => Subtype.ext (GlobalTheory.LGrp.mem_fixed.1 hy k hk)`. Rewrite `hy'` using `[hline]`. Take `⟨c, hc⟩` from `Submodule.mem_span_singleton.1 hy'`.

Conclude with `Submodule.mem_span_singleton.2 ⟨c, congrArg Subtype.val hc⟩`.
-/
theorem flathFactorisation_of_tensorProduct (h1 : GlobalTheory.Published.FlathTensorProduct)
    (h2 : GlobalTheory.Published.UnitaryIrreducibleAdmissible) : GlobalTheory.Published.FlathFactorisation := by
  intro F E _ _ _ _ _ σ hc n J hJ H _ _ π hπ
  obtain ⟨R, ξ, B, hf⟩ := h1 F E σ hc n J hJ H π hπ
  have hirr : ∀ v, (smRep (Flath.finFactor R v)).IsIrreducible ∧ IsAdmissible (smRep (Flath.finFactor R v)) := by
    intro v
    haveI := GlobalTheory.Doubling.nonarchimedeanGroup_GLoc σ J v
    exact GlobalTheory.T.unitary_irreducible_smooth_admissible (GLoc σ J v) (R (.inr v)).H (Flath.finFactor R v) (R (.inr v)).isIrr
      (fun K hK hK' => h2 F E σ hc n J hJ v (R (.inr v)).H (Flath.finFactor R v) (R (.inr v)).isIrr K hK hK')
  refine ⟨R, ξ, B, hf, hirr, fun L hL => ?_⟩
  haveI := hL
  have hu : ∀ᶠ v in cofinite, ‖ξ (.inr v)‖ = 1 := Sum.inr_injective.tendsto_cofinite.eventually hf.unit
  filter_upwards [hu, hf.eventually_fixed L, GlobalTheory.T.eventually_exists_doubleCoset_antiInvolution_unitary F E σ hc n J hJ L hL] with v hv hfix hθ
  obtain ⟨θ, hθ1, hθ2, hθ3⟩ := hθ
  have hKo : IsOpen (stabLoc σ J L v : Set (GLoc σ J v)) := isOpen_stabLoc σ J L v
  have hKc : IsCompact (stabLoc σ J L v : Set (GLoc σ J v)) := isCompact_stabLoc σ J L v
  have sm : ∀ y, y ∈ fixed (toRep (Flath.finFactor R v)) (stabLoc σ J L v) →
      y ∈ GlobalTheory.PRep.smoothPart (toRep (Flath.finFactor R v)) := by
    intro y hy
    let S : Subgroup (GLoc σ J v) :=
      { carrier := {g | toRep (Flath.finFactor R v) g y = y}
        mul_mem' := by
          intro a b ha hb
          simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *
          rw [hb, ha]
        one_mem' := by simp
        inv_mem' := by
          intro a ha
          simp only [Set.mem_setOf_eq] at *
          conv_lhs => rw [← ha]
          rw [← Module.End.mul_apply, ← map_mul]
          simp }
    have hle : stabLoc σ J L v ≤ S := fun k hk => GlobalTheory.LGrp.mem_fixed.1 hy k hk
    exact Subgroup.isOpen_mono hle hKo
  have hξ : ξ (.inr v) ∈ fixed (toRep (Flath.finFactor R v)) (stabLoc σ J L v) :=
    GlobalTheory.LGrp.mem_fixed.2 fun k hk => hfix k hk
  let x : GlobalTheory.PRep.smoothPart (toRep (Flath.finFactor R v)) := ⟨ξ (.inr v), sm _ hξ⟩
  have hx : x ∈ fixed (smRep (Flath.finFactor R v)) (stabLoc σ J L v) :=
    GlobalTheory.LGrp.mem_fixed.2 fun k hk => Subtype.ext (GlobalTheory.LGrp.mem_fixed.1 hξ k hk)
  have hx0 : x ≠ 0 := fun e => by
    have : ξ (.inr v) = 0 := congrArg Subtype.val e
    rw [this, norm_zero] at hv
    exact zero_ne_one hv
  have hline := GlobalTheory.T.gelfand_pair_spherical_vector_unique (GLoc σ J v) (stabLoc σ J L v) hKo hKc θ hθ1 hθ2 hθ3 _
    (smRep (Flath.finFactor R v)) (hirr v).1 (hirr v).2 x hx hx0
  refine le_antisymm (fun y hy => ?_) ((Submodule.span_singleton_le_iff_mem _ _).2 hξ)
  have hy' : (⟨y, sm y hy⟩ : GlobalTheory.PRep.smoothPart (toRep (Flath.finFactor R v))) ∈
      fixed (smRep (Flath.finFactor R v)) (stabLoc σ J L v) :=
    GlobalTheory.LGrp.mem_fixed.2 fun k hk => Subtype.ext (GlobalTheory.LGrp.mem_fixed.1 hy k hk)
  rw [hline] at hy'
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hy'
  exact Submodule.mem_span_singleton.2 ⟨c, congrArg Subtype.val hc⟩

end GlobalTheory
