import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IntegerSubgroupIntersection.IntInter

noncomputable section

namespace PI.GaugeCharW

/- English proof (translation)
Introduce `G _ _ _ K U hU g hg hKU`. Set `j : K →+ G ⧸ U` to `(QuotientAddGroup.mk' U).comp K.subtype`. Establish `hker : ∀ k ∈ j.ker, g.comp K.subtype k = 0`. Introduce `k hk`. Establish `hkU : (k : G) ∈ U` using `(QuotientAddGroup.eq_zero_iff _).mp hk`.

Conclude with `hKU k k.2 hkU`. Set `g' : K ⧸ j.ker →+ AddCircle (1 : ℝ)` to `QuotientAddGroup.lift j.ker (g.comp K.subtype) hker`. Take `⟨η', hη'⟩` from `(Module.Baer.of_divisible (AddCircle (1 : ℝ))).extension_property_addMonoidHom (QuotientAddGroup.kerLift j) (QuotientAddGroup.kerLift_injective j) g'`. Set `η : G →+ AddCircle (1 : ℝ)` to `η'.comp (QuotientAddGroup.mk' U)`. Establish `hηU : ∀ x ∈ U, η x = 0` using `fun x hx => by show η' (QuotientAddGroup.mk' U x) = 0`.

Rewrite using `[QuotientAddGroup.mk'_apply, (QuotientAddGroup.eq_zero_iff x).mpr hx, map_zero]`. Use `⟨g - η, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `continuous_of_continuousAt_zero (g - η) ?_` and prove the remaining obligations. Establish `hmem : (U : Set G) ∈ nhds (0 : G)` using `hU.mem_nhds U.zero_mem`. Use `hg.continuousAt.congr ?_` and prove the remaining obligations.

Use `filter_upwards [hmem] with u hu`. Rewrite using `[AddMonoidHom.sub_apply, hηU u hu, sub_zero]`. Introduce `x hx`. Establish `h1 : η x = g' (QuotientAddGroup.mk (⟨x, hx⟩ : K))`. Rewrite using `[← hη']`.

Both sides reduce to the same expression. Rewrite using `[AddMonoidHom.sub_apply, h1]`. Use `show g x - (g.comp K.subtype) ⟨x, hx⟩ = 0`. Conclude with `sub_self _`. Introduce `x hx`.

Rewrite using `[AddMonoidHom.sub_apply, hηU x hx, sub_zero]`.
-/
theorem extChar : ExtChar := by
  intro G _ _ _ K U hU g hg hKU
  let j : K →+ G ⧸ U := (QuotientAddGroup.mk' U).comp K.subtype
  have hker : ∀ k ∈ j.ker, g.comp K.subtype k = 0 := by
    intro k hk
    have hkU : (k : G) ∈ U := (QuotientAddGroup.eq_zero_iff _).mp hk
    exact hKU k k.2 hkU
  let g' : K ⧸ j.ker →+ AddCircle (1 : ℝ) := QuotientAddGroup.lift j.ker (g.comp K.subtype) hker
  obtain ⟨η', hη'⟩ := (Module.Baer.of_divisible (AddCircle (1 : ℝ))).extension_property_addMonoidHom
    (QuotientAddGroup.kerLift j) (QuotientAddGroup.kerLift_injective j) g'
  let η : G →+ AddCircle (1 : ℝ) := η'.comp (QuotientAddGroup.mk' U)
  have hηU : ∀ x ∈ U, η x = 0 := fun x hx => by
    show η' (QuotientAddGroup.mk' U x) = 0
    rw [QuotientAddGroup.mk'_apply, (QuotientAddGroup.eq_zero_iff x).mpr hx, map_zero]
  refine ⟨g - η, ?_, ?_, ?_⟩
  · refine continuous_of_continuousAt_zero (g - η) ?_
    have hmem : (U : Set G) ∈ nhds (0 : G) := hU.mem_nhds U.zero_mem
    refine hg.continuousAt.congr ?_
    filter_upwards [hmem] with u hu
    rw [AddMonoidHom.sub_apply, hηU u hu, sub_zero]
  · intro x hx
    have h1 : η x = g' (QuotientAddGroup.mk (⟨x, hx⟩ : K)) := by
      rw [← hη']; rfl
    rw [AddMonoidHom.sub_apply, h1]
    show g x - (g.comp K.subtype) ⟨x, hx⟩ = 0
    exact sub_self _
  · intro x hx
    rw [AddMonoidHom.sub_apply, hηU x hx, sub_zero]

end PI.GaugeCharW
