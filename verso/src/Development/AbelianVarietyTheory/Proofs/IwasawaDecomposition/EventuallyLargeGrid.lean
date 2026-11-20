import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GKeyFin
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowRatW
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodReductionCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionMv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResCharConj
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.RowEx GlobalTheory.Mem.LiteralAutomorphy
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.LiteralAutomorphy

/- English proof (translation)
Introduce `h`. Take `⟨CF0, hCF⟩` from `h`. Use `⟨CF0, fun CF hC => ?_⟩` and prove the remaining obligations. Use `⟨1 / 100, by norm_num, fun eps C8 C5 c6 Cb _ _ _ _ => ?_⟩` and prove the remaining obligations. Take `⟨x₀, hx⟩` from `hCF eps CF hC`.

Use `⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun C _ _ _ => ⟨0, fun cD _ => ⟨0, fun ch _ => ⟨x₀, fun K _ _ _ hKe hKx _ => ?_⟩⟩⟩⟩` and prove the remaining obligations. Establish `hS` using `fun (P : Pre) (f : Fr P) (Ξ : Set (Formalism.L2.Host.HChar P.host.E)) (hΞ : Ξ.Finite) => hx K.s hKe hKx P f Ξ hΞ`. Use `⟨fun _ _ _ => ∅, fun _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, fun P f _ _ Ξ => if hΞ : Ξ.Finite then Classical.choose (hS P f Ξ hΞ) else ∅, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `B f F z hz`. Simplify using `at hz`.

Introduce `B f F F₀ Ξ z hz`. Distinguish the cases in `hΞ : Ξ.Finite`. Simplify using `only [dif_pos hΞ] at hz`. Conclude with `(Classical.choose_spec (hS B f Ξ hΞ)).1 z hz`. Simplify using `[dif_neg hΞ] at hz`.

Introduce `B f T _ hHas _ _ C W V S N G`. Establish `hfin` using `(GlobalTheory.Mem.Top.TwFin.tw_fin B f T).1`. Establish `hspec` using `(Classical.choose_spec (hS B.toPre f (T.set f) hfin)).2`. Use `hspec ⟨B, C, W, V, S, N, G⟩ f (T.set f) rfl HEq.rfl HEq.rfl ?_` and prove the remaining obligations. Introduce `z hz`.

Establish `h2` using `hHas.2 z`. Simplify using `only [dif_pos hfin] at h2`. Conclude with `h2 hz`.
-/
theorem evLgG_gridA_of_exGrid : ExGrid → ∃ CF0 : ℝ, ∀ CF, CF0 ≤ CF → EvLgG (GridA CF) := by
  classical
  intro h
  obtain ⟨CF0, hCF⟩ := h
  refine ⟨CF0, fun CF hC => ?_⟩
  refine ⟨1 / 100, by norm_num, fun eps C8 C5 c6 Cb _ _ _ _ => ?_⟩
  obtain ⟨x₀, hx⟩ := hCF eps CF hC
  refine ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun C _ _ _ => ⟨0, fun cD _ => ⟨0, fun ch _ =>
    ⟨x₀, fun K _ _ _ hKe hKx _ => ?_⟩⟩⟩⟩
  have hS := fun (P : Pre) (f : Fr P) (Ξ : Set (Formalism.L2.Host.HChar P.host.E)) (hΞ : Ξ.Finite) =>
    hx K.s hKe hKx P f Ξ hΞ
  refine ⟨fun _ _ _ => ∅, fun _ _ _ _ => ∅, fun _ _ _ _ _ => ∅,
    fun P f _ _ Ξ => if hΞ : Ξ.Finite then Classical.choose (hS P f Ξ hΞ) else ∅, ?_, ?_, ?_⟩
  · intro B f F z hz
    simp at hz
  · intro B f F F₀ Ξ z hz
    by_cases hΞ : Ξ.Finite
    · simp only [dif_pos hΞ] at hz
      exact (Classical.choose_spec (hS B f Ξ hΞ)).1 z hz
    · simp [dif_neg hΞ] at hz
  · intro B f T _ hHas _ _ C W V S N G
    have hfin := (GlobalTheory.Mem.Top.TwFin.tw_fin B f T).1
    have hspec := (Classical.choose_spec (hS B.toPre f (T.set f) hfin)).2
    refine hspec ⟨B, C, W, V, S, N, G⟩ f (T.set f) rfl HEq.rfl HEq.rfl ?_
    intro z hz
    have h2 := hHas.2 z
    simp only [dif_pos hfin] at h2
    exact h2 hz

/- English proof (translation)
The claim follows from `evLgG_gridA_of_exGrid`.
-/
example : ExGrid → ∃ CF0 : ℝ, ∀ CF, CF0 ≤ CF → EvLgG (GridA CF) := evLgG_gridA_of_exGrid

end GlobalTheory.Mem.LiteralAutomorphy
