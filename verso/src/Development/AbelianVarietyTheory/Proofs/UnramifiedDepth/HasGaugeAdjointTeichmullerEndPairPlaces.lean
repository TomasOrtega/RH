import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.NondegenerateCharts
import Formalism.LocalToGlobal.CharacterGerms.RowTieSelf
import Formalism.LocalToGlobal.CharacterGerms.BlockAdmissibleChart
import Formalism.LocalToGlobal.CharacterGerms.NegMem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsAdjointIntegralEndOfLadicLimitStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.EqZeroOfGe

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.TeichPair

/- English proof (translation)
Introduce `C _ _ V O _ _ dd Y d _ I _ p g`. Take `⟨s, N, ζ, hs, hN, h1, h2, h3, hζ⟩` from `exists_seq V Y.cpl (p.em g) (p.em_int g) (p.em_frob g) (fun a a' h => p.em_sep (g, a) (g, a') fun h' => h (congrArg Prod.snd h')) (p.em_unr g)`. Take `⟨M, M', hM, -, hl, hl'⟩` from `GlobalTheory.T.exists_adjointIntegralEnd_of_ladicLimit C V O dd Y d I p s hs`. Establish `key : ∀ (a : ZMod d) (z w : C), V.Ge 0 w → (∀ N : ℕ, ∃ n0, ∀ n ≥ n0, V.Ge N (z - p.em g a (s n) * w)) → z = ζ a * w` using `fun a z w hw h => by`. Rewrite using `[← sub_eq_zero]`.

Use `eq_zero_of_ge (V := V) fun n => ?_` and prove the remaining obligations. Take `⟨n0, hn⟩` from `h n`. Establish `e1` using `hn (max n0 n) (le_max_left _ _)`. Establish `e2` using `(hw.mul_int (hζ a (max n0 n))).mono (w' := n) (by exact_mod_cast le_max_right _ _)`. Use `e1.sub e2` as an intermediate fact.

Use `this using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Establish `hconj : ∀ a x, p.em (1 - g) a (star x) = p.em g a x` using `fun a x => by fin_cases g`. Use `show p.em 1 a (star x) = p.em 0 a x`. Rewrite using `[p.em_conj, star_star]`.

Use `show p.em 0 a (star x) = p.em 1 a x`. Rewrite using `[p.em_conj]`. Use `⟨N, ζ, M, M', hN, h1, h2, h3, hM, fun c => funext fun i => ?_, fun q => funext fun i => ?_⟩` and prove the remaining obligations. Use `key _ _ _ (p.u_int g c i) fun n => ?_` and prove the remaining obligations. Use `hl n (p.u g c) i` as an intermediate fact.

Simplify using `only [p.u_eig] at this`. Conclude with `this`. Use `key _ _ _ (p.u_int (1 - g) q i) fun n => ?_` and prove the remaining obligations. Use `hl' n (p.u (1 - g) q) i` as an intermediate fact. Simplify using `only [p.u_eig, hconj] at this`.

Conclude with `this`.
-/
theorem hasTeich : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (p : PairData Y d I), ∀ g, HasTeich (Y.raw p) V g := by
  intro C _ _ V O _ _ dd Y d _ I _ p g
  obtain ⟨s, N, ζ, hs, hN, h1, h2, h3, hζ⟩ := exists_seq V Y.cpl (p.em g) (p.em_int g) (p.em_frob g)
    (fun a a' h => p.em_sep (g, a) (g, a') fun h' => h (congrArg Prod.snd h')) (p.em_unr g)
  obtain ⟨M, M', hM, -, hl, hl'⟩ := GlobalTheory.T.exists_adjointIntegralEnd_of_ladicLimit C V O dd Y d I p s hs
  have key : ∀ (a : ZMod d) (z w : C), V.Ge 0 w →
      (∀ N : ℕ, ∃ n0, ∀ n ≥ n0, V.Ge N (z - p.em g a (s n) * w)) → z = ζ a * w := fun a z w hw h => by
    rw [← sub_eq_zero]
    refine eq_zero_of_ge (V := V) fun n => ?_
    obtain ⟨n0, hn⟩ := h n
    have e1 := hn (max n0 n) (le_max_left _ _)
    have e2 := (hw.mul_int (hζ a (max n0 n))).mono (w' := n) (by exact_mod_cast le_max_right _ _)
    have := e1.sub e2
    convert this using 1
    ring
  have hconj : ∀ a x, p.em (1 - g) a (star x) = p.em g a x := fun a x => by
    fin_cases g
    · show p.em 1 a (star x) = p.em 0 a x
      rw [p.em_conj, star_star]
    · show p.em 0 a (star x) = p.em 1 a x
      rw [p.em_conj]
  refine ⟨N, ζ, M, M', hN, h1, h2, h3, hM, fun c => funext fun i => ?_, fun q => funext fun i => ?_⟩
  · refine key _ _ _ (p.u_int g c i) fun n => ?_
    have := hl n (p.u g c) i
    simp only [p.u_eig] at this
    exact this
  · refine key _ _ _ (p.u_int (1 - g) q i) fun n => ?_
    have := hl' n (p.u (1 - g) q) i
    simp only [p.u_eig, hconj] at this
    exact this

end GlobalTheory.TeichPair
