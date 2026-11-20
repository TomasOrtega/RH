import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CubWeilOfInjective
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj

namespace GlobalTheory

/- English proof (translation)
Introduce `T C _ _ V ι' h`. Establish `hnn : ∀ a : T.V, 0 ≤ vV T.V (algebraMap T.V T.Fr a)`. Introduce `a`. Unfold `vV`. Distinguish the cases in `ha : valV T.V (algebraMap T.V T.Fr a) = 0`.

Simplify using `[ha]`. Establish `h1 : valV T.V (algebraMap T.V T.Fr a) ≤ 1` using `IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ a`. Use `(WithZero.log_le_log ha one_ne_zero).2 h1` as an intermediate fact. Simplify using `at this`. Use linear arithmetic over natural numbers and integers.

Establish `hl0 : vV T.V ((V.l : ℕ) : T.Fr) ≠ 0`. Introduce `h0`. Establish `hl : ((V.l : ℕ) : T.Fr) ≠ 0` using `Nat.cast_ne_zero.2 V.l_prime.ne_zero`. Use `h _ hl` as an intermediate fact. Rewrite `this` using `[map_natCast, V.v_l, h0]`.

Simplify using `at this`. Establish `hl : (0 : ℝ) < (vV T.V ((V.l : ℕ) : T.Fr) : ℝ)`. Establish `h0` using `hnn (V.l : T.V)`. Rewrite `h0` using `[map_natCast]`. Conclude with `lt_of_le_of_ne h0 hl0.symm` after adjusting the coercions.

Establish `hR : ∀ x : T.V, (ι'.comp (algebraMap T.V T.Fr)) x ∈ V.RR`. Introduce `x`. Use `show V.Ge 0 (ι' (algebraMap T.V T.Fr x))`. Distinguish the cases in `h0 : algebraMap T.V T.Fr x = 0`. Rewrite using `[h0, map_zero]`.

Conclude with `VF.Ge.zero 0`. Unfold `VF.Ge`. Rewrite using `[h _ h0]`. Conclude with `WithTop.coe_le_coe.2 (div_nonneg (by exact_mod_cast hnn x) hl.le)`. Use `⟨(ι'.comp (algebraMap T.V T.Fr)).codRestrict V.RR hR, fun x => rfl, fun x hx => ?_⟩` and prove the remaining obligations.

Establish `key : ((0 : ℝ) : WithTop ℝ) < V.v (ι' (algebraMap T.V T.Fr x))`. Distinguish the cases in `h0 : algebraMap T.V T.Fr x = 0`. Rewrite using `[h0, map_zero, V.v.map_zero]`. Conclude with `WithTop.coe_lt_top _`. Rewrite using `[h _ h0]`.

Establish `h2 : valV T.V (algebraMap T.V T.Fr x) < 1`. Unfold `valV`. Rewrite using `[IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem]`. Conclude with `hx`. Establish `h3` using `(WithZero.log_lt_log (valV_ne_zero h0) one_ne_zero).2 h2`.

Establish `h4 : 0 < vV T.V (algebraMap T.V T.Fr x)`. Simplify using `at h3`. Unfold `vV`. Use linear arithmetic over natural numbers and integers. Conclude with `WithTop.coe_lt_coe.2 (div_pos (by exact_mod_cast h4) hl)`.

Conclude with `key`.
-/
theorem embOK_exists_ringHom :
    ∀ (T : CDVR) (C : Type) [Field C] [CharZero C] (V : VF C) (ι' : T.Fr →+* C), EmbOK T V ι' → ∃ j : T.V →+* V.RR, (∀ x, (j x : C) = ι' (algebraMap T.V T.Fr x)) ∧ ∀ x ∈ maximalIdeal T.V, V.MM (j x : C) := by
  intro T C _ _ V ι' h
  have hnn : ∀ a : T.V, 0 ≤ vV T.V (algebraMap T.V T.Fr a) := by
    intro a
    unfold vV
    by_cases ha : valV T.V (algebraMap T.V T.Fr a) = 0
    · simp [ha]
    have h1 : valV T.V (algebraMap T.V T.Fr a) ≤ 1 :=
      IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ a
    have := (WithZero.log_le_log ha one_ne_zero).2 h1
    simp at this
    omega
  have hl0 : vV T.V ((V.l : ℕ) : T.Fr) ≠ 0 := by
    intro h0
    have hl : ((V.l : ℕ) : T.Fr) ≠ 0 := Nat.cast_ne_zero.2 V.l_prime.ne_zero
    have := h _ hl
    rw [map_natCast, V.v_l, h0] at this
    simp at this
  have hl : (0 : ℝ) < (vV T.V ((V.l : ℕ) : T.Fr) : ℝ) := by
    have h0 := hnn (V.l : T.V)
    rw [map_natCast] at h0
    exact_mod_cast lt_of_le_of_ne h0 hl0.symm
  have hR : ∀ x : T.V, (ι'.comp (algebraMap T.V T.Fr)) x ∈ V.RR := by
    intro x
    show V.Ge 0 (ι' (algebraMap T.V T.Fr x))
    by_cases h0 : algebraMap T.V T.Fr x = 0
    · rw [h0, map_zero]; exact VF.Ge.zero 0
    unfold VF.Ge
    rw [h _ h0]
    exact WithTop.coe_le_coe.2 (div_nonneg (by exact_mod_cast hnn x) hl.le)
  refine ⟨(ι'.comp (algebraMap T.V T.Fr)).codRestrict V.RR hR, fun x => rfl, fun x hx => ?_⟩
  have key : ((0 : ℝ) : WithTop ℝ) < V.v (ι' (algebraMap T.V T.Fr x)) := by
    by_cases h0 : algebraMap T.V T.Fr x = 0
    · rw [h0, map_zero, V.v.map_zero]; exact WithTop.coe_lt_top _
    rw [h _ h0]
    have h2 : valV T.V (algebraMap T.V T.Fr x) < 1 := by
      unfold valV
      rw [IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem]
      exact hx
    have h3 := (WithZero.log_lt_log (valV_ne_zero h0) one_ne_zero).2 h2
    have h4 : 0 < vV T.V (algebraMap T.V T.Fr x) := by
      simp at h3
      unfold vV
      omega
    exact WithTop.coe_lt_coe.2 (div_pos (by exact_mod_cast h4) hl)
  exact key

end GlobalTheory
