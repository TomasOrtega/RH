import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerSeriesEvalTwoGroupsRules

set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.Katz.LawMonoid

variable {R : Type} [CommRing R] {d : ℕ}

/- English proof (translation)
The claim follows from `(GlobalTheory.Katz.SubstCalc.powerSeriesEvalTwoGroups_rules_alt R d τ τ u v hu hv).2.2.2.1 c`.
-/
theorem constantCoeff_bivariateSeriesSubstPair {τ : Type} [Finite τ] {u v : Fin d → MvPowerSeries τ R}
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0)
    (c : MvPowerSeries (Fin d ⊕ Fin d) R) : constantCoeff (at2 c u v) = constantCoeff c :=
  (GlobalTheory.Katz.SubstCalc.powerSeriesEvalTwoGroups_rules_alt R d τ τ u v hu hv).2.2.2.1 c

/- English proof (translation)
The claim follows from `(GlobalTheory.Katz.SubstCalc.powerSeriesEvalTwoGroups_rules_alt R d τ τ u v hu hv).2.2.2.2.1 c`.
-/
theorem powerSeriesEvalTwoGroups_swapVariableGroups {τ : Type} [Finite τ] {u v : Fin d → MvPowerSeries τ R}
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0)
    (c : MvPowerSeries (Fin d ⊕ Fin d) R) : at2 (swap c) u v = at2 c v u :=
  (GlobalTheory.Katz.SubstCalc.powerSeriesEvalTwoGroups_rules_alt R d τ τ u v hu hv).2.2.2.2.1 c

/- English proof (translation)
Use `show constantCoeff (at2 (μ i) u v) = 0`. Rewrite using `[constantCoeff_bivariateSeriesSubstPair hu hv, hμ]`.
-/
theorem cc_op {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R} (hμ : ∀ i, constantCoeff (μ i) = 0)
    {τ : Type} [Finite τ] {u v : Fin d → MvPowerSeries τ R}
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0) (i : Fin d) :
    constantCoeff (op μ u v i) = 0 := by
  show constantCoeff (at2 (μ i) u v) = 0
  rw [constantCoeff_bivariateSeriesSubstPair hu hv, hμ]

/- English proof (translation)
The claim follows from `GlobalTheory.Katz.SubstCalc.subst_powerSeriesEvalTwoGroups hu hv ha (μ i)`.
-/
theorem subst_op {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R}
    {τ τ' : Type} [Finite τ] {u v : Fin d → MvPowerSeries τ R}
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0)
    (a : τ → MvPowerSeries τ' R) (ha : ∀ t, constantCoeff (a t) = 0) (i : Fin d) :
    subst a (op μ u v i) = op μ (fun j => subst a (u j)) (fun j => subst a (v j)) i :=
  GlobalTheory.Katz.SubstCalc.subst_powerSeriesEvalTwoGroups hu hv ha (μ i)

/- English proof (translation)
The claim follows from `constantCoeff_X s`.
-/
theorem constantCoeff_mvPowerSeries_X_eq_zero {τ : Type} (s : τ) : constantCoeff (X s : MvPowerSeries τ R) = 0 := constantCoeff_X s

/- English proof (translation)
Introduce `R _ d μ hμ τ _ u v w hu hv hw`. Use `⟨cc_op hμ.const hu hv, ?_, ?_, ?_, fun τ' a ha i => subst_op hu hv a ha i⟩` and prove the remaining obligations. Set `a : Fin d ⊕ (Fin d ⊕ Fin d) → MvPowerSeries τ R` to `Sum.elim u (Sum.elim v w)`. Establish `ha : ∀ t, constantCoeff (a t) = 0`. Introduce `t`.

Break down `t with t | t | t` into its components or cases. Conclude with `hu t`. Conclude with `hv t`. Conclude with `hw t`. Establish `hs : HasSubst a` using `hasSubst_of_constantCoeff_zero ha`.

Establish `h1 : (fun j => subst a ((x1 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) j)) = u`. Use function extensionality and compare the values at `j`. Simplify using `only [x1]`. Rewrite using `[subst_X hs]`. Both sides reduce to the same expression.

Establish `h2 : (fun j => subst a ((x2 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) j)) = v`. Use function extensionality and compare the values at `j`. Simplify using `only [x2]`. Rewrite using `[subst_X hs]`. Both sides reduce to the same expression.

Establish `h3 : (fun j => subst a ((x3 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) j)) = w`. Use function extensionality and compare the values at `j`. Simplify using `only [x3]`. Rewrite using `[subst_X hs]`. Both sides reduce to the same expression.

Establish `hx1 : ∀ j, constantCoeff ((x1 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) j) = 0` using `fun j => constantCoeff_mvPowerSeries_X_eq_zero _`. Establish `hx2 : ∀ j, constantCoeff ((x2 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) j) = 0` using `fun j => constantCoeff_mvPowerSeries_X_eq_zero _`. Establish `hx3 : ∀ j, constantCoeff ((x3 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) j) = 0` using `fun j => constantCoeff_mvPowerSeries_X_eq_zero _`. Use function extensionality and compare the values at `i`. Establish `e` using `congrArg (fun F => subst a (F i)) hμ.assoc`.

Apply the tactic sequence `try simp only at e`. Rewrite `e` using `[subst_op (cc_op hμ.const hx1 hx2) hx3 a ha, subst_op hx1 (cc_op hμ.const hx2 hx3) a ha]`. Establish `e1 : (fun j => subst a (op μ x1 x2 j)) = op μ u v`. Use function extensionality and compare the values at `j`. Rewrite using `[subst_op hx1 hx2 a ha, h1, h2]`.

Establish `e2 : (fun j => subst a (op μ x2 x3 j)) = op μ v w`. Use function extensionality and compare the values at `j`. Rewrite using `[subst_op hx2 hx3 a ha, h2, h3]`. Rewrite `e` using `[e1, e2, h1, h3]`. Conclude with `e`.

Use function extensionality and compare the values at `i show at2 (μ i) u v = at2 (μ i) v u`. Rewrite using `[← powerSeriesEvalTwoGroups_swapVariableGroups hu hv, hμ.comm i]`. Establish `hs : HasSubst u` using `hasSubst_of_constantCoeff_zero hu`. Establish `hX : ∀ j, constantCoeff ((X j : MvPowerSeries (Fin d) R)) = 0` using `fun j => constantCoeff_X j`. Establish `h0 : ∀ j : Fin d, constantCoeff ((fun _ : Fin d => (0 : MvPowerSeries (Fin d) R)) j) = 0` using `fun _ => map_zero _`.

Use function extensionality and compare the values at `i`. Establish `e` using `congrArg (fun F => subst u (F i)) hμ.unit`. Apply the tactic sequence `try simp only at e`. Rewrite `e` using `[subst_op hX h0 u hu, subst_X hs]`. Establish `e1 : (fun j => subst u ((X j : MvPowerSeries (Fin d) R))) = u`.

Use function extensionality and compare the values at `j`. Rewrite using `[subst_X hs]`. Establish `e0 : (fun j : Fin d => subst u ((fun _ : Fin d => (0 : MvPowerSeries (Fin d) R)) j)) = fun _ => 0`. Use function extensionality and compare the values at `j`. Use `show subst u (0 : MvPowerSeries (Fin d) R) = 0`.

Rewrite using `[← coe_substAlgHom hs]`. Conclude with `map_zero _`. Rewrite `e` using `[e1, e0]`. Conclude with `e`.
-/
theorem mon : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), IsLaw μ → ∀ (τ : Type) [Finite τ] (u v w : Fin d → MvPowerSeries τ R), (∀ i, constantCoeff (u i) = 0) → (∀ i, constantCoeff (v i) = 0) → (∀ i, constantCoeff (w i) = 0) → (∀ i, constantCoeff (op μ u v i) = 0) ∧ op μ (op μ u v) w = op μ u (op μ v w) ∧ op μ u v = op μ v u ∧ op μ u (fun _ => 0) = u ∧ ∀ (τ' : Type) (a : τ → MvPowerSeries τ' R), (∀ t, constantCoeff (a t) = 0) → ∀ i, subst a (op μ u v i) = op μ (fun j => subst a (u j)) (fun j => subst a (v j)) i := by
  intro R _ d μ hμ τ _ u v w hu hv hw
  refine ⟨cc_op hμ.const hu hv, ?_, ?_, ?_, fun τ' a ha i => subst_op hu hv a ha i⟩
  ·
    let a : Fin d ⊕ (Fin d ⊕ Fin d) → MvPowerSeries τ R := Sum.elim u (Sum.elim v w)
    have ha : ∀ t, constantCoeff (a t) = 0 := by
      intro t; rcases t with t | t | t
      · exact hu t
      · exact hv t
      · exact hw t
    have hs : HasSubst a := hasSubst_of_constantCoeff_zero ha
    have h1 : (fun j => subst a ((x1 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) j)) = u := by
      funext j; simp only [x1]; rw [subst_X hs]; rfl
    have h2 : (fun j => subst a ((x2 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) j)) = v := by
      funext j; simp only [x2]; rw [subst_X hs]; rfl
    have h3 : (fun j => subst a ((x3 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) j)) = w := by
      funext j; simp only [x3]; rw [subst_X hs]; rfl
    have hx1 : ∀ j, constantCoeff ((x1 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) j) = 0 :=
      fun j => constantCoeff_mvPowerSeries_X_eq_zero _
    have hx2 : ∀ j, constantCoeff ((x2 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) j) = 0 :=
      fun j => constantCoeff_mvPowerSeries_X_eq_zero _
    have hx3 : ∀ j, constantCoeff ((x3 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) j) = 0 :=
      fun j => constantCoeff_mvPowerSeries_X_eq_zero _
    funext i
    have e := congrArg (fun F => subst a (F i)) hμ.assoc
    try simp only at e
    rw [subst_op (cc_op hμ.const hx1 hx2) hx3 a ha, subst_op hx1 (cc_op hμ.const hx2 hx3) a ha] at e
    have e1 : (fun j => subst a (op μ x1 x2 j)) = op μ u v := by
      funext j; rw [subst_op hx1 hx2 a ha, h1, h2]
    have e2 : (fun j => subst a (op μ x2 x3 j)) = op μ v w := by
      funext j; rw [subst_op hx2 hx3 a ha, h2, h3]
    rw [e1, e2, h1, h3] at e
    exact e
  · funext i
    show at2 (μ i) u v = at2 (μ i) v u
    rw [← powerSeriesEvalTwoGroups_swapVariableGroups hu hv, hμ.comm i]
  ·
    have hs : HasSubst u := hasSubst_of_constantCoeff_zero hu
    have hX : ∀ j, constantCoeff ((X j : MvPowerSeries (Fin d) R)) = 0 := fun j => constantCoeff_X j
    have h0 : ∀ j : Fin d, constantCoeff ((fun _ : Fin d => (0 : MvPowerSeries (Fin d) R)) j) = 0 := fun _ => map_zero _
    funext i
    have e := congrArg (fun F => subst u (F i)) hμ.unit
    try simp only at e
    rw [subst_op hX h0 u hu, subst_X hs] at e
    have e1 : (fun j => subst u ((X j : MvPowerSeries (Fin d) R))) = u := by
      funext j; rw [subst_X hs]
    have e0 : (fun j : Fin d => subst u ((fun _ : Fin d => (0 : MvPowerSeries (Fin d) R)) j)) = fun _ => 0 := by
      funext j; show subst u (0 : MvPowerSeries (Fin d) R) = 0
      rw [← coe_substAlgHom hs]; exact map_zero _
    rw [e1, e0] at e
    exact e

end GlobalTheory.Katz.LawMonoid
