import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSNef

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

/- English proof (translation)
Establish `e : (shiftA P u).nu a b σ y f = ‖ratVal (P.loc a b f (pick (P.L.φ σ).isLB y) (pick (P.A.φ σ).isLB y)) y‖ * Real.exp (-(a * (P.L.φ σ).φ (pick (P.L.φ σ).isLB y) y + b * ((P.A.φ σ).φ (pick (P.A.φ σ).isLB y) y + 2 * u)) / 2)` using `rfl`. Rewrite using `[e, Pair.nu, mul_assoc, ← Real.exp_add]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem shiftA_nu (P : Pair p) (u : ℝ) (a b : ℤ) (σ : k →+* ℂ) (y : CxPts p σ) (f : X.functionField) :
    (shiftA P u).nu a b σ y f = P.nu a b σ y f * Real.exp (-(b * u)) := by
  have e : (shiftA P u).nu a b σ y f = ‖ratVal (P.loc a b f (pick (P.L.φ σ).isLB y) (pick (P.A.φ σ).isLB y)) y‖ *
      Real.exp (-(a * (P.L.φ σ).φ (pick (P.L.φ σ).isLB y) y +
        b * ((P.A.φ σ).φ (pick (P.A.φ σ).isLB y) y + 2 * u)) / 2) := rfl
  rw [e, Pair.nu, mul_assoc, ← Real.exp_add]
  congr 2
  ring

/- English proof (translation)
Use extensionality with `f`. Simplify using `only [Pair.Bl, Set.mem_setOf_eq, shiftA_H, shiftA_nu]`. Use `and_congr_right fun _ => forall_congr' fun σ => forall_congr' fun y => ?_` and prove the remaining obligations. Rewrite using `[Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]`.
-/
theorem shiftA_Bl (P : Pair p) (u : ℝ) (a b : ℤ) (R : ℝ) :
    (shiftA P u).Bl a b R = P.Bl a b (R * Real.exp (b * u)) := by
  ext f
  simp only [Pair.Bl, Set.mem_setOf_eq, shiftA_H, shiftA_nu]
  refine and_congr_right fun _ => forall_congr' fun σ => forall_congr' fun y => ?_
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]

/- English proof (translation)
Take `⟨n, v, hv, hg⟩` from `h`. Use `⟨n, v, fun i => by rw [shiftA_H]; exact hv i, fun σ y => ?_⟩` and prove the remaining obligations. Take `⟨i, hi⟩` from `hg σ y`. Conclude with `⟨i, by rw [shiftA_nu]; exact mul_ne_zero hi (Real.exp_pos _).ne'⟩`.
-/
theorem genAt_shiftA (P : Pair p) (u : ℝ) (c : ℕ) (h : GenAt P c) : GenAt (shiftA P u) c := by
  obtain ⟨n, v, hv, hg⟩ := h
  refine ⟨n, v, fun i => by rw [shiftA_H]; exact hv i, fun σ y => ?_⟩
  obtain ⟨i, hi⟩ := hg σ y
  exact ⟨i, by rw [shiftA_nu]; exact mul_ne_zero hi (Real.exp_pos _).ne'⟩

/- English proof (translation)
Introduce `_ _ _ _ _ P u` and use `⟨shiftA_nu P u, shiftA_Bl P u, genAt_shiftA P u⟩`.
-/
theorem shiftA_props : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k), ∀ (P : Pair p) (u : ℝ), (∀ (a b : ℤ) (σ : k →+* ℂ) (y : CxPts p σ) (f : X.functionField), (shiftA P u).nu a b σ y f = P.nu a b σ y f * Real.exp (-(b * u))) ∧ (∀ (a b : ℤ) (R : ℝ), (shiftA P u).Bl a b R = P.Bl a b (R * Real.exp (b * u))) ∧ (∀ c : ℕ, GenAt P c → GenAt (shiftA P u) c) :=
  fun _ _ _ _ _ P u => ⟨shiftA_nu P u, shiftA_Bl P u, genAt_shiftA P u⟩

end GlobalTheory.HSNef
