import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.VolGe
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.VolBr

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

namespace Pair

/- English proof (translation)
Establish `hx : x ∈ M.B.U c ⊓ M.B.U i` using `⟨hc, hi⟩`. Rewrite using `[hρ c i (gen_mem hx), mul_div_cancel_right₀ _ (ρ i).ne_zero]`. Conclude with `unitAt_fnOf hx _ _`.
-/
theorem unitAt_div_of_isRatSec (M : HermLB p) {ρ : M.B.ι → X.functionFieldˣ} (hρ : IsRatSec M.B ρ)
    {x : X} {c i : M.B.ι} (hc : x ∈ M.B.U c) (hi : x ∈ M.B.U i) :
    UnitAt x ((ρ c : X.functionField) / (ρ i : X.functionField)) := by
  have hx : x ∈ M.B.U c ⊓ M.B.U i := ⟨hc, hi⟩
  rw [hρ c i (gen_mem hx), mul_div_cancel_right₀ _ (ρ i).ne_zero]
  exact unitAt_fnOf hx _ _

/- English proof (translation)
Establish `hy` using `mem_ptsIn_inf.2 ⟨hc, hi⟩`. Rewrite using `[hρ c i (gen_mem (mem_ptsIn.1 hy)), mul_div_cancel_right₀ _ (ρ i).ne_zero, ratVal_fnOf hy, (M.φ σ).trans c i y hc hi, Real.log_pow]`. Simplify using `only [GlobalTheory.CxPts.gv]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem log_norm_div_of_isRatSec (M : HermLB p) {ρ : M.B.ι → X.functionFieldˣ} (hρ : IsRatSec M.B ρ)
    (σ : k →+* ℂ) {y : CxPts p σ} {c i : M.B.ι} (hc : y ∈ ptsIn p σ (M.B.U c))
    (hi : y ∈ ptsIn p σ (M.B.U i)) :
    Real.log ‖ratVal ((ρ c : X.functionField) / (ρ i : X.functionField)) y‖ - (M.φ σ).φ c y / 2 = -((M.φ σ).φ i y) / 2 := by
  have hy := mem_ptsIn_inf.2 ⟨hc, hi⟩
  rw [hρ c i (gen_mem (mem_ptsIn.1 hy)), mul_div_cancel_right₀ _ (ρ i).ne_zero, ratVal_fnOf hy,
    (M.φ σ).trans c i y hc hi, Real.log_pow]
  simp only [GlobalTheory.CxPts.gv]
  push_cast
  ring

end Pair

/- English proof (translation)
Use `⟨⟨P.r, P.hr, fun x c i j hc hi _ => ?_, fun σ y c i j hc hi _ => ?_⟩, ⟨P.r', P.hr', fun x c i j hc _ hj => ?_, fun σ y c i j hc _ hj => ?_⟩, ⟨fun _ => 1, presents_zero.isRatSec, fun x c i j _ _ _ => ?_, fun σ y c i j _ _ _ => ?_⟩⟩` and prove the remaining obligations. Establish `e : P.loc 1 0 1 i j = P.r i` using `by simp [Pair.loc]`. Rewrite using `[e]`. Conclude with `Pair.unitAt_div_of_isRatSec P.L P.hr hc hi`. Establish `e : P.loc 1 0 1 i j = P.r i` using `by simp [Pair.loc]`.

Rewrite using `[e, Pair.log_norm_div_of_isRatSec P.L P.hr σ hc hi]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `e : P.loc 0 1 1 i j = P.r' j` using `by simp [Pair.loc]`. Rewrite using `[e]`.

Conclude with `Pair.unitAt_div_of_isRatSec P.A P.hr' hc hj`. Establish `e : P.loc 0 1 1 i j = P.r' j` using `by simp [Pair.loc]`. Rewrite using `[e, Pair.log_norm_div_of_isRatSec P.A P.hr' σ hc hj]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `e : P.loc 0 0 1 i j = 1` using `by simp [Pair.loc]`. Rewrite using `[e, Units.val_one, div_one]`. Conclude with `unitAt_one x`. Establish `e : P.loc 0 0 1 i j = 1` using `by simp [Pair.loc]`. Establish `hv` using `ratVal_fnOf (y := y) mem_ptsIn_top trivial (1 : Γ(X, ⊤))`.

Rewrite `hv` using `[map_one, ev_one mem_ptsIn_top]`. Rewrite using `[e, Units.val_one, div_one, hv]`. Simplify using `[HermLB.triv, Weight.ofFun]`.
-/
theorem Pair.rep_base (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k)
    (P : Pair p) : P.Rep 1 0 P.L ∧ P.Rep 0 1 P.A ∧ P.Rep 0 0 (HermLB.triv p) := by
  refine ⟨⟨P.r, P.hr, fun x c i j hc hi _ => ?_, fun σ y c i j hc hi _ => ?_⟩,
    ⟨P.r', P.hr', fun x c i j hc _ hj => ?_, fun σ y c i j hc _ hj => ?_⟩,
    ⟨fun _ => 1, presents_zero.isRatSec, fun x c i j _ _ _ => ?_, fun σ y c i j _ _ _ => ?_⟩⟩
  · have e : P.loc 1 0 1 i j = P.r i := by simp [Pair.loc]
    rw [e]
    exact Pair.unitAt_div_of_isRatSec P.L P.hr hc hi
  · have e : P.loc 1 0 1 i j = P.r i := by simp [Pair.loc]
    rw [e, Pair.log_norm_div_of_isRatSec P.L P.hr σ hc hi]
    push_cast
    ring
  · have e : P.loc 0 1 1 i j = P.r' j := by simp [Pair.loc]
    rw [e]
    exact Pair.unitAt_div_of_isRatSec P.A P.hr' hc hj
  · have e : P.loc 0 1 1 i j = P.r' j := by simp [Pair.loc]
    rw [e, Pair.log_norm_div_of_isRatSec P.A P.hr' σ hc hj]
    push_cast
    ring
  · have e : P.loc 0 0 1 i j = 1 := by simp [Pair.loc]
    rw [e, Units.val_one, div_one]
    exact unitAt_one x
  · have e : P.loc 0 0 1 i j = 1 := by simp [Pair.loc]
    have hv := ratVal_fnOf (y := y) mem_ptsIn_top trivial (1 : Γ(X, ⊤))
    rw [map_one, ev_one mem_ptsIn_top] at hv
    rw [e, Units.val_one, div_one, hv]
    simp [HermLB.triv, Weight.ofFun]

end GlobalTheory.VolBr
