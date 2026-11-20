import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPullHermPullLine
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedA
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.IsSmoothHermConstLine

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MPDict

/- English proof (translation)
Establish `hc : ∀ k, ∃ i, y ∈ ptsIn (mpStr ℤ m n) σ₀ (blockChart n k i)` using `fun k => ⟨ptChart _ k, CxPts.mem_ptsIn.2 (mem_ptChart _ k)⟩`. Use `choose c hc using hc`. Set `z : (Σ k, Bk n k) → ℂ` to `fun p => CxPts.ev (mpStr ℤ m n) σ₀ (blockChart n p.1 (c p.1)) (pullRatio (prB n p.1) _ (c p.1) le_rfl p.2) y`. Establish `hz1 : ∀ k, z ⟨k, c k⟩ = 1` using `fun k => by`. Express the relevant statement in the definitionally equal form `CxPts.ev (mpStr ℤ m n) σ₀ (blockChart n k (c k)) (pullRatio (prB n k) _ (c k) le_rfl (c k)) y = 1`.

Rewrite using `[pullRatio_self, CxPts.ev_eq (hc k), map_one]`. Use `⟨z, fun k => ⟨c k, by rw [hz1]; exact one_ne_zero⟩, fun k i => ?_⟩` and prove the remaining obligations. Establish `hmem : y ∈ ptsIn (mpStr ℤ m n) σ₀ (blockChart n k i) ↔ z ⟨k, i⟩ ≠ 0`. Establish `e` using `CxPts.mem_ptsIn_basicOpen (hc k) (pullRatio (prB n k) _ (c k) le_rfl i)`. Rewrite `e` using `[basicOpen_pullRatio, CxPts.mem_ptsIn_inf]`.

Conclude with `⟨fun h => e.1 ⟨hc k, h⟩, fun h => (e.2 h).2⟩`. Use `⟨hmem, fun j hi => ?_⟩` and prove the remaining obligations. Establish `hW : y ∈ ptsIn (mpStr ℤ m n) σ₀ (blockChart n k (c k) ⊓ blockChart n k i)` using `CxPts.mem_ptsIn_inf.2 ⟨hc k, hi⟩`. Establish `r1 : ∀ l, CxPts.ev (mpStr ℤ m n) σ₀ (blockChart n k (c k) ⊓ blockChart n k i) (pullRatio (prB n k) _ (c k) inf_le_left l) y = z ⟨k, l⟩` using `fun l => by`. Rewrite using `[← resG_pullRatio (φ := prB n k) (W := blockChart n k (c k)) (i := c k) (hi := le_rfl) inf_le_left]`.

Conclude with `CxPts.ev_res inf_le_left hW _`. Establish `r2 : CxPts.ev (mpStr ℤ m n) σ₀ (blockChart n k (c k) ⊓ blockChart n k i) (pullRatio (prB n k) _ i inf_le_right j) y = CxPts.ev (mpStr ℤ m n) σ₀ (blockChart n k i) (pullRatio (prB n k) _ i le_rfl j) y`. Rewrite using `[← resG_pullRatio (φ := prB n k) (W := blockChart n k i) (i := i) (hi := le_rfl) inf_le_right]`. Conclude with `CxPts.ev_res inf_le_right hW _`. Establish `e` using `congrArg (fun f => CxPts.ev (mpStr ℤ m n) σ₀ (blockChart n k (c k) ⊓ blockChart n k i) f y) (pullRatio_mul_pullRatio (φ := prB n k) (W := blockChart n k (c k) ⊓ blockChart n k i) (i := c k) (j := i) (k := j) (hi := inf_le_left) (hj := inf_le_right))`.

Simplify using `only [CxPts.ev_mul, r1, r2] at e`. Rewrite using `[eq_div_iff (hmem.1 hi), mul_comm]`. Conclude with `e`.
-/
theorem exists_isUnder_of_cxPt (m : ℕ) (n : Fin (m + 1) → ℕ) (y : CxPts (mpStr ℤ m n) σ₀) :
    ∃ z : (Σ k, Bk n k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) ∧ IsUnder y z := by
  have hc : ∀ k, ∃ i, y ∈ ptsIn (mpStr ℤ m n) σ₀ (blockChart n k i) := fun k =>
    ⟨ptChart _ k, CxPts.mem_ptsIn.2 (mem_ptChart _ k)⟩
  choose c hc using hc
  let z : (Σ k, Bk n k) → ℂ := fun p =>
    CxPts.ev (mpStr ℤ m n) σ₀ (blockChart n p.1 (c p.1)) (pullRatio (prB n p.1) _ (c p.1) le_rfl p.2) y
  have hz1 : ∀ k, z ⟨k, c k⟩ = 1 := fun k => by
    change CxPts.ev (mpStr ℤ m n) σ₀ (blockChart n k (c k)) (pullRatio (prB n k) _ (c k) le_rfl (c k)) y = 1
    rw [pullRatio_self, CxPts.ev_eq (hc k), map_one]
  refine ⟨z, fun k => ⟨c k, by rw [hz1]; exact one_ne_zero⟩, fun k i => ?_⟩
  have hmem : y ∈ ptsIn (mpStr ℤ m n) σ₀ (blockChart n k i) ↔ z ⟨k, i⟩ ≠ 0 := by
    have e := CxPts.mem_ptsIn_basicOpen (hc k) (pullRatio (prB n k) _ (c k) le_rfl i)
    rw [basicOpen_pullRatio, CxPts.mem_ptsIn_inf] at e
    exact ⟨fun h => e.1 ⟨hc k, h⟩, fun h => (e.2 h).2⟩
  refine ⟨hmem, fun j hi => ?_⟩
  have hW : y ∈ ptsIn (mpStr ℤ m n) σ₀ (blockChart n k (c k) ⊓ blockChart n k i) :=
    CxPts.mem_ptsIn_inf.2 ⟨hc k, hi⟩
  have r1 : ∀ l, CxPts.ev (mpStr ℤ m n) σ₀ (blockChart n k (c k) ⊓ blockChart n k i)
      (pullRatio (prB n k) _ (c k) inf_le_left l) y = z ⟨k, l⟩ := fun l => by
    rw [← resG_pullRatio (φ := prB n k) (W := blockChart n k (c k)) (i := c k) (hi := le_rfl) inf_le_left]
    exact CxPts.ev_res inf_le_left hW _
  have r2 : CxPts.ev (mpStr ℤ m n) σ₀ (blockChart n k (c k) ⊓ blockChart n k i)
      (pullRatio (prB n k) _ i inf_le_right j) y =
      CxPts.ev (mpStr ℤ m n) σ₀ (blockChart n k i) (pullRatio (prB n k) _ i le_rfl j) y := by
    rw [← resG_pullRatio (φ := prB n k) (W := blockChart n k i) (i := i) (hi := le_rfl) inf_le_right]
    exact CxPts.ev_res inf_le_right hW _
  have e := congrArg (fun f => CxPts.ev (mpStr ℤ m n) σ₀ (blockChart n k (c k) ⊓ blockChart n k i) f y)
    (pullRatio_mul_pullRatio (φ := prB n k) (W := blockChart n k (c k) ⊓ blockChart n k i) (i := c k) (j := i)
      (k := j) (hi := inf_le_left) (hj := inf_le_right))
  simp only [CxPts.ev_mul, r1, r2] at e
  rw [eq_div_iff (hmem.1 hi), mul_comm]
  exact e

end GlobalTheory.CompanionTheory.MPDict
