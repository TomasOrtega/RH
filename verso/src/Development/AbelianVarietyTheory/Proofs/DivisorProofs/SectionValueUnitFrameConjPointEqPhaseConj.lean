import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValueUnitFrameEqLocalFunctionUnitScalarStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryOfFrameNormConj
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSAmp

def conjPt {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} (y : CxPts p σ) :
    CxPts p ((starRingEnd ℂ).comp σ) :=
  ⟨spMap (starRingEnd ℂ) ≫ y.1, by
    have e : spMap ((starRingEnd ℂ).comp σ) = spMap (starRingEnd ℂ) ≫ spMap σ := by
      rw [spMap, spMap, spMap, ← Spec.map_comp]
      rfl
    rw [Category.assoc, y.2, e]⟩

/- English proof (translation)
Take `⟨U, hU, a, rfl⟩` from `hf.exists_fnOf`. Establish `hy : y ∈ ptsIn q σ U` using `mem_ptsIn.2 hU`. Rewrite using `[ratVal_fnOf hy, ratVal_fnOf (CxPts.mem_ptsIn_conj h hy), CxPts.ev_conj h hy]`.
-/
theorem ratVal_conj {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {q : X ⟶ Sp k} {σ σ' : k →+* ℂ}
    {f : X.functionField} {y : CxPts q σ} {y' : CxPts q σ'}
    (h : y'.1 = spMap (starRingEnd ℂ) ≫ y.1) (hf : RegAt (under y) f) :
    ratVal f y' = starRingEnd ℂ (ratVal f y) := by
  obtain ⟨U, hU, a, rfl⟩ := hf.exists_fnOf
  have hy : y ∈ ptsIn q σ U := mem_ptsIn.2 hU
  rw [ratVal_fnOf hy, ratVal_fnOf (CxPts.mem_ptsIn_conj h hy), CxPts.ev_conj h hy]

/- English proof (translation)
Introduce `k _ X _ p P a b σ y`. Establish `h : (conjPt y).1 = spMap (starRingEnd ℂ) ≫ y.1` using `rfl`. Establish `hi` using `mem_pick (P.L.φ σ).isLB y`. Establish `hj` using `mem_pick (P.A.φ σ).isLB y`. Take `⟨θ₁, h₁, e₁⟩` from `GlobalTheory.T.sectionValueUnitFrame_eq_localFunction_unitScalar k X p P a b σ y _ _ hi hj`.

Take `⟨θ₂, h₂, e₂⟩` from `GlobalTheory.T.sectionValueUnitFrame_eq_localFunction_unitScalar k X p P a b _ (conjPt y) _ _ (CxPts.mem_ptsIn_conj h hi) (CxPts.mem_ptsIn_conj h hj)`. Use `⟨_, conjPt y, θ₂ * θ₁, by rw [norm_mul, h₁, h₂, one_mul], fun f hf => ?_⟩` and prove the remaining obligations. Establish `hreg` using `hf _ _ _ (mem_ptsIn.1 hi) (mem_ptsIn.1 hj)`. Rewrite using `[e₁ f hf, e₂ f hf, ratVal_conj h hreg, P.L.conj σ _ _ y _ h hi, P.A.conj σ _ _ y _ h hj]`. Establish `hθ : θ₁ * starRingEnd ℂ θ₁ = 1`.

Rewrite using `[Complex.mul_conj', h₁]`. Simplify using the standard rewrite rules. Simplify using `only [map_mul, Complex.conj_ofReal]`. Take the linear combination `(-(θ₂ * starRingEnd ℂ (ratVal (P.loc a b f (pick (P.L.φ σ).isLB y) (pick (P.A.φ σ).isLB y)) y) * ((Real.exp (-(a * (P.L.φ σ).φ (pick (P.L.φ σ).isLB y) y + b * (P.A.φ σ).φ (pick (P.A.φ σ).isLB y) y) / 2) : ℝ) : ℂ))) * hθ`.
-/
theorem val_conj : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p), ∀ (a b : ℤ) (σ : k →+* ℂ) (y : CxPts p σ), ∃ (σ' : k →+* ℂ) (y' : CxPts p σ') (θ : ℂ), ‖θ‖ = 1 ∧ ∀ f ∈ P.H a b, val P a b σ' y' f = θ * (starRingEnd ℂ) (val P a b σ y f) := by
  intro k _ X _ p P a b σ y
  have h : (conjPt y).1 = spMap (starRingEnd ℂ) ≫ y.1 := rfl
  have hi := mem_pick (P.L.φ σ).isLB y
  have hj := mem_pick (P.A.φ σ).isLB y
  obtain ⟨θ₁, h₁, e₁⟩ := GlobalTheory.T.sectionValueUnitFrame_eq_localFunction_unitScalar k X p P a b σ y _ _ hi hj
  obtain ⟨θ₂, h₂, e₂⟩ := GlobalTheory.T.sectionValueUnitFrame_eq_localFunction_unitScalar k X p P a b _ (conjPt y) _ _
    (CxPts.mem_ptsIn_conj h hi) (CxPts.mem_ptsIn_conj h hj)
  refine ⟨_, conjPt y, θ₂ * θ₁, by rw [norm_mul, h₁, h₂, one_mul], fun f hf => ?_⟩
  have hreg := hf _ _ _ (mem_ptsIn.1 hi) (mem_ptsIn.1 hj)
  rw [e₁ f hf, e₂ f hf, ratVal_conj h hreg, P.L.conj σ _ _ y _ h hi, P.A.conj σ _ _ y _ h hj]
  have hθ : θ₁ * starRingEnd ℂ θ₁ = 1 := by
    rw [Complex.mul_conj', h₁]
    simp
  simp only [map_mul, Complex.conj_ofReal]
  linear_combination (-(θ₂ * starRingEnd ℂ (ratVal (P.loc a b f (pick (P.L.φ σ).isLB y) (pick (P.A.φ σ).isLB y)) y) *
    ((Real.exp (-(a * (P.L.φ σ).φ (pick (P.L.φ σ).isLB y) y + b * (P.A.φ σ).φ (pick (P.A.φ σ).isLB y) y) / 2) : ℝ) : ℂ))) * hθ

end GlobalTheory.HSAmp
