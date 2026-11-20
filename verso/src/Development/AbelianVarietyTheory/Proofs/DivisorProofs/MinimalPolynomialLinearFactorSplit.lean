import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EigProj

open Polynomial

/- English proof (translation)
Introduce `E _ _ b σ`. Establish `hint : IsIntegral ℚ b` using `Algebra.IsIntegral.isIntegral b`. Establish `hcomp : σ.comp (algebraMap ℚ E) = algebraMap ℚ ℂ` using `Subsingleton.elim _ _`. Establish `hroot : (minpoly ℚ b).eval₂ (algebraMap ℚ ℂ) (σ b) = 0`. Rewrite using `[← hcomp, ← Polynomial.hom_eval₂, ← Polynomial.aeval_def, minpoly.aeval, map_zero]`.

Establish `hmem : σ b ∈ algebraicClosure ℚ ℂ`. Conclude with `mem_algebraicClosure_iff.2 (hint.map (σ.toRatAlgHom)).isAlgebraic`. Use `set β : Qb := ⟨σ b, hmem⟩ with hβ`. Establish `hι : algebraMap Qb ℂ β = σ b` using `rfl`. Establish `hcompQ : (algebraMap Qb ℂ).comp (algebraMap ℚ Qb) = algebraMap ℚ ℂ` using `Subsingleton.elim _ _`.

Establish `hrootQ : (minpoly ℚ b).eval₂ (algebraMap ℚ Qb) β = 0`. Apply `(algebraMap Qb ℂ).injective` to reduce the goal to its premises. Rewrite using `[Polynomial.hom_eval₂, hcompQ, hι, hroot, map_zero]`. Use `set fQ := (minpoly ℚ b).map (algebraMap ℚ Qb) with hfQ`. Establish `hfQroot : fQ.IsRoot β`.

Rewrite using `[Polynomial.IsRoot, hfQ, Polynomial.eval_map]`. Conclude with `hrootQ`. Use `set g := fQ /ₘ (X - C β) with hg`. Establish `hfac : (X - C β) * g = fQ` using `(Polynomial.mul_divByMonic_eq_iff_isRoot).2 hfQroot`. Establish `hsep : (minpoly ℚ b).Separable` using `Algebra.IsSeparable.isSeparable ℚ b`.

Establish `hder` using `hsep.eval₂_derivative_ne_zero (algebraMap ℚ Qb) hrootQ`. Establish `hgβ : g.eval β ≠ 0`. Introduce `h0`. Apply `hder` to reduce the goal to its premises. Establish `: (derivative (minpoly ℚ b)).eval₂ (algebraMap ℚ Qb) β = (derivative fQ).eval β`.

Rewrite using `[hfQ, Polynomial.derivative_map, Polynomial.eval_map]`. Rewrite using `[this, ← hfac, derivative_mul]`. Simplify using `[h0]`. Use `⟨C (g.eval β)⁻¹ * g, (algebraMap Qb ℂ (g.eval β))⁻¹, ?_, ?_⟩` and prove the remaining obligations. Establish `key : (X - C β) * (C (g.eval β)⁻¹ * g) = C (g.eval β)⁻¹ * fQ` using `by rw [← hfac]; ring`.

Use `congrArg (Polynomial.map (algebraMap Qb ℂ)) key` as an intermediate fact. Simplify using `only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, hι, map_inv₀] at this`. Simplify using `only [Polynomial.map_mul, Polynomial.map_C, map_inv₀]`. Rewrite using `[this, hfQ, Polynomial.map_map, hcompQ]`. Rewrite using `[Polynomial.eval_map, ← hι, Polynomial.eval₂_at_apply, Polynomial.eval_mul, Polynomial.eval_C, inv_mul_cancel₀ hgβ, map_one]`.
-/
theorem eigProj_poly : ∀ (E : Type) [Field E] [NumberField E] (b : E) (σ : E →+* ℂ), ∃ (Q : Polynomial Qb) (c : ℂ),
    (Polynomial.X - Polynomial.C (σ b)) * Q.map (algebraMap Qb ℂ) = Polynomial.C c * (minpoly ℚ b).map (algebraMap ℚ ℂ) ∧
    (Q.map (algebraMap Qb ℂ)).eval (σ b) = 1 := by
  intro E _ _ b σ
  have hint : IsIntegral ℚ b := Algebra.IsIntegral.isIntegral b
  have hcomp : σ.comp (algebraMap ℚ E) = algebraMap ℚ ℂ := Subsingleton.elim _ _
  have hroot : (minpoly ℚ b).eval₂ (algebraMap ℚ ℂ) (σ b) = 0 := by
    rw [← hcomp, ← Polynomial.hom_eval₂, ← Polynomial.aeval_def, minpoly.aeval, map_zero]
  have hmem : σ b ∈ algebraicClosure ℚ ℂ := by
    exact mem_algebraicClosure_iff.2 (hint.map (σ.toRatAlgHom)).isAlgebraic
  set β : Qb := ⟨σ b, hmem⟩ with hβ
  have hι : algebraMap Qb ℂ β = σ b := rfl
  have hcompQ : (algebraMap Qb ℂ).comp (algebraMap ℚ Qb) = algebraMap ℚ ℂ := Subsingleton.elim _ _
  have hrootQ : (minpoly ℚ b).eval₂ (algebraMap ℚ Qb) β = 0 := by
    apply (algebraMap Qb ℂ).injective
    rw [Polynomial.hom_eval₂, hcompQ, hι, hroot, map_zero]
  set fQ := (minpoly ℚ b).map (algebraMap ℚ Qb) with hfQ
  have hfQroot : fQ.IsRoot β := by
    rw [Polynomial.IsRoot, hfQ, Polynomial.eval_map]; exact hrootQ
  set g := fQ /ₘ (X - C β) with hg
  have hfac : (X - C β) * g = fQ := (Polynomial.mul_divByMonic_eq_iff_isRoot).2 hfQroot
  have hsep : (minpoly ℚ b).Separable := Algebra.IsSeparable.isSeparable ℚ b
  have hder := hsep.eval₂_derivative_ne_zero (algebraMap ℚ Qb) hrootQ
  have hgβ : g.eval β ≠ 0 := by
    intro h0
    apply hder
    have : (derivative (minpoly ℚ b)).eval₂ (algebraMap ℚ Qb) β = (derivative fQ).eval β := by
      rw [hfQ, Polynomial.derivative_map, Polynomial.eval_map]
    rw [this, ← hfac, derivative_mul]
    simp [h0]
  refine ⟨C (g.eval β)⁻¹ * g, (algebraMap Qb ℂ (g.eval β))⁻¹, ?_, ?_⟩
  · have key : (X - C β) * (C (g.eval β)⁻¹ * g) = C (g.eval β)⁻¹ * fQ := by rw [← hfac]; ring
    have := congrArg (Polynomial.map (algebraMap Qb ℂ)) key
    simp only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, hι, map_inv₀] at this
    simp only [Polynomial.map_mul, Polynomial.map_C, map_inv₀]
    rw [this, hfQ, Polynomial.map_map, hcompQ]
  · rw [Polynomial.eval_map, ← hι, Polynomial.eval₂_at_apply, Polynomial.eval_mul, Polynomial.eval_C,
      inv_mul_cancel₀ hgβ, map_one]

end GlobalTheory.EigProj
