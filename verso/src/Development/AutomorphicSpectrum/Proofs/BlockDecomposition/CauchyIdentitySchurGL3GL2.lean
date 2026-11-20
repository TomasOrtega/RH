import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.CauchyIdentity.CauchyVariationInequality
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open scoped NumberField.AdeleRing ValuativeRel

namespace GlobalTheory.CompanionTheory.CauchyUnit

def antitonePairEquiv : ℕ × ℕ ≃ {l : Fin 2 → ℕ // Antitone l} where
  toFun p := ⟨![p.1 + p.2, p.2], by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all⟩
  invFun l := (l.1 0 - l.1 1, l.1 1)
  left_inv p := by simp
  right_inv l := by
    apply Subtype.ext
    have h : l.1 1 ≤ l.1 0 := l.2 (by simp)
    funext i
    fin_cases i
    · simp; omega
    · simp

/- English proof (translation)
Use function extensionality and compare the values at `i`. Apply the tactic sequence `fin_cases i <;> simp [PositivityTheory.RgJS.padN]`.
-/
theorem padN_pair (m n : ℕ) :
    (fun i : Fin 3 => ((PositivityTheory.RgJS.padN 3 (![m + n, n] : Fin 2 → ℕ) i : ℕ) : ℤ)) =
      ![((m + n : ℕ) : ℤ), (n : ℤ), 0] := by
  funext i
  fin_cases i <;> simp [PositivityTheory.RgJS.padN]

/- English proof (translation)
Use function extensionality and compare the values at `j`. Apply the tactic sequence `fin_cases j <;> simp`.
-/
theorem pair_cast (m n : ℕ) :
    (fun j : Fin 2 => (((![m + n, n] : Fin 2 → ℕ) j : ℕ) : ℤ)) = ![((m + n : ℕ) : ℤ), (n : ℤ)] := by
  funext j
  fin_cases j <;> simp

/- English proof (translation)
Simplify using `[Fin.sum_univ_two]`. Use linear arithmetic over natural numbers and integers.
-/
theorem pair_sum (m n : ℕ) : ∑ j, (![m + n, n] : Fin 2 → ℕ) j = m + 2 * n := by
  simp [Fin.sum_univ_two]; omega

/- English proof (translation)
Introduce `x y X hx hy hX`. Establish `h` using `(PositivityTheory.RgJS.cauchy_variation_inequality 3 2 (by norm_num) x y X 1 1 (fun i => (hx i).le) (fun j => (hy j).le) (by simpa using hX)).2`. Establish `h2` using `(Equiv.hasSum_iff antitonePairEquiv).2 h`. Use `h2 using 2 with p` and compare the differences between its conclusion and the goal. Take `⟨m, n⟩` from `p`.

Simplify using `only [Function.comp_apply, antitonePairEquiv, Equiv.coe_fn_mk]`. Rewrite using `[padN_pair, pair_cast, pair_sum]`.
-/
theorem cauchy_unit : ∀ (x : Fin 3 → ℂˣ) (y : Fin 2 → ℂˣ) (X : ℂ), (∀ i, ‖(x i : ℂ)‖ = 1) → (∀ j, ‖(y j : ℂ)‖ = 1) → ‖X‖ < 1 → HasSum (fun p : ℕ × ℕ => Spherical.evalAt x (Spherical.schur ![((p.1 + p.2 : ℕ) : ℤ), (p.2 : ℤ), 0]) * Spherical.evalAt y (Spherical.schur ![((p.1 + p.2 : ℕ) : ℤ), (p.2 : ℤ)]) * X ^ (p.1 + 2 * p.2)) (∏ i, ∏ j, (1 - (x i : ℂ) * (y j : ℂ) * X)⁻¹) := by
  intro x y X hx hy hX
  have h := (PositivityTheory.RgJS.cauchy_variation_inequality 3 2 (by norm_num) x y X 1 1
    (fun i => (hx i).le) (fun j => (hy j).le) (by simpa using hX)).2
  have h2 := (Equiv.hasSum_iff antitonePairEquiv).2 h
  convert h2 using 2 with p
  obtain ⟨m, n⟩ := p
  simp only [Function.comp_apply, antitonePairEquiv, Equiv.coe_fn_mk]
  rw [padN_pair, pair_cast, pair_sum]

end GlobalTheory.CompanionTheory.CauchyUnit
