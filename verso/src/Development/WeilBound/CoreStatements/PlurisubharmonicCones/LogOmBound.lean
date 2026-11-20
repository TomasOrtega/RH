import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.TowerOrigin
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsIsKroneckerCharOfDiscr

open NumberField GlobalTheory.CompanionTheory.Ar

namespace LevelTowerAlt

/- English proof (translation)
Establish `hγ : 0 < Real.eulerMascheroniConstant` using `lt_trans (by norm_num) Real.one_half_lt_eulerMascheroniConstant`. Use `⟨1 + Real.eulerMascheroniConstant + |Real.log (2 * Real.pi)|, by positivity, ?_⟩` and prove the remaining obligations. Introduce `E _ _ _ H`. Use `haveI : Fact (Nat.Prime H.d) := ⟨H.d_prime⟩`. Use `⟨⟨H.d_prime.ne_zero⟩, (quadraticChar (ZMod H.d)).ringHomComp (Int.castRingHom ℂ), GlobalTheory.isKroneckerChar_quadraticChar (by have := H.d_mod; omega), ?_⟩` and prove the remaining obligations.

Establish `hL : (GlobalTheory.CM.logOm E ((quadraticChar (ZMod H.d)).ringHomComp (Int.castRingHom ℂ))).re = Real.eulerMascheroniConstant + Real.log (2 * Real.pi / rootDiscr E) - hostLval H`. Simplify using `only [GlobalTheory.CM.logOm, Complex.sub_re, Complex.ofReal_re]`. Both sides reduce to the same expression. Establish `hrd : rootDiscr E = hostRd E`. Unfold `hostRd rootDiscr`.

Rewrite using `[Int.cast_abs, one_div]`. Establish `h1 : 1 ≤ hostRd E`. Unfold `hostRd`. Apply `Real.one_le_rpow` to reduce the goal to its premises. Use `Int.one_le_abs (NumberField.discr_ne_zero E)` as an intermediate fact.

Rewrite using `[← Int.cast_abs]`. Conclude with `this` after adjusting the coercions. Check the signs of the components of the expression. Establish `hb0 : 0 ≤ Real.log (hostRd E)` using `Real.log_nonneg h1`. Establish `hlogdiv : Real.log (2 * Real.pi / rootDiscr E) = Real.log (2 * Real.pi) - Real.log (hostRd E)`.

Rewrite using `[hrd, Real.log_div (by positivity) (by linarith)]`. Rewrite using `[hL, hlogdiv]`. Establish `ha1` using `le_abs_self (Real.log (2 * Real.pi))`. Establish `ha2` using `neg_abs_le (Real.log (2 * Real.pi))`. Establish `hl1` using `le_abs_self (hostLval H)`.

Establish `hl2` using `neg_abs_le (hostLval H)`. Establish `hb : |Real.eulerMascheroniConstant + (Real.log (2 * Real.pi) - Real.log (hostRd E)) - hostLval H| ≤ Real.eulerMascheroniConstant + |Real.log (2 * Real.pi)| + Real.log (hostRd E) + |hostLval H|` using `abs_le.2 ⟨by linarith, by linarith⟩`. Establish `hm : 0 ≤ (Real.eulerMascheroniConstant + |Real.log (2 * Real.pi)|) * (Real.log (hostRd E) + |hostLval H|)` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem logOm_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E), ∃ (_ : NeZero H.d) (χ : DirichletCharacter ℂ H.d),
      GlobalTheory.IsKroneckerChar χ ∧ |(GlobalTheory.CM.logOm E χ).re| ≤ C * (1 + Real.log (hostRd E) + |hostLval H|) := by
  have hγ : 0 < Real.eulerMascheroniConstant :=
    lt_trans (by norm_num) Real.one_half_lt_eulerMascheroniConstant
  refine ⟨1 + Real.eulerMascheroniConstant + |Real.log (2 * Real.pi)|, by positivity, ?_⟩
  intro E _ _ _ H
  haveI : Fact (Nat.Prime H.d) := ⟨H.d_prime⟩
  refine ⟨⟨H.d_prime.ne_zero⟩, (quadraticChar (ZMod H.d)).ringHomComp (Int.castRingHom ℂ),
    GlobalTheory.isKroneckerChar_quadraticChar (by have := H.d_mod; omega), ?_⟩
  have hL : (GlobalTheory.CM.logOm E ((quadraticChar (ZMod H.d)).ringHomComp (Int.castRingHom ℂ))).re =
      Real.eulerMascheroniConstant + Real.log (2 * Real.pi / rootDiscr E) - hostLval H := by
    simp only [GlobalTheory.CM.logOm, Complex.sub_re, Complex.ofReal_re]
    rfl
  have hrd : rootDiscr E = hostRd E := by
    unfold hostRd rootDiscr
    rw [Int.cast_abs, one_div]
  have h1 : 1 ≤ hostRd E := by
    unfold hostRd
    apply Real.one_le_rpow
    · have := Int.one_le_abs (NumberField.discr_ne_zero E)
      rw [← Int.cast_abs]
      exact_mod_cast this
    · positivity
  have hb0 : 0 ≤ Real.log (hostRd E) := Real.log_nonneg h1
  have hlogdiv : Real.log (2 * Real.pi / rootDiscr E) = Real.log (2 * Real.pi) - Real.log (hostRd E) := by
    rw [hrd, Real.log_div (by positivity) (by linarith)]
  rw [hL, hlogdiv]
  have ha1 := le_abs_self (Real.log (2 * Real.pi))
  have ha2 := neg_abs_le (Real.log (2 * Real.pi))
  have hl1 := le_abs_self (hostLval H)
  have hl2 := neg_abs_le (hostLval H)
  have hb : |Real.eulerMascheroniConstant + (Real.log (2 * Real.pi) - Real.log (hostRd E)) - hostLval H| ≤
      Real.eulerMascheroniConstant + |Real.log (2 * Real.pi)| + Real.log (hostRd E) + |hostLval H| :=
    abs_le.2 ⟨by linarith, by linarith⟩
  have hm : 0 ≤ (Real.eulerMascheroniConstant + |Real.log (2 * Real.pi)|) *
      (Real.log (hostRd E) + |hostLval H|) := by positivity
  nlinarith

end LevelTowerAlt
