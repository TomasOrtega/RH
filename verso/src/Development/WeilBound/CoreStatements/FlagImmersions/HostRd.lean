import Development.WeilBound.CoreStatements.FlagImmersions.FibSandwich

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl

namespace RootFieldNumerics.RF

/- English proof (translation)
Introduce `E _ _ _ H _`. Use `haveI : Fact (Nat.Prime H.d) := ⟨H.d_prime⟩`. Establish `h4 : H.d % 4 = 3`. Use `H.d_mod` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Use `⟨(quadraticChar (ZMod H.d)).ringHomComp (Int.castRingHom ℂ), GlobalTheory.isKroneckerChar_quadraticChar h4, ?_⟩` and prove the remaining obligations. Establish `hr : rootDiscr E = hostRd E`. Simplify using `[rootDiscr, hostRd, Int.cast_abs, one_div]`. Establish `hpos : 0 < hostRd E`. Unfold `hostRd`.

Apply `Real.rpow_pos_of_pos` to reduce the goal to its premises. Conclude with `abs_pos.2 (Int.cast_ne_zero.2 (NumberField.discr_ne_zero E))`. Simplify using `only [GlobalTheory.CM.logOm, hostLval]`. Rewrite using `[Complex.sub_re, Complex.ofReal_re, hr, Real.log_div (by positivity) hpos.ne']`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem chiEx : ChiEx := by
  intro E _ _ _ H _
  haveI : Fact (Nat.Prime H.d) := ⟨H.d_prime⟩
  have h4 : H.d % 4 = 3 := by
    have := H.d_mod
    omega
  refine ⟨(quadraticChar (ZMod H.d)).ringHomComp (Int.castRingHom ℂ), GlobalTheory.isKroneckerChar_quadraticChar h4, ?_⟩
  have hr : rootDiscr E = hostRd E := by
    simp [rootDiscr, hostRd, Int.cast_abs, one_div]
  have hpos : 0 < hostRd E := by
    unfold hostRd
    apply Real.rpow_pos_of_pos
    exact abs_pos.2 (Int.cast_ne_zero.2 (NumberField.discr_ne_zero E))
  simp only [GlobalTheory.CM.logOm, hostLval]
  rw [Complex.sub_re, Complex.ofReal_re, hr, Real.log_div (by positivity) hpos.ne']
  ring

end RootFieldNumerics.RF
