import Development.WeilBound.CoreStatements.SesquilinearFractions.DTrans

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

noncomputable section

namespace PositivityTheory.Xgf.DPer

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
variable {Ix : Type} [Fintype Ix] (x : Ix → D.La) (hx : LinearIndependent (𝓞 E) x) (n : ℕ)
  (hn : ∀ y : D.La, n • y ∈ Submodule.span (𝓞 E) (Set.range x))

def toSpan : D.La →ₗ[𝓞 E] Submodule.span (𝓞 E) (Set.range x) where
  toFun y := ⟨n • y, hn y⟩
  map_add' y y' := Subtype.ext (smul_add _ _ _)
  map_smul' c y := Subtype.ext (smul_comm n c y)

def coef : D.La →ₗ[𝓞 E] (Ix →₀ 𝓞 E) := hx.repr ∘ₗ toSpan D x n hn

/- English proof (translation)
Establish `h` using `hx.linearCombination_repr (toSpan D x n hn y)`. Rewrite `h` using `[Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)]`. Conclude with `h`.
-/
theorem coef_sum (y : D.La) : ∑ m, coef D x hx n hn y m • x m = n • y := by
  have h := hx.linearCombination_repr (toSpan D x n hn y)
  rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)] at h
  exact h

/- English proof (translation)
Establish `e : toSpan D x n hn (x m) = (n : 𝓞 E) • (⟨x m, Submodule.subset_span ⟨m, rfl⟩⟩ : Submodule.span (𝓞 E) (Set.range x))`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[toSpan, Nat.cast_smul_eq_nsmul]`. Use `show hx.repr (toSpan D x n hn (x m)) = _`. Rewrite using `[e, map_smul, LinearIndependent.repr_eq_single hx m _ rfl, Finsupp.smul_single_one]`.
-/
theorem planeCoef_mulVec_smul_x_eq_zero_of_ne (m : Ix) : coef D x hx n hn (x m) = Finsupp.single m (n : 𝓞 E) := by
  have e : toSpan D x n hn (x m) = (n : 𝓞 E) • (⟨x m, Submodule.subset_span ⟨m, rfl⟩⟩ : Submodule.span (𝓞 E) (Set.range x)) := by
    apply Subtype.ext
    simp [toSpan, Nat.cast_smul_eq_nsmul]
  show hx.repr (toSpan D x n hn (x m)) = _
  rw [e, map_smul, LinearIndependent.repr_eq_single hx m _ rfl, Finsupp.smul_single_one]

/- English proof (translation)
Establish `h0 : n • y = 0`. Rewrite using `[← coef_sum D x hx n hn y, h]`. Simplify using the standard rewrite rules. Establish `h1 : (n : 𝓞 E) • y = 0`. Rewrite using `[Nat.cast_smul_eq_nsmul]`.

Conclude with `h0`. Establish `hn' : (n : 𝓞 E) ≠ 0` using `by exact_mod_cast hn0.ne'`. Take `⟨s, hs⟩` from `D.proj.out`. Establish `h2 : s y = 0`. Establish `h3` using `congrArg s h1`.

Rewrite `h3` using `[map_smul, map_zero]`. Conclude with `(smul_eq_zero.mp h3).resolve_left hn'`. Rewrite using `[← hs y, h2, map_zero]`.
-/
theorem eq_zero_of_coef (hn0 : 0 < n) (y : D.La) (h : coef D x hx n hn y = 0) : y = 0 := by
  have h0 : n • y = 0 := by
    rw [← coef_sum D x hx n hn y, h]
    simp
  have h1 : (n : 𝓞 E) • y = 0 := by
    rw [Nat.cast_smul_eq_nsmul]
    exact h0
  have hn' : (n : 𝓞 E) ≠ 0 := by exact_mod_cast hn0.ne'
  obtain ⟨s, hs⟩ := D.proj.out
  have h2 : s y = 0 := by
    have h3 := congrArg s h1
    rw [map_smul, map_zero] at h3
    exact (smul_eq_zero.mp h3).resolve_left hn'
  rw [← hs y, h2, map_zero]

end PositivityTheory.Xgf.DPer

end
