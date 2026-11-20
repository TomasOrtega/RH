import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFormsFiniteDimensionalOf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GGConn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SiegelSpaceAlgebraHolds

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.CompRat

namespace GlobalTheory.CompRat

/- English proof (translation)
Break down `s.eq_empty_or_nonempty with rfl | ⟨x0, hx0⟩` into its components or cases. Conclude with `⟨0, fun _ h => h.elim⟩`. Use `⟨g x0, fun x hx => ?_⟩` and prove the remaining obligations. Establish `hfin : (g '' s).Finite`. Use `(Set.toFinite ({0, 1} : Set ℂ)).subset ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨y, hy, rfl⟩`. Establish `h` using `hi y hy`. Establish `: g y * (g y - 1) = 0` using `by linear_combination h`. Break down `mul_eq_zero.1 this with h | h` into its components or cases. Conclude with `Or.inl h`.

Conclude with `Or.inr (sub_eq_zero.1 h)`. Conclude with `hs.constant_of_mapsTo hfin.isDiscrete hg (Set.mapsTo_image g s) hx hx0`.
-/
theorem const_of_idem_on {Y : Type} [TopologicalSpace Y] {s : Set Y} (hs : IsPreconnected s) {g : Y → ℂ}
    (hg : ContinuousOn g s) (hi : ∀ x ∈ s, g x * g x = g x) : ∃ w : ℂ, ∀ x ∈ s, g x = w := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨x0, hx0⟩
  · exact ⟨0, fun _ h => h.elim⟩
  refine ⟨g x0, fun x hx => ?_⟩
  have hfin : (g '' s).Finite := by
    refine (Set.toFinite ({0, 1} : Set ℂ)).subset ?_
    rintro _ ⟨y, hy, rfl⟩
    have h := hi y hy
    have : g y * (g y - 1) = 0 := by linear_combination h
    rcases mul_eq_zero.1 this with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.1 h)
  exact hs.constant_of_mapsTo hfin.isDiscrete hg (Set.mapsTo_image g s) hx hx0

/- English proof (translation)
Distinguish the cases in `h : x ∈ (U.X k).dom`. Establish `e1 : ∀ g : Rul Xo c, rdU U g k x = toC (evR Xo c g (U.un k ⟨x, h⟩))` using `fun g => dif_pos h`. Rewrite using `[e1, e1, e1]`. Conclude with `evalAt_mul (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f f' (U.un k ⟨x, h⟩)`. Rewrite using `[rdU_mem_offZero U _ k x h, rdU_mem_offZero U f k x h, zero_mul]`.
-/
theorem rdU_mul_apply' {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} (U : Unf Xo c σ r)
    (f f' : Rul Xo c) (k : U.Comp) (x : Frame (U.X k).Ψ r) :
    rdU U (f * f') k x = rdU U f k x * rdU U f' k x := by
  by_cases h : x ∈ (U.X k).dom
  · have e1 : ∀ g : Rul Xo c, rdU U g k x = toC (evR Xo c g (U.un k ⟨x, h⟩)) := fun g => dif_pos h
    rw [e1, e1, e1]
    exact evalAt_mul (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f f' (U.un k ⟨x, h⟩)
  · rw [rdU_mem_offZero U _ k x h, rdU_mem_offZero U f k x h, zero_mul]

end GlobalTheory.CompRat
