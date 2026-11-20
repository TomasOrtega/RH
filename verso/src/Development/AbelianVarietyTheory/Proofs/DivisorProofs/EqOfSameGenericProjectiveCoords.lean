import Development.AbelianVarietyTheory.Definitions.Divisors.NotSymEOfNe
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveHomogeneousCoordsFieldDetermineDescend
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SiegCrd

/- English proof (translation)
Introduce `o _ n X _ _ s h h' K _ x c hs hs' hx hc hc'`. Establish `: IsSeparated (PSpace.str o n)`. Use `isProper_str o n` as an intermediate fact. Use `infer_instance`. Establish `hd : IsDominant x`.

Use `⟨?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Dense (Set.range x.base)`. Establish `e : Set.range x.base = {genericPoint X}` using `hx`. Rewrite using `[e, dense_iff_closure_eq]`. Conclude with `genericPoint_closure X`.

Establish `he : x ≫ h = x ≫ h'` using `CrdUniq.eq_of_pCrd (by rw [Category.assoc, Category.assoc, hs, hs']) hc hc'`. Conclude with `ext_of_isDominant_of_isSeparated (PSpace.str o n) (hs.trans hs'.symm) x he`.
-/
theorem eq_of_generic_pCrd : ∀ (o : Type) [CommRing o] (n : ℕ) (X : Scheme.{0}) [IsIntegral X] [IsReduced X] (s : X ⟶ Sp o) (h h' : X ⟶ PSpace o n) (K : Type) [Field K] (x : Sp K ⟶ X) (c : Fin (n + 1) → K), h ≫ PSpace.str o n = s → h' ≫ PSpace.str o n = s → Set.range x = {genericPoint X} → PCrd (x ≫ h) c → PCrd (x ≫ h') c → h = h' := by
  intro o _ n X _ _ s h h' K _ x c hs hs' hx hc hc'
  have : IsSeparated (PSpace.str o n) := by
    have := isProper_str o n
    infer_instance
  have hd : IsDominant x := by
    refine ⟨?_⟩
    change Dense (Set.range x.base)
    have e : Set.range x.base = {genericPoint X} := hx
    rw [e, dense_iff_closure_eq]
    exact genericPoint_closure X
  have he : x ≫ h = x ≫ h' :=
    CrdUniq.eq_of_pCrd (by rw [Category.assoc, Category.assoc, hs, hs']) hc hc'
  exact ext_of_isDominant_of_isSeparated (PSpace.str o n) (hs.trans hs'.symm) x he

end GlobalTheory.SiegCrd
