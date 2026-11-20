import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

namespace GlobalTheory.Poinc

/- English proof (translation)
Introduce `hu`. Establish `h` using `hu.map (Scheme.stalkClosedPointTo y).hom`. Rewrite `h` using `[map_natCast]`. Use `(not_isUnit_OO_iff ((p : ℕ) : OO p)).2 ?_ h` and prove the remaining obligations. Establish `e : (((p : ℕ) : OO p) : PadicAlgCl p) = algebraMap ℚ_[p] (PadicAlgCl p) ((p : ℕ) : ℚ_[p])` using `by simp`.

Rewrite using `[e, PadicAlgCl.norm_extends]`. Conclude with `Padic.norm_natCast_lt_one_iff.2 dvd_rfl`.
-/
theorem natCast_prime_not_isUnit_stalk (X : Scheme.{0}) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ X) :
    ¬ IsUnit ((p : ℕ) : X.presheaf.stalk (y (cPt p))) := by
  intro hu
  have h := hu.map (Scheme.stalkClosedPointTo y).hom
  rw [map_natCast] at h
  refine (not_isUnit_OO_iff ((p : ℕ) : OO p)).2 ?_ h
  have e : (((p : ℕ) : OO p) : PadicAlgCl p) = algebraMap ℚ_[p] (PadicAlgCl p) ((p : ℕ) : ℚ_[p]) := by simp
  rw [e, PadicAlgCl.norm_extends]
  exact Padic.norm_natCast_lt_one_iff.2 dvd_rfl

/- English proof (translation)
Establish `h1 : ¬ IsUnit ((Scheme.stalkClosedPointTo y).hom (n : X.presheaf.stalk (y (cPt q))))` using `fun hu => h ((isUnit_map_iff (Scheme.stalkClosedPointTo y).hom _).1 hu)`. Rewrite `h1` using `[map_natCast, not_isUnit_OO_iff]`. Establish `e : (((n : ℕ) : OO q) : PadicAlgCl q) = algebraMap ℚ_[q] (PadicAlgCl q) ((n : ℕ) : ℚ_[q])` using `by simp`. Rewrite `h1` using `[e, PadicAlgCl.norm_extends]`. Conclude with `Padic.norm_natCast_lt_one_iff.1 h1`.
-/
theorem dvd_of_not_isUnit_stalk (X : Scheme.{0}) (q : ℕ) [Fact q.Prime] (y : Sp (OO q) ⟶ X) (n : ℕ)
    (h : ¬ IsUnit ((n : ℕ) : X.presheaf.stalk (y (cPt q)))) : q ∣ n := by
  have h1 : ¬ IsUnit ((Scheme.stalkClosedPointTo y).hom (n : X.presheaf.stalk (y (cPt q)))) :=
    fun hu => h ((isUnit_map_iff (Scheme.stalkClosedPointTo y).hom _).1 hu)
  rw [map_natCast, not_isUnit_OO_iff] at h1
  have e : (((n : ℕ) : OO q) : PadicAlgCl q) = algebraMap ℚ_[q] (PadicAlgCl q) ((n : ℕ) : ℚ_[q]) := by simp
  rw [e, PadicAlgCl.norm_extends] at h1
  exact Padic.norm_natCast_lt_one_iff.1 h1

/- English proof (translation)
Introduce `X p q hp hq y y' h`. Establish `h1` using `natCast_prime_not_isUnit_stalk X p y`. Establish `h2 : ¬ IsUnit ((p : ℕ) : X.presheaf.stalk (y' (cPt q)))`. Rewrite using `[← h]`. Conclude with `h1`.

Establish `h3` using `dvd_of_not_isUnit_stalk X q y' p h2`. Conclude with `((Nat.prime_dvd_prime_iff_eq hq.out hp.out).1 h3).symm`.
-/
theorem eq_of_cPt_eq : ∀ (X : Scheme.{0}) (p q : ℕ) [Fact p.Prime] [Fact q.Prime] (y : Sp (OO p) ⟶ X)
    (y' : Sp (OO q) ⟶ X), y (cPt p) = y' (cPt q) → p = q := by
  intro X p q hp hq y y' h
  have h1 := natCast_prime_not_isUnit_stalk X p y
  have h2 : ¬ IsUnit ((p : ℕ) : X.presheaf.stalk (y' (cPt q))) := by
    rw [← h]; exact h1
  have h3 := dvd_of_not_isUnit_stalk X q y' p h2
  exact ((Nat.prime_dvd_prime_iff_eq hq.out hp.out).1 h3).symm

end GlobalTheory.Poinc
