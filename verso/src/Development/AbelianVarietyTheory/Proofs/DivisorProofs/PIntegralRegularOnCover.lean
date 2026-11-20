import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriModOfBlockTriangular
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx GlobalTheory.ConstLat GlobalTheory.LatChain Filter Topology
open scoped Classical

namespace GlobalTheory.LatChain

/- English proof (translation)
Introduce `F _ _ Y V p _ f hf x hx`. Take `⟨r, hr, hint⟩` from `hf`. Use `haveI := GlobalTheory.IsNormalScheme.of_pred V.normal`. Establish `h1 : IsIntegral (V.X.presheaf.stalk x) ((r : V.X.functionField) * f)` using `hint.tower_top`. Take `⟨a, ha⟩` from `(IsIntegrallyClosed.isIntegral_iff (R := V.X.presheaf.stalk x)).1 h1`.

Establish `hu : IsUnit (r : V.X.presheaf.stalk x)`. Establish `hb` using `Nat.gcd_eq_gcd_ab r p`. Rewrite `hb` using `[hr.gcd_eq_one]`. Establish `hb' : ((r : ℤ) * Nat.gcdA r p : V.X.presheaf.stalk x) + ((p : ℤ) * Nat.gcdB r p : V.X.presheaf.stalk x) = 1`. Conclude with `congrArg (Int.cast : ℤ → V.X.presheaf.stalk x) hb.symm` after adjusting the coercions.

Break down `IsLocalRing.isUnit_or_isUnit_of_add_one hb' with h | h` into its components or cases. Move the coercions through the operations in `at h`. Conclude with `isUnit_of_mul_isUnit_left h`. Move the coercions through the operations in `at h`. Conclude with `absurd (isUnit_of_mul_isUnit_left h) hx`.

Use `⟨(hu.unit⁻¹ : (V.X.presheaf.stalk x)ˣ) * a, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, ha, ← mul_assoc]`. Establish `: algebraMap (V.X.presheaf.stalk x) V.X.functionField (hu.unit⁻¹ : (V.X.presheaf.stalk x)ˣ) * (r : V.X.functionField) = 1`. Establish `e : ((hu.unit⁻¹ : (V.X.presheaf.stalk x)ˣ) : V.X.presheaf.stalk x) * (r : V.X.presheaf.stalk x) = 1` using `hu.val_inv_mul`. Rewrite using `[← map_natCast (algebraMap (V.X.presheaf.stalk x) V.X.functionField) r, ← map_mul, e, map_one]`.

Rewrite using `[this, one_mul]`.
-/
theorem regAt_of_pInt : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (p : ℕ), p.Prime → ∀ (f : V.X.functionField), PInt p f → ∀ x : V.X, Ov p x → RegAt x f := by
  intro F _ _ Y V p _ f hf x hx
  obtain ⟨r, hr, hint⟩ := hf
  haveI := GlobalTheory.IsNormalScheme.of_pred V.normal
  have h1 : IsIntegral (V.X.presheaf.stalk x) ((r : V.X.functionField) * f) := hint.tower_top
  obtain ⟨a, ha⟩ := (IsIntegrallyClosed.isIntegral_iff (R := V.X.presheaf.stalk x)).1 h1
  have hu : IsUnit (r : V.X.presheaf.stalk x) := by
    have hb := Nat.gcd_eq_gcd_ab r p
    rw [hr.gcd_eq_one] at hb
    have hb' : ((r : ℤ) * Nat.gcdA r p : V.X.presheaf.stalk x) + ((p : ℤ) * Nat.gcdB r p : V.X.presheaf.stalk x) = 1 := by
      exact_mod_cast congrArg (Int.cast : ℤ → V.X.presheaf.stalk x) hb.symm
    rcases IsLocalRing.isUnit_or_isUnit_of_add_one hb' with h | h
    · push_cast at h
      exact isUnit_of_mul_isUnit_left h
    · push_cast at h
      exact absurd (isUnit_of_mul_isUnit_left h) hx
  refine ⟨(hu.unit⁻¹ : (V.X.presheaf.stalk x)ˣ) * a, ?_⟩
  rw [map_mul, ha, ← mul_assoc]
  have : algebraMap (V.X.presheaf.stalk x) V.X.functionField (hu.unit⁻¹ : (V.X.presheaf.stalk x)ˣ) * (r : V.X.functionField) = 1 := by
    have e : ((hu.unit⁻¹ : (V.X.presheaf.stalk x)ˣ) : V.X.presheaf.stalk x) * (r : V.X.presheaf.stalk x) = 1 := hu.val_inv_mul
    rw [← map_natCast (algebraMap (V.X.presheaf.stalk x) V.X.functionField) r, ← map_mul, e, map_one]
  rw [this, one_mul]

end GlobalTheory.LatChain
