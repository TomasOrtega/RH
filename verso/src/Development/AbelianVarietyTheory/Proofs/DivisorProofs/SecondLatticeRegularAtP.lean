import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNonarchimedeanW
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag GlobalTheory.WholeFlag GlobalTheory.ConstLat
open scoped Classical

namespace GlobalTheory.ConstLat.RegJ

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

/- English proof (translation)
Use `haveI := (V.normal x).2`. Conclude with `IsIntegrallyClosed.algebraMap_eq_of_integral (hf.tower_top (A := V.X.presheaf.stalk x))`.
-/
theorem regAt_of_isIntegral (V : Cover Y) (x : V.X) {f : V.X.functionField} (hf : IsIntegral ℤ f) : RegAt x f := by
  haveI := (V.normal x).2
  exact IsIntegrallyClosed.algebraMap_eq_of_integral (hf.tower_top (A := V.X.presheaf.stalk x))

/- English proof (translation)
Take `⟨a, b, hab⟩` from `Nat.isCoprime_iff_coprime.2 hs`. Establish `h1 : (a : V.X.presheaf.stalk x) * (s : V.X.presheaf.stalk x) + (b : V.X.presheaf.stalk x) * (p : V.X.presheaf.stalk x) = 1`. Use `congrArg (Int.castRingHom (V.X.presheaf.stalk x)) hab` as an intermediate fact. Simplify using `using this`. Break down `IsLocalRing.isUnit_or_isUnit_of_add_one h1 with h | h` into its components or cases.

Conclude with `⟨s, isUnit_of_mul_isUnit_right h, map_natCast _ _⟩`. Conclude with `(hx (isUnit_of_mul_isUnit_right h)).elim`.
-/
theorem unitAt_natCast_of_coprime (V : Cover Y) (x : V.X) {s p : ℕ} (hs : s.Coprime p)
    (hx : ¬ IsUnit (p : V.X.presheaf.stalk x)) : UnitAt x (s : V.X.functionField) := by
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hs
  have h1 : (a : V.X.presheaf.stalk x) * (s : V.X.presheaf.stalk x) + (b : V.X.presheaf.stalk x) * (p : V.X.presheaf.stalk x) = 1 := by
    have := congrArg (Int.castRingHom (V.X.presheaf.stalk x)) hab
    simpa using this
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one h1 with h | h
  · exact ⟨s, isUnit_of_mul_isUnit_right h, map_natCast _ _⟩
  · exact (hx (isUnit_of_mul_isUnit_right h)).elim

/- English proof (translation)
Establish `hu` using `unitAt_natCast_of_coprime V x hs hx`. Establish `h1 : RegAt x ((s : V.X.functionField) * κ e)`. Use `regAt_of_isIntegral V x (he.map κ.toIntAlgHom)` as an intermediate fact. Simplify using `using this`. Establish `h2 : κ e = (s : V.X.functionField)⁻¹ * ((s : V.X.functionField) * κ e)`.

Rewrite using `[← mul_assoc, inv_mul_cancel₀ hu.ne_zero, one_mul]`. Rewrite using `[h2]`. Conclude with `hu.inv.regAt.mul h1`.
-/
theorem regAt_of_mul (V : Cover Y) (κ : F →+* V.X.functionField) (x : V.X) {s p : ℕ} (hs : s.Coprime p)
    (hx : ¬ IsUnit (p : V.X.presheaf.stalk x)) {e : F} (he : IsIntegral ℤ ((s : F) * e)) : RegAt x (κ e) := by
  have hu := unitAt_natCast_of_coprime V x hs hx
  have h1 : RegAt x ((s : V.X.functionField) * κ e) := by
    have := regAt_of_isIntegral V x (he.map κ.toIntAlgHom)
    simpa using this
  have h2 : κ e = (s : V.X.functionField)⁻¹ * ((s : V.X.functionField) * κ e) := by
    rw [← mul_assoc, inv_mul_cancel₀ hu.ne_zero, one_mul]
  rw [h2]
  exact hu.inv.regAt.mul h1

/- English proof (translation)
Apply `Matrix.inv_eq_left_inv` to reduce the goal to its premises. Rewrite using `[← Matrix.map_mul, Matrix.nonsing_inv_mul A h, Matrix.map_one f (map_zero f) (map_one f)]`.
-/
theorem map_inv_of_isUnit {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {N : ℕ}
    (A : Matrix (Fin N) (Fin N) R) (h : IsUnit A.det) : (A.map f)⁻¹ = A⁻¹.map f := by
  apply Matrix.inv_eq_left_inv
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul A h, Matrix.map_one f (map_zero f) (map_one f)]

/- English proof (translation)
Use extensionality with `i j`. Simplify using the standard rewrite rules.
-/
theorem castMap_eq {N : ℕ} {K : Type} [Field K] (κ : F →+* K) (J : Matrix (Fin N) (Fin N) ℤ) :
    J.map (Int.castRingHom K) = (J.map (Int.castRingHom F)).map κ := by
  ext i j; simp

end GlobalTheory.ConstLat.RegJ

open GlobalTheory.ConstLat.RegJ in

/- English proof (translation)
Introduce `F _ _ Y V κ N J p n P Q _ hJ hL x hx i j`. Take `⟨_, hn, s, hs, hint⟩` from `hL`. Establish `hinvK : (J.map (Int.castRingHom V.X.functionField))⁻¹ = J⁻¹.map (Int.castRingHom V.X.functionField)` using `map_inv_of_isUnit _ J hJ`. Establish `hinvF : (J.map (Int.castRingHom F))⁻¹ = J⁻¹.map (Int.castRingHom F)` using `map_inv_of_isUnit _ J hJ`. Establish `hint_reg : ∀ z : ℤ, RegAt x (z : V.X.functionField)` using `fun z => ⟨(z : V.X.presheaf.stalk x), map_intCast _ _⟩`.

Use `⟨?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `e1 : ((Q.map κ).transpose * J.map (Int.castRingHom V.X.functionField) * Q.map κ) = (Q.transpose * J.map (Int.castRingHom F) * Q).map κ`. Rewrite using `[castMap_eq κ J, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]`. Rewrite using `[e1, Matrix.map_apply]`. Conclude with `regAt_of_mul V κ x hs hx (hint i j).1`.

Establish `e1 : (P.map κ * (J.map (Int.castRingHom V.X.functionField))⁻¹ * (P.map κ).transpose) = (P * (J.map (Int.castRingHom F))⁻¹ * P.transpose).map κ`. Rewrite using `[hinvK, hinvF, castMap_eq κ (J⁻¹), Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]`. Rewrite using `[e1, Matrix.map_apply]`. Conclude with `regAt_of_mul V κ x hs hx (hint i j).2`. Rewrite using `[hinvK, Matrix.map_apply]`.

Conclude with `hint_reg _`. Establish `e1 : (n : V.X.functionField) * P.map κ i j = κ ((n : F) * P i j)` using `by simp`. Rewrite using `[e1]`. Conclude with `regAt_of_isIntegral V x ((hn i j).1.map κ.toIntAlgHom)`. Rewrite using `[Matrix.map_apply]`.

Conclude with `hint_reg _`.
-/
theorem GlobalTheory.ConstLat.regAt_secondLat : ∀ {F : Type} [Field F] [NumberField F] {Y : Var F} (V : Cover Y) (κ : F →+* V.X.functionField) {N : ℕ}
    (J : Matrix (Fin N) (Fin N) ℤ) (p n : ℕ) (P Q : Matrix (Fin N) (Fin N) F), p.Prime → IsUnit J.det →
    SecondLat J p n P Q → ∀ x : V.X, ¬ IsUnit (p : V.X.presheaf.stalk x) → ∀ i j,
      RegAt x (((Q.map κ).transpose * J.map (Int.castRingHom V.X.functionField) * Q.map κ) i j) ∧
      RegAt x ((P.map κ * (J.map (Int.castRingHom V.X.functionField))⁻¹ * (P.map κ).transpose) i j) ∧
      RegAt x ((J.map (Int.castRingHom V.X.functionField))⁻¹ i j) ∧ RegAt x ((n : V.X.functionField) * P.map κ i j) ∧
      RegAt x (J.map (Int.castRingHom V.X.functionField) i j) := by
  intro F _ _ Y V κ N J p n P Q _ hJ hL x hx i j
  obtain ⟨_, hn, s, hs, hint⟩ := hL
  have hinvK : (J.map (Int.castRingHom V.X.functionField))⁻¹ = J⁻¹.map (Int.castRingHom V.X.functionField) :=
    map_inv_of_isUnit _ J hJ
  have hinvF : (J.map (Int.castRingHom F))⁻¹ = J⁻¹.map (Int.castRingHom F) := map_inv_of_isUnit _ J hJ
  have hint_reg : ∀ z : ℤ, RegAt x (z : V.X.functionField) := fun z => ⟨(z : V.X.presheaf.stalk x), map_intCast _ _⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have e1 : ((Q.map κ).transpose * J.map (Int.castRingHom V.X.functionField) * Q.map κ) =
        (Q.transpose * J.map (Int.castRingHom F) * Q).map κ := by
      rw [castMap_eq κ J, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
    rw [e1, Matrix.map_apply]
    exact regAt_of_mul V κ x hs hx (hint i j).1
  · have e1 : (P.map κ * (J.map (Int.castRingHom V.X.functionField))⁻¹ * (P.map κ).transpose) =
        (P * (J.map (Int.castRingHom F))⁻¹ * P.transpose).map κ := by
      rw [hinvK, hinvF, castMap_eq κ (J⁻¹), Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
    rw [e1, Matrix.map_apply]
    exact regAt_of_mul V κ x hs hx (hint i j).2
  · rw [hinvK, Matrix.map_apply]; exact hint_reg _
  · have e1 : (n : V.X.functionField) * P.map κ i j = κ ((n : F) * P i j) := by simp
    rw [e1]
    exact regAt_of_isIntegral V x ((hn i j).1.map κ.toIntAlgHom)
  · rw [Matrix.map_apply]; exact hint_reg _
