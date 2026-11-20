import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegPull
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory

namespace GlobalTheory.SiegLoc

/- English proof (translation)
The claim follows from `le_antisymm ((pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit).1 h.dvd) ((pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit).1 h.symm.dvd)`.
-/
theorem eq_of_associated_pow_irreducible {W : Type} [CommRing W] [IsDomain W] {ϖ : W} (hϖ : Irreducible ϖ) {a b : ℕ}
    (h : Associated (ϖ ^ a) (ϖ ^ b)) : a = b :=
  le_antisymm ((pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit).1 h.dvd)
    ((pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit).1 h.symm.dvd)

/- English proof (translation)
Introduce `W _ _ _ hW ϖ hϖ f be hbe hF`. Use `haveI : IsDiscreteValuationRing W := hW.1`. Establish `hv : ∀ i, ∃ v : ℕ, (f (t i) = 0 ∧ v = 0) ∨ Associated (f (t i)) (ϖ ^ v)` using `fun i => by`. Distinguish the cases in `h : f (t i) = 0`. Conclude with `⟨0, Or.inl ⟨h, rfl⟩⟩`.

Take `⟨v, hv⟩` from `IsDiscreteValuationRing.associated_pow_irreducible h hϖ`. Conclude with `⟨v, Or.inr hv⟩`. Use `choose v hv using hv`. Establish `diag : ∀ y, be y y = ∑ i, ((v i * k : ℕ) : ℤ) * γ i y y` using `fun y => by`. Take `⟨r, u, hr, e⟩` from `hm y`.

Take `⟨r', n, hr', hn, ha⟩` from `hF y`. Take `⟨w, hw⟩` from `GlobalTheory.PsiCoordLocal.exists_unit_of_coord hr hr'`. Establish `h1 : Associated (f r) (ϖ ^ n)`. Use `Associated.trans ?_ ha` and prove the remaining obligations. Rewrite using `[hw, map_mul]`.

Conclude with `(associated_unit_mul_right _ _ (w.isUnit.map f))`. Establish `h2 : Associated (∏ i, f (t i) ^ (k * (γ i y y).toNat)) (ϖ ^ (n * 2))`. Rewrite using `[pow_mul]`. Use `Associated.trans ?_ h1.pow_pow` and prove the remaining obligations. Rewrite using `[← map_pow, e, map_mul, map_prod]`.

Simplify using `only [map_pow]`. Conclude with `(associated_unit_mul_right _ _ (u.isUnit.map f))`. Establish `hne : ∏ i, f (t i) ^ (k * (γ i y y).toNat) ≠ 0` using `fun h0 => pow_ne_zero _ hϖ.ne_zero (h2.eq_zero_iff.1 h0)`. Establish `h3 : Associated (∏ i, f (t i) ^ (k * (γ i y y).toNat)) (∏ i, ϖ ^ (v i * (k * (γ i y y).toNat)))`. Use `Associated.prod _ _ _ fun i hi => ?_` and prove the remaining obligations.

Break down `hv i with ⟨h0, hv0⟩ | h` into its components or cases. Use `Finset.prod_ne_zero_iff.1 hne i hi` as an intermediate fact. Rewrite `this`, the goal using `[h0]`. Establish `e0 : k * (γ i y y).toNat = 0`. Assume the negation of the conclusion as `hc`.

Conclude with `this (zero_pow hc)`. Rewrite using `[e0]`. Simplify using the standard rewrite rules. Rewrite using `[pow_mul ϖ]`. Conclude with `h.pow_pow`.

Rewrite `h3` using `[Finset.prod_pow_eq_pow_sum]`. Establish `h4` using `eq_of_associated_pow_irreducible hϖ (h2.symm.trans h3)`. Establish `h5 : ((n * 2 : ℕ) : ℤ) = ((∑ i, v i * (k * (γ i y y).toNat) : ℕ) : ℤ)` using `by rw [h4]`. Rewrite using `[hn, mul_comm]`. Move the coercions through the operations in `at h5 ⊢`.

Rewrite using `[h5]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Int.toNat_of_nonneg (hp i y), mul_assoc]`. Establish `full : ∀ y z, be y z = ∑ i, ((v i * k : ℕ) : ℤ) * γ i y z` using `fun y z => by`. Establish `h` using `diag (y + z)`.

Simplify using `only [map_add, LinearMap.add_apply, mul_add, Finset.sum_add_distrib, hbe z y, fun i => hs i z y] at h`. Rewrite `h` using `[← diag y, ← diag z]`. Use linear arithmetic over natural numbers and integers. Use `⟨fun i => ((v i * k : ℕ) : ℝ), fun i => Nat.cast_nonneg _, LinearMap.ext₂ fun y z => ?_⟩` and prove the remaining obligations. Simplify using `only [LinearMap.sum_apply, LinearMap.smul_apply, toReal_apply, smul_eq_mul, full y z]`.

Use `push_cast`. Both sides reduce to the same expression.
-/
theorem inCone_of_sq_monomial (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (Dg : DegPre R) (m : ℕ)
    (t : Fin m → R) (k : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ Dg.X) (hs : ∀ i y z, γ i y z = γ i z y)
    (hp : ∀ i y, 0 ≤ γ i y y)
    (hm : ∀ y, ∃ (r : R) (u : Rˣ), PsiCoord Dg y r ∧ r ^ 2 = u * ∏ i, t i ^ (k * (γ i y y).toNat)) :
    InCone Dg γ := by
  intro W _ _ _ hW ϖ hϖ f be hbe hF
  haveI : IsDiscreteValuationRing W := hW.1
  have hv : ∀ i, ∃ v : ℕ, (f (t i) = 0 ∧ v = 0) ∨ Associated (f (t i)) (ϖ ^ v) := fun i => by
    by_cases h : f (t i) = 0
    · exact ⟨0, Or.inl ⟨h, rfl⟩⟩
    · obtain ⟨v, hv⟩ := IsDiscreteValuationRing.associated_pow_irreducible h hϖ
      exact ⟨v, Or.inr hv⟩
  choose v hv using hv
  have diag : ∀ y, be y y = ∑ i, ((v i * k : ℕ) : ℤ) * γ i y y := fun y => by
    obtain ⟨r, u, hr, e⟩ := hm y
    obtain ⟨r', n, hr', hn, ha⟩ := hF y
    obtain ⟨w, hw⟩ := GlobalTheory.PsiCoordLocal.exists_unit_of_coord hr hr'
    have h1 : Associated (f r) (ϖ ^ n) := by
      refine Associated.trans ?_ ha
      rw [hw, map_mul]
      exact (associated_unit_mul_right _ _ (w.isUnit.map f))
    have h2 : Associated (∏ i, f (t i) ^ (k * (γ i y y).toNat)) (ϖ ^ (n * 2)) := by
      rw [pow_mul]
      refine Associated.trans ?_ h1.pow_pow
      rw [← map_pow, e, map_mul, map_prod]
      simp only [map_pow]
      exact (associated_unit_mul_right _ _ (u.isUnit.map f))
    have hne : ∏ i, f (t i) ^ (k * (γ i y y).toNat) ≠ 0 := fun h0 =>
      pow_ne_zero _ hϖ.ne_zero (h2.eq_zero_iff.1 h0)
    have h3 : Associated (∏ i, f (t i) ^ (k * (γ i y y).toNat)) (∏ i, ϖ ^ (v i * (k * (γ i y y).toNat))) := by
      refine Associated.prod _ _ _ fun i hi => ?_
      rcases hv i with ⟨h0, hv0⟩ | h
      · have := Finset.prod_ne_zero_iff.1 hne i hi
        rw [h0] at this ⊢
        have e0 : k * (γ i y y).toNat = 0 := by
          by_contra hc
          exact this (zero_pow hc)
        rw [e0]; simp
      · rw [pow_mul ϖ]; exact h.pow_pow
    rw [Finset.prod_pow_eq_pow_sum] at h3
    have h4 := eq_of_associated_pow_irreducible hϖ (h2.symm.trans h3)
    have h5 : ((n * 2 : ℕ) : ℤ) = ((∑ i, v i * (k * (γ i y y).toNat) : ℕ) : ℤ) := by rw [h4]
    rw [hn, mul_comm]
    push_cast at h5 ⊢
    rw [h5]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Int.toNat_of_nonneg (hp i y), mul_assoc]
  have full : ∀ y z, be y z = ∑ i, ((v i * k : ℕ) : ℤ) * γ i y z := fun y z => by
    have h := diag (y + z)
    simp only [map_add, LinearMap.add_apply, mul_add, Finset.sum_add_distrib, hbe z y, fun i => hs i z y] at h
    rw [← diag y, ← diag z] at h
    omega
  refine ⟨fun i => ((v i * k : ℕ) : ℝ), fun i => Nat.cast_nonneg _, LinearMap.ext₂ fun y z => ?_⟩
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, toReal_apply, smul_eq_mul, full y z]
  push_cast
  rfl

end GlobalTheory.SiegLoc
