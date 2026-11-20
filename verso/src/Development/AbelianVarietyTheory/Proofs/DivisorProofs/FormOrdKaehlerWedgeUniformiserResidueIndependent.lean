import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormOrdDFormUniformiserCons
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

namespace GlobalTheory

/- English proof (translation)
Introduce `K _ cK F m π y hπ hy hP hB`. Establish `hπ0 : π ≠ 0`. Introduce and unpack `rfl`. Simplify using `[Place.ord] at hπ`. Establish `hπm : π ∈ F.ring` using `(F.ord_nonneg_iff hπ0).1 (by rw [hπ]; norm_num)`.

Establish `hirr : Irreducible (⟨π, hπm⟩ : F.ring)`. Take `⟨t, ht⟩` from `IsDiscreteValuationRing.exists_irreducible F.ring`. Establish `hne : (⟨π, hπm⟩ : F.ring) ≠ 0` using `fun h => hπ0 (congrArg Subtype.val h)`. Take `⟨n, u, hu⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hne ht`. Establish `e : π = ((u : F.ring) : K) * (t : K) ^ n`.

Simplify using `using congrArg Subtype.val hu`. Establish `hu0 : ((u : F.ring) : K) ≠ 0` using `(u.isUnit.map F.ring.subtype).ne_zero`. Establish `ht0 : (t : K) ≠ 0` using `fun h => ht.ne_zero (Subtype.ext h)`. Establish `h1 : F.ord π = n`. Rewrite using `[e, F.ord_mul hu0 (pow_ne_zero _ ht0), F.ord_eq_zero u.isUnit, F.ord_pow, F.ord_irreducible ht]`.

Simplify using the standard rewrite rules. Choose the witnesses or unpack the hypotheses as in `rfl : n = 1 := by`. Rewrite `h1` using `[hπ]`. Conclude with `h1.symm` after adjusting the coercions. Rewrite using `[hu, pow_one]`.

Conclude with `(irreducible_units_mul u).2 ht`. Use `formOrd_dForm_uniformiser_cons cK m F ⟨π, hπm⟩ (fun i => ⟨y i, hy i⟩) hirr ?_ ⟨_, hB⟩` and prove the remaining obligations. Introduce `P hP0`. Take `⟨h0, hi⟩` from `hP P hP0`. Establish `e : ((MvPolynomial.eval₂ F.const (fun i => (⟨y i, hy i⟩ : F.ring)) P : F.ring) : K) = MvPolynomial.eval₂ cK y P` using `MvPolynomial.eval₂_comp_left F.ring.subtype F.const (fun i => (⟨y i, hy i⟩ : F.ring)) P`.

Use `IsUnit.of_mul_eq_one (⟨_, hi⟩ : F.ring) (Subtype.ext ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `((MvPolynomial.eval₂ F.const (fun i => (⟨y i, hy i⟩ : F.ring)) P : F.ring) : K) * _ = 1`. Rewrite using `[e]`. Conclude with `mul_inv_cancel₀ h0`.
-/
theorem formOrd_dForm_cons_of_ord_eq_one : ∀ {K : Type} [Field K] (cK : ℂ →+* K) (F : Place cK) (m : ℕ) (π : K) (y : Fin m → K),
  F.ord π = 1 → (∀ i, y i ∈ F.ring) →
  (∀ P : MvPolynomial (Fin m) ℂ, P ≠ 0 → MvPolynomial.eval₂ cK y P ≠ 0 ∧ (MvPolynomial.eval₂ cK y P)⁻¹ ∈ F.ring) →
  TrBasis cK (Fin.cons π y : Fin (m + 1) → K) →
  F.formOrd (dForm cK (Fin.cons π y : Fin (m + 1) → K)) = 0 := by
  intro K _ cK F m π y hπ hy hP hB
  have hπ0 : π ≠ 0 := by
    rintro rfl
    simp [Place.ord] at hπ
  have hπm : π ∈ F.ring := (F.ord_nonneg_iff hπ0).1 (by rw [hπ]; norm_num)
  have hirr : Irreducible (⟨π, hπm⟩ : F.ring) := by
    obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible F.ring
    have hne : (⟨π, hπm⟩ : F.ring) ≠ 0 := fun h => hπ0 (congrArg Subtype.val h)
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hne ht
    have e : π = ((u : F.ring) : K) * (t : K) ^ n := by
      simpa using congrArg Subtype.val hu
    have hu0 : ((u : F.ring) : K) ≠ 0 := (u.isUnit.map F.ring.subtype).ne_zero
    have ht0 : (t : K) ≠ 0 := fun h => ht.ne_zero (Subtype.ext h)
    have h1 : F.ord π = n := by
      rw [e, F.ord_mul hu0 (pow_ne_zero _ ht0), F.ord_eq_zero u.isUnit, F.ord_pow,
        F.ord_irreducible ht]
      simp
    obtain rfl : n = 1 := by
      rw [hπ] at h1
      exact_mod_cast h1.symm
    rw [hu, pow_one]
    exact (irreducible_units_mul u).2 ht
  refine formOrd_dForm_uniformiser_cons cK m F ⟨π, hπm⟩ (fun i => ⟨y i, hy i⟩) hirr ?_ ⟨_, hB⟩
  intro P hP0
  obtain ⟨h0, hi⟩ := hP P hP0
  have e : ((MvPolynomial.eval₂ F.const (fun i => (⟨y i, hy i⟩ : F.ring)) P : F.ring) : K) =
      MvPolynomial.eval₂ cK y P :=
    MvPolynomial.eval₂_comp_left F.ring.subtype F.const (fun i => (⟨y i, hy i⟩ : F.ring)) P
  refine IsUnit.of_mul_eq_one (⟨_, hi⟩ : F.ring) (Subtype.ext ?_)
  change ((MvPolynomial.eval₂ F.const (fun i => (⟨y i, hy i⟩ : F.ring)) P : F.ring) : K) * _ = 1
  rw [e]
  exact mul_inv_cancel₀ h0

end GlobalTheory
