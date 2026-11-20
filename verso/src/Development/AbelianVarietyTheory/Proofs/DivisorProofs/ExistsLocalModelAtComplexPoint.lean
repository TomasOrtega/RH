import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldPair

/- English proof (translation)
Introduce `A _ _ _ _ ε`. Set `K` to `FractionRing A`. Set `P : Ideal A` to `RingHom.ker (ε : A →+* ℂ)`. Use `haveI : P.IsPrime := RingHom.ker_isPrime _`. Establish `hle : P.primeCompl ≤ nonZeroDivisors A` using `P.primeCompl_le_nonZeroDivisors`.

Set `B : Subalgebra A K` to `Localization.subalgebra.ofField K P.primeCompl hle`. Use `haveI hB : IsLocalization P.primeCompl B := Localization.subalgebra.isLocalization_ofField K _ hle`. Set `b : A →+* B` to `algebraMap A B`. Establish `hu : ∀ y : P.primeCompl, IsUnit ((ε : A →+* ℂ) y)` using `fun y => by`. Use `isUnit_iff_ne_zero.2 fun h => y.2 ?_` and prove the remaining obligations.

Conclude with `RingHom.mem_ker.2 h`. Set `ψ : B →+* ℂ` to `IsLocalization.lift hu`. Establish `hψ : ∀ x, ψ (b x) = ε x` using `IsLocalization.lift_eq hu`. Establish `hcK : ∀ z : ℂ, algebraMap ℂ K z = algebraMap A K (algebraMap ℂ A z)` using `fun z => IsScalarTower.algebraMap_apply ℂ A K z`. Establish `hc : ∀ z : ℂ, algebraMap ℂ K z ∈ B.toSubring` using `fun z => by`.

Rewrite using `[hcK]`. Conclude with `B.algebraMap_mem _`. Establish `hψc : ∀ z : ℂ, ψ ⟨algebraMap ℂ K z, hc z⟩ = z` using `fun z => by`. Establish `: (⟨algebraMap ℂ K z, hc z⟩ : B) = b (algebraMap ℂ A z)` using `Subtype.ext (hcK z)`. Rewrite using `[this, hψ]`.

Conclude with `ε.commutes z`. Establish `key : ∀ x : B, ψ x = 0 → NonUnit B.toSubring (x : K)` using `fun x hx => by`. Use `(nonUnit_iff (R := B.toSubring) x).2 fun h => ?_` and prove the remaining obligations. Use `h.map ψ` as an intermediate fact. Rewrite `this` using `[hx]`.

Conclude with `not_isUnit_zero this`. Use `⟨B.toSubring, ⟨hc, IsLocalization.AtPrime.isLocalRing B P, ?_, ?_⟩, ?_, fun a => ?_⟩` and prove the remaining obligations. Establish `e : (algebraMap ℂ K).codRestrict B.toSubring hc = b.comp (algebraMap ℂ A)`. Use extensionality with `z`. Conclude with `hcK z`.

Rewrite using `[e]`. Use `RingHom.EssFiniteType.comp ?_ ?_` and prove the remaining obligations. Conclude with `RingHom.essFiniteType_algebraMap.2 (inferInstance : Algebra.EssFiniteType ℂ A)`. Conclude with `(RingHom.essFiniteType_algebraMap (R := A) (S := B)).2 (Algebra.EssFiniteType.of_isLocalization B P.primeCompl)`. Introduce `f`.

Take `⟨x, y, hy, rfl⟩` from `IsFractionRing.div_surjective (A := A) f`. Establish `hy' : algebraMap A K y ≠ 0` using `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hy`. Conclude with `⟨_, B.algebraMap_mem x, _, B.algebraMap_mem y, hy', div_mul_cancel₀ _ hy'⟩`. Introduce `r hr`. Use `⟨ψ ⟨r, hr⟩, key (⟨r, hr⟩ - ⟨algebraMap ℂ K (ψ ⟨r, hr⟩), hc _⟩) ?_⟩` and prove the remaining obligations.

Rewrite using `[map_sub, hψc, sub_self]`. Use `⟨B.algebraMap_mem a, fun ha => key (b a) ?_⟩` and prove the remaining obligations. Rewrite using `[hψ, ha]`.
-/
theorem exists_locModel_at_point :
    ∀ (A : Type) [CommRing A] [IsDomain A] [Algebra ℂ A] [Algebra.EssFiniteType ℂ A] (ε : A →ₐ[ℂ] ℂ),
      ∃ T : Subring (FractionRing A), IsLocModel (algebraMap ℂ (FractionRing A)) T ∧
        RatRes (algebraMap ℂ (FractionRing A)) T ∧
        ∀ a : A, algebraMap A (FractionRing A) a ∈ T ∧
          (ε a = 0 → NonUnit T (algebraMap A (FractionRing A) a)) := by
  intro A _ _ _ _ ε
  let K := FractionRing A
  let P : Ideal A := RingHom.ker (ε : A →+* ℂ)
  haveI : P.IsPrime := RingHom.ker_isPrime _
  have hle : P.primeCompl ≤ nonZeroDivisors A := P.primeCompl_le_nonZeroDivisors
  let B : Subalgebra A K := Localization.subalgebra.ofField K P.primeCompl hle
  haveI hB : IsLocalization P.primeCompl B := Localization.subalgebra.isLocalization_ofField K _ hle
  let b : A →+* B := algebraMap A B
  have hu : ∀ y : P.primeCompl, IsUnit ((ε : A →+* ℂ) y) := fun y => by
    refine isUnit_iff_ne_zero.2 fun h => y.2 ?_
    exact RingHom.mem_ker.2 h
  let ψ : B →+* ℂ := IsLocalization.lift hu
  have hψ : ∀ x, ψ (b x) = ε x := IsLocalization.lift_eq hu
  have hcK : ∀ z : ℂ, algebraMap ℂ K z = algebraMap A K (algebraMap ℂ A z) :=
    fun z => IsScalarTower.algebraMap_apply ℂ A K z
  have hc : ∀ z : ℂ, algebraMap ℂ K z ∈ B.toSubring := fun z => by
    rw [hcK]; exact B.algebraMap_mem _
  have hψc : ∀ z : ℂ, ψ ⟨algebraMap ℂ K z, hc z⟩ = z := fun z => by
    have : (⟨algebraMap ℂ K z, hc z⟩ : B) = b (algebraMap ℂ A z) := Subtype.ext (hcK z)
    rw [this, hψ]; exact ε.commutes z
  have key : ∀ x : B, ψ x = 0 → NonUnit B.toSubring (x : K) := fun x hx => by
    refine (nonUnit_iff (R := B.toSubring) x).2 fun h => ?_
    have := h.map ψ
    rw [hx] at this
    exact not_isUnit_zero this
  refine ⟨B.toSubring, ⟨hc, IsLocalization.AtPrime.isLocalRing B P, ?_, ?_⟩, ?_, fun a => ?_⟩
  · have e : (algebraMap ℂ K).codRestrict B.toSubring hc = b.comp (algebraMap ℂ A) := by
      ext z; exact hcK z
    rw [e]
    refine RingHom.EssFiniteType.comp ?_ ?_
    · exact RingHom.essFiniteType_algebraMap.2 (inferInstance : Algebra.EssFiniteType ℂ A)
    · exact (RingHom.essFiniteType_algebraMap (R := A) (S := B)).2
        (Algebra.EssFiniteType.of_isLocalization B P.primeCompl)
  · intro f
    obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := A) f
    have hy' : algebraMap A K y ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hy
    exact ⟨_, B.algebraMap_mem x, _, B.algebraMap_mem y, hy', div_mul_cancel₀ _ hy'⟩
  · intro r hr
    refine ⟨ψ ⟨r, hr⟩, key (⟨r, hr⟩ - ⟨algebraMap ℂ K (ψ ⟨r, hr⟩), hc _⟩) ?_⟩
    rw [map_sub, hψc, sub_self]
  · refine ⟨B.algebraMap_mem a, fun ha => key (b a) ?_⟩
    rw [hψ, ha]

end GlobalTheory.FieldPair
