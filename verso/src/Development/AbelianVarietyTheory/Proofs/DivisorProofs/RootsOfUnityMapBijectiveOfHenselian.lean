import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDefiniteDatumGoodObj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateCondCongr
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UnitOnInjectiveOfCommRing
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel GlobalTheory.UPelLevel
open scoped CategoryTheory.Obj TensorProduct
namespace GlobalTheory

/- English proof (translation)
Establish `hx : w - 1 ∈ IsLocalRing.maximalIdeal R`. Rewrite using `[IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`. Introduce `h`. Use `h.map φ` as an intermediate fact. Rewrite `this` using `[map_sub, hφ, map_one, sub_self]`.

Conclude with `not_isUnit_zero this`. Establish `hres : IsLocalRing.residue R w = 1`. Rewrite using `[← sub_eq_zero, ← map_one (IsLocalRing.residue R), ← map_sub, IsLocalRing.residue_eq_zero_iff]`. Conclude with `hx`. Establish `hS : IsUnit (∑ i ∈ Finset.range n, w ^ i)`.

Rewrite using `[← IsLocalRing.residue_ne_zero_iff_isUnit, map_sum]`. Simplify using `only [map_pow, hres, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, _root_.mul_one]`. Use `(IsLocalRing.residue_ne_zero_iff_isUnit (n : R)).2 hn` as an intermediate fact. Simplify using `using this`. Establish `h0 : (∑ i ∈ Finset.range n, w ^ i) * (w - 1) = 0`.

Rewrite using `[geom_sum_mul, hw, sub_self]`. Conclude with `sub_eq_zero.1 (hS.mul_right_eq_zero.1 h0)`.
-/
theorem rootOfUnity_eq_one_of_map_eq_one {R K : Type} [CommRing R] [IsLocalRing R] [CommRing K]
    [Nontrivial K] (φ : R →+* K) (n : ℕ) (hn : IsUnit (n : R)) (w : R) (hw : w ^ n = 1)
    (hφ : φ w = 1) : w = 1 := by
  have hx : w - 1 ∈ IsLocalRing.maximalIdeal R := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro h
    have := h.map φ
    rw [map_sub, hφ, map_one, sub_self] at this
    exact not_isUnit_zero this
  have hres : IsLocalRing.residue R w = 1 := by
    rw [← sub_eq_zero, ← map_one (IsLocalRing.residue R), ← map_sub, IsLocalRing.residue_eq_zero_iff]
    exact hx
  have hS : IsUnit (∑ i ∈ Finset.range n, w ^ i) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, map_sum]
    simp only [map_pow, hres, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, _root_.mul_one]
    have := (IsLocalRing.residue_ne_zero_iff_isUnit (n : R)).2 hn
    simpa using this
  have h0 : (∑ i ∈ Finset.range n, w ^ i) * (w - 1) = 0 := by
    rw [geom_sum_mul, hw, sub_self]
  exact sub_eq_zero.1 (hS.mul_right_eq_zero.1 h0)

/- English proof (translation)
Establish `hφ : φ (u : R) = φ (v : R)`. Use `congrArg (fun x : Kˣ => (x : K)) huv` as an intermediate fact. Simplify using `using this`. Establish `hw : ((u * v⁻¹ : Rˣ) : R) = 1`. Apply `rootOfUnity_eq_one_of_map_eq_one φ n hn` to reduce the goal to its premises.

Rewrite using `[← Units.val_pow_eq_pow_val, mul_pow, hu, inv_pow, hv, inv_one, _root_.mul_one, Units.val_one]`. Rewrite using `[Units.val_mul, map_mul, hφ, ← map_mul, Units.mul_inv, map_one]`. Conclude with `mul_inv_eq_one.1 (Units.ext hw)`.
-/
theorem units_rootOfUnity_map_injective {R K : Type} [CommRing R] [IsLocalRing R] [CommRing K]
    [Nontrivial K] (φ : R →+* K) (n : ℕ) (hn : IsUnit (n : R)) (u v : Rˣ) (hu : u ^ n = 1)
    (hv : v ^ n = 1) (huv : Units.map φ.toMonoidHom u = Units.map φ.toMonoidHom v) : u = v := by
  have hφ : φ (u : R) = φ (v : R) := by
    have := congrArg (fun x : Kˣ => (x : K)) huv
    simpa using this
  have hw : ((u * v⁻¹ : Rˣ) : R) = 1 := by
    apply rootOfUnity_eq_one_of_map_eq_one φ n hn
    · rw [← Units.val_pow_eq_pow_val, mul_pow, hu, inv_pow, hv, inv_one, _root_.mul_one, Units.val_one]
    · rw [Units.val_mul, map_mul, hφ, ← map_mul, Units.mul_inv, map_one]
  exact mul_inv_eq_one.1 (Units.ext hw)

/- English proof (translation)
Take `⟨a₀, rfl⟩` from `IsLocalRing.residue_surjective z`. Establish `hm : (Polynomial.X ^ n - 1 : Polynomial R).Monic`. Simplify using `using Polynomial.monic_X_pow_sub_C (1 : R) hn0.ne'`. Establish `ha₀ : IsUnit a₀`. Rewrite using `[← IsLocalRing.residue_ne_zero_iff_isUnit]`.

Introduce `h`. Rewrite `hz` using `[h, zero_pow hn0.ne']`. Conclude with `zero_ne_one hz`. Take `⟨a, ha, hd⟩` from `HenselianLocalRing.is_henselian (Polynomial.X ^ n - 1) hm a₀ (by`. Rewrite using `[← IsLocalRing.residue_eq_zero_iff]`.

Simplify using `[hz]) (by`. Simplify using `[Polynomial.derivative_X_pow]`. Conclude with `⟨hn, ha₀.pow _⟩)`. Use `⟨a, ?_, ?_⟩` and prove the remaining obligations. Simplify `ha` using `[sub_eq_zero]`.

Rewrite using `[← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]`. Conclude with `hd`.
-/
theorem exists_rootOfUnity_lift {R : Type} [CommRing R] [HenselianLocalRing R] (n : ℕ)
    (hn0 : 0 < n) (hn : IsUnit (n : R)) (z : IsLocalRing.ResidueField R) (hz : z ^ n = 1) :
    ∃ a : R, a ^ n = 1 ∧ IsLocalRing.residue R a = z := by
  obtain ⟨a₀, rfl⟩ := IsLocalRing.residue_surjective z
  have hm : (Polynomial.X ^ n - 1 : Polynomial R).Monic := by
    simpa using Polynomial.monic_X_pow_sub_C (1 : R) hn0.ne'
  have ha₀ : IsUnit a₀ := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
    intro h
    rw [h, zero_pow hn0.ne'] at hz
    exact zero_ne_one hz
  obtain ⟨a, ha, hd⟩ := HenselianLocalRing.is_henselian (Polynomial.X ^ n - 1) hm a₀ (by
      rw [← IsLocalRing.residue_eq_zero_iff]
      simp [hz]) (by
      simp [Polynomial.derivative_X_pow]
      exact ⟨hn, ha₀.pow _⟩)
  refine ⟨a, ?_, ?_⟩
  · simpa [sub_eq_zero] using ha
  · rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    exact hd

end GlobalTheory

namespace GlobalTheory

/- English proof (translation)
Introduce `R _ _ _ K _ φ n hn0 hn`. Use `⟨fun u v hu hv huv => units_rootOfUnity_map_injective φ n hn u v hu hv huv, ?_⟩` and prove the remaining obligations. Use `haveI : NeZero n := ⟨hn0.ne'⟩`. Use `set ρ := IsLocalRing.residue R`. Use `haveI : NeZero (n : IsLocalRing.ResidueField R) := ⟨by simpa [ρ] using (IsLocalRing.residue_ne_zero_iff_isUnit (n : R)).2 hn⟩`.

Set `f` to `restrictRootsOfUnity φ n`. Set `g` to `restrictRootsOfUnity ρ n`. Establish `hf : ∀ x : rootsOfUnity n R, ((f x : Kˣ) : K) = φ ((x : Rˣ) : R)` using `fun x => by`. Simplify using `[f]`. Establish `hg : ∀ x : rootsOfUnity n R, ((g x : (IsLocalRing.ResidueField R)ˣ) : IsLocalRing.ResidueField R) = ρ ((x : Rˣ) : R)` using `fun x => by simp [g]`.

Establish `ginj : Function.Injective g`. Introduce `x y hxy`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `units_rootOfUnity_map_injective ρ n hn _ _ ((mem_rootsOfUnity _ _).1 x.2) ((mem_rootsOfUnity _ _).1 y.2)` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises.

Use `congrArg (fun w : rootsOfUnity n (IsLocalRing.ResidueField R) => ((w : (IsLocalRing.ResidueField R)ˣ) : IsLocalRing.ResidueField R)) hxy` as an intermediate fact. Simplify `this` using `[hg]`. Establish `gsurj : Function.Surjective g`. Introduce `ζ`. Take `⟨a, ha, hρ⟩` from `exists_rootOfUnity_lift n hn0 hn ((ζ : (IsLocalRing.ResidueField R)ˣ) : IsLocalRing.ResidueField R) (by rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity _ _).1 ζ.2, Units.val_one])`.

Use `⟨⟨Units.ofPowEqOne a n ha hn0.ne', (mem_rootsOfUnity _ _).2 (Units.ext (by simp [ha]))⟩, ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[hg]`. Simplify using `using hρ`.

Establish `hcardR : Nat.card (rootsOfUnity n R) = n`. Rewrite using `[Nat.card_eq_of_bijective g ⟨ginj, gsurj⟩, HasEnoughRootsOfUnity.natCard_rootsOfUnity]`. Establish `finj : Function.Injective f`. Introduce `x y hxy`. Apply `Subtype.ext` to reduce the goal to its premises.

Apply `units_rootOfUnity_map_injective φ n hn _ _ ((mem_rootsOfUnity _ _).1 x.2) ((mem_rootsOfUnity _ _).1 y.2)` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Use `congrArg (fun w : rootsOfUnity n K => ((w : Kˣ) : K)) hxy` as an intermediate fact. Simplify `this` using `[hf]`. Establish `fbij : Function.Bijective f` using `finj.bijective_of_nat_card_le (by rw [hcardR]; exact card_rootsOfUnity K n)`.

Introduce `z hz`. Take `⟨x, hx⟩` from `fbij.2 ⟨z, (mem_rootsOfUnity _ _).2 hz⟩`. Use `⟨x, (mem_rootsOfUnity _ _).1 x.2, ?_⟩` and prove the remaining obligations. Apply `Units.ext` to reduce the goal to its premises. Use `congrArg (fun w : rootsOfUnity n K => ((w : Kˣ) : K)) hx` as an intermediate fact.

Simplify `this` using `[hf]`.
-/
theorem rootsOfUnity_map_bijective_of_henselian : ∀ (R : Type) [CommRing R] [HenselianLocalRing R]
    [IsAlgClosed (IsLocalRing.ResidueField R)] (K : Type) [Field K] (φ : R →+* K) (n : ℕ), 0 < n →
    IsUnit (n : R) →
    (∀ u v : Rˣ, u ^ n = 1 → v ^ n = 1 → Units.map φ.toMonoidHom u = Units.map φ.toMonoidHom v → u = v) ∧
    ∀ z : Kˣ, z ^ n = 1 → ∃ u : Rˣ, u ^ n = 1 ∧ Units.map φ.toMonoidHom u = z := by
  intro R _ _ _ K _ φ n hn0 hn
  refine ⟨fun u v hu hv huv => units_rootOfUnity_map_injective φ n hn u v hu hv huv, ?_⟩
  haveI : NeZero n := ⟨hn0.ne'⟩
  set ρ := IsLocalRing.residue R
  haveI : NeZero (n : IsLocalRing.ResidueField R) :=
    ⟨by simpa [ρ] using (IsLocalRing.residue_ne_zero_iff_isUnit (n : R)).2 hn⟩
  let f := restrictRootsOfUnity φ n
  let g := restrictRootsOfUnity ρ n
  have hf : ∀ x : rootsOfUnity n R, ((f x : Kˣ) : K) = φ ((x : Rˣ) : R) := fun x => by
    simp [f]
  have hg : ∀ x : rootsOfUnity n R, ((g x : (IsLocalRing.ResidueField R)ˣ) : IsLocalRing.ResidueField R) = ρ ((x : Rˣ) : R) :=
    fun x => by simp [g]
  have ginj : Function.Injective g := by
    intro x y hxy
    apply Subtype.ext
    apply units_rootOfUnity_map_injective ρ n hn _ _ ((mem_rootsOfUnity _ _).1 x.2)
      ((mem_rootsOfUnity _ _).1 y.2)
    apply Units.ext
    have := congrArg (fun w : rootsOfUnity n (IsLocalRing.ResidueField R) => ((w : (IsLocalRing.ResidueField R)ˣ) : IsLocalRing.ResidueField R)) hxy
    simpa [hg] using this
  have gsurj : Function.Surjective g := by
    intro ζ
    obtain ⟨a, ha, hρ⟩ := exists_rootOfUnity_lift n hn0 hn ((ζ : (IsLocalRing.ResidueField R)ˣ) : IsLocalRing.ResidueField R)
      (by rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity _ _).1 ζ.2, Units.val_one])
    refine ⟨⟨Units.ofPowEqOne a n ha hn0.ne', (mem_rootsOfUnity _ _).2 (Units.ext (by simp [ha]))⟩, ?_⟩
    apply Subtype.ext
    apply Units.ext
    rw [hg]
    simpa using hρ
  have hcardR : Nat.card (rootsOfUnity n R) = n := by
    rw [Nat.card_eq_of_bijective g ⟨ginj, gsurj⟩, HasEnoughRootsOfUnity.natCard_rootsOfUnity]
  have finj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply units_rootOfUnity_map_injective φ n hn _ _ ((mem_rootsOfUnity _ _).1 x.2)
      ((mem_rootsOfUnity _ _).1 y.2)
    apply Units.ext
    have := congrArg (fun w : rootsOfUnity n K => ((w : Kˣ) : K)) hxy
    simpa [hf] using this
  have fbij : Function.Bijective f :=
    finj.bijective_of_nat_card_le (by rw [hcardR]; exact card_rootsOfUnity K n)
  intro z hz
  obtain ⟨x, hx⟩ := fbij.2 ⟨z, (mem_rootsOfUnity _ _).2 hz⟩
  refine ⟨x, (mem_rootsOfUnity _ _).1 x.2, ?_⟩
  apply Units.ext
  have := congrArg (fun w : rootsOfUnity n K => ((w : Kˣ) : K)) hx
  simpa [hf] using this

end GlobalTheory
