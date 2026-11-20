import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AbVarRed

/- English proof (translation)
Introduce `R K _ _ _ _ _ _ L _ _ _ V h`. Use `letI : Algebra R L := ((algebraMap K L).comp (algebraMap R K)).toAlgebra`. Establish `: IsScalarTower R K L` using `.of_algebraMap_eq fun _ => rfl`. Establish `memV : ∀ a : K, algebraMap K L a ∈ V ↔ a ∈ (algebraMap R K).range` using `fun a => by`. Rewrite using `[← h]`.

Both sides reduce to the same expression. Set `W : Subalgebra R L` to `{ V.toSubring with algebraMap_mem' := fun r => (memV (algebraMap R K r)).2 ⟨r, rfl⟩ }`. Establish `hVn : IsNoetherianRing V` using `(GlobalTheory.krullAkizuki K W).1`. Establish `hnf : ¬ IsField V`. Introduce `hf`.

Apply `IsDiscreteValuationRing.not_isField R` to reduce the goal to its premises. Establish `hs : Function.Surjective (algebraMap R K)` using `fun x => by`. Distinguish the cases in `hx : x = 0`. Conclude with `⟨0, by simp [hx]⟩`. Establish `hxL : algebraMap K L x ≠ 0` using `(map_ne_zero _).2 hx`.

Establish `hmem : algebraMap K L x ∈ V`. Break down `V.mem_or_inv_mem (algebraMap K L x) with h1 | h1` into its components or cases. Conclude with `h1`. Take `⟨y, hy⟩` from `hf.mul_inv_cancel (a := (⟨_, h1⟩ : V)) (fun e => inv_ne_zero hxL (congrArg Subtype.val e))`. Establish `hy' : (algebraMap K L x)⁻¹ * (y : L) = 1` using `congrArg Subtype.val hy`.

Establish `: (y : L) = algebraMap K L x`. Rewrite using `[← inv_inv (algebraMap K L x)]`. Conclude with `eq_inv_of_mul_eq_one_right hy'`. Conclude with `this ▸ y.2`. Conclude with `(memV x).1 hmem`.

Conclude with `(RingEquiv.ofBijective (algebraMap R K) ⟨IsFractionRing.injective R K, hs⟩).toMulEquiv.isField (Field.toIsField K)`. Establish `hval : ValuationRing V` using `inferInstance`. Conclude with `((IsDiscreteValuationRing.TFAE V hnf).out 1 0).mp hval`.
-/
theorem isDiscreteValuationRing_of_isAbove :
    ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
      [IsFractionRing R K] (L : Type) [Field L] [Algebra K L] [FiniteDimensional K L]
      (V : ValuationSubring L), IsAbove R K V.toSubring → IsDiscreteValuationRing V := by
  intro R K _ _ _ _ _ _ L _ _ _ V h
  letI : Algebra R L := ((algebraMap K L).comp (algebraMap R K)).toAlgebra
  have : IsScalarTower R K L := .of_algebraMap_eq fun _ => rfl
  have memV : ∀ a : K, algebraMap K L a ∈ V ↔ a ∈ (algebraMap R K).range := fun a => by
    rw [← h]; rfl
  let W : Subalgebra R L :=
    { V.toSubring with
      algebraMap_mem' := fun r => (memV (algebraMap R K r)).2 ⟨r, rfl⟩ }
  have hVn : IsNoetherianRing V := (GlobalTheory.krullAkizuki K W).1
  have hnf : ¬ IsField V := by
    intro hf
    apply IsDiscreteValuationRing.not_isField R
    have hs : Function.Surjective (algebraMap R K) := fun x => by
      by_cases hx : x = 0
      · exact ⟨0, by simp [hx]⟩
      have hxL : algebraMap K L x ≠ 0 := (map_ne_zero _).2 hx
      have hmem : algebraMap K L x ∈ V := by
        rcases V.mem_or_inv_mem (algebraMap K L x) with h1 | h1
        · exact h1
        · obtain ⟨y, hy⟩ := hf.mul_inv_cancel (a := (⟨_, h1⟩ : V))
            (fun e => inv_ne_zero hxL (congrArg Subtype.val e))
          have hy' : (algebraMap K L x)⁻¹ * (y : L) = 1 := congrArg Subtype.val hy
          have : (y : L) = algebraMap K L x := by
            rw [← inv_inv (algebraMap K L x)]
            exact eq_inv_of_mul_eq_one_right hy'
          exact this ▸ y.2
      exact (memV x).1 hmem
    exact (RingEquiv.ofBijective (algebraMap R K) ⟨IsFractionRing.injective R K, hs⟩).toMulEquiv.isField
      (Field.toIsField K)
  have hval : ValuationRing V := inferInstance
  exact ((IsDiscreteValuationRing.TFAE V hnf).out 1 0).mp hval

end GlobalTheory.AbVarRed
