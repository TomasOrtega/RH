import Mathlib

namespace GlobalTheory.InjectiveOfIntegral

/- English proof (translation)
Set `_ : Algebra A C` to `((algebraMap O C).comp j).toAlgebra`. Set `_ : Algebra A O` to `j.toAlgebra`. Establish `: IsScalarTower A O C` using `IsScalarTower.of_algebraMap_eq fun _ => rfl`. Establish `hAC : Function.Injective (algebraMap A C)` using `hj`. Establish `: Module.IsTorsionFree A B` using `Module.isTorsionFree_iff_algebraMap_injective.mpr hAB`.

Establish `: Module.IsTorsionFree A C` using `Module.isTorsionFree_iff_algebraMap_injective.mpr hAC`. Establish `: Algebra.IsAlgebraic A B` using `Algebra.IsIntegral.isAlgebraic`. Set `ψ : B →ₐ[A] C` to `IsAlgClosed.lift`. Establish `hker : RingHom.ker (ψ : B →+* C) = ⊥`. Apply `Ideal.eq_bot_of_comap_eq_bot (R := A)` to reduce the goal to its premises.

Use extensionality with `a`. Rewrite using `[Ideal.mem_comap, RingHom.mem_ker, Ideal.mem_bot, show (ψ : B →+* C) (algebraMap A B a) = algebraMap A C a from ψ.commutes a]`. Conclude with `⟨fun h => hAC (h.trans (map_zero _).symm), fun h => by rw [h, map_zero]⟩`. Establish `hψ : Function.Injective (ψ : B →+* C)` using `(RingHom.injective_iff_ker_eq_bot _).mpr hker`. Establish `hint : ∀ b : B, v (ψ b) ≤ 1`.

Introduce `b`. Establish `hb : IsIntegral A (ψ b)` using `(Algebra.IsIntegral.isIntegral b).map ψ`. Conclude with `hv.mem_of_integral hb.tower_top`. Use `choose g hg using fun b => hv.exists_of_le_one (hint b)`. Set `j' : B →+* O` to `{ toFun := g map_one' := hv.hom_inj (by simp only [hg, map_one]) map_mul' := fun x y => hv.hom_inj (by simp only [hg, map_mul]) map_zero' := hv.hom_inj (by simp only [hg, map_zero]) map_add' := fun x y => hv.hom_inj (by simp only [hg, map_add]) }`.

Use `⟨j', ?_⟩` and prove the remaining obligations. Establish `e : (algebraMap O C).comp j' = (ψ : B →+* C)` using `RingHom.ext hg`. Rewrite using `[e]`. Conclude with `hψ`.
-/
theorem exists_injective_of_isIntegral {A B O C : Type} [CommRing A] [IsDomain A] [CommRing B]
    [IsDomain B] [CommRing O] [Field C] [IsAlgClosed C] [Algebra O C] (v : Valuation C NNReal)
    (hv : Valuation.Integers v O) [Algebra A B] [Algebra.IsIntegral A B]
    (hAB : Function.Injective (algebraMap A B)) (j : A →+* O)
    (hj : Function.Injective ((algebraMap O C).comp j)) :
    ∃ j' : B →+* O, Function.Injective ((algebraMap O C).comp j') := by
  classical
  let _ : Algebra A C := ((algebraMap O C).comp j).toAlgebra
  let _ : Algebra A O := j.toAlgebra
  have : IsScalarTower A O C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hAC : Function.Injective (algebraMap A C) := hj
  have : Module.IsTorsionFree A B := Module.isTorsionFree_iff_algebraMap_injective.mpr hAB
  have : Module.IsTorsionFree A C := Module.isTorsionFree_iff_algebraMap_injective.mpr hAC
  have : Algebra.IsAlgebraic A B := Algebra.IsIntegral.isAlgebraic
  let ψ : B →ₐ[A] C := IsAlgClosed.lift
  have hker : RingHom.ker (ψ : B →+* C) = ⊥ := by
    apply Ideal.eq_bot_of_comap_eq_bot (R := A)
    ext a
    rw [Ideal.mem_comap, RingHom.mem_ker, Ideal.mem_bot,
      show (ψ : B →+* C) (algebraMap A B a) = algebraMap A C a from ψ.commutes a]
    exact ⟨fun h => hAC (h.trans (map_zero _).symm), fun h => by rw [h, map_zero]⟩
  have hψ : Function.Injective (ψ : B →+* C) := (RingHom.injective_iff_ker_eq_bot _).mpr hker
  have hint : ∀ b : B, v (ψ b) ≤ 1 := by
    intro b
    have hb : IsIntegral A (ψ b) := (Algebra.IsIntegral.isIntegral b).map ψ
    exact hv.mem_of_integral hb.tower_top
  choose g hg using fun b => hv.exists_of_le_one (hint b)
  let j' : B →+* O :=
    { toFun := g
      map_one' := hv.hom_inj (by simp only [hg, map_one])
      map_mul' := fun x y => hv.hom_inj (by simp only [hg, map_mul])
      map_zero' := hv.hom_inj (by simp only [hg, map_zero])
      map_add' := fun x y => hv.hom_inj (by simp only [hg, map_add]) }
  refine ⟨j', ?_⟩
  have e : (algebraMap O C).comp j' = (ψ : B →+* C) := RingHom.ext hg
  rw [e]
  exact hψ

end GlobalTheory.InjectiveOfIntegral
