import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.FaceDSingle
import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.Subquot
import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.ImportsAlt

open CategoryTheory UpperTheory.V.KH

/- English proof (translation)
Introduce `S _ _ j`. Establish `hi : Function.Injective (groupHomology.iCycles (Rep.trivial ℤ S ℤ) (j + 1)).hom` using `(ModuleCat.mono_iff_injective _).1 inferInstance`. Establish `hq : Function.Surjective (groupHomology.π (Rep.trivial ℤ S ℤ) (j + 1)).hom` using `fun x => groupHomology_induction_on x fun y => ⟨y, rfl⟩`. Establish `h` using `subquot (Fin (j + 1) → S) (groupHomology.cycles (Rep.trivial ℤ S ℤ) (j + 1)) (HZ S (j + 1)) (groupHomology.iCycles (Rep.trivial ℤ S ℤ) (j + 1)).hom.toAddMonoidHom (groupHomology.π (Rep.trivial ℤ S ℤ) (j + 1)).hom.toAddMonoidHom (Nat.card S) Nat.card_pos hi hq (kill S j)`. Rewrite `h` using `[Nat.card_fun, Nat.card_fin]`. Then use the resulting hypothesis.
-/
theorem UpperTheory.V.KH.finGroup :
    ∀ (S : Type) [Group S] [Finite S] (j : ℕ),
      CardLe (HZ S (j + 1)) (Nat.card S ^ (Nat.card S ^ (j + 1))) := by
  intro S _ _ j
  have hi : Function.Injective (groupHomology.iCycles (Rep.trivial ℤ S ℤ) (j + 1)).hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  have hq : Function.Surjective (groupHomology.π (Rep.trivial ℤ S ℤ) (j + 1)).hom :=
    fun x => groupHomology_induction_on x fun y => ⟨y, rfl⟩
  have h := subquot (Fin (j + 1) → S) (groupHomology.cycles (Rep.trivial ℤ S ℤ) (j + 1))
    (HZ S (j + 1)) (groupHomology.iCycles (Rep.trivial ℤ S ℤ) (j + 1)).hom.toAddMonoidHom
    (groupHomology.π (Rep.trivial ℤ S ℤ) (j + 1)).hom.toAddMonoidHom (Nat.card S)
    Nat.card_pos hi hq (kill S j)
  rwa [Nat.card_fun, Nat.card_fin] at h
