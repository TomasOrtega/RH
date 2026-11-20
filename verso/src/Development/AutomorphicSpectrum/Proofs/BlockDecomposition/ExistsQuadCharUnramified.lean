import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntInd
import GroundTheory.LocalFields.QuadraticAbelian.WeilRepQuadratic

open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 GlobalTheory.CompanionTheory.SphTheta
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.SphTheta.UnramQuad

/- English proof (translation)
Introduce `F _ _ _ _ _ _ _ E _ _ _ _ _ _ _ _ hfin _ hord`. Use `haveI : Fact (Module.finrank F E = 2) := ⟨hfin⟩`. Use `haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)`. Use `haveI : Algebra.IsSeparable F E := inferInstance`. Establish `hf : (GroundTheory.LocalField.residueDegree F E : ℤ) = 2`.

Establish `h` using `GroundTheory.LocalField.ord_norm (K := F) (L := E) (algebraMap F E (unifUnit F : F))`. Rewrite `h` using `[hord, GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.norm_algebraMap_eq_sq, GroundTheory.LocalField.ord_pow (Units.ne_zero _), GroundTheory.LocalField.ord_unifUnit]`. Simplify using `using h.symm`. Establish `heven : ∀ a ∈ (normUnits F E).range, Even (GroundTheory.LocalField.ord (a : F))`. Introduce and unpack `_ ⟨x, rfl⟩`.

Rewrite using `[coe_normUnits, GroundTheory.LocalField.ord_norm (K := F) (L := E), hf]`. Conclude with `even_two_mul _`. Establish `hind` using `GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.index_range_normUnits_eq_two F E`. Establish `hπ : unifUnit F ∉ (normUnits F E).range` using `fun h => by`. Use `heven _ h` as an intermediate fact.

Rewrite `this` using `[GroundTheory.LocalField.ord_unifUnit]`. Conclude with `absurd this (by decide)`. Establish `hmem : ∀ a : Fˣ, a ∈ (normUnits F E).range ↔ Even (GroundTheory.LocalField.ord (a : F))`. Use `fun a => ⟨heven a, fun ha => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hn`.

Establish `h1 : a * unifUnit F ∈ (normUnits F E).range` using `(Subgroup.mul_mem_iff_of_index_two hind).2 (iff_of_false hn hπ)`. Establish `h2` using `heven _ h1`. Rewrite `h2` using `[Units.val_mul, GroundTheory.LocalField.ord_mul (Units.ne_zero _) (Units.ne_zero _), GroundTheory.LocalField.ord_unifUnit]`. Conclude with `(Int.even_add_one.1 h2) ha`. Establish `hex : ∀ a : Fˣ, (∃ t : Eˣ, Algebra.norm F (t : E) = (a : F)) ↔ a ∈ (normUnits F E).range`.

Use `fun a => ⟨fun ⟨t, ht⟩ => ⟨t, Units.ext ((coe_normUnits t).trans ht)⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨t, rfl⟩`. Conclude with `⟨t, (coe_normUnits t).symm⟩`. Establish `hnsg : ∀ a : Fˣ, a ∈ (normUnits F E).range → Ad3.K.GL2LocalData.nsg E (a : F) = 1`. Introduce `a ha`.

Unfold `Ad3.K.GL2LocalData.nsg`. Rewrite using `[if_pos ((hex a).2 ha)]`. Establish `hnsg' : ∀ a : Fˣ, a ∉ (normUnits F E).range → Ad3.K.GL2LocalData.nsg E (a : F) = -1`. Introduce `a ha`. Unfold `Ad3.K.GL2LocalData.nsg`.

Rewrite using `[if_neg (fun h => ha ((hex a).1 h))]`. Use `⟨GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.quadChar F E, fun a => ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Distinguish the cases in `ha : a ∈ (normUnits F E).range`. Rewrite using `[GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.quadChar_apply_of_mem ha, hnsg a ha, Units.val_one]`. Rewrite using `[GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.quadChar_apply_of_notMem ha, hnsg' a ha]`.

Simplify using the standard rewrite rules. Use `isUnramifiedChar_iff.2 fun u hu => ?_` and prove the remaining obligations. Conclude with `GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.quadChar_apply_of_mem ((hmem u).2 (by rw [hu]; exact Even.zero))`. Use extensionality with `t`. Rewrite using `[MonoidHom.mul_apply, ← sq, GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.quadChar_sq]`.

Simplify using the standard rewrite rules. Establish `h0 : GroundTheory.LocalField.ord (-1 : F) = 0`. Establish `h` using `GroundTheory.LocalField.ord_mul (K := F) (x := -1) (y := -1) (by simp) (by simp)`. Rewrite `h` using `[neg_mul_neg, one_mul, GroundTheory.LocalField.ord_one]`. Use linear arithmetic over natural numbers and integers.

Use `hnsg (-1) ((hmem (-1)).2 (by rw [Units.val_neg, Units.val_one, h0]; exact Even.zero))` as an intermediate fact. Simplify using `using this`.
-/
theorem exists_quadChar_unramified : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] [CharZero F] (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E], Module.finrank F E = 2 → Continuous (algebraMap F E) → GroundTheory.LocalField.ord (algebraMap F E (unifUnit F : F)) = 1 → ∃ η : Fˣ →* ℂˣ, (∀ a, ((η a : ℂˣ) : ℂ) = Ad3.K.GL2LocalData.nsg E (a : F)) ∧ IsUnramifiedChar η ∧ η * η = 1 ∧ Ad3.K.GL2LocalData.nsg E (-1 : F) = 1 := by
  intro F _ _ _ _ _ _ _ E _ _ _ _ _ _ _ _ hfin _ hord
  haveI : Fact (Module.finrank F E = 2) := ⟨hfin⟩
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  haveI : Algebra.IsSeparable F E := inferInstance
  have hf : (GroundTheory.LocalField.residueDegree F E : ℤ) = 2 := by
    have h := GroundTheory.LocalField.ord_norm (K := F) (L := E) (algebraMap F E (unifUnit F : F))
    rw [hord, GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.norm_algebraMap_eq_sq,
      GroundTheory.LocalField.ord_pow (Units.ne_zero _), GroundTheory.LocalField.ord_unifUnit] at h
    simpa using h.symm
  have heven : ∀ a ∈ (normUnits F E).range, Even (GroundTheory.LocalField.ord (a : F)) := by
    rintro _ ⟨x, rfl⟩
    rw [coe_normUnits, GroundTheory.LocalField.ord_norm (K := F) (L := E), hf]
    exact even_two_mul _
  have hind := GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.index_range_normUnits_eq_two F E
  have hπ : unifUnit F ∉ (normUnits F E).range := fun h => by
    have := heven _ h
    rw [GroundTheory.LocalField.ord_unifUnit] at this
    exact absurd this (by decide)
  have hmem : ∀ a : Fˣ, a ∈ (normUnits F E).range ↔ Even (GroundTheory.LocalField.ord (a : F)) := by
    refine fun a => ⟨heven a, fun ha => ?_⟩
    by_contra hn
    have h1 : a * unifUnit F ∈ (normUnits F E).range :=
      (Subgroup.mul_mem_iff_of_index_two hind).2 (iff_of_false hn hπ)
    have h2 := heven _ h1
    rw [Units.val_mul, GroundTheory.LocalField.ord_mul (Units.ne_zero _) (Units.ne_zero _),
      GroundTheory.LocalField.ord_unifUnit] at h2
    exact (Int.even_add_one.1 h2) ha
  have hex : ∀ a : Fˣ, (∃ t : Eˣ, Algebra.norm F (t : E) = (a : F)) ↔
      a ∈ (normUnits F E).range := by
    refine fun a => ⟨fun ⟨t, ht⟩ => ⟨t, Units.ext ((coe_normUnits t).trans ht)⟩, ?_⟩
    rintro ⟨t, rfl⟩
    exact ⟨t, (coe_normUnits t).symm⟩
  have hnsg : ∀ a : Fˣ, a ∈ (normUnits F E).range → Ad3.K.GL2LocalData.nsg E (a : F) = 1 := by
    intro a ha
    unfold Ad3.K.GL2LocalData.nsg
    rw [if_pos ((hex a).2 ha)]
  have hnsg' : ∀ a : Fˣ, a ∉ (normUnits F E).range → Ad3.K.GL2LocalData.nsg E (a : F) = -1 := by
    intro a ha
    unfold Ad3.K.GL2LocalData.nsg
    rw [if_neg (fun h => ha ((hex a).1 h))]
  refine ⟨GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.quadChar F E, fun a => ?_, ?_, ?_, ?_⟩
  · by_cases ha : a ∈ (normUnits F E).range
    · rw [GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.quadChar_apply_of_mem ha, hnsg a ha, Units.val_one]
    · rw [GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.quadChar_apply_of_notMem ha, hnsg' a ha]
      simp
  · refine isUnramifiedChar_iff.2 fun u hu => ?_
    exact GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.quadChar_apply_of_mem ((hmem u).2 (by rw [hu]; exact Even.zero))
  · ext t
    rw [MonoidHom.mul_apply, ← sq, GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.quadChar_sq]
    simp
  · have h0 : GroundTheory.LocalField.ord (-1 : F) = 0 := by
      have h := GroundTheory.LocalField.ord_mul (K := F) (x := -1) (y := -1) (by simp) (by simp)
      rw [neg_mul_neg, one_mul, GroundTheory.LocalField.ord_one] at h
      omega
    have := hnsg (-1) ((hmem (-1)).2 (by rw [Units.val_neg, Units.val_one, h0]; exact Even.zero))
    simpa using this

end GlobalTheory.CompanionTheory.SphTheta.UnramQuad
