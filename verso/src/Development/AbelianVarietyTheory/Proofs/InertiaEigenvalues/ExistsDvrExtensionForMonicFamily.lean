import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstruction
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIdempotentSubMemOfPowSubMem
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

namespace GlobalTheory

open Polynomial

/- English proof (translation)
Use `IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun b => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hcon`. Rewrite `hcon` using `[not_or]`. Take `⟨h0, h1⟩` from `hcon`. Take `⟨E, hE, hM⟩` from `GlobalTheory.exists_idempotent_sub_mem_of_pow_sub_mem l b`.

Establish `e0 : E - 0 ∈ (Ideal.span {b}).restrictScalars ℤ_[l]` using `hM _ 0 fun n => by`. Simplify using `only [sub_zero, Submodule.restrictScalars_mem, Ideal.mem_span_singleton]`. Conclude with `dvd_pow_self b (Nat.succ_ne_zero n)`. Establish `e1 : E - 1 ∈ (Ideal.span {1 - b}).restrictScalars ℤ_[l]` using `hM _ 1 fun n => by`. Simplify using `only [Submodule.restrictScalars_mem, Ideal.mem_span_singleton]`.

Use `one_sub_dvd_one_sub_pow b (n + 1)` as an intermediate fact. Rewrite using `[← neg_sub 1 (b ^ (n + 1))]`. Conclude with `this.neg_right`. Simplify using `only [sub_zero, Submodule.restrictScalars_mem, Ideal.mem_span_singleton] at e0 e1`. Break down `(IsIdempotentElem.iff_eq_zero_or_one (p := E)).1 hE with h | h` into its components or cases.

Rewrite `e1` using `[h, zero_sub]`. Conclude with `h1 (isUnit_of_dvd_one (dvd_neg.1 e1))`. Rewrite `e0` using `[h]`. Conclude with `h0 (isUnit_of_dvd_one e0)`.
-/
theorem isLocalRing_of_domain_finite_padicInt (l : ℕ) [Fact l.Prime] (B : Type) [CommRing B]
    [IsDomain B] [Algebra ℤ_[l] B] [Module.Finite ℤ_[l] B] : IsLocalRing B := by
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun b => ?_
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨h0, h1⟩ := hcon
  obtain ⟨E, hE, hM⟩ := GlobalTheory.exists_idempotent_sub_mem_of_pow_sub_mem l b
  have e0 : E - 0 ∈ (Ideal.span {b}).restrictScalars ℤ_[l] := hM _ 0 fun n => by
    simp only [sub_zero, Submodule.restrictScalars_mem, Ideal.mem_span_singleton]
    exact dvd_pow_self b (Nat.succ_ne_zero n)
  have e1 : E - 1 ∈ (Ideal.span {1 - b}).restrictScalars ℤ_[l] := hM _ 1 fun n => by
    simp only [Submodule.restrictScalars_mem, Ideal.mem_span_singleton]
    have := one_sub_dvd_one_sub_pow b (n + 1)
    rw [← neg_sub 1 (b ^ (n + 1))]
    exact this.neg_right
  simp only [sub_zero, Submodule.restrictScalars_mem, Ideal.mem_span_singleton] at e0 e1
  rcases (IsIdempotentElem.iff_eq_zero_or_one (p := E)).1 hE with h | h
  · rw [h, zero_sub] at e1
    exact h1 (isUnit_of_dvd_one (dvd_neg.1 e1))
  · rw [h] at e0
    exact h0 (isUnit_of_dvd_one e0)

/- English proof (translation)
Establish `hc : f.roots.toList.length = t`. Rewrite using `[Multiset.length_toList, ← hs.natDegree_eq_card_roots, ht]`. Substitute `hc` using the available equality. Use `⟨f.roots.toList.get, ?_⟩` and prove the remaining obligations. Use `conv_lhs => rw [hs.eq_prod_roots_of_monic hm, ← Multiset.coe_toList f.roots]`.

Rewrite using `[Multiset.map_coe, Multiset.prod_coe, ← List.prod_ofFn]`. Use `congr 1`. Use `conv_lhs => rw [← List.ofFn_get f.roots.toList]`. Rewrite using `[List.map_ofFn]`. Both sides reduce to the same expression.
-/
theorem exists_fin_prod_of_splits {L : Type} [Field L] (t : ℕ) (f : L[X]) (hs : f.Splits)
    (hm : f.Monic) (ht : f.natDegree = t) : ∃ α : Fin t → L, f = ∏ c, (X - C (α c)) := by
  have hc : f.roots.toList.length = t := by
    rw [Multiset.length_toList, ← hs.natDegree_eq_card_roots, ht]
  subst hc
  refine ⟨f.roots.toList.get, ?_⟩
  conv_lhs => rw [hs.eq_prod_roots_of_monic hm, ← Multiset.coe_toList f.roots]
  rw [Multiset.map_coe, Multiset.prod_coe, ← List.prod_ofFn]
  congr 1
  conv_lhs => rw [← List.ofFn_get f.roots.toList]
  rw [List.map_ofFn]
  rfl

/- English proof (translation)
Introduce `l _ A ι _ _ _ _ _ _ _ t P hP`. Use `haveI := Fintype.ofFinite ι`. Set `K` to `FractionRing A`. Use `haveI : CharZero K := IsFractionRing.charZero_of_isFractionRing A`. Set `F : K[X]` to `∏ i, (P i).map (toFr A)`.

Establish `hF : F.Monic` using `monic_prod_of_monic _ _ fun i _ => (hP i).1`. Set `L` to `F.SplittingField`. Use `haveI : IsScalarTower A K L := inferInstance`. Set `S` to `integralClosure A L`. Use `haveI : Module.Finite A S := IsIntegralClosure.finite A K L S`.

Use `haveI : IsDedekindDomain S := IsIntegralClosure.isDedekindDomain A K L S`. Use `haveI : IsFractionRing S L := IsIntegralClosure.isFractionRing_of_finite_extension A K L S`. Use `haveI : IsLocalRing S := by`. Use `letI : Algebra ℤ_[l] S := ((algebraMap A S).comp (algebraMap ℤ_[l] A)).toAlgebra`. Use `haveI : IsScalarTower ℤ_[l] A S := .of_algebraMap_eq fun _ => rfl`.

Use `haveI : Module.Finite ℤ_[l] S := Module.Finite.trans A S`. Conclude with `isLocalRing_of_domain_finite_padicInt l S`. Establish `hinj : Function.Injective (algebraMap A S)` using `algebraMap_injective_of_field_isFractionRing A S K L`. Establish `hnf : ¬ IsField S` using `fun h => IsDiscreteValuationRing.not_isField A (isField_of_isIntegral_of_isField hinj h)`. Use `haveI : IsDiscreteValuationRing S := ((IsDiscreteValuationRing.TFAE S hnf).out 2 0).1 (inferInstance : IsDedekindDomain S)`.

Use `⟨S, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, hinj, fun i => ?_⟩` and prove the remaining obligations. Set `e : L ≃ₐ[S] FractionRing S` to `(FractionRing.algEquiv S L).symm`. Establish `hsF : (F.map (algebraMap K L)).Splits` using `SplittingField.splits F`. Establish `hsi : (((P i).map (toFr A)).map (algebraMap K L)).Splits` using `hsF.of_dvd (hF.map _).ne_zero (Polynomial.map_dvd _ (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)))`. Establish `hcomp : (toFr S).comp (algebraMap A S) = ((e : L →+* FractionRing S).comp (algebraMap K L)).comp (toFr A)`.

Use extensionality with `a`. Establish `: algebraMap K L (toFr A a) = algebraMap S L (algebraMap A S a)`. Rewrite using `[← IsScalarTower.algebraMap_apply A S L]`. Conclude with `(IsScalarTower.algebraMap_apply A K L a).symm`. Simplify using `only [RingHom.comp_apply, this]`.

Conclude with `(e.commutes _).symm`. Rewrite using `[hcomp, ← Polynomial.map_map, ← Polynomial.map_map]`. Use `exists_fin_prod_of_splits t _ (hsi.map _) (((hP i).1.map _).map _) ?_` and prove the remaining obligations. Rewrite using `[natDegree_map, natDegree_map, (hP i).2]`.
-/
theorem exists_finite_dvr_splitting : ∀ (l : ℕ) [Fact l.Prime] {A ι : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CharZero A] [Algebra ℤ_[l] A] [Module.Finite ℤ_[l] A] [Finite ι] (t : ℕ) (P : ι → Polynomial A), (∀ i, ((P i).map (toFr A)).Monic ∧ ((P i).map (toFr A)).natDegree = t) → ∃ (B : Type) (_ : CommRing B) (_ : IsDomain B) (_ : IsDiscreteValuationRing B) (_ : Algebra A B), Module.Finite A B ∧ Function.Injective (algebraMap A B) ∧ ∀ i, ∃ α : Fin t → FractionRing B, (P i).map ((toFr B).comp (algebraMap A B)) = ∏ c, (Polynomial.X - Polynomial.C (α c)) := by
  intro l _ A ι _ _ _ _ _ _ _ t P hP
  classical
  haveI := Fintype.ofFinite ι
  let K := FractionRing A
  haveI : CharZero K := IsFractionRing.charZero_of_isFractionRing A
  let F : K[X] := ∏ i, (P i).map (toFr A)
  have hF : F.Monic := monic_prod_of_monic _ _ fun i _ => (hP i).1
  let L := F.SplittingField
  haveI : IsScalarTower A K L := inferInstance
  let S := integralClosure A L
  haveI : Module.Finite A S := IsIntegralClosure.finite A K L S
  haveI : IsDedekindDomain S := IsIntegralClosure.isDedekindDomain A K L S
  haveI : IsFractionRing S L := IsIntegralClosure.isFractionRing_of_finite_extension A K L S
  haveI : IsLocalRing S := by
    letI : Algebra ℤ_[l] S := ((algebraMap A S).comp (algebraMap ℤ_[l] A)).toAlgebra
    haveI : IsScalarTower ℤ_[l] A S := .of_algebraMap_eq fun _ => rfl
    haveI : Module.Finite ℤ_[l] S := Module.Finite.trans A S
    exact isLocalRing_of_domain_finite_padicInt l S
  have hinj : Function.Injective (algebraMap A S) :=
    algebraMap_injective_of_field_isFractionRing A S K L
  have hnf : ¬ IsField S := fun h =>
    IsDiscreteValuationRing.not_isField A (isField_of_isIntegral_of_isField hinj h)
  haveI : IsDiscreteValuationRing S := ((IsDiscreteValuationRing.TFAE S hnf).out 2 0).1
    (inferInstance : IsDedekindDomain S)
  refine ⟨S, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, hinj,
    fun i => ?_⟩
  let e : L ≃ₐ[S] FractionRing S := (FractionRing.algEquiv S L).symm
  have hsF : (F.map (algebraMap K L)).Splits := SplittingField.splits F
  have hsi : (((P i).map (toFr A)).map (algebraMap K L)).Splits :=
    hsF.of_dvd (hF.map _).ne_zero
      (Polynomial.map_dvd _ (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)))
  have hcomp : (toFr S).comp (algebraMap A S) =
      ((e : L →+* FractionRing S).comp (algebraMap K L)).comp (toFr A) := by
    ext a
    have : algebraMap K L (toFr A a) = algebraMap S L (algebraMap A S a) := by
      rw [← IsScalarTower.algebraMap_apply A S L]
      exact (IsScalarTower.algebraMap_apply A K L a).symm
    simp only [RingHom.comp_apply, this]
    exact (e.commutes _).symm
  rw [hcomp, ← Polynomial.map_map, ← Polynomial.map_map]
  refine exists_fin_prod_of_splits t _ (hsi.map _) (((hP i).1.map _).map _) ?_
  rw [natDegree_map, natDegree_map, (hP i).2]

end GlobalTheory
