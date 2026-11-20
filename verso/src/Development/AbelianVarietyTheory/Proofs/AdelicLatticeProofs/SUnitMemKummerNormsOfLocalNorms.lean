import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemPowsSUnitsChooseTStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FirstInequalitySUnitsPrimeDegreeStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PowOfSUnitLocalPowerAtPlacesStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitsMappingToPowersLeUnitsLocalKummerNormsStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsAdmissiblePlacesContainingPrimeSupersetMon
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PowsSubgroupOfSelfSPow
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SUnitsUnionSupPowersEqTopAtPlacesStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PowCountPlacesNotLocalPowerLeIndexStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitsLocalPowersAtPlacesIndexLeStatement

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

/- English proof (translation)
Rewrite using `[← Subgroup.relIndex_mul_index (le_sup_right : W ≤ U ⊔ W), Subgroup.relIndex_sup_right]`.
-/
theorem index_eq_relIndex_mul_index_sup_normThm {G : Type} [CommGroup G] (U W : Subgroup G) :
    W.index = W.relIndex U * (U ⊔ W).index := by
  rw [← Subgroup.relIndex_mul_index (le_sup_right : W ≤ U ⊔ W), Subgroup.relIndex_sup_right]

/- English proof (translation)
Establish `e1` using `index_eq_relIndex_mul_index_sup_normThm U W`. Establish `e2` using `index_eq_relIndex_mul_index_sup_normThm U D`. Establish `h4 : p ^ (2 * s) = p ^ k * p`. Rewrite using `[← pow_succ, hk]`. Establish `hUW0 : (U ⊔ W).index ≠ 0`.

Introduce `h`. Rewrite `e1` using `[h, mul_zero]`. Conclude with `hW0 e1`. Establish `hUW : (U ⊔ W).index ≤ p`. Rewrite `hW` using `[e1, hWU, h4]`.

Conclude with `Nat.le_of_mul_le_mul_left hW (by positivity)`. Establish `hUD : (U ⊔ D).index ≤ p` using `le_trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hUW0) (Subgroup.index_dvd_of_le (sup_le_sup_left hWD U))) hUW`. Establish `h3 : N.relIndex U ≤ D.relIndex U`. Establish `: p * N.relIndex U ≤ p * D.relIndex U`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[← e2]`. Conclude with `hN.trans hD`. Use `_ ≤ D.relIndex U * p := Nat.mul_le_mul_left _ hUD`. Use `_ = p * D.relIndex U := mul_comm _ _`. Conclude with `Nat.le_of_mul_le_mul_left this hp`.

Establish `e3 : N.relIndex (D ⊓ U) * D.relIndex U = N.relIndex U`. Use `Subgroup.relIndex_inf_mul_relIndex N D U` as an intermediate fact. Rewrite `this` using `[inf_eq_left.mpr hND]`. Then use the resulting hypothesis. Establish `hD0 : D.relIndex U ≠ 0`. Introduce `h`.

Rewrite `e3` using `[h, mul_zero]`. Conclude with `hN0 e3.symm`. Establish `hm0 : N.relIndex (D ⊓ U) ≠ 0`. Introduce `h`. Rewrite `e3` using `[h, zero_mul]`.

Conclude with `hN0 e3.symm`. Establish `hm : N.relIndex (D ⊓ U) ≤ 1`. Rewrite `h3` using `[← e3]`. Establish `: N.relIndex (D ⊓ U) * D.relIndex U ≤ 1 * D.relIndex U` using `by rwa [one_mul]`. Conclude with `Nat.le_of_mul_le_mul_right this (Nat.pos_of_ne_zero hD0)`.

Conclude with `Subgroup.relIndex_eq_one.mp (by omega)`.
-/
theorem inf_le_of_index_count_normThm {G : Type} [CommGroup G] (p : ℕ) (hp : 0 < p)
    (U W D N : Subgroup G) (s k t : ℕ)
    (hWD : W ≤ D) (hND : N ≤ D) (hk : k + 1 = 2 * s) (hW0 : W.index ≠ 0)
    (hW : W.index ≤ p ^ (2 * s)) (hWU : W.relIndex U = p ^ k) (hD : p ^ t ≤ D.index)
    (hN0 : N.relIndex U ≠ 0) (hN : p * N.relIndex U ≤ p ^ t) : D ⊓ U ≤ N := by
  have e1 := index_eq_relIndex_mul_index_sup_normThm U W
  have e2 := index_eq_relIndex_mul_index_sup_normThm U D
  have h4 : p ^ (2 * s) = p ^ k * p := by
    rw [← pow_succ, hk]
  have hUW0 : (U ⊔ W).index ≠ 0 := by
    intro h; rw [h, mul_zero] at e1; exact hW0 e1
  have hUW : (U ⊔ W).index ≤ p := by
    rw [e1, hWU, h4] at hW
    exact Nat.le_of_mul_le_mul_left hW (by positivity)
  have hUD : (U ⊔ D).index ≤ p :=
    le_trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hUW0)
      (Subgroup.index_dvd_of_le (sup_le_sup_left hWD U))) hUW
  have h3 : N.relIndex U ≤ D.relIndex U := by
    have : p * N.relIndex U ≤ p * D.relIndex U := by
      calc p * N.relIndex U ≤ D.relIndex U * (U ⊔ D).index := by
            rw [← e2]; exact hN.trans hD
        _ ≤ D.relIndex U * p := Nat.mul_le_mul_left _ hUD
        _ = p * D.relIndex U := mul_comm _ _
    exact Nat.le_of_mul_le_mul_left this hp
  have e3 : N.relIndex (D ⊓ U) * D.relIndex U = N.relIndex U := by
    have := Subgroup.relIndex_inf_mul_relIndex N D U
    rwa [inf_eq_left.mpr hND] at this
  have hD0 : D.relIndex U ≠ 0 := by
    intro h; rw [h, mul_zero] at e3; exact hN0 e3.symm
  have hm0 : N.relIndex (D ⊓ U) ≠ 0 := by
    intro h; rw [h, zero_mul] at e3; exact hN0 e3.symm
  have hm : N.relIndex (D ⊓ U) ≤ 1 := by
    rw [← e3] at h3
    have : N.relIndex (D ⊓ U) * D.relIndex U ≤ 1 * D.relIndex U := by rwa [one_mul]
    exact Nat.le_of_mul_le_mul_right this (Nat.pos_of_ne_zero hD0)
  exact Subgroup.relIndex_eq_one.mp (by omega)

/- English proof (translation)
Introduce and unpack `_ ⟨y, -, rfl⟩`. Establish `h : ∀ {L : Type} [Field L] (φ : F →+* L), powMonoidHom p y ∈ powSub p φ`. Introduce `L _ φ`. Conclude with `⟨φ y, by simp⟩`. Conclude with `Subgroup.mem_iInf.mpr fun _ => Subgroup.mem_iInf.mpr fun _ => h _`.
-/
theorem pows_le_finPow_normThm (p : ℕ) (F : Type) [Field F] [NumberField F] (U : Subgroup Fˣ)
    (S : Finset (HeightOneSpectrum (𝓞 F))) : pows p U ≤ finPow p F S := by
  rintro _ ⟨y, -, rfl⟩
  have h : ∀ {L : Type} [Field L] (φ : F →+* L), powMonoidHom p y ∈ powSub p φ := by
    intro L _ φ
    exact ⟨φ y, by simp⟩
  exact Subgroup.mem_iInf.mpr fun _ => Subgroup.mem_iInf.mpr fun _ => h _

/- English proof (translation)
Take `⟨r, hr⟩` from `h`. Establish `hr0 : r ≠ 0`. Introduce and unpack `rfl`. Conclude with `y.ne_zero (by rw [← hr, zero_pow hp.ne'])`. Use `⟨Units.mk0 r hr0, ?_, ?_⟩` and prove the remaining obligations.

Introduce `v hv`. Establish `h1` using `hy v hv`. Establish `h2 : v.valuation F r ^ p = 1`. Rewrite using `[← map_pow, hr]`. Conclude with `h1`.

Conclude with `(pow_eq_one_iff_of_nonneg zero_le' hp.ne').mp h2`. Use `ext`. Simplify using `[hr]`.
-/
theorem mem_pows_sUnits_normThm (p : ℕ) (hp : 0 < p) (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (y : Fˣ) (hy : y ∈ sUnits F S)
    (h : ∃ r : F, r ^ p = (y : F)) : y ∈ pows p (sUnits F S) := by
  obtain ⟨r, hr⟩ := h
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact y.ne_zero (by rw [← hr, zero_pow hp.ne'])
  refine ⟨Units.mk0 r hr0, ?_, ?_⟩
  · intro v hv
    have h1 := hy v hv
    have h2 : v.valuation F r ^ p = 1 := by
      rw [← map_pow, hr]; exact h1
    exact (pow_eq_one_iff_of_nonneg zero_le' hp.ne').mp h2
  · ext
    simp [hr]

/- English proof (translation)
Introduce `p F _ _ _ ζ δ S hp hζ hS hδ hns x hx hxl`. Establish `hp0` using `hp.pos`. Take `⟨T, hST, hcard, hsq, hA⟩` from `GlobalTheory.T.exists_places_with_pth_roots_and_separating_units p F ζ δ S hp hζ hS hδ hns`. Establish `hsurj` using `GlobalTheory.T.sUnits_union_sup_powers_eq_top_at_places p F S T hp hS hST hA`. Establish `hinj` using `GlobalTheory.T.pow_of_sUnit_localPower_at_places p F ζ S T hp hζ hS hsurj`.

Establish `hmono : sUnits F S ≤ sUnits F (S ∪ T)` using `fun y hy v hv => hy v (fun h => hv (by simp only [Finset.coe_union, Set.mem_union]; exact Or.inl h))`. Establish `hS' : AdmP p F (S ∪ T)` using `(exists_admissiblePlaces_superset_and_mono p F hp0).2 S (S ∪ T) Finset.subset_union_left hS`. Take `⟨hN0, hN⟩` from `GlobalTheory.T.first_inequality_sUnits_prime_degree p F ζ δ (S ∪ T) hp hζ hS' (hmono hδ) hns`. Establish `ht : tNon p F δ (S ∪ T) = tNon p F δ S`. Unfold `tNon`.

Use `congr 1`. Use extensionality with `v`. Simplify using `only [Finset.mem_union, Set.mem_setOf_eq]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h | h, h'⟩`.

Conclude with `⟨h, h'⟩`. Take `⟨r, hr⟩` from `hsq v h`. Conclude with `absurd hr (h' r)`. Introduce and unpack `⟨h, h'⟩`. Conclude with `⟨Or.inl h, h'⟩`.

Rewrite `hN` using `[ht]`. Take `⟨-, hD⟩` from `GlobalTheory.T.pow_countPlacesNotLocalPower_le_index p F ζ δ S hp hζ`. Take `⟨hW0, hW⟩` from `GlobalTheory.T.unitsLocalPowersAtPlaces_index_le p F S hp0`. Establish `hU` using `(pTor_pIdx_sUnits p F ζ (S ∪ T) hp hζ).2`. Unfold `pIdx at hU`.

Establish `hinf : finPow p F S ⊓ sUnits F (S ∪ T) = pows p (sUnits F (S ∪ T)) ⊓ sUnits F (S ∪ T)`. Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `y ⟨h1, h2⟩`. Conclude with `⟨mem_pows_sUnits_normThm p hp0 F _ y h2 (hinj y h2 h1), h2⟩`. Conclude with `inf_le_inf_right _ (pows_le_finPow_normThm p F _ S)`.

Establish `hWU : (finPow p F S).relIndex (sUnits F (S ∪ T)) = p ^ ((S ∪ T).card + Fintype.card (InfinitePlace F))`. Rewrite using `[← Subgroup.inf_relIndex_right, hinf, Subgroup.inf_relIndex_right, hU]`. Take `⟨k1, k2⟩` from `GlobalTheory.T.unitsMappingToPowers_le_unitsLocalKummerNorms p hp0`. Establish `hWD : finPow p F S ≤ finNorm p F δ S` using `iInf₂_mono fun _ _ => k1 _ _ _ _`. Establish `hND : kNorm p (RingHom.id F) (δ : F) ≤ finNorm p F δ S` using `le_iInf₂ fun _ _ => k2 _ _ _ _`.

Use `inf_le_of_index_count_normThm p hp0 (sUnits F (S ∪ T)) (finPow p F S) (finNorm p F δ S) _ _ _ _ hWD hND ?_ hW0 hW hWU hD hN0 hN ⟨hxl, hmono hx⟩` and prove the remaining obligations. Rewrite using `[Finset.card_union_of_disjoint hST]`. Use linear arithmetic over natural numbers and integers.
-/
theorem sUnit_mem_kNorm_of_mem_finNorm : ∀ (p : ℕ) (F : Type) [Field F] [NumberField F] [IsTotallyComplex F] (ζ : F) (δ : Fˣ) (S : Finset (HeightOneSpectrum (𝓞 F))), p.Prime → IsPrimitiveRoot ζ p → AdmP p F S → δ ∈ sUnits F S → (∀ r : F, r ^ p ≠ (δ : F)) → ∀ x ∈ sUnits F S, x ∈ finNorm p F δ S → x ∈ kNorm p (RingHom.id F) (δ : F) := by
  intro p F _ _ _ ζ δ S hp hζ hS hδ hns x hx hxl
  classical
  have hp0 := hp.pos
  obtain ⟨T, hST, hcard, hsq, hA⟩ := GlobalTheory.T.exists_places_with_pth_roots_and_separating_units p F ζ δ S hp hζ hS hδ hns
  have hsurj := GlobalTheory.T.sUnits_union_sup_powers_eq_top_at_places p F S T hp hS hST hA
  have hinj := GlobalTheory.T.pow_of_sUnit_localPower_at_places p F ζ S T hp hζ hS hsurj
  have hmono : sUnits F S ≤ sUnits F (S ∪ T) := fun y hy v hv =>
    hy v (fun h => hv (by simp only [Finset.coe_union, Set.mem_union]; exact Or.inl h))
  have hS' : AdmP p F (S ∪ T) :=
    (exists_admissiblePlaces_superset_and_mono p F hp0).2 S (S ∪ T) Finset.subset_union_left hS
  obtain ⟨hN0, hN⟩ := GlobalTheory.T.first_inequality_sUnits_prime_degree p F ζ δ (S ∪ T) hp hζ hS' (hmono hδ) hns
  have ht : tNon p F δ (S ∪ T) = tNon p F δ S := by
    unfold tNon
    congr 1
    ext v
    simp only [Finset.mem_union, Set.mem_setOf_eq]
    constructor
    · rintro ⟨h | h, h'⟩
      · exact ⟨h, h'⟩
      · obtain ⟨r, hr⟩ := hsq v h
        exact absurd hr (h' r)
    · rintro ⟨h, h'⟩
      exact ⟨Or.inl h, h'⟩
  rw [ht] at hN
  obtain ⟨-, hD⟩ := GlobalTheory.T.pow_countPlacesNotLocalPower_le_index p F ζ δ S hp hζ
  obtain ⟨hW0, hW⟩ := GlobalTheory.T.unitsLocalPowersAtPlaces_index_le p F S hp0
  have hU := (pTor_pIdx_sUnits p F ζ (S ∪ T) hp hζ).2
  unfold pIdx at hU
  have hinf : finPow p F S ⊓ sUnits F (S ∪ T) = pows p (sUnits F (S ∪ T)) ⊓ sUnits F (S ∪ T) := by
    apply le_antisymm
    · rintro y ⟨h1, h2⟩
      exact ⟨mem_pows_sUnits_normThm p hp0 F _ y h2 (hinj y h2 h1), h2⟩
    · exact inf_le_inf_right _ (pows_le_finPow_normThm p F _ S)
  have hWU : (finPow p F S).relIndex (sUnits F (S ∪ T)) =
      p ^ ((S ∪ T).card + Fintype.card (InfinitePlace F)) := by
    rw [← Subgroup.inf_relIndex_right, hinf, Subgroup.inf_relIndex_right, hU]
  obtain ⟨k1, k2⟩ := GlobalTheory.T.unitsMappingToPowers_le_unitsLocalKummerNorms p hp0
  have hWD : finPow p F S ≤ finNorm p F δ S := iInf₂_mono fun _ _ => k1 _ _ _ _
  have hND : kNorm p (RingHom.id F) (δ : F) ≤ finNorm p F δ S :=
    le_iInf₂ fun _ _ => k2 _ _ _ _
  refine inf_le_of_index_count_normThm p hp0 (sUnits F (S ∪ T)) (finPow p F S) (finNorm p F δ S)
    _ _ _ _ hWD hND ?_ hW0 hW hWU hD hN0 hN ⟨hxl, hmono hx⟩
  rw [Finset.card_union_of_disjoint hST]
  omega

end GlobalTheory.CNorm
