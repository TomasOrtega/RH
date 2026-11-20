import Mathlib
import GroundTheory.GlobalFields.Artin.Brauer
import GroundTheory.GlobalFields.Artin.OneDimExistence
import GroundTheory.GlobalFields.TateThesis.FiniteOrderParams
set_option maxSynthPendingDepth 1

noncomputable section

open IsDedekindDomain NumberField IntermediateField Filter Topology Set Complex

namespace GroundTheory.Global

open GroundTheory.LocalField

section Group

variable {G : Type*} [Group G] [Fintype G]

/- English proof (translation)
Establish `hG : (Fintype.card G : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 Fintype.card_ne_zero`. Set `_ : Invertible (Fintype.card G : ℂ)` to `invertibleOfNonzero hG`. Rewrite using `[← (ρ.isProj_averageMap).trace, charInner_apply]`. Simplify using `[Representation.character, GroupAlgebra.average, map_sum, Nat.card_eq_fintype_card]`.
-/
theorem charInner_character_one {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) :
    charInner G ρ.character 1 = Module.finrank ℂ ρ.invariants := by
  have hG : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  let _ : Invertible (Fintype.card G : ℂ) := invertibleOfNonzero hG
  rw [← (ρ.isProj_averageMap).trace, charInner_apply]
  simp [Representation.character, GroupAlgebra.average, map_sum, Nat.card_eq_fintype_card]

/- English proof (translation)
Rewrite using `[charInner_indFun _ _ (fun _ _ ↦ rfl), charInner_apply]`. Simplify using `only [Function.comp_apply, Pi.one_apply, mul_one]`. Use `split_ifs with h`. Substitute `h` using the available equality. Establish `hH : (Nat.card H : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 Nat.card_pos.ne'`.

Simplify using `[Nat.card_eq_fintype_card] at hH ⊢`. Establish `hψ : (Units.coeHom ℂ).comp l ≠ 1`. Introduce `h1`. Apply `h` to reduce the goal to its premises. Use extensionality with `k`.

Conclude with `congrArg Units.val (Units.ext (DFunLike.congr_fun h1 k) : l k = 1) ▸ rfl`. Establish `hs : ∑ k : H, ((l k : ℂˣ) : ℂ) = 0` using `sum_hom_units_eq_zero _ hψ`. Rewrite using `[hs, mul_zero]`.
-/
theorem charInner_indFun_char_one (H : Subgroup G) [Fintype H] (l : H →* ℂˣ) :
    charInner G (indFun H.subtype (fun k ↦ (l k : ℂ))) 1 = if l = 1 then 1 else 0 := by
  rw [charInner_indFun _ _ (fun _ _ ↦ rfl), charInner_apply]
  simp only [Function.comp_apply, Pi.one_apply, mul_one]
  split_ifs with h
  · subst h
    have hH : (Nat.card H : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
    simp [Nat.card_eq_fintype_card] at hH ⊢
  · have hψ : (Units.coeHom ℂ).comp l ≠ 1 := by
      intro h1
      apply h
      ext k
      exact congrArg Units.val (Units.ext (DFunLike.congr_fun h1 k) : l k = 1) ▸ rfl
    have hs : ∑ k : H, ((l k : ℂˣ) : ℂ) = 0 := sum_hom_units_eq_zero _ hψ
    rw [hs, mul_zero]

/- English proof (translation)
Establish `hsum : charInner G (∑ i, n i • indFun (H i).subtype (fun k ↦ (l i k : ℂ))) 1 = ((∑ i, n i * if l i = 1 then 1 else 0 : ℕ) : ℂ)`. Rewrite using `[map_sum, LinearMap.sum_apply]`. Use `push_cast`. Use `Finset.sum_congr rfl fun j _ ↦ ?_` and prove the remaining obligations. Rewrite using `[map_nsmul, LinearMap.smul_apply, charInner_indFun_char_one, nsmul_eq_mul]`.

Rewrite `h` using `[hsum, Nat.cast_eq_zero, Finset.sum_eq_zero_iff]`. Introduce `hl`. Use `h i (Finset.mem_univ i)` as an intermediate fact. Rewrite `this` using `[if_pos hl, mul_one]`. Conclude with `hi this`.
-/
theorem ne_one_of_charInner_sum_indFun_eq_zero {ι : Type*} [Fintype ι] {H : ι → Subgroup G}
    [∀ i, Fintype (H i)] (n : ι → ℕ) (l : ∀ i, H i →* ℂˣ)
    (h : charInner G (∑ i, n i • indFun (H i).subtype (fun k ↦ (l i k : ℂ))) 1 = 0) (i : ι)
    (hi : n i ≠ 0) : l i ≠ 1 := by
  classical
  have hsum : charInner G (∑ i, n i • indFun (H i).subtype (fun k ↦ (l i k : ℂ))) 1 =
      ((∑ i, n i * if l i = 1 then 1 else 0 : ℕ) : ℂ) := by
    rw [map_sum, LinearMap.sum_apply]
    push_cast
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [map_nsmul, LinearMap.smul_apply, charInner_indFun_char_one, nsmul_eq_mul]
  rw [hsum, Nat.cast_eq_zero, Finset.sum_eq_zero_iff] at h
  intro hl
  have := h i (Finset.mem_univ i)
  rw [if_pos hl, mul_one] at this
  exact hi this

end Group

namespace HeckeCharacter

variable {K : Type*} [Field K] [NumberField K]

open IdeleGroup

/- English proof (translation)
Introduce and unpack `⟨τ, hτ⟩`. Apply `hne` to reduce the goal to its premises. Take `⟨n, hn, hpow⟩` from `ψ.exists_toIdele_pow_eq_one hψ`. Set `w : InfinitePlace K` to `Classical.arbitrary _`. Establish `hs : ∀ t : {x : ℝ // 0 < x}, ψ.toIdele (moduleSection w t) = 1`.

Introduce `t`. Establish `ht : (⟨(t : ℝ) ^ (n⁻¹ : ℝ), Real.rpow_pos_of_pos t.2 _⟩ : {x : ℝ // 0 < x}) ^ n = t` using `Subtype.ext (by simp [Real.rpow_inv_natCast_pow t.2.le hn.ne'])`. Rewrite using `[← ht, map_pow, map_pow]`. Conclude with `hpow _`. Establish `h0 : archExponent w ψ = 0` using `archExponent_unique w ψ fun t ↦ by simp [hs t]`.

Establish `hτ0 : τ = 0` using `(archExponent_eq_of_forall hτ w).symm.trans h0`. Use `ContinuousMonoidHom.ext fun c ↦ ?_` and prove the remaining obligations. Take `⟨x, rfl⟩` from `IdeleClassGroup.mk_surjective K c`. Establish `hx` using `hτ x`. Rewrite `hx` using `[hτ0]`.

Simplify using `only [ofReal_zero, zero_mul, cpow_zero] at hx`. Rewrite using `[← toIdele_apply]`. Conclude with `Circle.ext (by simpa using hx)`.
-/
theorem not_exists_cpow_of_isOfFinOrder (ψ : HeckeCharacter K) (hψ : IsOfFinOrder ψ) (hne : ψ ≠ 1) :
    ¬ ∃ τ : ℝ, ∀ x : IdeleGroup K,
      (ψ.toIdele x : ℂ) = ((ideleModule K x : ℝ) : ℂ) ^ ((τ : ℂ) * I) := by
  rintro ⟨τ, hτ⟩
  apply hne
  obtain ⟨n, hn, hpow⟩ := ψ.exists_toIdele_pow_eq_one hψ
  let w : InfinitePlace K := Classical.arbitrary _
  have hs : ∀ t : {x : ℝ // 0 < x}, ψ.toIdele (moduleSection w t) = 1 := by
    intro t
    have ht : (⟨(t : ℝ) ^ (n⁻¹ : ℝ), Real.rpow_pos_of_pos t.2 _⟩ : {x : ℝ // 0 < x}) ^ n = t :=
      Subtype.ext (by simp [Real.rpow_inv_natCast_pow t.2.le hn.ne'])
    rw [← ht, map_pow, map_pow]
    exact hpow _
  have h0 : archExponent w ψ = 0 := archExponent_unique w ψ fun t ↦ by simp [hs t]
  have hτ0 : τ = 0 := (archExponent_eq_of_forall hτ w).symm.trans h0
  refine ContinuousMonoidHom.ext fun c ↦ ?_
  obtain ⟨x, rfl⟩ := IdeleClassGroup.mk_surjective K c
  have hx := hτ x
  rw [hτ0] at hx
  simp only [ofReal_zero, zero_mul, cpow_zero] at hx
  rw [← toIdele_apply]
  exact Circle.ext (by simpa using hx)

end HeckeCharacter

section Hecke

universe u

/- English proof (translation)
Use extensionality with `σ`. Take `⟨c, hc⟩` from `reciprocityMap_surjective (K := K) (L := ↥(charField χ)) (AlgEquiv.restrictNormalHom (charField χ) σ)`. Establish `h1` using `heckeCharacterOfChar_apply χ c`. Rewrite `h1` using `[h, hc, charBar_restrictNormalHom]`. Simplify using `using h1.symm`.
-/
theorem eq_one_of_heckeCharacterOfChar_eq_one {K L : Type u} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [IsGalois K L] (χ : Gal(L/K) →* ℂˣ) (h : heckeCharacterOfChar χ = 1) :
    χ = 1 := by
  ext σ
  obtain ⟨c, hc⟩ := reciprocityMap_surjective (K := K) (L := ↥(charField χ))
    (AlgEquiv.restrictNormalHom (charField χ) σ)
  have h1 := heckeCharacterOfChar_apply χ c
  rw [h, hc, charBar_restrictNormalHom] at h1
  simpa using h1.symm

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

/- English proof (translation)
Use `HeckeCharacter.not_exists_cpow_of_isOfFinOrder _ (isOfFinOrder_heckeCharacterOfChar _) fun h ↦ hl ?_` and prove the remaining obligations. Establish `h1` using `eq_one_of_heckeCharacterOfChar_eq_one _ h`. Use extensionality with `k`. Use `DFunLike.congr_fun h1 (Artin.fixedFieldMulEquiv H k)` as an intermediate fact. Simplify `congrArg Units.val this` using `[fixedFieldChar]`.
-/
theorem not_exists_cpow_heckeCharacterOfChar_fixedFieldChar (H : Subgroup Gal(L/K)) (l : H →* ℂˣ)
    (hl : l ≠ 1) :
    ¬ ∃ τ : ℝ, ∀ x : IdeleGroup (fixedField H),
      ((heckeCharacterOfChar (fixedFieldChar H l)).toIdele x : ℂ) =
        ((IdeleGroup.ideleModule (fixedField H) x : ℝ) : ℂ) ^ ((τ : ℂ) * I) := by
  refine HeckeCharacter.not_exists_cpow_of_isOfFinOrder _ (isOfFinOrder_heckeCharacterOfChar _)
    fun h ↦ hl ?_
  have h1 := eq_one_of_heckeCharacterOfChar_eq_one _ h
  ext k
  have := DFunLike.congr_fun h1 (Artin.fixedFieldMulEquiv H k)
  simpa [fixedFieldChar] using congrArg Units.val this

end Hecke

end GroundTheory.Global
