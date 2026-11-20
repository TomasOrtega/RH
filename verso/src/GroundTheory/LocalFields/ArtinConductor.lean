import Mathlib
import GroundTheory.LocalFields.DifferentGalois

noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel Module Representation

section Codim

variable {H V : Type*} [Group H] [Fintype H] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/- English proof (translation)
Establish `hpos : (Nat.card H : ℂ) ≠ 0` using `Nat.cast_ne_zero.mpr Nat.card_pos.ne'`. Set `_ : Invertible (Nat.card H : ℂ)` to `invertibleOfNonzero hpos`. Establish `h1` using `card_inv_mul_sum_char_eq_finrank ρ`. Establish `hle : finrank ℂ (invariants ρ) ≤ finrank ℂ V` using `Submodule.finrank_le _`. Rewrite using `[Nat.cast_sub hle, ← h1, Finset.sum_sub_distrib, mul_sub, char_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card]`.

Clear the denominators using the available nonvanishing facts.
-/
theorem codim_invariants_eq (ρ : Representation ℂ H V) :
    ((finrank ℂ V - finrank ℂ (invariants ρ) : ℕ) : ℂ) =
      (Nat.card H : ℂ)⁻¹ * ∑ h : H, (ρ.character 1 - ρ.character h) := by
  have hpos : (Nat.card H : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  let _ : Invertible (Nat.card H : ℂ) := invertibleOfNonzero hpos
  have h1 := card_inv_mul_sum_char_eq_finrank ρ
  have hle : finrank ℂ (invariants ρ) ≤ finrank ℂ V := Submodule.finrank_le _
  rw [Nat.cast_sub hle, ← h1, Finset.sum_sub_distrib, mul_sub, char_one, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card]
  field_simp

omit [Fintype H] [FiniteDimensional ℂ V] in

/- English proof (translation)
Use extensionality with `v`. Simplify using `only [Submodule.mem_top, iff_true, mem_invariants]`. Introduce `h`. Establish `h1 : (h : H) = 1`. Substitute `hS` using the available equality.

Conclude with `Subgroup.mem_bot.mp h.2`. Simplify using `[h1]`.
-/
theorem invariants_comp_subtype_of_eq_bot (ρ : Representation ℂ H V) {S : Subgroup H} (hS : S = ⊥) :
    invariants (ρ.comp S.subtype) = ⊤ := by
  ext v
  simp only [Submodule.mem_top, iff_true, mem_invariants]
  intro h
  have h1 : (h : H) = 1 := by
    subst hS
    exact Subgroup.mem_bot.mp h.2
  simp [h1]

end Codim

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

section Count

open Classical in

/- English proof (translation)
Take `⟨n, hn⟩` from `ENat.ne_top_iff_exists.mp (lowerIndex_ne_top hσ)`. Establish `hnN : n ≤ N`. Assume the negation of the conclusion as `hlt'`. Establish `hlt` using `not_le.mp hlt'`. Establish `hmem : σ ∈ lowerRamificationGroup K L N`.

Rewrite using `[mem_lowerRamificationGroup_natCast_iff_lowerIndex, ← hn]`. Conclude with `hlt` after adjusting the coercions. Rewrite `hmem` using `[hN, Subgroup.mem_bot]`. Conclude with `hσ hmem`. Establish `hfilter : (Finset.range N).filter (fun i : ℕ ↦ σ ∈ lowerRamificationGroup K L i) = Finset.range n`.

Use extensionality with `i`. Rewrite using `[Finset.mem_filter, Finset.mem_range, Finset.mem_range, mem_lowerRamificationGroup_natCast_iff_lowerIndex, ← hn, Nat.cast_le]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[hfilter, Finset.card_range, ← hn, ENat.toNat_natCast]`.
-/
theorem card_filter_mem_lowerRamificationGroup {N : ℕ} (hN : lowerRamificationGroup K L N = ⊥)
    {σ : L ≃ₐ[K] L} (hσ : σ ≠ 1) :
    ((Finset.range N).filter (fun i : ℕ ↦ σ ∈ lowerRamificationGroup K L i)).card =
      (lowerIndex K L σ).toNat := by
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (lowerIndex_ne_top hσ)
  have hnN : n ≤ N := by
    by_contra hlt'
    have hlt := not_le.mp hlt'
    have hmem : σ ∈ lowerRamificationGroup K L N := by
      rw [mem_lowerRamificationGroup_natCast_iff_lowerIndex, ← hn]
      exact_mod_cast hlt
    rw [hN, Subgroup.mem_bot] at hmem
    exact hσ hmem
  have hfilter : (Finset.range N).filter (fun i : ℕ ↦ σ ∈ lowerRamificationGroup K L i) =
      Finset.range n := by
    ext i
    rw [Finset.mem_filter, Finset.mem_range, Finset.mem_range,
      mem_lowerRamificationGroup_natCast_iff_lowerIndex, ← hn, Nat.cast_le]
    omega
  rw [hfilter, Finset.card_range, ← hn, ENat.toNat_natCast]

end Count

variable (K L) in
open Classical in

def artinCharacter (σ : L ≃ₐ[K] L) : ℤ :=
  if σ = 1 then
    ((residueDegree K L * ∑ τ ∈ Finset.univ.erase (1 : L ≃ₐ[K] L), (lowerIndex K L τ).toNat : ℕ) : ℤ)
  else -((residueDegree K L * (lowerIndex K L σ).toNat : ℕ) : ℤ)

open Classical in

/- English proof (translation)
Distinguish the cases in `h : σ = 1`. Substitute `h` using the available equality. Simplify using `only [artinCharacter, if_true]`. Use `push_cast`. Rewrite using `[Finset.sum_erase_eq_sub (Finset.mem_univ _)]`.

Simplify using `only [artinCharacter, h, if_false]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem artinCharacter_eq (σ : L ≃ₐ[K] L) :
    (artinCharacter K L σ : ℂ) = residueDegree K L *
      ((if σ = 1 then ∑ τ : L ≃ₐ[K] L, ((lowerIndex K L τ).toNat : ℂ) else 0) -
        (lowerIndex K L σ).toNat) := by
  by_cases h : σ = 1
  · subst h
    simp only [artinCharacter, if_true]
    push_cast
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ _)]
  · simp only [artinCharacter, h, if_false]
    push_cast
    ring

/- English proof (translation)
Unfold `artinCharacter`. Rewrite using `[if_neg hσ]`.
-/
theorem artinCharacter_of_ne_one {σ : L ≃ₐ[K] L} (hσ : σ ≠ 1) :
    artinCharacter K L σ = -((residueDegree K L * (lowerIndex K L σ).toNat : ℕ) : ℤ) := by
  classical
  unfold artinCharacter
  rw [if_neg hσ]

/- English proof (translation)
Establish `h : ∀ σ : L ≃ₐ[K] L, χ σ * (artinCharacter K L σ : ℂ) = residueDegree K L * ((if σ = 1 then χ 1 * ∑ τ : L ≃ₐ[K] L, ((lowerIndex K L τ).toNat : ℂ) else 0) - (lowerIndex K L σ).toNat * χ σ)`. Introduce `σ`. Rewrite using `[artinCharacter_eq]`. Use `split_ifs with hσ`. Substitute `hσ` using the available equality.

Expand and normalize the polynomial expressions, which then agree. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Finset.sum_congr rfl fun σ _ ↦ h σ, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]`. Use `congr 1`. Rewrite using `[Finset.mul_sum, ← Finset.sum_sub_distrib]`.

Conclude with `Finset.sum_congr rfl fun σ _ ↦ by ring`.
-/
theorem sum_mul_artinCharacter (χ : (L ≃ₐ[K] L) → ℂ) :
    ∑ σ : L ≃ₐ[K] L, χ σ * (artinCharacter K L σ : ℂ) =
      residueDegree K L * ∑ σ : L ≃ₐ[K] L, ((lowerIndex K L σ).toNat : ℂ) * (χ 1 - χ σ) := by
  classical
  have h : ∀ σ : L ≃ₐ[K] L, χ σ * (artinCharacter K L σ : ℂ) = residueDegree K L *
      ((if σ = 1 then χ 1 * ∑ τ : L ≃ₐ[K] L, ((lowerIndex K L τ).toNat : ℂ) else 0) -
        (lowerIndex K L σ).toNat * χ σ) := by
    intro σ
    rw [artinCharacter_eq]
    split_ifs with hσ
    · subst hσ
      ring
    · ring
  rw [Finset.sum_congr rfl fun σ _ ↦ h σ, ← Finset.mul_sum, Finset.sum_sub_distrib,
    Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
  congr 1
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun σ _ ↦ by ring

section Conductor

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

def artinConductor (ρ : Representation ℂ (L ≃ₐ[K] L) V) : ℚ :=
  ∑ᶠ i : ℕ, (Nat.card (lowerRamificationGroup K L i) / Nat.card (lowerRamificationGroup K L 0) : ℚ) *
    ((finrank ℂ V - finrank ℂ (invariants (ρ.comp (lowerRamificationGroup K L i).subtype)) : ℕ) : ℚ)

omit [FiniteDimensional ℂ V] in

/- English proof (translation)
Unfold `artinConductor`. Apply `finsum_eq_sum_of_support_subset` to reduce the goal to its premises. Introduce `i hi`. Rewrite `hi` using `[Function.mem_support]`. Rewrite using `[Finset.coe_range, Set.mem_Iio]`.

Assume the negation of the conclusion as `h'`. Apply `hi` to reduce the goal to its premises. Establish `hle : lowerRamificationGroup K L i ≤ lowerRamificationGroup K L N` using `lowerRamificationGroup_antitone K L (by exact_mod_cast not_lt.mp h')`. Rewrite using `[invariants_comp_subtype_of_eq_bot ρ (eq_bot_iff.mpr (hN ▸ hle)), finrank_top, Nat.sub_self]`. Simplify using the standard rewrite rules.
-/
theorem artinConductor_eq_sum (ρ : Representation ℂ (L ≃ₐ[K] L) V) {N : ℕ}
    (hN : lowerRamificationGroup K L N = ⊥) :
    artinConductor ρ = ∑ i ∈ Finset.range N,
      (Nat.card (lowerRamificationGroup K L i) / Nat.card (lowerRamificationGroup K L 0) : ℚ) *
        ((finrank ℂ V - finrank ℂ (invariants (ρ.comp (lowerRamificationGroup K L i).subtype)) : ℕ) : ℚ) := by
  unfold artinConductor
  apply finsum_eq_sum_of_support_subset
  intro i hi
  rw [Function.mem_support] at hi
  rw [Finset.coe_range, Set.mem_Iio]
  by_contra h'
  apply hi
  have hle : lowerRamificationGroup K L i ≤ lowerRamificationGroup K L N :=
    lowerRamificationGroup_antitone K L (by exact_mod_cast not_lt.mp h')
  rw [invariants_comp_subtype_of_eq_bot ρ (eq_bot_iff.mpr (hN ▸ hle)), finrank_top, Nat.sub_self]
  simp

omit [FiniteDimensional ℂ V] in

/- English proof (translation)
The claim follows from `finsum_nonneg fun _ ↦ mul_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)`.
-/
theorem artinConductor_nonneg (ρ : Representation ℂ (L ≃ₐ[K] L) V) : 0 ≤ artinConductor ρ :=
  finsum_nonneg fun _ ↦ mul_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    (Nat.cast_nonneg _)

variable (K L) in

def charArtinConductor (χ : (L ≃ₐ[K] L) → ℂ) : ℂ :=
  (Nat.card (L ≃ₐ[K] L) : ℂ)⁻¹ * ∑ σ : L ≃ₐ[K] L, χ σ * artinCharacter K L σ

/- English proof (translation)
Rewrite using `[IsGalois.card_aut_eq_finrank, ← ramificationIndex_mul_residueDegree, card_lowerRamificationGroup_zero]`.
-/
theorem card_aut_eq_card_lowerRamificationGroup_zero_mul [IsGalois K L] :
    Nat.card (L ≃ₐ[K] L) = Nat.card (lowerRamificationGroup K L 0) * residueDegree K L := by
  rw [IsGalois.card_aut_eq_finrank, ← ramificationIndex_mul_residueDegree,
    card_lowerRamificationGroup_zero]

/- English proof (translation)
Establish `hf : (residueDegree K L : ℂ) ≠ 0` using `Nat.cast_ne_zero.mpr (residueDegree_pos K L).ne'`. Rewrite using `[charArtinConductor, sum_mul_artinCharacter, card_aut_eq_card_lowerRamificationGroup_zero_mul]`. Use `push_cast`. Rewrite using `[mul_inv, mul_assoc, ← mul_assoc (residueDegree K L : ℂ)⁻¹, inv_mul_cancel₀ hf, one_mul]`.
-/
theorem charArtinConductor_eq_sum_lowerIndex [IsGalois K L] (χ : (L ≃ₐ[K] L) → ℂ) :
    charArtinConductor K L χ = (Nat.card (lowerRamificationGroup K L 0) : ℂ)⁻¹ *
      ∑ σ : L ≃ₐ[K] L, ((lowerIndex K L σ).toNat : ℂ) * (χ 1 - χ σ) := by
  have hf : (residueDegree K L : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (residueDegree_pos K L).ne'
  rw [charArtinConductor, sum_mul_artinCharacter, card_aut_eq_card_lowerRamificationGroup_zero_mul]
  push_cast
  rw [mul_inv, mul_assoc, ← mul_assoc (residueDegree K L : ℂ)⁻¹, inv_mul_cancel₀ hf, one_mul]

/- English proof (translation)
Take `⟨N, hN⟩` from `exists_lowerRamificationGroup_eq_bot K L`. Establish `hN' : lowerRamificationGroup K L (N : ℕ) = ⊥` using `hN N le_rfl`. Establish `he : (Nat.card (lowerRamificationGroup K L 0) : ℂ) ≠ 0` using `Nat.cast_ne_zero.mpr Nat.card_pos.ne'`. Establish `hterm : ∀ i : ℕ, (((Nat.card (lowerRamificationGroup K L i) / Nat.card (lowerRamificationGroup K L 0) : ℚ) * ((finrank ℂ V - finrank ℂ (invariants (ρ.comp (lowerRamificationGroup K L i).subtype)) : ℕ) : ℚ) : ℚ) : ℂ) = (Nat.card (lowerRamificationGroup K L 0) : ℂ)⁻¹ * ∑ σ : L ≃ₐ[K …`. Introduce `i`.

Establish `hc` using `codim_invariants_eq (ρ.comp (lowerRamificationGroup K L i).subtype)`. Establish `hci : (Nat.card (lowerRamificationGroup K L i) : ℂ) ≠ 0` using `Nat.cast_ne_zero.mpr Nat.card_pos.ne'`. Establish `hsum : ∑ h : lowerRamificationGroup K L i, (Representation.character (ρ.comp (lowerRamificationGroup K L i).subtype) 1 - Representation.character (ρ.comp (lowerRamificationGroup K L i).subtype) h) = ∑ σ : L ≃ₐ[K] L, if σ ∈ lowerRamificationGroup K L i then ρ.character 1 - ρ.chara …`. Rewrite using `[← Finset.sum_filter]`. Conclude with `(Finset.sum_subtype _ (by simp) (fun σ ↦ ρ.character 1 - ρ.character σ)).symm`.

Use `push_cast`. Rewrite using `[hc, hsum]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[artinConductor_eq_sum ρ hN', Rat.cast_sum, Finset.sum_congr rfl fun i _ ↦ hterm i, ← Finset.mul_sum, Finset.sum_comm, charArtinConductor_eq_sum_lowerIndex]`. Use `congr 1`.

Use `Finset.sum_congr rfl fun σ _ ↦ ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]`. Distinguish the cases in `hσ : σ = 1`. Substitute `hσ` using the available equality. Simplify using the standard rewrite rules.

Rewrite using `[card_filter_mem_lowerRamificationGroup hN' hσ]`.
-/
theorem artinConductor_eq_charArtinConductor [IsGalois K L] (ρ : Representation ℂ (L ≃ₐ[K] L) V) :
    (artinConductor ρ : ℂ) = charArtinConductor K L ρ.character := by
  classical
  obtain ⟨N, hN⟩ := exists_lowerRamificationGroup_eq_bot K L
  have hN' : lowerRamificationGroup K L (N : ℕ) = ⊥ := hN N le_rfl
  have he : (Nat.card (lowerRamificationGroup K L 0) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hterm : ∀ i : ℕ,
      (((Nat.card (lowerRamificationGroup K L i) / Nat.card (lowerRamificationGroup K L 0) : ℚ) *
        ((finrank ℂ V - finrank ℂ (invariants (ρ.comp (lowerRamificationGroup K L i).subtype)) : ℕ) : ℚ)
          : ℚ) : ℂ) =
      (Nat.card (lowerRamificationGroup K L 0) : ℂ)⁻¹ * ∑ σ : L ≃ₐ[K] L,
        if σ ∈ lowerRamificationGroup K L i then ρ.character 1 - ρ.character σ else 0 := by
    intro i
    have hc := codim_invariants_eq (ρ.comp (lowerRamificationGroup K L i).subtype)
    have hci : (Nat.card (lowerRamificationGroup K L i) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr Nat.card_pos.ne'
    have hsum : ∑ h : lowerRamificationGroup K L i,
        (Representation.character (ρ.comp (lowerRamificationGroup K L i).subtype) 1 -
          Representation.character (ρ.comp (lowerRamificationGroup K L i).subtype) h) =
        ∑ σ : L ≃ₐ[K] L,
          if σ ∈ lowerRamificationGroup K L i then ρ.character 1 - ρ.character σ else 0 := by
      rw [← Finset.sum_filter]
      exact (Finset.sum_subtype _ (by simp) (fun σ ↦ ρ.character 1 - ρ.character σ)).symm
    push_cast
    rw [hc, hsum]
    field_simp
  rw [artinConductor_eq_sum ρ hN', Rat.cast_sum, Finset.sum_congr rfl fun i _ ↦ hterm i,
    ← Finset.mul_sum, Finset.sum_comm, charArtinConductor_eq_sum_lowerIndex]
  congr 1
  refine Finset.sum_congr rfl fun σ _ ↦ ?_
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  by_cases hσ : σ = 1
  · subst hσ
    simp
  · rw [card_filter_mem_lowerRamificationGroup hN' hσ]

end Conductor

section Discriminant

variable [IsGalois K L]

/- English proof (translation)
Establish `h` using `differentExponent_eq_sum_lowerIndex K L`. Rewrite `h` using `[Finset.sum_congr rfl fun σ hσ ↦ (ENat.natCast_toNat (lowerIndex_ne_top (Finset.ne_of_mem_erase hσ))).symm, ← Nat.cast_sum]`. Conclude with `h` after adjusting the coercions.
-/
theorem differentExponent_eq_sum_toNat [DecidableEq (L ≃ₐ[K] L)] :
    differentExponent K L =
      ∑ σ ∈ Finset.univ.erase (1 : L ≃ₐ[K] L), (lowerIndex K L σ).toNat := by
  have h := differentExponent_eq_sum_lowerIndex K L
  rw [Finset.sum_congr rfl fun σ hσ ↦
    (ENat.natCast_toNat (lowerIndex_ne_top (Finset.ne_of_mem_erase hσ))).symm, ← Nat.cast_sum] at h
  exact_mod_cast h

/- English proof (translation)
Unfold `artinCharacter`. Rewrite using `[if_pos rfl, differentExponent_eq_sum_toNat]`.
-/
theorem artinCharacter_one :
    artinCharacter K L 1 = ((residueDegree K L * differentExponent K L : ℕ) : ℤ) := by
  classical
  unfold artinCharacter
  rw [if_pos rfl, differentExponent_eq_sum_toNat]

/- English proof (translation)
Rewrite using `[addVal_discr, artinCharacter_one, Int.toNat_natCast]`.
-/
theorem addVal_discr_eq_artinCharacter_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι 𝒪[K] 𝒪[L]) :
    IsDiscreteValuationRing.addVal 𝒪[K] (Algebra.discr 𝒪[K] b) = (artinCharacter K L 1).toNat := by
  rw [addVal_discr, artinCharacter_one, Int.toNat_natCast]

open Classical in

/- English proof (translation)
Establish `hG : (Nat.card (L ≃ₐ[K] L) : ℂ) ≠ 0` using `Nat.cast_ne_zero.mpr Nat.card_pos.ne'`. Rewrite using `[charArtinConductor]`. Repeatedly rewrite using `[ite_mul, zero_mul]`. Rewrite using `[Finset.sum_ite_eq', if_pos (Finset.mem_univ _), artinCharacter_one, ← mul_assoc, inv_mul_cancel₀ hG, one_mul]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem charArtinConductor_regular :
    charArtinConductor K L (fun σ ↦ if σ = 1 then (Nat.card (L ≃ₐ[K] L) : ℂ) else 0) =
      ((residueDegree K L * differentExponent K L : ℕ) : ℂ) := by
  have hG : (Nat.card (L ≃ₐ[K] L) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  rw [charArtinConductor]
  simp_rw [ite_mul, zero_mul]
  rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ _), artinCharacter_one, ← mul_assoc,
    inv_mul_cancel₀ hG, one_mul]
  push_cast
  ring

end Discriminant

section Regular

variable {G : Type*} [Group G] [Fintype G]

/- English proof (translation)
Rewrite using `[Representation.character, Representation.ofMulAction_def]`. Establish `: ((MonoidAlgebra.coeffLinearEquiv ℂ).symm.toLinearMap ∘ₗ Finsupp.lmapDomain ℂ ℂ (g • · : G → G) ∘ₗ (MonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap) = (MonoidAlgebra.coeffLinearEquiv (R` using `ℂ) (S := ℂ) (M := G)).symm.conj (Finsupp.lmapDomain ℂ ℂ (g • · : G → G)) := by`. Use extensionality with `x`. Simplify using `[LinearEquiv.conj_apply]`. Rewrite using `[this, LinearMap.trace_conj', LinearMap.trace_eq_matrix_trace ℂ (Finsupp.basisSingleOne), Matrix.trace]`.

Simplify using `only [Matrix.diag, LinearMap.toMatrix_apply, Finsupp.coe_basisSingleOne, Finsupp.basisSingleOne_repr, LinearEquiv.refl_apply, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, Finsupp.single_apply, smul_eq_mul, mul_eq_right]`. Use `split_ifs with hg`. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem character_leftRegular [DecidableEq G] (g : G) :
    (Representation.leftRegular ℂ G).character g = if g = 1 then (Fintype.card G : ℂ) else 0 := by
  rw [Representation.character, Representation.ofMulAction_def]
  have : ((MonoidAlgebra.coeffLinearEquiv ℂ).symm.toLinearMap ∘ₗ
      Finsupp.lmapDomain ℂ ℂ (g • · : G → G) ∘ₗ (MonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap) =
      (MonoidAlgebra.coeffLinearEquiv (R := ℂ) (S := ℂ) (M := G)).symm.conj
        (Finsupp.lmapDomain ℂ ℂ (g • · : G → G)) := by
    ext x
    simp [LinearEquiv.conj_apply]
  rw [this, LinearMap.trace_conj', LinearMap.trace_eq_matrix_trace ℂ (Finsupp.basisSingleOne),
    Matrix.trace]
  simp only [Matrix.diag, LinearMap.toMatrix_apply, Finsupp.coe_basisSingleOne,
    Finsupp.basisSingleOne_repr, LinearEquiv.refl_apply, Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_single, Finsupp.single_apply, smul_eq_mul, mul_eq_right]
  split_ifs with hg
  · simp
  · simp

end Regular

section RegularConductor

variable [IsGalois K L]

end RegularConductor

section Swan

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

def swanConductor (ρ : Representation ℂ (L ≃ₐ[K] L) V) : ℚ :=
  ∑ᶠ i : ℕ, (Nat.card (lowerRamificationGroup K L ((i + 1 : ℕ) : ℤ)) /
      Nat.card (lowerRamificationGroup K L 0) : ℚ) *
    ((finrank ℂ V -
      finrank ℂ (invariants (ρ.comp (lowerRamificationGroup K L ((i + 1 : ℕ) : ℤ)).subtype)) : ℕ) : ℚ)

omit [FiniteDimensional ℂ V] in

/- English proof (translation)
The claim follows from `finsum_nonneg fun _ ↦ mul_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)`.
-/
theorem swanConductor_nonneg (ρ : Representation ℂ (L ≃ₐ[K] L) V) : 0 ≤ swanConductor ρ :=
  finsum_nonneg fun _ ↦ mul_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    (Nat.cast_nonneg _)

omit [FiniteDimensional ℂ V] in

/- English proof (translation)
Unfold `swanConductor`. Apply `finsum_eq_sum_of_support_subset` to reduce the goal to its premises. Introduce `i hi`. Rewrite `hi` using `[Function.mem_support]`. Rewrite using `[Finset.coe_range, Set.mem_Iio]`.

Assume the negation of the conclusion as `h'`. Apply `hi` to reduce the goal to its premises. Establish `hle : lowerRamificationGroup K L ((i + 1 : ℕ) : ℤ) ≤ lowerRamificationGroup K L N` using `lowerRamificationGroup_antitone K L (by push_cast; omega)`. Rewrite using `[invariants_comp_subtype_of_eq_bot ρ (eq_bot_iff.mpr (hN ▸ hle)), finrank_top, Nat.sub_self]`. Simplify using the standard rewrite rules.
-/
theorem swanConductor_eq_sum (ρ : Representation ℂ (L ≃ₐ[K] L) V) {N : ℕ}
    (hN : lowerRamificationGroup K L N = ⊥) :
    swanConductor ρ = ∑ i ∈ Finset.range N,
      (Nat.card (lowerRamificationGroup K L ((i + 1 : ℕ) : ℤ)) /
          Nat.card (lowerRamificationGroup K L 0) : ℚ) *
        ((finrank ℂ V -
          finrank ℂ (invariants (ρ.comp (lowerRamificationGroup K L ((i + 1 : ℕ) : ℤ)).subtype)) : ℕ)
            : ℚ) := by
  unfold swanConductor
  apply finsum_eq_sum_of_support_subset
  intro i hi
  rw [Function.mem_support] at hi
  rw [Finset.coe_range, Set.mem_Iio]
  by_contra h'
  apply hi
  have hle : lowerRamificationGroup K L ((i + 1 : ℕ) : ℤ) ≤ lowerRamificationGroup K L N :=
    lowerRamificationGroup_antitone K L (by push_cast; omega)
  rw [invariants_comp_subtype_of_eq_bot ρ (eq_bot_iff.mpr (hN ▸ hle)), finrank_top, Nat.sub_self]
  simp

/- English proof (translation)
Take `⟨N, hN⟩` from `exists_lowerRamificationGroup_eq_bot K L`. Rewrite using `[artinConductor_eq_sum ρ (hN ((N + 1 : ℕ) : ℤ) (by push_cast; omega)), swanConductor_eq_sum ρ (hN N le_rfl), Finset.sum_range_succ', add_comm]`. Establish `h0 : (Nat.card (lowerRamificationGroup K L 0) : ℚ) ≠ 0` using `Nat.cast_ne_zero.mpr Nat.card_pos.ne'`. Use `congr 1`. Simplify using the standard rewrite rules.
-/
theorem artinConductor_eq_codim_add_swanConductor (ρ : Representation ℂ (L ≃ₐ[K] L) V) :
    artinConductor ρ = ((finrank ℂ V -
      finrank ℂ (invariants (ρ.comp (lowerRamificationGroup K L 0).subtype)) : ℕ) : ℚ) +
        swanConductor ρ := by
  obtain ⟨N, hN⟩ := exists_lowerRamificationGroup_eq_bot K L
  rw [artinConductor_eq_sum ρ (hN ((N + 1 : ℕ) : ℤ) (by push_cast; omega)),
    swanConductor_eq_sum ρ (hN N le_rfl), Finset.sum_range_succ', add_comm]
  have h0 : (Nat.card (lowerRamificationGroup K L 0) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  congr 1
  simp

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Rewrite `h` using `[artinConductor_eq_codim_add_swanConductor]`. Establish `hs` using `swanConductor_nonneg ρ`. Establish `hc : ((finrank ℂ V - finrank ℂ (invariants (ρ.comp (lowerRamificationGroup K L 0).subtype)) : ℕ) : ℚ) = 0`.

Use `Nat.cast_nonneg (α := ℚ) (finrank ℂ V - finrank ℂ (invariants (ρ.comp (lowerRamificationGroup K L 0).subtype)))` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hle : finrank ℂ (invariants (ρ.comp (lowerRamificationGroup K L 0).subtype)) ≤ finrank ℂ V` using `Submodule.finrank_le _`. Establish `htop : invariants (ρ.comp (lowerRamificationGroup K L 0).subtype) = ⊤` using `Submodule.eq_top_of_finrank_eq (by rw [Nat.cast_eq_zero] at hc; omega)`. Introduce `σ hσ`.

Use extensionality with `v`. Establish `hv : v ∈ invariants (ρ.comp (lowerRamificationGroup K L 0).subtype)` using `htop ▸ trivial`. Conclude with `hv ⟨σ, hσ⟩`. Introduce `h`. Apply `finsum_eq_zero_of_forall_eq_zero` to reduce the goal to its premises.

Introduce `i`. Establish `htop : invariants (ρ.comp (lowerRamificationGroup K L i).subtype) = ⊤`. Use extensionality with `v`. Simplify using `only [Submodule.mem_top, iff_true, mem_invariants]`. Introduce `g`.

Establish `hg : (g : L ≃ₐ[K] L) ∈ lowerRamificationGroup K L 0` using `lowerRamificationGroup_antitone K L (by omega) g.2`. Simplify using `[h _ hg]`. Rewrite using `[htop, finrank_top, Nat.sub_self]`. Simplify using the standard rewrite rules.
-/
theorem artinConductor_eq_zero_iff (ρ : Representation ℂ (L ≃ₐ[K] L) V) :
    artinConductor ρ = 0 ↔ ∀ σ ∈ lowerRamificationGroup K L 0, ρ σ = 1 := by
  constructor
  · intro h
    rw [artinConductor_eq_codim_add_swanConductor] at h
    have hs := swanConductor_nonneg ρ
    have hc : ((finrank ℂ V -
        finrank ℂ (invariants (ρ.comp (lowerRamificationGroup K L 0).subtype)) : ℕ) : ℚ) = 0 := by
      have := Nat.cast_nonneg (α := ℚ) (finrank ℂ V -
        finrank ℂ (invariants (ρ.comp (lowerRamificationGroup K L 0).subtype)))
      linarith
    have hle : finrank ℂ (invariants (ρ.comp (lowerRamificationGroup K L 0).subtype)) ≤
        finrank ℂ V := Submodule.finrank_le _
    have htop : invariants (ρ.comp (lowerRamificationGroup K L 0).subtype) = ⊤ :=
      Submodule.eq_top_of_finrank_eq (by rw [Nat.cast_eq_zero] at hc; omega)
    intro σ hσ
    ext v
    have hv : v ∈ invariants (ρ.comp (lowerRamificationGroup K L 0).subtype) := htop ▸ trivial
    exact hv ⟨σ, hσ⟩
  · intro h
    apply finsum_eq_zero_of_forall_eq_zero
    intro i
    have htop : invariants (ρ.comp (lowerRamificationGroup K L i).subtype) = ⊤ := by
      ext v
      simp only [Submodule.mem_top, iff_true, mem_invariants]
      intro g
      have hg : (g : L ≃ₐ[K] L) ∈ lowerRamificationGroup K L 0 :=
        lowerRamificationGroup_antitone K L (by omega) g.2
      simp [h _ hg]
    rw [htop, finrank_top, Nat.sub_self]
    simp

variable (K L) in
open Classical in

def swanCharacter (σ : L ≃ₐ[K] L) : ℤ :=
  artinCharacter K L σ - ((if σ = 1 then (Nat.card (L ≃ₐ[K] L) : ℤ) else 0) -
    (if σ ∈ lowerRamificationGroup K L 0 then (residueDegree K L : ℤ) else 0))

variable (K L) in

def charSwanConductor (χ : (L ≃ₐ[K] L) → ℂ) : ℂ :=
  (Nat.card (L ≃ₐ[K] L) : ℂ)⁻¹ * ∑ σ : L ≃ₐ[K] L, χ σ * swanCharacter K L σ

/- English proof (translation)
Establish `hG0 : (Nat.card (lowerRamificationGroup K L 0) : ℂ) ≠ 0` using `Nat.cast_ne_zero.mpr Nat.card_pos.ne'`. Establish `hf : (residueDegree K L : ℂ) ≠ 0` using `Nat.cast_ne_zero.mpr (residueDegree_pos K L).ne'`. Establish `hcard : (Nat.card (L ≃ₐ[K] L) : ℂ) = Nat.card (lowerRamificationGroup K L 0) * residueDegree K L`. Conclude with `card_aut_eq_card_lowerRamificationGroup_zero_mul` after adjusting the coercions. Establish `hsub : ∑ σ : L ≃ₐ[K] L, (if σ ∈ lowerRamificationGroup K L 0 then ρ.character σ else 0) = ∑ h : lowerRamificationGroup K L 0, ρ.character h`.

Rewrite using `[← Finset.sum_filter]`. Conclude with `Finset.sum_subtype _ (by simp) _`. Establish `hc` using `codim_invariants_eq (ρ.comp (lowerRamificationGroup K L 0).subtype)`. Establish `hc' : ∑ h : lowerRamificationGroup K L 0, (Representation.character (ρ.comp (lowerRamificationGroup K L 0).subtype) 1 - Representation.character (ρ.comp (lowerRamificationGroup K L 0).subtype) h) = Nat.card (lowerRamificationGroup K L 0) * ρ.character 1 - ∑ h : lowerRamificationG …`. Rewrite using `[Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]`.

Both sides reduce to the same expression. Establish `hsplit` using `artinConductor_eq_codim_add_swanConductor ρ`. Establish `hswan : (swanConductor ρ : ℂ) = (artinConductor ρ : ℂ) - ((finrank ℂ V - finrank ℂ (invariants (ρ.comp (lowerRamificationGroup K L 0).subtype)) : ℕ) : ℂ)`. Rewrite using `[hsplit]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `hsum : ∑ σ : L ≃ₐ[K] L, ρ.character σ * (swanCharacter K L σ : ℂ) = ∑ σ : L ≃ₐ[K] L, ρ.character σ * (artinCharacter K L σ : ℂ) - (Nat.card (L ≃ₐ[K] L) * ρ.character 1 - residueDegree K L * ∑ h : lowerRamificationGroup K L 0, ρ.character h)`. Establish `hpt : ∀ σ : L ≃ₐ[K] L, ρ.character σ * (swanCharacter K L σ : ℂ) = ρ.character σ * artinCharacter K L σ - ((if σ = 1 then (Nat.card (L ≃ₐ[K] L) : ℂ) * ρ.character 1 else 0) - residueDegree K L * (if σ ∈ lowerRamificationGroup K L 0 then ρ.character σ else 0))`. Introduce `σ`. Simplify using `only [swanCharacter]`.

Use `push_cast`. Apply the tactic sequence `split_ifs with h1 h2 <;> (try subst h1) <;> ring`. Rewrite using `[Finset.sum_congr rfl fun σ _ ↦ hpt σ, Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq', if_pos (Finset.mem_univ _), ← Finset.mul_sum, hsub]`. Rewrite using `[hswan, artinConductor_eq_charArtinConductor, hc, hc', charSwanConductor, charArtinConductor, hsum, hcard]`. Clear the denominators using the available nonvanishing facts.
-/
theorem swanConductor_eq_charSwanConductor [IsGalois K L] (ρ : Representation ℂ (L ≃ₐ[K] L) V) :
    (swanConductor ρ : ℂ) = charSwanConductor K L ρ.character := by
  classical
  have hG0 : (Nat.card (lowerRamificationGroup K L 0) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hf : (residueDegree K L : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (residueDegree_pos K L).ne'
  have hcard : (Nat.card (L ≃ₐ[K] L) : ℂ) =
      Nat.card (lowerRamificationGroup K L 0) * residueDegree K L := by
    exact_mod_cast card_aut_eq_card_lowerRamificationGroup_zero_mul
  have hsub : ∑ σ : L ≃ₐ[K] L,
      (if σ ∈ lowerRamificationGroup K L 0 then ρ.character σ else 0) =
        ∑ h : lowerRamificationGroup K L 0, ρ.character h := by
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype _ (by simp) _
  have hc := codim_invariants_eq (ρ.comp (lowerRamificationGroup K L 0).subtype)
  have hc' : ∑ h : lowerRamificationGroup K L 0,
      (Representation.character (ρ.comp (lowerRamificationGroup K L 0).subtype) 1 -
        Representation.character (ρ.comp (lowerRamificationGroup K L 0).subtype) h) =
      Nat.card (lowerRamificationGroup K L 0) * ρ.character 1 -
        ∑ h : lowerRamificationGroup K L 0, ρ.character h := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      Nat.card_eq_fintype_card]
    rfl
  have hsplit := artinConductor_eq_codim_add_swanConductor ρ
  have hswan : (swanConductor ρ : ℂ) = (artinConductor ρ : ℂ) -
      ((finrank ℂ V - finrank ℂ (invariants (ρ.comp (lowerRamificationGroup K L 0).subtype)) : ℕ)
        : ℂ) := by
    rw [hsplit]
    push_cast
    ring
  have hsum : ∑ σ : L ≃ₐ[K] L, ρ.character σ * (swanCharacter K L σ : ℂ) =
      ∑ σ : L ≃ₐ[K] L, ρ.character σ * (artinCharacter K L σ : ℂ) -
        (Nat.card (L ≃ₐ[K] L) * ρ.character 1 -
          residueDegree K L * ∑ h : lowerRamificationGroup K L 0, ρ.character h) := by
    have hpt : ∀ σ : L ≃ₐ[K] L, ρ.character σ * (swanCharacter K L σ : ℂ) =
        ρ.character σ * artinCharacter K L σ -
          ((if σ = 1 then (Nat.card (L ≃ₐ[K] L) : ℂ) * ρ.character 1 else 0) -
            residueDegree K L *
              (if σ ∈ lowerRamificationGroup K L 0 then ρ.character σ else 0)) := by
      intro σ
      simp only [swanCharacter]
      push_cast
      split_ifs with h1 h2 <;> (try subst h1) <;> ring
    rw [Finset.sum_congr rfl fun σ _ ↦ hpt σ, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      Finset.sum_ite_eq', if_pos (Finset.mem_univ _), ← Finset.mul_sum, hsub]
  rw [hswan, artinConductor_eq_charArtinConductor, hc, hc', charSwanConductor, charArtinConductor,
    hsum, hcard]
  field_simp

end Swan

end GroundTheory.LocalField
