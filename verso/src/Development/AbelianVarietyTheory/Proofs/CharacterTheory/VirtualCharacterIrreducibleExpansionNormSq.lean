import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterOverSubfieldInductionIrreducibleStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.FiniteGroupFunctionPairingSelfIrreducibleAlgClosStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.MemVirtualCharactersIffSubCharactersStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.StarVirtualCharacterEqApplyInvStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.FiniteGroupFunctionPairingEqZeroOfDistinctIrreduStatement
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
noncomputable section
namespace GlobalTheory.BI

open Polynomial in
/- English proof (translation)
Use `_root_.GlobalTheory.BI.isChar_induction ℂ ℂ G (fun a => ∃ c : (G → ℂ) →₀ ℤ, (∀ χ ∈ c.support, _root_.GlobalTheory.BI.IsIrrChar ℂ ℂ χ) ∧ a = c.sum (fun χ m => m • χ)) ⟨0, by simp, by simp⟩ ?_ a ha` and prove the remaining obligations. Introduce and unpack `φ b hφ - ⟨c, hc, rfl⟩`. Use `⟨Finsupp.single φ 1 + c, fun χ hχ => ?_, ?_⟩` and prove the remaining obligations. Break down `Finset.mem_union.1 (Finsupp.support_add hχ) with h | h` into its components or cases. Rewrite `h`, `with`, `e` using `[Finsupp.mem_support_iff, Finsupp.single_apply] at h split_ifs`.

Conclude with `e ▸ hφ`. Conclude with `absurd rfl h`. Conclude with `hc χ h`. Rewrite using `[Finsupp.sum_add_index' (by simp) (fun _ _ _ => add_smul _ _ _), Finsupp.sum_single_index (by simp), one_smul]`.
-/
private theorem exists_irreducible_expansion_of_isCharacter_lemma_3 {G : Type} [Group G] [Finite G]
    (a : G → ℂ) (ha : _root_.GlobalTheory.BI.IsChar ℂ ℂ a) :
    ∃ c : (G → ℂ) →₀ ℤ, (∀ χ ∈ c.support, _root_.GlobalTheory.BI.IsIrrChar ℂ ℂ χ) ∧
      a = c.sum (fun χ m => m • χ) := by
  classical
  refine _root_.GlobalTheory.BI.isChar_induction ℂ ℂ G
    (fun a => ∃ c : (G → ℂ) →₀ ℤ, (∀ χ ∈ c.support, _root_.GlobalTheory.BI.IsIrrChar ℂ ℂ χ) ∧
      a = c.sum (fun χ m => m • χ)) ⟨0, by simp, by simp⟩ ?_ a ha
  rintro φ b hφ - ⟨c, hc, rfl⟩
  refine ⟨Finsupp.single φ 1 + c, fun χ hχ => ?_, ?_⟩
  · rcases Finset.mem_union.1 (Finsupp.support_add hχ) with h | h
    · rw [Finsupp.mem_support_iff, Finsupp.single_apply] at h
      split_ifs at h with e
      · exact e ▸ hφ
      · exact absurd rfl h
    · exact hc χ h
  · rw [Finsupp.sum_add_index' (by simp) (fun _ _ _ => add_smul _ _ _),
      Finsupp.sum_single_index (by simp), one_smul]

open Polynomial in
/- English proof (translation)
Take `⟨a, b, ha, hb, rfl⟩` from `(_root_.GlobalTheory.BI.mem_virt_iff_sub ℂ ℂ G φ).1 hφ`. Take `⟨ca, hca, rfl⟩` from `exists_irreducible_expansion_of_isCharacter_lemma_3 a ha`. Take `⟨cb, hcb, rfl⟩` from `exists_irreducible_expansion_of_isCharacter_lemma_3 b hb`. Use `⟨ca - cb, fun χ hχ => ?_, ?_⟩` and prove the remaining obligations. Break down `Finset.mem_union.1 (Finsupp.support_sub hχ) with h | h` into its components or cases.

Conclude with `hca χ h`. Conclude with `hcb χ h`. Rewrite using `[Finsupp.sum_sub_index (fun _ _ _ => sub_smul _ _ _)]`.
-/
private theorem exists_irreducible_expansion_of_mem_lemma {G : Type} [Group G] [Finite G]
    (φ : G → ℂ) (hφ : φ ∈ _root_.GlobalTheory.BI.Virt ℂ ℂ G) :
    ∃ c : (G → ℂ) →₀ ℤ, (∀ χ ∈ c.support, _root_.GlobalTheory.BI.IsIrrChar ℂ ℂ χ) ∧
      φ = c.sum (fun χ m => m • χ) := by
  classical
  obtain ⟨a, b, ha, hb, rfl⟩ := (_root_.GlobalTheory.BI.mem_virt_iff_sub ℂ ℂ G φ).1 hφ
  obtain ⟨ca, hca, rfl⟩ := exists_irreducible_expansion_of_isCharacter_lemma_3 a ha
  obtain ⟨cb, hcb, rfl⟩ := exists_irreducible_expansion_of_isCharacter_lemma_3 b hb
  refine ⟨ca - cb, fun χ hχ => ?_, ?_⟩
  · rcases Finset.mem_union.1 (Finsupp.support_sub hχ) with h | h
    · exact hca χ h
    · exact hcb χ h
  · rw [Finsupp.sum_sub_index (fun _ _ _ => sub_smul _ _ _)]

open Polynomial in
/- English proof (translation)
Establish `hG : (Nat.card G : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 Nat.card_pos.ne'`. Use `split_ifs with h`. Substitute `h` using the available equality. Use `_root_.GlobalTheory.BI.pair_self_of_isIrrChar_algClosed ℂ G χ hχ` as an intermediate fact. Unfold `_root_.GlobalTheory.BI.pair at this`.

Rewrite `this` using `[inv_mul_eq_one₀ hG, finsum_eq_sum_of_fintype]`. Conclude with `this.symm`. Use `_root_.GlobalTheory.BI.pair_eq_zero_of_isIrrChar_ne G χ ψ hχ hψ h` as an intermediate fact. Unfold `_root_.GlobalTheory.BI.pair at this`. Rewrite `this` using `[finsum_eq_sum_of_fintype]`.

Simplify `this` using `[hG]`.
-/
private theorem sum_mul_inv_irreducible_lemma_2 {G : Type} [Group G] [Fintype G] (χ ψ : G → ℂ)
    (hχ : _root_.GlobalTheory.BI.IsIrrChar ℂ ℂ χ) (hψ : _root_.GlobalTheory.BI.IsIrrChar ℂ ℂ ψ) :
    ∑ g, χ g * ψ g⁻¹ = if χ = ψ then (Nat.card G : ℂ) else 0 := by
  classical
  have hG : (Nat.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  split_ifs with h
  · subst h
    have := _root_.GlobalTheory.BI.pair_self_of_isIrrChar_algClosed ℂ G χ hχ
    unfold _root_.GlobalTheory.BI.pair at this
    rw [inv_mul_eq_one₀ hG, finsum_eq_sum_of_fintype] at this
    exact this.symm
  · have := _root_.GlobalTheory.BI.pair_eq_zero_of_isIrrChar_ne G χ ψ hχ hψ h
    unfold _root_.GlobalTheory.BI.pair at this
    rw [finsum_eq_sum_of_fintype] at this
    simpa [hG] using this

open Polynomial in

/- English proof (translation)
Introduce `G _ _ φ hφ`. Use `haveI := Fintype.ofFinite G`. Take `⟨c, hc, he⟩` from `exists_irreducible_expansion_of_mem_lemma φ hφ`. Use `⟨c, hc, he, ?_⟩` and prove the remaining obligations. Establish `hev : ∀ g, φ g = ∑ χ ∈ c.support, (c χ : ℂ) * χ g`.

Introduce `g`. Rewrite using `[he, Finsupp.sum, Finset.sum_apply]`. Simplify using `[zsmul_eq_mul]`. Rewrite using `[finsum_eq_sum_of_fintype]`. Repeatedly rewrite using `[_root_.GlobalTheory.CuspGL.star_virt_eq_inv G φ hφ, hev, Finset.sum_mul_sum]`.

Rewrite using `[Finset.sum_comm]`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl fun χ _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun ψ _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun g _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Use `_ = ∑ χ ∈ c.support, (c χ : ℂ) ^ 2 * (Nat.card G : ℂ) := by`. Use `Finset.sum_congr rfl fun χ hχ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.sum_congr rfl fun ψ hψ => by rw [sum_mul_inv_irreducible_lemma_2 χ ψ (hc χ hχ) (hc ψ hψ)]]`. Simplify using `only [mul_ite, mul_zero]`. Rewrite using `[Finset.sum_ite_eq c.support χ, if_pos hχ]`. Expand and normalize the polynomial expressions, which then agree. Use `_ = _ := by rw [Finsupp.sum, Finset.sum_mul]`.
-/
theorem _root_.GlobalTheory.BI.virt_expand : ∀ (G : Type) [Group G] [Finite G]
    (φ : G → ℂ), φ ∈ _root_.GlobalTheory.BI.Virt ℂ ℂ G →
    ∃ c : (G → ℂ) →₀ ℤ, (∀ χ ∈ c.support, _root_.GlobalTheory.BI.IsIrrChar ℂ ℂ χ) ∧
      φ = c.sum (fun χ m => m • χ) ∧
      ∑ᶠ g, φ g * star (φ g) = (c.sum fun _ m => (m : ℂ) ^ 2) * (Nat.card G : ℂ) := by
  intro G _ _ φ hφ
  classical
  haveI := Fintype.ofFinite G
  obtain ⟨c, hc, he⟩ := exists_irreducible_expansion_of_mem_lemma φ hφ
  refine ⟨c, hc, he, ?_⟩
  have hev : ∀ g, φ g = ∑ χ ∈ c.support, (c χ : ℂ) * χ g := by
    intro g
    rw [he, Finsupp.sum, Finset.sum_apply]
    simp [zsmul_eq_mul]
  rw [finsum_eq_sum_of_fintype]
  simp_rw [_root_.GlobalTheory.CuspGL.star_virt_eq_inv G φ hφ, hev, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  calc ∑ χ ∈ c.support, ∑ g, ∑ ψ ∈ c.support, (c χ : ℂ) * χ g * ((c ψ : ℂ) * ψ g⁻¹)
      = ∑ χ ∈ c.support, ∑ ψ ∈ c.support, (c χ : ℂ) * c ψ * ∑ g, χ g * ψ g⁻¹ := by
        refine Finset.sum_congr rfl fun χ _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun ψ _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun g _ => ?_
        ring
    _ = ∑ χ ∈ c.support, (c χ : ℂ) ^ 2 * (Nat.card G : ℂ) := by
        refine Finset.sum_congr rfl fun χ hχ => ?_
        rw [Finset.sum_congr rfl fun ψ hψ => by rw [sum_mul_inv_irreducible_lemma_2 χ ψ (hc χ hχ) (hc ψ hψ)]]
        simp only [mul_ite, mul_zero]
        rw [Finset.sum_ite_eq c.support χ, if_pos hχ]
        ring
    _ = _ := by rw [Finsupp.sum, Finset.sum_mul]

end GlobalTheory.BI
