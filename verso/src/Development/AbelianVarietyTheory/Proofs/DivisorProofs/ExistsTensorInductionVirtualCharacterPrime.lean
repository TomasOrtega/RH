import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.MemVirtualCharactersIffSubCharacters
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorInductionCharStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVirtualCharacterSemidirectOrbitCrossTermsStatement
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
namespace GlobalTheory.Shin

/- English proof (translation)
Introduce `G Γ _ _ _ _ φ s hp hs χ hχ`. Establish `hgen : ∀ t : Γ, t ∈ Subgroup.zpowers s` using `by haveI : Fact (Nat.card Γ).Prime := ⟨hp⟩`. Introduce `t`. Conclude with `mem_zpowers_of_prime_card rfl hs`. Take `⟨a, b, ha, hb, rfl⟩` from `(mem_virt_iff_sub ℂ ℂ G χ).1 hχ`.

Take `⟨A, hA, hA1, hA2⟩` from `GlobalTheory.T.exists_tensorInduction_char' G Γ φ s hgen a ha`. Take `⟨B, hB, hB1, hB2⟩` from `GlobalTheory.T.exists_tensorInduction_char' G Γ φ s hgen b hb`. Take `⟨Z, hZ, hZ1, hZ2⟩` from `GlobalTheory.T.exists_virtualCharacter_semidirect_orbit_cross_terms G Γ φ s hp hs (a - b) b ((mem_virt_iff_sub ℂ ℂ G _).2 ⟨a, b, ha, hb, rfl⟩) ((mem_virt_iff_sub ℂ ℂ G b).2 ⟨b, 0, hb, (GlobalTheory.T.isCharacterOverSubfield_zero_and_add ℂ ℂ G).1, by simp⟩)`. Establish `hAv : A ∈ Virt ℂ ℂ (G ⋊[φ] Γ)` using `AddSubgroup.subset_closure hA`. Establish `hBv : B ∈ Virt ℂ ℂ (G ⋊[φ] Γ)` using `AddSubgroup.subset_closure hB`.

Use `⟨A - B - Z, (Virt ℂ ℂ _).sub_mem ((Virt ℂ ℂ _).sub_mem hAv hBv) hZ, ?_, ?_⟩` and prove the remaining obligations. Introduce `g`. Simplify using `only [Pi.sub_apply, hA1, hB1, hZ1, sub_add_cancel]`. Expand and normalize the polynomial expressions, which then agree. Introduce `δ`.

Simplify using `only [Pi.sub_apply, hA2, hB2, hZ2, sub_zero]`.
-/
theorem tensorInd_virt_prime : ∀ (G Γ : Type) [Group G] [Finite G] [Group Γ] [Fintype Γ] (φ : Γ →* MulAut G) (s : Γ), (Nat.card Γ).Prime → s ≠ 1 → ∀ χ ∈ Virt ℂ ℂ G, ∃ X ∈ Virt ℂ ℂ (G ⋊[φ] Γ), (∀ g, X (inl g) = ∏ t : Γ, χ (φ t g)) ∧ ∀ δ, X (inl δ * inr s) = χ (nrmG φ s (Nat.card Γ) δ) := by
  intro G Γ _ _ _ _ φ s hp hs χ hχ
  have hgen : ∀ t : Γ, t ∈ Subgroup.zpowers s := by
    haveI : Fact (Nat.card Γ).Prime := ⟨hp⟩
    intro t
    exact mem_zpowers_of_prime_card rfl hs
  obtain ⟨a, b, ha, hb, rfl⟩ := (mem_virt_iff_sub ℂ ℂ G χ).1 hχ
  obtain ⟨A, hA, hA1, hA2⟩ := GlobalTheory.T.exists_tensorInduction_char' G Γ φ s hgen a ha
  obtain ⟨B, hB, hB1, hB2⟩ := GlobalTheory.T.exists_tensorInduction_char' G Γ φ s hgen b hb
  obtain ⟨Z, hZ, hZ1, hZ2⟩ := GlobalTheory.T.exists_virtualCharacter_semidirect_orbit_cross_terms G Γ φ s hp hs (a - b) b
    ((mem_virt_iff_sub ℂ ℂ G _).2 ⟨a, b, ha, hb, rfl⟩)
    ((mem_virt_iff_sub ℂ ℂ G b).2 ⟨b, 0, hb, (GlobalTheory.T.isCharacterOverSubfield_zero_and_add ℂ ℂ G).1, by simp⟩)
  have hAv : A ∈ Virt ℂ ℂ (G ⋊[φ] Γ) := AddSubgroup.subset_closure hA
  have hBv : B ∈ Virt ℂ ℂ (G ⋊[φ] Γ) := AddSubgroup.subset_closure hB
  refine ⟨A - B - Z, (Virt ℂ ℂ _).sub_mem ((Virt ℂ ℂ _).sub_mem hAv hBv) hZ, ?_, ?_⟩
  · intro g
    simp only [Pi.sub_apply, hA1, hB1, hZ1, sub_add_cancel]
    ring
  · intro δ
    simp only [Pi.sub_apply, hA2, hB2, hZ2, sub_zero]

end GlobalTheory.Shin
