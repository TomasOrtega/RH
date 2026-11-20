import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterOverSubfieldRestrictClassFunctionOne
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.VirtualCharacterIrreducibleExpansionNormSqStatement

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
namespace GlobalTheory.BI

/- English proof (translation)
Simplify using `only [Finsupp.sum] at h`. Establish `hge : ∀ b ∈ c.support, (1 : ℤ) ≤ c b ^ 2`. Introduce `b hb`. Establish `hb' : c b ≠ 0` using `Finsupp.mem_support_iff.mp hb`. Apply the tactic sequence `rcases lt_or_gt_of_ne hb' with hlt | hgt <;> nlinarith`.

Establish `hle : (c.support.card : ℤ) ≤ 1`. Combine the equalities or inequalities in the displayed calculation. Establish `hne : c.support.Nonempty`. Rewrite using `[Finset.nonempty_iff_ne_empty]`. Introduce `he`.

Rewrite `h` using `[he, Finset.sum_empty]`. Conclude with `zero_ne_one h`. Establish `hcard : c.support.card = 1`. Use `hne.card_pos` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Take `⟨a, ha⟩` from `Finset.card_eq_one.mp hcard`. Use `⟨a, ha, ?_⟩` and prove the remaining obligations. Rewrite `h` using `[ha, Finset.sum_singleton]`. Establish `h1 : c a ≤ 1` using `by nlinarith`. Establish `h2 : -1 ≤ c a` using `by nlinarith`.

Establish `h3 : c a ≠ 0`. Introduce `h0`. Rewrite `h` using `[h0]`. Evaluate the numerical expressions using `at h`. Use linear arithmetic over natural numbers and integers.
-/
theorem finsupp_eq_single_of_sum_sq_eq_one {α : Type} (c : α →₀ ℤ)
    (h : (c.sum fun _ m => m ^ 2) = 1) :
    ∃ a, c.support = {a} ∧ (c a = 1 ∨ c a = -1) := by
  simp only [Finsupp.sum] at h
  have hge : ∀ b ∈ c.support, (1 : ℤ) ≤ c b ^ 2 := by
    intro b hb
    have hb' : c b ≠ 0 := Finsupp.mem_support_iff.mp hb
    rcases lt_or_gt_of_ne hb' with hlt | hgt <;> nlinarith
  have hle : (c.support.card : ℤ) ≤ 1 := by
    calc (c.support.card : ℤ) = ∑ _b ∈ c.support, (1 : ℤ) := by simp
      _ ≤ ∑ b ∈ c.support, c b ^ 2 := Finset.sum_le_sum hge
      _ = 1 := h
  have hne : c.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    rw [he, Finset.sum_empty] at h
    exact zero_ne_one h
  have hcard : c.support.card = 1 := by
    have := hne.card_pos
    omega
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcard
  refine ⟨a, ha, ?_⟩
  rw [ha, Finset.sum_singleton] at h
  have h1 : c a ≤ 1 := by nlinarith
  have h2 : -1 ≤ c a := by nlinarith
  have h3 : c a ≠ 0 := by
    intro h0
    rw [h0] at h
    norm_num at h
  omega

/- English proof (translation)
Take `⟨n, ρ, hρ, hχ⟩` from `h`. Use `⟨n, ?_, ?_⟩` and prove the remaining obligations. Establish `hs : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule` using `(Representation.irreducible_iff_isSimpleModule_asModule ρ).mp hρ`. Establish `hnt : Nontrivial ρ.asModule` using `IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) _`. Break down `Nat.eq_zero_or_pos n with h0 | hn` into its components or cases.

It suffices to derive a contradiction. Substitute `h0` using the available equality. Take `⟨x, y, hxy⟩` from `hnt`. Conclude with `hxy (Subsingleton.elim (α := Fin 0 → ℂ) x y)`. Conclude with `hn`.

Rewrite using `[hχ, Representation.char_one]`. Simplify using the standard rewrite rules.
-/
private theorem exists_pos_nat_apply_one_of_isIrrChar {G : Type} [Group G] (χ : G → ℂ) (h : IsIrrChar ℂ ℂ χ) :
    ∃ n : ℕ, 0 < n ∧ χ 1 = n := by
  obtain ⟨n, ρ, hρ, hχ⟩ := h
  refine ⟨n, ?_, ?_⟩
  · have hs : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule :=
      (Representation.irreducible_iff_isSimpleModule_asModule ρ).mp hρ
    have hnt : Nontrivial ρ.asModule := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) _
    rcases Nat.eq_zero_or_pos n with h0 | hn
    · exfalso
      subst h0
      obtain ⟨x, y, hxy⟩ := hnt
      exact hxy (Subsingleton.elim (α := Fin 0 → ℂ) x y)
    · exact hn
  · rw [hχ, Representation.char_one]
    simp

/- English proof (translation)
Introduce `G _ _ φ hφ hnorm`. Take `⟨c, hirr, hsum, hsq⟩` from `GlobalTheory.T.virtualCharacter_irreducible_expansion_normSq G φ hφ`. Establish `hG : (Nat.card G : ℂ) ≠ 0` using `by exact_mod_cast Nat.card_pos.ne'`. Establish `h1 : (c.sum fun _ m => (m : ℂ) ^ 2) = 1` using `mul_right_cancel₀ hG ((hsq.symm.trans hnorm).trans (one_mul _).symm)`. Establish `h2 : (c.sum fun _ m => m ^ 2) = 1`.

Simplify using `only [Finsupp.sum] at h1 ⊢`. Conclude with `h1` after adjusting the coercions. Take `⟨χ, hsupp, hc⟩` from `finsupp_eq_single_of_sum_sq_eq_one c h2`. Establish `hχ : IsIrrChar ℂ ℂ χ` using `hirr χ (by rw [hsupp]; exact Finset.mem_singleton_self χ)`. Establish `hφχ : φ = c χ • χ`.

Rewrite using `[hsum, Finsupp.sum, hsupp, Finset.sum_singleton]`. Establish `key : φ = χ ∨ φ = -χ`. Break down `hc with h | h` into its components or cases. Use `left`. Rewrite using `[hφχ, h, one_smul]`.

Use `right`. Rewrite using `[hφχ, h, neg_smul, one_smul]`. Take `⟨n, hn, hn1⟩` from `exists_pos_nat_apply_one_of_isIrrChar χ hχ`. Break down `key with rfl | rfl` into its components or cases. Conclude with `⟨Or.inl hχ, fun _ => ⟨hχ, n, hn, hn1⟩⟩`.

Use `⟨Or.inr (by simpa using hχ), fun hc' => ?_⟩` and prove the remaining obligations. It suffices to derive a contradiction. Take `⟨-, -, m, hm, -⟩` from `GlobalTheory.isChar_restrict_conj_one ℂ ℂ G (-χ) hc'`. Establish `h3 : ((m + n : ℕ) : ℂ) = 0`. Use `push_cast`.

Rewrite using `[← hm, ← hn1, Pi.neg_apply]`. Expand and normalize the polynomial expressions, which then agree. Establish `h4 : m + n = 0` using `by exact_mod_cast h3`. Use linear arithmetic over natural numbers and integers.
-/
theorem irr_of_norm_one : ∀ (G : Type) [Group G] [Finite G] (φ : G → ℂ), φ ∈ Virt ℂ ℂ G → ∑ᶠ g, φ g * star (φ g) = (Nat.card G : ℂ) → (IsIrrChar ℂ ℂ φ ∨ IsIrrChar ℂ ℂ (-φ)) ∧ (IsChar ℂ ℂ φ → IsIrrChar ℂ ℂ φ ∧ ∃ n : ℕ, 0 < n ∧ φ 1 = n) := by
  intro G _ _ φ hφ hnorm
  obtain ⟨c, hirr, hsum, hsq⟩ := GlobalTheory.T.virtualCharacter_irreducible_expansion_normSq G φ hφ
  have hG : (Nat.card G : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have h1 : (c.sum fun _ m => (m : ℂ) ^ 2) = 1 :=
    mul_right_cancel₀ hG ((hsq.symm.trans hnorm).trans (one_mul _).symm)
  have h2 : (c.sum fun _ m => m ^ 2) = 1 := by
    simp only [Finsupp.sum] at h1 ⊢
    exact_mod_cast h1
  obtain ⟨χ, hsupp, hc⟩ := finsupp_eq_single_of_sum_sq_eq_one c h2
  have hχ : IsIrrChar ℂ ℂ χ := hirr χ (by rw [hsupp]; exact Finset.mem_singleton_self χ)
  have hφχ : φ = c χ • χ := by
    rw [hsum, Finsupp.sum, hsupp, Finset.sum_singleton]
  have key : φ = χ ∨ φ = -χ := by
    rcases hc with h | h
    · left
      rw [hφχ, h, one_smul]
    · right
      rw [hφχ, h, neg_smul, one_smul]
  obtain ⟨n, hn, hn1⟩ := exists_pos_nat_apply_one_of_isIrrChar χ hχ
  rcases key with rfl | rfl
  · exact ⟨Or.inl hχ, fun _ => ⟨hχ, n, hn, hn1⟩⟩
  · refine ⟨Or.inr (by simpa using hχ), fun hc' => ?_⟩
    exfalso
    obtain ⟨-, -, m, hm, -⟩ := GlobalTheory.isChar_restrict_conj_one ℂ ℂ G (-χ) hc'
    have h3 : ((m + n : ℕ) : ℂ) = 0 := by
      push_cast
      rw [← hm, ← hn1, Pi.neg_apply]
      ring
    have h4 : m + n = 0 := by exact_mod_cast h3
    omega

end GlobalTheory.BI
