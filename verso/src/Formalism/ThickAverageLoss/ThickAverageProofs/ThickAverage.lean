import Formalism.ThickAverageLoss.ParametersAveragedDifferenceBound
import Formalism.ThickAverageLoss.PartnersToFactorsAt

open Finset

noncomputable section

namespace Formalism.D5

open Formalism Formalism.CMTypeGaloisData Formalism.WT Formalism.WeightedSieveThreeParameter

section
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

/- English proof (translation)
Use `first`. Consider the case `(revert x; decide)`. Consider the case `(fin_cases x <;> simp)`.
-/
lemma zmod_two_cases_bis (x : ZMod 2) : x = 0 ∨ x = 1 := by
  first
    | (revert x; decide)
    | (fin_cases x <;> simp)

/- English proof (translation)
Evaluate the decidable proposition.
-/
lemma zmod_two_one_add_one : (1 : ZMod 2) + 1 = 0 := by
  decide

/- English proof (translation)
Evaluate the decidable proposition.
-/
lemma zmod_two_one_ne_zero : (1 : ZMod 2) ≠ 0 := by
  decide

/- English proof (translation)
Evaluate the decidable proposition.
-/
lemma zmod_two_neg_one : -(1 : ZMod 2) = 1 := by
  decide

/- English proof (translation)
Simplify using `[sgn2]`.
-/
lemma signZModTwo_zero : sgn2 0 = 1 := by
  simp [sgn2]

/- English proof (translation)
Simplify using `[sgn2, zmod_two_one_ne_zero]`.
-/
lemma signZModTwo_one : sgn2 1 = -1 := by
  simp [sgn2, zmod_two_one_ne_zero]

def e10 : E0 × H := (((1 : ZMod 2), (0 : ZMod 2)), 0)

def e01 : E0 × H := (((0 : ZMod 2), (1 : ZMod 2)), 0)

/- English proof (translation)
Establish `h1 : PhiSet (H` using `H) = (Finset.univ.filter (fun e : E0 => e.1 = 0)) ×ˢ (Finset.univ : Finset H) := by`. Use extensionality with `⟨⟨a, b⟩, h⟩`. Simplify using `[PhiSet, InPhi]`. Establish `h2 : (Finset.univ.filter (fun e : E0 => e.1 = 0)).card = 2` using `by first`. Consider the case `decide`.

Consider the case `rfl`. Rewrite using `[h1, Finset.card_product, h2, Finset.card_univ]`.
-/
lemma phiSet_card : (PhiSet (H := H)).card = 2 * Fintype.card H := by
  have h1 : PhiSet (H := H) =
      (Finset.univ.filter (fun e : E0 => e.1 = 0)) ×ˢ (Finset.univ : Finset H) := by
    ext ⟨⟨a, b⟩, h⟩
    simp [PhiSet, InPhi]
  have h2 : (Finset.univ.filter (fun e : E0 => e.1 = 0)).card = 2 := by
    first
      | decide
      | rfl
  rw [h1, Finset.card_product, h2, Finset.card_univ]

def TrivH (ψ : AddChar (E0 × H) ℂ) : Prop := ∀ h : H, ψ ((0, 0), h) = 1

open Classical in
/- English proof (translation)
Use `split_ifs with hT`. Establish `hT' : ∀ h : H, ψ ((0, 0), h) = 1` using `hT`. Simplify using `[hT']`. Establish `hT' : ¬ ∀ h : H, ψ ((0, 0), h) = 1` using `hT push_neg at hT'`. Take `⟨h0, hh0⟩` from `hT'`.

Establish `key : ψ ((0, 0), h0) * ∑ h : H, ψ ((0, 0), h) = ∑ h : H, ψ ((0, 0), h)`. Rewrite using `[Finset.mul_sum]`. Use `Fintype.sum_equiv (Equiv.addLeft h0) _ _ (fun h => ?_)` and prove the remaining obligations. Use `show ψ ((0, 0), h0) * ψ ((0, 0), h) = ψ ((0, 0), h0 + h)`. Rewrite using `[← AddChar.map_add_eq_mul]`.

Use `congr 1`. Apply the tactic sequence `all_goals (ext <;> simp)`. Establish `h2 : (ψ ((0, 0), h0) - 1) * ∑ h : H, ψ ((0, 0), h) = 0`. Rewrite using `[sub_mul, key, one_mul, sub_self]`. Break down `mul_eq_zero.mp h2 with h3 | h3` into its components or cases.

Conclude with `absurd (sub_eq_zero.mp h3) hh0`. Conclude with `h3`.
-/
lemma sum_H (ψ : AddChar (E0 × H) ℂ) :
    ∑ h : H, ψ ((0, 0), h) = if TrivH ψ then (Fintype.card H : ℂ) else 0 := by
  split_ifs with hT
  · have hT' : ∀ h : H, ψ ((0, 0), h) = 1 := hT
    simp [hT']
  · have hT' : ¬ ∀ h : H, ψ ((0, 0), h) = 1 := hT
    push_neg at hT'
    obtain ⟨h0, hh0⟩ := hT'
    have key : ψ ((0, 0), h0) * ∑ h : H, ψ ((0, 0), h) = ∑ h : H, ψ ((0, 0), h) := by
      rw [Finset.mul_sum]
      refine Fintype.sum_equiv (Equiv.addLeft h0) _ _ (fun h => ?_)
      show ψ ((0, 0), h0) * ψ ((0, 0), h) = ψ ((0, 0), h0 + h)
      rw [← AddChar.map_add_eq_mul]
      congr 1
      all_goals (ext <;> simp)
    have h2 : (ψ ((0, 0), h0) - 1) * ∑ h : H, ψ ((0, 0), h) = 0 := by
      rw [sub_mul, key, one_mul, sub_self]
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact absurd (sub_eq_zero.mp h3) hh0
    · exact h3

/- English proof (translation)
Take `⟨⟨a, b⟩, h⟩` from `g`. Establish `h0 : ψ ((0, 0), h) = 1` using `hψ h`. Apply the tactic sequence `rcases zmod_two_cases_bis a with rfl | rfl <;> rcases zmod_two_cases_bis b with rfl | rfl`. Simplify using `[h0]`. Establish `e : ((((0 : ZMod 2), (1 : ZMod 2)), h) : E0 × H) = e01 + ((0, 0), h)` using `by simp [e01] conv_lhs => rw [e]`.

Rewrite using `[AddChar.map_add_eq_mul, h0]`. Simplify using `[zmod_two_one_ne_zero]`. Establish `e : ((((1 : ZMod 2), (0 : ZMod 2)), h) : E0 × H) = e10 + ((0, 0), h)` using `by simp [e10] conv_lhs => rw [e]`. Rewrite using `[AddChar.map_add_eq_mul, h0]`. Simplify using `[zmod_two_one_ne_zero]`.

Establish `e : ((((1 : ZMod 2), (1 : ZMod 2)), h) : E0 × H) = e10 + e01 + ((0, 0), h)`. Simplify using `[e10, e01]`. Use `conv_lhs => rw [e]`. Rewrite using `[AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, h0]`. Simplify using `[zmod_two_one_ne_zero]`.
-/
lemma trivH_formula (ψ : AddChar (E0 × H) ℂ) (hψ : TrivH ψ) (g : E0 × H) :
    ψ g = (if g.1.1 = 0 then 1 else ψ e10) * (if g.1.2 = 0 then 1 else ψ e01) := by
  obtain ⟨⟨a, b⟩, h⟩ := g
  have h0 : ψ ((0, 0), h) = 1 := hψ h
  rcases zmod_two_cases_bis a with rfl | rfl <;> rcases zmod_two_cases_bis b with rfl | rfl
  · simp [h0]
  · have e : ((((0 : ZMod 2), (1 : ZMod 2)), h) : E0 × H) = e01 + ((0, 0), h) := by simp [e01]
    conv_lhs => rw [e]
    rw [AddChar.map_add_eq_mul, h0]
    simp [zmod_two_one_ne_zero]
  · have e : ((((1 : ZMod 2), (0 : ZMod 2)), h) : E0 × H) = e10 + ((0, 0), h) := by simp [e10]
    conv_lhs => rw [e]
    rw [AddChar.map_add_eq_mul, h0]
    simp [zmod_two_one_ne_zero]
  · have e : ((((1 : ZMod 2), (1 : ZMod 2)), h) : E0 × H) = e10 + e01 + ((0, 0), h) := by
      simp [e10, e01]
    conv_lhs => rw [e]
    rw [AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, h0]
    simp [zmod_two_one_ne_zero]

/- English proof (translation)
Rewrite using `[← AddChar.map_add_eq_mul, hg, AddChar.map_zero_eq_one]`.
-/
lemma sq_one_of_order2 (ψ : AddChar (E0 × H) ℂ) (g : E0 × H) (hg : g + g = 0) : ψ g * ψ g = 1 := by
  rw [← AddChar.map_add_eq_mul, hg, AddChar.map_zero_eq_one]

/- English proof (translation)
Establish `h2 : (2 : ZMod 2) = 0` using `by decide`. Simplify using `[e10, zmod_two_one_add_one, h2]`.
-/
lemma firstBasis_add_self : (e10 : E0 × H) + e10 = 0 := by
  have h2 : (2 : ZMod 2) = 0 := by decide
  simp [e10, zmod_two_one_add_one, h2]

/- English proof (translation)
Establish `h2 : (2 : ZMod 2) = 0` using `by decide`. Simplify using `[e01, zmod_two_one_add_one, h2]`.
-/
lemma secondBasis_add_self : (e01 : E0 × H) + e01 = 0 := by
  have h2 : (2 : ZMod 2) = 0 := by decide
  simp [e01, zmod_two_one_add_one, h2]

/- English proof (translation)
Establish `hx` using `sq_one_of_order2 ψ e10 firstBasis_add_self`. Establish `hy` using `sq_one_of_order2 ψ e01 secondBasis_add_self`. Establish `key : ∀ g : E0 × H, ψ g = (if g.1.1 = 0 then 1 else ψ e10) * (if g.1.2 = 0 then 1 else ψ e01)` using `trivH_formula ψ hψ`. Apply the tactic sequence `rcases mul_self_eq_one_iff.mp hx with hx1 | hx1 <;>`. Break down `mul_self_eq_one_iff.mp hy with hy1 | hy1` into its components or cases.

Use `left`. Use extensionality with `⟨⟨a, b⟩, h⟩`. Rewrite using `[key, hx1, hy1, AddChar.zero_apply]`. Simplify using the standard rewrite rules. Use `right`.

Use `right`. Use `left`. Use extensionality with `⟨⟨a, b⟩, h⟩`. Rewrite using `[key, hx1, hy1, Hs.psC_apply]`. Apply the tactic sequence `rcases zmod_two_cases_bis b with rfl | rfl <;> simp [signZModTwo_zero, signZModTwo_one, zmod_two_one_ne_zero]`.

Use `right`. Use `left`. Use extensionality with `⟨⟨a, b⟩, h⟩`. Rewrite using `[key, hx1, hy1, Hs.chC_apply]`. Apply the tactic sequence `rcases zmod_two_cases_bis a with rfl | rfl <;> simp [signZModTwo_zero, signZModTwo_one, zmod_two_one_ne_zero]`.

Use `right`. Use `right`. Use `right`. Use extensionality with `⟨⟨a, b⟩, h⟩`. Rewrite using `[key, hx1, hy1, Hs.chpsC_apply]`.

Apply the tactic sequence `rcases zmod_two_cases_bis a with rfl | rfl <;> rcases zmod_two_cases_bis b with rfl | rfl <;>`. Simplify using `[signZModTwo_zero, signZModTwo_one, zmod_two_one_ne_zero]`.
-/
lemma trivH_cases (Hs : CycHost H) (ψ : AddChar (E0 × H) ℂ) (hψ : TrivH ψ) :
    ψ = 0 ∨ ψ = Hs.chC ∨ ψ = Hs.psC ∨ ψ = Hs.chpsC := by
  have hx := sq_one_of_order2 ψ e10 firstBasis_add_self
  have hy := sq_one_of_order2 ψ e01 secondBasis_add_self
  have key : ∀ g : E0 × H,
      ψ g = (if g.1.1 = 0 then 1 else ψ e10) * (if g.1.2 = 0 then 1 else ψ e01) :=
    trivH_formula ψ hψ
  rcases mul_self_eq_one_iff.mp hx with hx1 | hx1 <;>
    rcases mul_self_eq_one_iff.mp hy with hy1 | hy1
  · left
    ext ⟨⟨a, b⟩, h⟩
    rw [key, hx1, hy1, AddChar.zero_apply]
    simp
  · right; right; left
    ext ⟨⟨a, b⟩, h⟩
    rw [key, hx1, hy1, Hs.psC_apply]
    rcases zmod_two_cases_bis b with rfl | rfl <;> simp [signZModTwo_zero, signZModTwo_one, zmod_two_one_ne_zero]
  · right; left
    ext ⟨⟨a, b⟩, h⟩
    rw [key, hx1, hy1, Hs.chC_apply]
    rcases zmod_two_cases_bis a with rfl | rfl <;> simp [signZModTwo_zero, signZModTwo_one, zmod_two_one_ne_zero]
  · right; right; right
    ext ⟨⟨a, b⟩, h⟩
    rw [key, hx1, hy1, Hs.chpsC_apply]
    rcases zmod_two_cases_bis a with rfl | rfl <;> rcases zmod_two_cases_bis b with rfl | rfl <;>
      simp [signZModTwo_zero, signZModTwo_one, zmod_two_one_ne_zero]

/- English proof (translation)
Simplify using `[Hs.chC_apply, e10, signZModTwo_one, signZModTwo_zero]`.
-/
lemma cyclicCharacter_first_basis (Hs : CycHost H) : Hs.chC e10 = -1 := by
  simp [Hs.chC_apply, e10, signZModTwo_one, signZModTwo_zero]
/- English proof (translation)
Simplify using `[Hs.psC_apply, e10, signZModTwo_one, signZModTwo_zero]`.
-/
lemma quadraticCharacter_first_basis (Hs : CycHost H) : Hs.psC e10 = 1 := by
  simp [Hs.psC_apply, e10, signZModTwo_one, signZModTwo_zero]
/- English proof (translation)
Simplify using `[Hs.chpsC_apply, e10, signZModTwo_one, signZModTwo_zero]`.
-/
lemma productCharacter_first_basis (Hs : CycHost H) : Hs.chpsC e10 = -1 := by
  simp [Hs.chpsC_apply, e10, signZModTwo_one, signZModTwo_zero]
/- English proof (translation)
Simplify using `[Hs.chC_apply, e01, signZModTwo_one, signZModTwo_zero]`.
-/
lemma cyclicCharacter_second_basis (Hs : CycHost H) : Hs.chC e01 = 1 := by
  simp [Hs.chC_apply, e01, signZModTwo_one, signZModTwo_zero]
/- English proof (translation)
Simplify using `[Hs.psC_apply, e01, signZModTwo_one, signZModTwo_zero]`.
-/
lemma quadraticCharacter_second_basis (Hs : CycHost H) : Hs.psC e01 = -1 := by
  simp [Hs.psC_apply, e01, signZModTwo_one, signZModTwo_zero]
/- English proof (translation)
Simplify using `[Hs.chpsC_apply, e01, signZModTwo_one, signZModTwo_zero]`.
-/
lemma productCharacter_second_basis (Hs : CycHost H) : Hs.chpsC e01 = -1 := by
  simp [Hs.chpsC_apply, e01, signZModTwo_one, signZModTwo_zero]

/- English proof (translation)
Unfold `TrivH`. Introduce `h`. Simplify using the standard rewrite rules.
-/
lemma trivH_zero : TrivH (0 : AddChar (E0 × H) ℂ) := by
  unfold TrivH
  intro h
  simp
/- English proof (translation)
Unfold `TrivH`. Introduce `h`. Simplify using `[Hs.chC_apply, signZModTwo_zero]`.
-/
lemma trivH_chC (Hs : CycHost H) : TrivH Hs.chC := by
  unfold TrivH
  intro h
  simp [Hs.chC_apply, signZModTwo_zero]
/- English proof (translation)
Unfold `TrivH`. Introduce `h`. Simplify using `[Hs.psC_apply, signZModTwo_zero]`.
-/
lemma trivH_psC (Hs : CycHost H) : TrivH Hs.psC := by
  unfold TrivH
  intro h
  simp [Hs.psC_apply, signZModTwo_zero]
/- English proof (translation)
Unfold `TrivH`. Introduce `h`. Simplify using `[Hs.chpsC_apply, signZModTwo_zero]`.
-/
lemma trivH_chpsC (Hs : CycHost H) : TrivH Hs.chpsC := by
  unfold TrivH
  intro h
  simp [Hs.chpsC_apply, signZModTwo_zero]

/- English proof (translation)
Introduce and unpack `rfl`. Conclude with `h rfl`.
-/
lemma ne_of_val {ψ φ : AddChar (E0 × H) ℂ} (g : E0 × H) (h : ψ g ≠ φ g) : ψ ≠ φ := by
  rintro rfl
  exact h rfl

open Classical in
/- English proof (translation)
Establish `hmem : ∀ ψ : AddChar (E0 × H) ℂ, TrivH ψ ↔ ψ ∈ ({0, Hs.chC, Hs.psC, Hs.chpsC} : Finset (AddChar (E0 × H) ℂ))`. Introduce `ψ`. Simplify using `only [Finset.mem_insert, Finset.mem_singleton]`. Prove the components needed by the constructor for the conclusion. Conclude with `trivH_cases Hs ψ`.

Introduce and unpack `(rfl | rfl | rfl | rfl) exacts [trivH_zero, trivH_chC Hs, trivH_psC Hs, trivH_chpsC Hs]`. Establish `h1 : ∑ ψ ∈ ({0, Hs.chC, Hs.psC, Hs.chpsC} : Finset (AddChar (E0 × H) ℂ)), (if TrivH ψ then ψ e10 * F ψ else 0) = ∑ ψ : AddChar (E0 × H) ℂ, (if TrivH ψ then ψ e10 * F ψ else 0)` using `Finset.sum_subset (Finset.subset_univ _) (fun ψ _ hψ => if_neg (fun h => hψ ((hmem ψ).1 h)))`. Rewrite using `[← h1]`. Establish `n1 : (0 : AddChar (E0 × H) ℂ) ∉ ({Hs.chC, Hs.psC, Hs.chpsC} : Finset (AddChar (E0 × H) ℂ))`. Simplify using `only [Finset.mem_insert, Finset.mem_singleton, not_or]`.

Use `⟨ne_of_val e10 ?_, ne_of_val e01 ?_, ne_of_val e10 ?_⟩` and prove the remaining obligations. Rewrite using `[AddChar.zero_apply, cyclicCharacter_first_basis]`. Evaluate the numerical expressions. Rewrite using `[AddChar.zero_apply, quadraticCharacter_second_basis]`. Evaluate the numerical expressions.

Rewrite using `[AddChar.zero_apply, productCharacter_first_basis]`. Evaluate the numerical expressions. Establish `n2 : Hs.chC ∉ ({Hs.psC, Hs.chpsC} : Finset (AddChar (E0 × H) ℂ))`. Simplify using `only [Finset.mem_insert, Finset.mem_singleton, not_or]`. Use `⟨ne_of_val e10 ?_, ne_of_val e01 ?_⟩` and prove the remaining obligations.

Rewrite using `[cyclicCharacter_first_basis, quadraticCharacter_first_basis]`. Evaluate the numerical expressions. Rewrite using `[cyclicCharacter_second_basis, productCharacter_second_basis]`. Evaluate the numerical expressions. Establish `n3 : Hs.psC ∉ ({Hs.chpsC} : Finset (AddChar (E0 × H) ℂ))`.

Simplify using `only [Finset.mem_singleton]`. Conclude with `ne_of_val e10 (by rw [quadraticCharacter_first_basis, productCharacter_first_basis]; norm_num)`. Rewrite using `[Finset.sum_insert n1, Finset.sum_insert n2, Finset.sum_insert n3, Finset.sum_singleton, if_pos (trivH_zero (H := H)), if_pos (trivH_chC Hs), if_pos (trivH_psC Hs), if_pos (trivH_chpsC Hs), AddChar.zero_apply, cyclicCharacter_first_basis, quadraticCharacter_first_basis, productCh …`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma sum_trivH (Hs : CycHost H) (F : AddChar (E0 × H) ℂ → ℂ) :
    ∑ ψ : AddChar (E0 × H) ℂ, (if TrivH ψ then ψ e10 * F ψ else 0)
      = F 0 + F Hs.psC - F Hs.chC - F Hs.chpsC := by
  have hmem : ∀ ψ : AddChar (E0 × H) ℂ,
      TrivH ψ ↔ ψ ∈ ({0, Hs.chC, Hs.psC, Hs.chpsC} : Finset (AddChar (E0 × H) ℂ)) := by
    intro ψ
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · exact trivH_cases Hs ψ
    · rintro (rfl | rfl | rfl | rfl)
      exacts [trivH_zero, trivH_chC Hs, trivH_psC Hs, trivH_chpsC Hs]
  have h1 : ∑ ψ ∈ ({0, Hs.chC, Hs.psC, Hs.chpsC} : Finset (AddChar (E0 × H) ℂ)),
      (if TrivH ψ then ψ e10 * F ψ else 0)
      = ∑ ψ : AddChar (E0 × H) ℂ, (if TrivH ψ then ψ e10 * F ψ else 0) :=
    Finset.sum_subset (Finset.subset_univ _) (fun ψ _ hψ => if_neg (fun h => hψ ((hmem ψ).1 h)))
  rw [← h1]
  have n1 : (0 : AddChar (E0 × H) ℂ) ∉
      ({Hs.chC, Hs.psC, Hs.chpsC} : Finset (AddChar (E0 × H) ℂ)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    refine ⟨ne_of_val e10 ?_, ne_of_val e01 ?_, ne_of_val e10 ?_⟩
    · rw [AddChar.zero_apply, cyclicCharacter_first_basis]; norm_num
    · rw [AddChar.zero_apply, quadraticCharacter_second_basis]; norm_num
    · rw [AddChar.zero_apply, productCharacter_first_basis]; norm_num
  have n2 : Hs.chC ∉ ({Hs.psC, Hs.chpsC} : Finset (AddChar (E0 × H) ℂ)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    refine ⟨ne_of_val e10 ?_, ne_of_val e01 ?_⟩
    · rw [cyclicCharacter_first_basis, quadraticCharacter_first_basis]; norm_num
    · rw [cyclicCharacter_second_basis, productCharacter_second_basis]; norm_num
  have n3 : Hs.psC ∉ ({Hs.chpsC} : Finset (AddChar (E0 × H) ℂ)) := by
    simp only [Finset.mem_singleton]
    exact ne_of_val e10 (by rw [quadraticCharacter_first_basis, productCharacter_first_basis]; norm_num)
  rw [Finset.sum_insert n1, Finset.sum_insert n2, Finset.sum_insert n3, Finset.sum_singleton,
    if_pos (trivH_zero (H := H)), if_pos (trivH_chC Hs), if_pos (trivH_psC Hs),
    if_pos (trivH_chpsC Hs), AddChar.zero_apply, cyclicCharacter_first_basis, quadraticCharacter_first_basis, productCharacter_first_basis]
  ring

/- English proof (translation)
Establish `h2 : (2 : ZMod 2) = 0` using `by decide`. Use extensionality with `⟨⟨a, b⟩, h⟩`. Apply the tactic sequence `rcases zmod_two_cases_bis a with rfl | rfl <;> rcases zmod_two_cases_bis b with rfl | rfl <;>`. Simplify using `[InPhi, IsThickAt, topPl, cconj, thickPl, zmod_two_one_add_one, zmod_two_one_ne_zero, zmod_two_one_ne_zero.symm, h2, sub_eq_iff_eq_add]`.
-/
lemma thick_filter (T2 : Finset H) (u0 t : H) :
    univ.filter (fun g : E0 × H => ¬ InPhi (g + topPl t) ∧ IsThickAt T2 u0 (cconj + g + topPl t))
      = T2.image (fun s => ((((1 : ZMod 2), (0 : ZMod 2)), s + u0 - t) : E0 × H)) := by
  have h2 : (2 : ZMod 2) = 0 := by decide
  ext ⟨⟨a, b⟩, h⟩
  rcases zmod_two_cases_bis a with rfl | rfl <;> rcases zmod_two_cases_bis b with rfl | rfl <;>
    simp [InPhi, IsThickAt, topPl, cconj, thickPl, zmod_two_one_add_one, zmod_two_one_ne_zero,
      zmod_two_one_ne_zero.symm, h2, sub_eq_iff_eq_add]

/- English proof (translation)
Introduce `x _ y _ hxy`. Simplify using `using hxy`.
-/
lemma thick_inj (u0 t : H) :
    Set.InjOn (fun s => ((((1 : ZMod 2), (0 : ZMod 2)), s + u0 - t) : E0 × H)) Set.univ := by
  intro x _ y _ hxy
  simpa using hxy

/- English proof (translation)
Establish `h2 : (2 : ZMod 2) = 0` using `by decide`. Simplify using `[cconj, topPl, thickPl, zmod_two_one_add_one, h2]`.
-/
lemma rho_thick (s u0 t : H) :
    cconj + ((((1 : ZMod 2), (0 : ZMod 2)), s + u0 - t) : E0 × H) + topPl t = thickPl (s + u0) := by
  have h2 : (2 : ZMod 2) = 0 := by decide
  simp [cconj, topPl, thickPl, zmod_two_one_add_one, h2]

def thickZ {m : ℕ} (Hs : CycHost H) (Nd : Nodes H m) (u0 t : H) (j : Fin m) : ℂ :=
  (1 / ((PhiSet (H := H)).card : ℂ)) * ∑ s ∈ Nd.T2, ∑ ψ : AddChar (E0 × H) ℂ,
    ψ (-((((1 : ZMod 2), (0 : ZMod 2)), s + u0 - t) : E0 × H)) * ((Nd.bj j : ℝ) : ℂ)
      * GC Hs ψ (Nd.a t / Nd.bj j)

/- English proof (translation)
Rewrite using `[Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]`. Establish `h1 : ∑ g ∈ s, F g = ∑ g, (if g ∈ s then F g else 0)`. Rewrite using `[← Finset.sum_filter]`. Use `congr 1`. Use extensionality with `g`.

Simplify using the standard rewrite rules. Rewrite using `[h1]`. Use `Finset.sum_congr rfl (fun g _ => ?_)` and prove the remaining obligations. Establish `h` using `hs g`. Apply the tactic sequence `split_ifs <;> first | (simp; done) | (exfalso; tauto) | rfl`.
-/
private lemma sum_filter_sub_sum_filter_and_not_eq_sum {α : Type} [Fintype α] {p q : α → Prop}
    {hp : DecidablePred p} {hpq : DecidablePred (fun g => p g ∧ ¬ q g)}
    {s : Finset α} {F : α → ℂ} (hs : ∀ g, (p g ∧ q g) ↔ g ∈ s) :
    ∑ g ∈ Finset.univ.filter p, F g - ∑ g ∈ Finset.univ.filter (fun g => p g ∧ ¬ q g), F g
      = ∑ g ∈ s, F g := by
  classical
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
  have h1 : ∑ g ∈ s, F g = ∑ g, (if g ∈ s then F g else 0) := by
    rw [← Finset.sum_filter]
    congr 1
    ext g
    simp
  rw [h1]
  refine Finset.sum_congr rfl (fun g _ => ?_)
  have h := hs g
  split_ifs <;> first | (simp; done) | (exfalso; tauto) | rfl

/- English proof (translation)
Establish `hmem : ∀ g : E0 × H, (¬ InPhi (g + topPl t) ∧ IsThickAt Nd.T2 u0 (cconj + g + topPl t)) ↔ g ∈ Nd.T2.image (fun s => ((((1 : ZMod 2), (0 : ZMod 2)), s + u0 - t) : E0 × H))`. Introduce `g`. Establish `h` using `Finset.ext_iff.mp (thick_filter Nd.T2 u0 t) g`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at h`. Conclude with `h`.

Rewrite using `[balTop, thickZ, ← Complex.add_re, ← mul_add]`. Use `congr 2`. Rewrite using `[← sub_eq_iff_eq_add]`. Use `(sum_filter_sub_sum_filter_and_not_eq_sum (p := fun g : E0 × H => ¬ InPhi (g + topPl t)) (q := fun g : E0 × H => IsThickAt Nd.T2 u0 (cconj + g + topPl t)) hmem).trans ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_image ((thick_inj u0 t).mono (Set.subset_univ _))]`.

Use `Finset.sum_congr rfl (fun s hs => ?_)` and prove the remaining obligations. Rewrite using `[rho_thick, Nd.w_thick u0 j s hs]`.
-/
lemma balTop_split {m : ℕ} (Hs : CycHost H) (Nd : Nodes H m) (u0 t : H) (j : Fin m) :
    balTop Hs (Nd.a t) t (Nd.w u0 j) = (thickZ Hs Nd u0 t j).re +
      ((1 / ((PhiSet (H := H)).card : ℂ)) * ∑ g ∈ univ.filter (fun g : E0 × H =>
        ¬ InPhi (g + topPl t) ∧ ¬ IsThickAt Nd.T2 u0 (cconj + g + topPl t)),
      ∑ ψ : AddChar (E0 × H) ℂ, ψ (-g) * ((Nd.w u0 j (cconj + g + topPl t) : ℝ) : ℂ)
        * GC Hs ψ (Nd.a t / Nd.w u0 j (cconj + g + topPl t))).re := by
  have hmem : ∀ g : E0 × H,
      (¬ InPhi (g + topPl t) ∧ IsThickAt Nd.T2 u0 (cconj + g + topPl t)) ↔
        g ∈ Nd.T2.image (fun s => ((((1 : ZMod 2), (0 : ZMod 2)), s + u0 - t) : E0 × H)) := by
    intro g
    have h := Finset.ext_iff.mp (thick_filter Nd.T2 u0 t) g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h
    exact h
  rw [balTop, thickZ, ← Complex.add_re, ← mul_add]
  congr 2
  rw [← sub_eq_iff_eq_add]
  refine (sum_filter_sub_sum_filter_and_not_eq_sum (p := fun g : E0 × H => ¬ InPhi (g + topPl t))
    (q := fun g : E0 × H => IsThickAt Nd.T2 u0 (cconj + g + topPl t)) hmem).trans ?_
  rw [Finset.sum_image ((thick_inj u0 t).mono (Set.subset_univ _))]
  refine Finset.sum_congr rfl (fun s hs => ?_)
  rw [rho_thick, Nd.w_thick u0 j s hs]

/- English proof (translation)
Rewrite using `[Finset.mul_sum]`. Use `Fintype.sum_equiv (Equiv.subLeft (t - s)) _ _ (fun u0 => ?_)` and prove the remaining obligations. Use `show ψ (-((((1 : ZMod 2), (0 : ZMod 2)), s + u0 - t) : E0 × H)) = ψ e10 * ψ ((0, 0), t - s - u0)`. Rewrite using `[← AddChar.map_add_eq_mul]`. Use `congr 1`.

Use `Prod.ext (Prod.ext ?_ ?_) ?_` and prove the remaining obligations. Use `first`. Consider the case `(show -(1 : ZMod 2) = 1 + 0; decide)`. Consider the case `(simp [e10, zmod_two_neg_one]; done)`. Use `first`.

Consider the case `(show -(0 : ZMod 2) = 0 + 0; decide)`. Consider the case `(simp [e10]; done)`. Use `show -(s + u0 - t) = (0 : H) + (t - s - u0)`. Normalize the expressions using the abelian group laws.
-/
lemma sum_character_shift_eq (ψ : AddChar (E0 × H) ℂ) (s t : H) :
    ∑ u0 : H, ψ (-((((1 : ZMod 2), (0 : ZMod 2)), s + u0 - t) : E0 × H))
      = ψ e10 * ∑ h : H, ψ ((0, 0), h) := by
  rw [Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.subLeft (t - s)) _ _ (fun u0 => ?_)
  show ψ (-((((1 : ZMod 2), (0 : ZMod 2)), s + u0 - t) : E0 × H)) = ψ e10 * ψ ((0, 0), t - s - u0)
  rw [← AddChar.map_add_eq_mul]
  congr 1
  refine Prod.ext (Prod.ext ?_ ?_) ?_
  · first
      | (show -(1 : ZMod 2) = 1 + 0; decide)
      | (simp [e10, zmod_two_neg_one]; done)
  · first
      | (show -(0 : ZMod 2) = 0 + 0; decide)
      | (simp [e10]; done)
  · show -(s + u0 - t) = (0 : H) + (t - s - u0)
    abel

open Classical in
/- English proof (translation)
Unfold `thickZ`. Rewrite using `[← Finset.mul_sum, Finset.sum_comm]`. Establish `hin : ∀ s ∈ Nd.T2, ∑ u0 : H, ∑ ψ : AddChar (E0 × H) ℂ, ψ (-((((1 : ZMod 2), (0 : ZMod 2)), s + u0 - t) : E0 × H)) * ((Nd.bj j : ℝ) : ℂ) * GC Hs ψ (Nd.a t / Nd.bj j) = (Fintype.card H : ℂ) * ((Nd.bj j : ℝ) : ℂ) * ∑ ψ : AddChar (E0 × H) ℂ, (if TrivH ψ then ψ e10 * GC Hs ψ (Nd.a t / …`. Introduce `s _`. Rewrite using `[Finset.sum_comm, Finset.mul_sum]`.

Use `Finset.sum_congr rfl (fun ψ _ => ?_)` and prove the remaining obligations. Rewrite using `[← Finset.sum_mul, ← Finset.sum_mul, sum_character_shift_eq, sum_H]`. Apply the tactic sequence `split_ifs <;> ring`. Rewrite using `[Finset.sum_congr rfl hin, Finset.sum_const, nsmul_eq_mul, sum_trivH, phiSet_card]`. Establish `hH : (Fintype.card H : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 Fintype.card_ne_zero`.

Use `push_cast`. Clear the denominators using the available nonvanishing facts.
-/
lemma sum_thick_term_eq_gaussSums {m : ℕ} (Hs : CycHost H) (Nd : Nodes H m) (t : H) (j : Fin m) :
    ∑ u0 : H, thickZ Hs Nd u0 t j = ((Nd.T2.card : ℂ) / 2) * ((Nd.bj j : ℝ) : ℂ) *
      (GC Hs 0 (Nd.a t / Nd.bj j) + GC Hs Hs.psC (Nd.a t / Nd.bj j) - GC Hs Hs.chC (Nd.a t / Nd.bj j)
        - GC Hs Hs.chpsC (Nd.a t / Nd.bj j)) := by
  unfold thickZ
  rw [← Finset.mul_sum, Finset.sum_comm]
  have hin : ∀ s ∈ Nd.T2, ∑ u0 : H, ∑ ψ : AddChar (E0 × H) ℂ,
      ψ (-((((1 : ZMod 2), (0 : ZMod 2)), s + u0 - t) : E0 × H)) * ((Nd.bj j : ℝ) : ℂ)
        * GC Hs ψ (Nd.a t / Nd.bj j)
      = (Fintype.card H : ℂ) * ((Nd.bj j : ℝ) : ℂ) * ∑ ψ : AddChar (E0 × H) ℂ,
          (if TrivH ψ then ψ e10 * GC Hs ψ (Nd.a t / Nd.bj j) else 0) := by
    intro s _
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun ψ _ => ?_)
    rw [← Finset.sum_mul, ← Finset.sum_mul, sum_character_shift_eq, sum_H]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl hin, Finset.sum_const, nsmul_eq_mul, sum_trivH, phiSet_card]
  have hH : (Fintype.card H : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  push_cast
  field_simp

end

/- English proof (translation)
Unfold `ThickAverage`. Introduce `m Hs Nd`. Establish `hj : ∀ (t : H) (j : Fin m), ∑ u0 : H, (thickZ Hs Nd u0 t j).re = (Nd.T2.card : ℝ) / 2 * (Nd.bj j * (GC Hs 0 (Nd.a t / Nd.bj j) + GC Hs Hs.psC (Nd.a t / Nd.bj j) - GC Hs Hs.chC (Nd.a t / Nd.bj j) - GC Hs Hs.chpsC (Nd.a t / Nd.bj j)).re)`. Introduce `t j`. Apply the tactic sequence `rw [← Complex.re_sum, sum_thick_term_eq_gaussSums, show ((Nd.T2.card : ℂ) / 2 * ((Nd.bj j : ℝ) : ℂ)) = (((Nd.T2.card : ℝ) / 2 * Nd.bj j : ℝ) : ℂ) by push_cast; try ring, Complex.re_ofReal_mul]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hswap : ∑ u0 : H, ∑ t ∈ Nd.T, ∑ j : Fin m, (thickZ Hs Nd u0 t j).re = ∑ t ∈ Nd.T, ∑ j : Fin m, ∑ u0 : H, (thickZ Hs Nd u0 t j).re`. Combine the equalities or inequalities in the displayed calculation. Repeatedly rewrite using `[balTop_split Hs Nd, Finset.sum_add_distrib, mul_add]`. Use `congr 1`.

Rewrite using `[hswap, signal]`. Repeatedly rewrite using `[hj, ← Finset.mul_sum]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem thick_average_formula {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] :
    ThickAverage (H := H) := by
  unfold ThickAverage
  intro m Hs Nd
  have hj : ∀ (t : H) (j : Fin m), ∑ u0 : H, (thickZ Hs Nd u0 t j).re =
      (Nd.T2.card : ℝ) / 2 * (Nd.bj j * (GC Hs 0 (Nd.a t / Nd.bj j)
        + GC Hs Hs.psC (Nd.a t / Nd.bj j) - GC Hs Hs.chC (Nd.a t / Nd.bj j)
        - GC Hs Hs.chpsC (Nd.a t / Nd.bj j)).re) := by
    intro t j
    rw [← Complex.re_sum, sum_thick_term_eq_gaussSums,
      show ((Nd.T2.card : ℂ) / 2 * ((Nd.bj j : ℝ) : ℂ))
        = (((Nd.T2.card : ℝ) / 2 * Nd.bj j : ℝ) : ℂ) by push_cast; try ring,
      Complex.re_ofReal_mul]
    ring
  have hswap : ∑ u0 : H, ∑ t ∈ Nd.T, ∑ j : Fin m, (thickZ Hs Nd u0 t j).re
      = ∑ t ∈ Nd.T, ∑ j : Fin m, ∑ u0 : H, (thickZ Hs Nd u0 t j).re := by
    calc ∑ u0 : H, ∑ t ∈ Nd.T, ∑ j : Fin m, (thickZ Hs Nd u0 t j).re
        = ∑ t ∈ Nd.T, ∑ u0 : H, ∑ j : Fin m, (thickZ Hs Nd u0 t j).re := Finset.sum_comm
      _ = ∑ t ∈ Nd.T, ∑ j : Fin m, ∑ u0 : H, (thickZ Hs Nd u0 t j).re :=
          Finset.sum_congr rfl (fun t _ => Finset.sum_comm)
  simp_rw [balTop_split Hs Nd, Finset.sum_add_distrib, mul_add]
  congr 1
  · rw [hswap, signal]
    simp_rw [hj, ← Finset.mul_sum]
    ring

end Formalism.D5
