import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.Imports

open Finset

noncomputable section

namespace GlobalTheory.WigSh.Model

def Box {n : ℕ} (L : Fin (n + 1) → ℤ) (M : Fin n → ℤ) : Prop :=
  ∀ j : Fin n, L j.succ < M j ∧ M j ≤ L j.castSucc

/- English proof (translation)
Rewrite using `[Fin.strictAnti_iff_succ_lt]`. Introduce `j`. Conclude with `lt_of_lt_of_le (h j).1 (h j).2`.
-/
theorem Box.strictAnti {n : ℕ} {L : Fin (n + 1) → ℤ} {M : Fin n → ℤ} (h : Box L M) :
    StrictAnti L := by
  rw [Fin.strictAnti_iff_succ_lt]
  intro j
  exact lt_of_lt_of_le (h j).1 (h j).2

/- English proof (translation)
Rewrite using `[← Finset.compl_singleton, ← Fin.image_succAbove_univ, Finset.prod_image (fun a _ b _ hab => Fin.succAbove_right_injective hab)]`.
-/
theorem prod_erase_eq {n : ℕ} (f : Fin (n + 1) → ℝ) (l : Fin (n + 1)) :
    ∏ j ∈ univ.erase l, f j = ∏ j : Fin n, f (l.succAbove j) := by
  rw [← Finset.compl_singleton, ← Fin.image_succAbove_univ,
    Finset.prod_image (fun a _ b _ hab => Fin.succAbove_right_injective hab)]

/- English proof (translation)
Establish `hA` using `h.strictAnti`. Establish `he0' : (0 : ℝ) ≤ e` using `by exact_mod_cast he0`. Establish `he1' : (e : ℝ) ≤ 1` using `by exact_mod_cast he1`. Break down `lt_or_ge (Fin.castSucc j) l with hj | hj` into its components or cases. Rewrite using `[Fin.succAbove_of_castSucc_lt l j hj]`.

Establish `h1 : L l ≤ L j.succ` using `hA.antitone (Fin.castSucc_lt_iff_succ_le.mp hj)`. Establish `h2 : L l < L j.castSucc` using `hA hj`. Establish `h3` using `(h j).1`. Establish `h4 : (L l : ℝ) + 1 ≤ M j` using `by exact_mod_cast (by omega : L l + 1 ≤ M j)`. Establish `h5 : (L l : ℝ) < L j.castSucc` using `by exact_mod_cast h2`.

Apply the tactic sequence `apply div_nonneg <;> linarith`. Rewrite using `[Fin.succAbove_of_le_castSucc l j hj]`. Establish `h1 : L j.castSucc ≤ L l` using `hA.antitone hj`. Establish `h2 : L j.succ < L l` using `hA (lt_of_le_of_lt hj Fin.castSucc_lt_succ)`. Establish `h4 : (M j : ℝ) ≤ L l` using `by exact_mod_cast le_trans (h j).2 h1`.

Establish `h5 : (L j.succ : ℝ) < L l` using `by exact_mod_cast h2`. Apply the tactic sequence `apply div_nonneg_of_nonpos <;> linarith`.
-/
theorem factor_nonneg {n : ℕ} {L : Fin (n + 1) → ℤ} {M : Fin n → ℤ} (h : Box L M)
    (l : Fin (n + 1)) (j : Fin n) (e : ℤ) (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    0 ≤ ((M j : ℝ) - e - L l) / ((L (l.succAbove j) : ℝ) - L l) := by
  have hA := h.strictAnti
  have he0' : (0 : ℝ) ≤ e := by exact_mod_cast he0
  have he1' : (e : ℝ) ≤ 1 := by exact_mod_cast he1
  rcases lt_or_ge (Fin.castSucc j) l with hj | hj
  · rw [Fin.succAbove_of_castSucc_lt l j hj]
    have h1 : L l ≤ L j.succ := hA.antitone (Fin.castSucc_lt_iff_succ_le.mp hj)
    have h2 : L l < L j.castSucc := hA hj
    have h3 := (h j).1
    have h4 : (L l : ℝ) + 1 ≤ M j := by exact_mod_cast (by omega : L l + 1 ≤ M j)
    have h5 : (L l : ℝ) < L j.castSucc := by exact_mod_cast h2
    apply div_nonneg <;> linarith
  · rw [Fin.succAbove_of_le_castSucc l j hj]
    have h1 : L j.castSucc ≤ L l := hA.antitone hj
    have h2 : L j.succ < L l := hA (lt_of_le_of_lt hj Fin.castSucc_lt_succ)
    have h4 : (M j : ℝ) ≤ L l := by exact_mod_cast le_trans (h j).2 h1
    have h5 : (L j.succ : ℝ) < L l := by exact_mod_cast h2
    apply div_nonneg_of_nonpos <;> linarith

/- English proof (translation)
Unfold `GlobalTheory.WigSh.wP`. Rewrite using `[prod_erase_eq, ← Finset.prod_div_distrib]`. Use `Finset.prod_nonneg fun j _ => ?_` and prove the remaining obligations. Simplify using `using factor_nonneg h l j 1 zero_le_one le_rfl`.
-/
theorem placeWeight_nonneg {n : ℕ} {L : Fin (n + 1) → ℤ} {M : Fin n → ℤ} (h : Box L M)
    (l : Fin (n + 1)) : 0 ≤ wP L M l := by
  unfold GlobalTheory.WigSh.wP
  rw [prod_erase_eq, ← Finset.prod_div_distrib]
  refine Finset.prod_nonneg fun j _ => ?_
  simpa using factor_nonneg h l j 1 zero_le_one le_rfl

/- English proof (translation)
Unfold `GlobalTheory.WigSh.wM`. Rewrite using `[prod_erase_eq, ← Finset.prod_div_distrib]`. Use `Finset.prod_nonneg fun j _ => ?_` and prove the remaining obligations. Simplify using `using factor_nonneg h l j 0 le_rfl zero_le_one`.
-/
theorem wM_nonneg {n : ℕ} {L : Fin (n + 1) → ℤ} {M : Fin n → ℤ} (h : Box L M)
    (l : Fin (n + 1)) : 0 ≤ wM L M l := by
  unfold GlobalTheory.WigSh.wM
  rw [prod_erase_eq, ← Finset.prod_div_distrib]
  refine Finset.prod_nonneg fun j _ => ?_
  simpa using factor_nonneg h l j 0 le_rfl zero_le_one

/- English proof (translation)
Rewrite using `[prod_erase_eq]`. Use `Finset.prod_ne_zero_iff.mpr fun j _ => sub_ne_zero.mpr ?_` and prove the remaining obligations. Conclude with `h.strictAnti.injective.ne (Fin.succAbove_ne l j)` after adjusting the coercions.
-/
theorem denom_ne_zero {n : ℕ} {L : Fin (n + 1) → ℤ} {M : Fin n → ℤ} (h : Box L M)
    (l : Fin (n + 1)) : ∏ j ∈ univ.erase l, ((L j : ℝ) - (L l : ℝ)) ≠ 0 := by
  rw [prod_erase_eq]
  refine Finset.prod_ne_zero_iff.mpr fun j _ => sub_ne_zero.mpr ?_
  exact_mod_cast h.strictAnti.injective.ne (Fin.succAbove_ne l j)

/- English proof (translation)
Rewrite using `[← abs_of_nonneg (placeWeight_nonneg h l)]`. Unfold `GlobalTheory.WigSh.wP`. Rewrite using `[abs_div, Finset.abs_prod, Finset.abs_prod]`. Apply the tactic sequence `congr 1 <;> refine Finset.prod_congr rfl fun i _ => ?_`. Rewrite using `[hρ, hu, ← abs_neg]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hu i, hu l, ← abs_neg]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem weight_eq_abs_prod_div_prod {n : ℕ} {L : Fin (n + 1) → ℤ} {M : Fin n → ℤ} (h : Box L M) (β : ℝ)
    (u : Fin (n + 1) → ℝ) (ρ : Fin n → ℝ)
    (hu : ∀ j, (L j : ℝ) = u j - (n : ℝ) / 2 - β)
    (hρ : ∀ j, (M j : ℝ) = ρ j - ((n : ℝ) - 1) / 2 - β) (l : Fin (n + 1)) :
    wP L M l = (∏ i, |u l + 1 / 2 - ρ i|) / ∏ i ∈ univ.erase l, |u l - u i| := by
  rw [← abs_of_nonneg (placeWeight_nonneg h l)]
  unfold GlobalTheory.WigSh.wP
  rw [abs_div, Finset.abs_prod, Finset.abs_prod]
  congr 1 <;> refine Finset.prod_congr rfl fun i _ => ?_
  · rw [hρ, hu, ← abs_neg]
    congr 1
    ring
  · rw [hu i, hu l, ← abs_neg]
    congr 1
    ring

/- English proof (translation)
Rewrite using `[← abs_of_nonneg (wM_nonneg h l)]`. Unfold `GlobalTheory.WigSh.wM`. Rewrite using `[abs_div, Finset.abs_prod, Finset.abs_prod]`. Apply the tactic sequence `congr 1 <;> refine Finset.prod_congr rfl fun i _ => ?_`. Rewrite using `[hρ, hu, ← abs_neg]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hu i, hu l, ← abs_neg]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem wM_eq_abs {n : ℕ} {L : Fin (n + 1) → ℤ} {M : Fin n → ℤ} (h : Box L M) (β : ℝ)
    (u : Fin (n + 1) → ℝ) (ρ : Fin n → ℝ)
    (hu : ∀ j, (L j : ℝ) = u j - (n : ℝ) / 2 - β)
    (hρ : ∀ j, (M j : ℝ) = ρ j - ((n : ℝ) - 1) / 2 - β) (l : Fin (n + 1)) :
    wM L M l = (∏ i, |u l - 1 / 2 - ρ i|) / ∏ i ∈ univ.erase l, |u l - u i| := by
  rw [← abs_of_nonneg (wM_nonneg h l)]
  unfold GlobalTheory.WigSh.wM
  rw [abs_div, Finset.abs_prod, Finset.abs_prod]
  congr 1 <;> refine Finset.prod_congr rfl fun i _ => ?_
  · rw [hρ, hu, ← abs_neg]
    congr 1
    ring
  · rw [hu i, hu l, ← abs_neg]
    congr 1
    ring

/- English proof (translation)
Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `j fin_cases j`. Evaluate the decidable proposition. Simplify using `[GlobalTheory.WigSh.wP, prod_erase_eq]`. Evaluate the numerical expressions.

Simplify using `[GlobalTheory.WigSh.wP, prod_erase_eq, Fin.succAbove]`. Evaluate the numerical expressions.
-/
theorem example_wP : Box ![3, -1] ![1] ∧ wP ![3, -1] ![1] 0 = 3 / 4 ∧ wP ![3, -1] ![1] 1 = 1 / 4 := by
  refine ⟨?_, ?_, ?_⟩
  · intro j
    fin_cases j
    decide
  · simp [GlobalTheory.WigSh.wP, prod_erase_eq]
    norm_num
  · simp [GlobalTheory.WigSh.wP, prod_erase_eq, Fin.succAbove]
    norm_num

/- English proof (translation)
Use `⟨?_, ?_⟩` and prove the remaining obligations. Simplify using `[GlobalTheory.WigSh.wM, prod_erase_eq]`. Evaluate the numerical expressions. Simplify using `[GlobalTheory.WigSh.wM, prod_erase_eq, Fin.succAbove]`. Evaluate the numerical expressions.
-/
theorem example_wM : wM ![3, -1] ![1] 0 = 1 / 2 ∧ wM ![3, -1] ![1] 1 = 1 / 2 := by
  refine ⟨?_, ?_⟩
  · simp [GlobalTheory.WigSh.wM, prod_erase_eq]
    norm_num
  · simp [GlobalTheory.WigSh.wM, prod_erase_eq, Fin.succAbove]
    norm_num

/- English proof (translation)
Apply the tactic sequence `constructor <;> simp [GlobalTheory.WigSh.wP, GlobalTheory.WigSh.wM]`.
-/
theorem rank_one (L : Fin 1 → ℤ) (M : Fin 0 → ℤ) : wP L M 0 = 1 ∧ wM L M 0 = 1 := by
  constructor <;> simp [GlobalTheory.WigSh.wP, GlobalTheory.WigSh.wM]

end GlobalTheory.WigSh.Model
