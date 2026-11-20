import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairStructureOnLine

noncomputable section

open Finset

namespace GlobalTheory.CompanionTheory.RealMult.Short

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open Formalism.REAL (dot nsq)

variable {n : ℕ}

/- English proof (translation)
Simplify using `[dot, add_mul, sum_add_distrib]`.
-/
theorem dL_add (u v w : Fin n → ℝ) : dot (u + v) w = dot u w + dot v w := by
  simp [dot, add_mul, sum_add_distrib]

/- English proof (translation)
Simplify using `[dot, sub_mul, sum_sub_distrib]`.
-/
theorem dL_sub (u v w : Fin n → ℝ) : dot (u - v) w = dot u w - dot v w := by
  simp [dot, sub_mul, sum_sub_distrib]

/- English proof (translation)
Simplify using `[dot, mul_sum, mul_assoc]`.
-/
theorem dL_smul (c : ℝ) (u w : Fin n → ℝ) : dot (c • u) w = c * dot u w := by
  simp [dot, mul_sum, mul_assoc]

/- English proof (translation)
Simplify using `[dot, mul_comm]`.
-/
theorem d_comm (u v : Fin n → ℝ) : dot u v = dot v u := by
  simp [dot, mul_comm]

/- English proof (translation)
Simplify using `[dot, mul_add, sum_add_distrib]`.
-/
theorem dR_add (u v w : Fin n → ℝ) : dot u (v + w) = dot u v + dot u w := by
  simp [dot, mul_add, sum_add_distrib]

/- English proof (translation)
Simplify using `[dot, mul_sub, sum_sub_distrib]`.
-/
theorem dR_sub (u v w : Fin n → ℝ) : dot u (v - w) = dot u v - dot u w := by
  simp [dot, mul_sub, sum_sub_distrib]

/- English proof (translation)
Rewrite using `[d_comm, dL_smul, d_comm]`.
-/
theorem dR_smul (c : ℝ) (u w : Fin n → ℝ) : dot u (c • w) = c * dot u w := by
  rw [d_comm, dL_smul, d_comm]

/- English proof (translation)
Simplify `Equiv.sum_comp w (fun a => u a * v a)` using `[dot]`.
-/
theorem d_perm (u v : Fin n → ℝ) (w : Equiv.Perm (Fin n)) : dot (u ∘ w) (v ∘ w) = dot u v := by
  simpa [dot] using Equiv.sum_comp w (fun a => u a * v a)

/- English proof (translation)
The claim follows from `sum_nonneg fun a _ => mul_self_nonneg _`.
-/
theorem d_self_nonneg (u : Fin n → ℝ) : 0 ≤ dot u u :=
  sum_nonneg fun a _ => mul_self_nonneg _

/- English proof (translation)
Simplify using `only [rhoV]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem rho_sub (a b : Fin n) : rhoV n a - rhoV n b = (b : ℕ) - (a : ℕ) := by
  simp only [rhoV]; ring

/- English proof (translation)
Introduce `a b h`. Establish `h' : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ)` using `by exact_mod_cast h`. Use `rho_sub a b` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem rho_anti : StrictAnti (rhoV n) := by
  intro a b h
  have h' : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast h
  have := rho_sub a b
  linarith

/- English proof (translation)
The claim follows from `Monovary.sum_mul_comp_perm_le_sum_mul (hu.monovary rho_anti.antitone)`.
-/
theorem rearr (u : Fin n → ℝ) (hu : Antitone u) (σ : Equiv.Perm (Fin n)) :
    dot u (rhoV n ∘ σ) ≤ dot u (rhoV n) :=
  Monovary.sum_mul_comp_perm_le_sum_mul (hu.monovary rho_anti.antitone)

def s0 (a b : Fin n) : ℝ := if a < b then 1 else if b < a then -1 else 0

def mB (B : Finset (Fin n × Fin n)) (a b : Fin n) : ℝ := if (a, b) ∈ B then 1 else 0

def sg (B : Finset (Fin n × Fin n)) (a b : Fin n) : ℝ := s0 a b - 2 * mB B a b + 2 * mB B b a

/- English proof (translation)
Unfold `s0`. Break down `lt_trichotomy a b with h | h | h` into its components or cases. Simplify using `[h, asymm h]`. Simplify using `[h]`. Simplify using `[h, asymm h]`.
-/
theorem sign_antisymmetric_alt (a b : Fin n) : s0 b a = -s0 a b := by
  unfold s0
  rcases lt_trichotomy a b with h | h | h
  · simp [h, asymm h]
  · simp [h]
  · simp [h, asymm h]

/- English proof (translation)
Unfold `sg`. Rewrite using `[sign_antisymmetric_alt a b]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sg_anti (B : Finset (Fin n × Fin n)) (a b : Fin n) : sg B b a = -sg B a b := by
  unfold sg; rw [sign_antisymmetric_alt a b]; ring

/- English proof (translation)
Simplify using `[s0]`.
-/
theorem sign_self_eq_zero (a : Fin n) : s0 a a = 0 := by simp [s0]

/- English proof (translation)
Establish `h : ∀ b, s0 a b = (if a < b then (1 : ℝ) else 0) - (if b < a then (1 : ℝ) else 0)`. Introduce `b`. Unfold `s0`. Break down `lt_trichotomy a b with h | h | h` into its components or cases. Simplify using `[h, asymm h]`.

Simplify using `[h]`. Simplify using `[h, asymm h]`. Simplify using `only [h, sum_sub_distrib, sum_boole]`. Rewrite using `[Finset.filter_lt_eq_Ioi, Finset.filter_gt_eq_Iio, Fin.card_Ioi, Fin.card_Iio]`. Establish `ha` using `a.2`.

Rewrite using `[Nat.cast_sub (by omega), Nat.cast_sub (by omega)]`. Simplify using `[rhoV]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sum_sign_eq_two_rho (a : Fin n) : ∑ b, s0 a b = 2 * rhoV n a := by
  have h : ∀ b, s0 a b = (if a < b then (1 : ℝ) else 0) - (if b < a then (1 : ℝ) else 0) := by
    intro b
    unfold s0
    rcases lt_trichotomy a b with h | h | h
    · simp [h, asymm h]
    · simp [h]
    · simp [h, asymm h]
  simp only [h, sum_sub_distrib, sum_boole]
  rw [Finset.filter_lt_eq_Ioi, Finset.filter_gt_eq_Iio, Fin.card_Ioi, Fin.card_Iio]
  have ha := a.2
  rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  simp [rhoV]
  ring

/- English proof (translation)
Establish `: B.filter (fun p => p.1 = a) = (univ.filter fun b => (a, b) ∈ B).image (fun b => (a, b))`. Use extensionality with `⟨x, y⟩`. Simplify using `only [mem_filter, mem_image, mem_univ, true_and, Prod.mk.injEq]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h, rfl⟩`.

Conclude with `⟨y, h, rfl, rfl⟩`. Introduce and unpack `⟨c, h, rfl, rfl⟩`. Conclude with `⟨h, rfl⟩`. Rewrite using `[this, card_image_of_injective _ (fun x y h => (Prod.mk.inj h).2)]`. Simplify using `[mB]`.
-/
theorem sum_row_count (B : Finset (Fin n × Fin n)) (a : Fin n) :
    ∑ b, mB B a b = ((B.filter fun p => p.1 = a).card : ℝ) := by
  have : B.filter (fun p => p.1 = a) = (univ.filter fun b => (a, b) ∈ B).image (fun b => (a, b)) := by
    ext ⟨x, y⟩
    simp only [mem_filter, mem_image, mem_univ, true_and, Prod.mk.injEq]
    constructor
    · rintro ⟨h, rfl⟩; exact ⟨y, h, rfl, rfl⟩
    · rintro ⟨c, h, rfl, rfl⟩; exact ⟨h, rfl⟩
  rw [this, card_image_of_injective _ (fun x y h => (Prod.mk.inj h).2)]
  simp [mB]

/- English proof (translation)
Establish `: B.filter (fun p => p.2 = a) = (univ.filter fun b => (b, a) ∈ B).image (fun b => (b, a))`. Use extensionality with `⟨x, y⟩`. Simplify using `only [mem_filter, mem_image, mem_univ, true_and, Prod.mk.injEq]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h, rfl⟩`.

Conclude with `⟨x, h, rfl, rfl⟩`. Introduce and unpack `⟨c, h, rfl, rfl⟩`. Conclude with `⟨h, rfl⟩`. Rewrite using `[this, card_image_of_injective _ (fun x y h => (Prod.mk.inj h).1)]`. Simplify using `[mB]`.
-/
theorem sum_column_count (B : Finset (Fin n × Fin n)) (a : Fin n) :
    ∑ b, mB B b a = ((B.filter fun p => p.2 = a).card : ℝ) := by
  have : B.filter (fun p => p.2 = a) = (univ.filter fun b => (b, a) ∈ B).image (fun b => (b, a)) := by
    ext ⟨x, y⟩
    simp only [mem_filter, mem_image, mem_univ, true_and, Prod.mk.injEq]
    constructor
    · rintro ⟨h, rfl⟩; exact ⟨x, h, rfl, rfl⟩
    · rintro ⟨c, h, rfl, rfl⟩; exact ⟨h, rfl⟩
  rw [this, card_image_of_injective _ (fun x y h => (Prod.mk.inj h).1)]
  simp [mB]

/- English proof (translation)
Simplify using `only [sg, sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_sign_eq_two_rho, sum_row_count, sum_column_count, wtB]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sum_sg (B : Finset (Fin n × Fin n)) (a : Fin n) :
    ∑ b, sg B a b = 2 * (rhoV n a - wtB B a) := by
  simp only [sg, sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_sign_eq_two_rho, sum_row_count, sum_column_count, wtB]
  ring

/- English proof (translation)
Establish `key : ∀ a b : Fin n, a < b → sg B a b = 1 ∨ sg B a b = -1`. Introduce `a b h`. Establish `h1 : (b, a) ∉ B` using `fun hm => asymm h (hB _ hm)`. Distinguish the cases in `hm : (a, b) ∈ B`. Use `right`.

Simplify using `[sg, s0, mB, h, h1, hm]`. Evaluate the numerical expressions. Use `left`. Simplify using `[sg, s0, mB, h, h1, hm]`. Break down `lt_or_gt_of_ne hab with h | h` into its components or cases.

Conclude with `key a b h`. Rewrite using `[sg_anti B b a]`. Apply the tactic sequence `rcases key b a h with h' | h' <;> simp [h']`.
-/
theorem sg_val (B : Finset (Fin n × Fin n)) (hB : ∀ p ∈ B, p.1 < p.2) {a b : Fin n} (hab : a ≠ b) :
    sg B a b = 1 ∨ sg B a b = -1 := by
  have key : ∀ a b : Fin n, a < b → sg B a b = 1 ∨ sg B a b = -1 := by
    intro a b h
    have h1 : (b, a) ∉ B := fun hm => asymm h (hB _ hm)
    by_cases hm : (a, b) ∈ B
    · right; simp [sg, s0, mB, h, h1, hm]; norm_num
    · left; simp [sg, s0, mB, h, h1, hm]
  rcases lt_or_gt_of_ne hab with h | h
  · exact key a b h
  · rw [sg_anti B b a]
    rcases key b a h with h' | h' <;> simp [h']

/- English proof (translation)
Rewrite using `[sum_comm]`. Use `sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[sum_comm]`.
-/
theorem cyc (f : Fin n → Fin n → Fin n → ℝ) : ∑ a, ∑ b, ∑ c, f b c a = ∑ a, ∑ b, ∑ c, f a b c := by
  rw [sum_comm]
  refine sum_congr rfl fun b _ => ?_
  rw [sum_comm]

end GlobalTheory.CompanionTheory.RealMult.Short

namespace GlobalTheory.CompanionTheory.RealMult

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open Formalism.REAL (dot nsq)
open Short

end GlobalTheory.CompanionTheory.RealMult
