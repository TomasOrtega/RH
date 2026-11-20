import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.UpUMul

namespace Formalism.L2.SG.PtCell

open Matrix

variable {K : Type*} [Field K] {N : ℕ}

def LoU (L : Matrix (Fin N) (Fin N) K) : Prop := ∀ i j, (i < j → L i j = 0) ∧ (i = j → L i j = 1)

def UpU (U : Matrix (Fin N) (Fin N) K) : Prop := ∀ i j, (j < i → U i j = 0) ∧ (i = j → U i j = 1)

/- English proof (translation)
Introduce `i j hij` and use `(h i j).1 hij`.
-/
theorem loU_bt {L : Matrix (Fin N) (Fin N) K} (h : LoU L) : L.BlockTriangular OrderDual.toDual :=
  fun i j hij => (h i j).1 hij

/- English proof (translation)
Introduce `i j hij` and use `(h i j).1 hij`.
-/
theorem upU_bt {U : Matrix (Fin N) (Fin N) K} (h : UpU U) : U.BlockTriangular id :=
  fun i j hij => (h i j).1 hij

/- English proof (translation)
Rewrite using `[det_of_isLowerTriangular L (loU_bt h)]`. Conclude with `Finset.prod_eq_one fun i _ => (h i i).2 rfl`.
-/
theorem loU_det {L : Matrix (Fin N) (Fin N) K} (h : LoU L) : L.det = 1 := by
  rw [det_of_isLowerTriangular L (loU_bt h)]
  exact Finset.prod_eq_one fun i _ => (h i i).2 rfl

/- English proof (translation)
Rewrite using `[det_of_isUpperTriangular (upU_bt h)]`. Conclude with `Finset.prod_eq_one fun i _ => (h i i).2 rfl`.
-/
theorem upU_det {U : Matrix (Fin N) (Fin N) K} (h : UpU U) : U.det = 1 := by
  rw [det_of_isUpperTriangular (upU_bt h)]
  exact Finset.prod_eq_one fun i _ => (h i i).2 rfl

/- English proof (translation)
Introduce `i j`. Use `⟨fun hij => (BlockTriangular.mul (loU_bt hA) (loU_bt hB)) hij, fun hij => ?_⟩` and prove the remaining obligations. Substitute `hij` using the available equality. Rewrite using `[mul_apply, Finset.sum_eq_single i]`. Rewrite using `[(hA i i).2 rfl, (hB i i).2 rfl, one_mul]`.

Introduce `k _ hk`. Break down `lt_or_gt_of_ne hk with h | h` into its components or cases. Rewrite using `[(hB k i).1 h, mul_zero]`. Rewrite using `[(hA i k).1 h, zero_mul]`. Simplify using the standard rewrite rules.
-/
theorem loU_mul {A B : Matrix (Fin N) (Fin N) K} (hA : LoU A) (hB : LoU B) : LoU (A * B) := by
  intro i j
  refine ⟨fun hij => (BlockTriangular.mul (loU_bt hA) (loU_bt hB)) hij, fun hij => ?_⟩
  subst hij
  rw [mul_apply, Finset.sum_eq_single i]
  · rw [(hA i i).2 rfl, (hB i i).2 rfl, one_mul]
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with h | h
    · rw [(hB k i).1 h, mul_zero]
    · rw [(hA i k).1 h, zero_mul]
  · simp

/- English proof (translation)
Apply the tactic sequence `first | exact UpperTheory.Reformulated.B.Qh21.upU_mul .. | (apply UpperTheory.Reformulated.B.Qh21.upU_mul <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qh21.upU_mul <;> assumption) | (apply @UpperTheory.Reformulated.B.Qh21.upU_mul <;> assumption) | (intros; apply @U …`.
-/
theorem upU_mul {A B : Matrix (Fin N) (Fin N) K} (hA : UpU A) (hB : UpU B) : UpU (A * B) := by
  first | exact UpperTheory.Reformulated.B.Qh21.upU_mul .. | (apply UpperTheory.Reformulated.B.Qh21.upU_mul <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qh21.upU_mul <;> assumption) | (apply @UpperTheory.Reformulated.B.Qh21.upU_mul <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qh21.upU_mul <;> assumption) | (apply @UpperTheory.Reformulated.B.Qh21.upU_mul <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.Qh21.upU_mul K ‹_› N A B hA hB | exact @UpperTheory.Reformulated.B.Qh21.upU_mul K ‹_› N A B hA | exact @UpperTheory.Reformulated.B.Qh21.upU_mul K ‹_› N A B | exact @UpperTheory.Reformulated.B.Qh21.upU_mul K ‹_› N A | exact @UpperTheory.Reformulated.B.Qh21.upU_mul K ‹_› N | exact @UpperTheory.Reformulated.B.Qh21.upU_mul K ‹_› | exact @UpperTheory.Reformulated.B.Qh21.upU_mul K

/- English proof (translation)
Establish `hu : IsUnit L.det` using `by rw [loU_det h]; exact isUnit_one`. Use `haveI := invertibleOfIsUnitDet L hu`. Establish `hbt : L⁻¹.BlockTriangular OrderDual.toDual` using `blockTriangular_inv_of_blockTriangular (loU_bt h)`. Introduce `i j`. Use `⟨fun hij => hbt hij, fun hij => ?_⟩` and prove the remaining obligations.

Substitute `hij` using the available equality. Establish `e` using `congrFun (congrFun (mul_nonsing_inv L hu) i) i`. Rewrite `e` using `[mul_apply, Finset.sum_eq_single i, (h i i).2 rfl, one_mul]`. Simplify using `using e`. Introduce `k _ hk`.

Break down `lt_or_gt_of_ne hk with h' | h'` into its components or cases. Rewrite using `[hbt h', mul_zero]`. Rewrite using `[(h i k).1 h', zero_mul]`. Simplify using the standard rewrite rules.
-/
theorem loU_inv {L : Matrix (Fin N) (Fin N) K} (h : LoU L) : LoU L⁻¹ := by
  have hu : IsUnit L.det := by rw [loU_det h]; exact isUnit_one
  haveI := invertibleOfIsUnitDet L hu
  have hbt : L⁻¹.BlockTriangular OrderDual.toDual := blockTriangular_inv_of_blockTriangular (loU_bt h)
  intro i j
  refine ⟨fun hij => hbt hij, fun hij => ?_⟩
  subst hij
  have e := congrFun (congrFun (mul_nonsing_inv L hu) i) i
  rw [mul_apply, Finset.sum_eq_single i, (h i i).2 rfl, one_mul] at e
  · simpa using e
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with h' | h'
    · rw [hbt h', mul_zero]
    · rw [(h i k).1 h', zero_mul]
  · simp

/- English proof (translation)
Establish `hu : IsUnit U.det` using `by rw [upU_det h]; exact isUnit_one`. Use `haveI := invertibleOfIsUnitDet U hu`. Establish `hbt : U⁻¹.BlockTriangular id` using `blockTriangular_inv_of_blockTriangular (upU_bt h)`. Introduce `i j`. Use `⟨fun hij => hbt hij, fun hij => ?_⟩` and prove the remaining obligations.

Substitute `hij` using the available equality. Establish `e` using `congrFun (congrFun (mul_nonsing_inv U hu) i) i`. Rewrite `e` using `[mul_apply, Finset.sum_eq_single i, (h i i).2 rfl, one_mul]`. Simplify using `using e`. Introduce `k _ hk`.

Break down `lt_or_gt_of_ne hk with h' | h'` into its components or cases. Rewrite using `[(h i k).1 h', zero_mul]`. Rewrite using `[hbt h', mul_zero]`. Simplify using the standard rewrite rules.
-/
theorem upU_inv {U : Matrix (Fin N) (Fin N) K} (h : UpU U) : UpU U⁻¹ := by
  have hu : IsUnit U.det := by rw [upU_det h]; exact isUnit_one
  haveI := invertibleOfIsUnitDet U hu
  have hbt : U⁻¹.BlockTriangular id := blockTriangular_inv_of_blockTriangular (upU_bt h)
  intro i j
  refine ⟨fun hij => hbt hij, fun hij => ?_⟩
  subst hij
  have e := congrFun (congrFun (mul_nonsing_inv U hu) i) i
  rw [mul_apply, Finset.sum_eq_single i, (h i i).2 rfl, one_mul] at e
  · simpa using e
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with h' | h'
    · rw [(h i k).1 h', zero_mul]
    · rw [hbt h', mul_zero]
  · simp

/- English proof (translation)
It suffices to establish `h : ∀ n (a : Fin N), a.val = n → f a = a from h _ a rfl`. Introduce `n`. Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Introduce `a ha`.

Break down `(hle a).lt_or_eq with hlt | heq` into its components or cases. It suffices to derive a contradiction. Establish `h1 : f (f a) = f a` using `ih (f a).val (by rw [← ha]; exact hlt) (f a) rfl`. Conclude with `(ne_of_lt hlt) (hf h1)`. Conclude with `heq`.
-/
theorem eq_self_of_le {f : Fin N → Fin N} (hf : Function.Injective f) (hle : ∀ a, f a ≤ a) (a : Fin N) : f a = a := by
  suffices h : ∀ n (a : Fin N), a.val = n → f a = a from h _ a rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a ha
    rcases (hle a).lt_or_eq with hlt | heq
    · exfalso
      have h1 : f (f a) = f a := ih (f a).val (by rw [← ha]; exact hlt) (f a) rfl
      exact (ne_of_lt hlt) (hf h1)
    · exact heq

def mono (π : Fin N → Fin N) (c : Fin N → K) : Matrix (Fin N) (Fin N) K := fun a b => if b = π a then c a else 0

/- English proof (translation)
Rewrite using `[mul_apply, Finset.sum_eq_single (π b)]`. Simplify using `[mono, hπ]`. Introduce `k _ hk`. Establish `: b ≠ π k` using `fun hb => hk (by rw [hb, hπ])`. Simplify using `[mono, this]`.

Simplify using the standard rewrite rules.
-/
theorem mul_mono_apply (A : Matrix (Fin N) (Fin N) K) {π : Fin N → Fin N} (hπ : ∀ a, π (π a) = a) (c : Fin N → K)
    (a b : Fin N) : (A * mono π c) a b = A a (π b) * c (π b) := by
  rw [mul_apply, Finset.sum_eq_single (π b)]
  · simp [mono, hπ]
  · intro k _ hk
    have : b ≠ π k := fun hb => hk (by rw [hb, hπ])
    simp [mono, this]
  · simp

/- English proof (translation)
Rewrite using `[mul_apply, Finset.sum_eq_single (π a)]`. Simplify using `[mono]`. Introduce `k _ hk`. Simplify using `[mono, hk]`. Simplify using the standard rewrite rules.
-/
theorem mono_mul_apply (A : Matrix (Fin N) (Fin N) K) (π : Fin N → Fin N) (c : Fin N → K) (a b : Fin N) :
    (mono π c * A) a b = c a * A (π a) b := by
  rw [mul_apply, Finset.sum_eq_single (π a)]
  · simp [mono]
  · intro k _ hk
    simp [mono, hk]
  · simp

/- English proof (translation)
Establish `hu1 : IsUnit U₁.det` using `by rw [upU_det hU₁]; exact isUnit_one`. Establish `hu2 : IsUnit L₂.det` using `by rw [loU_det hL₂]; exact isUnit_one`. Establish `key : L₂⁻¹ * L₁ * mono π c = mono ρ d * (U₂ * U₁⁻¹)`. Establish `h' : L₁ * (mono π c * U₁) = L₂ * (mono ρ d * U₂)` using `by simpa only [Matrix.mul_assoc] using h`. Establish `e1 : L₂⁻¹ * L₁ * mono π c = L₂⁻¹ * ((L₁ * (mono π c * U₁)) * U₁⁻¹)`.

Simplify using `only [Matrix.mul_assoc, mul_nonsing_inv _ hu1, Matrix.mul_one]`. Establish `e2 : L₂⁻¹ * ((L₂ * (mono ρ d * U₂)) * U₁⁻¹) = mono ρ d * (U₂ * U₁⁻¹)`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc L₂⁻¹ L₂, nonsing_inv_mul _ hu2, Matrix.one_mul]`. Rewrite using `[e1, h', e2]`.

Establish `hL` using `loU_mul (loU_inv hL₂) hL₁`. Establish `hU` using `upU_mul hU₂ (upU_inv hU₁)`. Establish `e : ∀ a b, (L₂⁻¹ * L₁) a (π b) * c (π b) = d a * (U₂ * U₁⁻¹) (ρ a) b`. Introduce `a b`. Use `congrFun (congrFun key a) b` as an intermediate fact.

Rewrite `this` using `[mul_mono_apply _ hπ, mono_mul_apply]`. Then use the resulting hypothesis. Establish `hle : ∀ a, π (ρ a) ≤ a`. Introduce `a`. Establish `h1` using `e a (ρ a)`. Rewrite `h1` using `[(hU (ρ a) (ρ a)).2 rfl, mul_one]`.

Assume the negation of the conclusion as `hlt`. Use `push Not at hlt`. Rewrite `h1` using `[(hL a (π (ρ a))).1 hlt, zero_mul]`. Conclude with `hd a h1.symm`. Establish `hinj : Function.Injective (fun a => π (ρ a))`.

Introduce `a b hab`. Use `congrArg π hab` as an intermediate fact. Simplify using `only [hπ] at this`. Simplify `congrArg ρ this` using `[hρ]`. Establish `hid : ∀ a, π (ρ a) = a` using `eq_self_of_le hinj hle`.

Establish `hpr : π = ρ`. Use function extensionality and compare the values at `a`. Use `congrArg π (hid a)` as an intermediate fact. Rewrite `this` using `[hπ]`. Conclude with `this.symm`.

Use `⟨hpr, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `a`. Establish `h2` using `e a (π a)`. Rewrite `h2` using `[hπ, (hL a a).2 rfl, one_mul, ← hpr, (hU (π a) (π a)).2 rfl, mul_one]`. Conclude with `h2`.
-/
theorem mono_uniq {π ρ : Fin N → Fin N} (hπ : ∀ a, π (π a) = a) (hρ : ∀ a, ρ (ρ a) = a) {c d : Fin N → K}
    (hd : ∀ a, d a ≠ 0) {L₁ L₂ U₁ U₂ : Matrix (Fin N) (Fin N) K} (hL₁ : LoU L₁) (hL₂ : LoU L₂)
    (hU₁ : UpU U₁) (hU₂ : UpU U₂) (h : L₁ * mono π c * U₁ = L₂ * mono ρ d * U₂) : π = ρ ∧ c = d := by
  have hu1 : IsUnit U₁.det := by rw [upU_det hU₁]; exact isUnit_one
  have hu2 : IsUnit L₂.det := by rw [loU_det hL₂]; exact isUnit_one
  have key : L₂⁻¹ * L₁ * mono π c = mono ρ d * (U₂ * U₁⁻¹) := by
    have h' : L₁ * (mono π c * U₁) = L₂ * (mono ρ d * U₂) := by simpa only [Matrix.mul_assoc] using h
    have e1 : L₂⁻¹ * L₁ * mono π c = L₂⁻¹ * ((L₁ * (mono π c * U₁)) * U₁⁻¹) := by
      simp only [Matrix.mul_assoc, mul_nonsing_inv _ hu1, Matrix.mul_one]
    have e2 : L₂⁻¹ * ((L₂ * (mono ρ d * U₂)) * U₁⁻¹) = mono ρ d * (U₂ * U₁⁻¹) := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc L₂⁻¹ L₂, nonsing_inv_mul _ hu2, Matrix.one_mul]
    rw [e1, h', e2]
  have hL := loU_mul (loU_inv hL₂) hL₁
  have hU := upU_mul hU₂ (upU_inv hU₁)
  have e : ∀ a b, (L₂⁻¹ * L₁) a (π b) * c (π b) = d a * (U₂ * U₁⁻¹) (ρ a) b := by
    intro a b
    have := congrFun (congrFun key a) b
    rwa [mul_mono_apply _ hπ, mono_mul_apply] at this
  have hle : ∀ a, π (ρ a) ≤ a := by
    intro a
    have h1 := e a (ρ a)
    rw [(hU (ρ a) (ρ a)).2 rfl, mul_one] at h1
    by_contra hlt
    push Not at hlt
    rw [(hL a (π (ρ a))).1 hlt, zero_mul] at h1
    exact hd a h1.symm
  have hinj : Function.Injective (fun a => π (ρ a)) := by
    intro a b hab
    have := congrArg π hab
    simp only [hπ] at this
    simpa [hρ] using congrArg ρ this
  have hid : ∀ a, π (ρ a) = a := eq_self_of_le hinj hle
  have hpr : π = ρ := by
    funext a
    have := congrArg π (hid a)
    rw [hπ] at this
    exact this.symm
  refine ⟨hpr, ?_⟩
  funext a
  have h2 := e a (π a)
  rw [hπ, (hL a a).2 rfl, one_mul, ← hpr, (hU (π a) (π a)).2 rfl, mul_one] at h2
  exact h2

section Pt

open Formalism.MainNotions.S

def pperm : List (K × ℕ) → ℕ → ℕ
  | [], i => i
  | (_, s) :: bs, i => if i < s then s - 1 - i else s + pperm bs (i - s)

def pval : List (K × ℕ) → ℕ → K
  | [], _ => 0
  | (t, s) :: bs, i => if i < s then t else pval bs (i - s)

/- English proof (translation)
Proceed by induction on `bs generalizing i j with`. Consider the case `nil => simp at hi`. Consider the case `cons b bs ih`. Take `⟨t, s⟩` from `b`. Simplify using `only [List.map_cons, List.sum_cons] at hi`.

Distinguish the cases in `his : i < s`. Distinguish the cases in `hjs : j < s`. Simplify using `only [ptEntry, pperm, pval, his, hjs, and_self, if_true]`. Distinguish the cases in `h : i + j + 1 = s`. Rewrite using `[if_pos h, if_pos (by omega)]`.

Rewrite using `[if_neg h, if_neg (by omega)]`. Establish `hn : ¬ (s ≤ i ∧ s ≤ j)` using `by omega`. Simplify using `only [ptEntry, pperm, pval, his, hjs, and_false, if_false, if_true, hn]`. Rewrite using `[if_neg (by omega)]`. Distinguish the cases in `hjs : s ≤ j`.

Establish `hsi : s ≤ i` using `by omega`. Simplify using `only [ptEntry, pperm, pval, his, false_and, if_false, hsi, hjs, and_self, if_true]`. Rewrite using `[ih (i - s) (j - s) (by omega)]`. Distinguish the cases in `h : j - s = pperm bs (i - s)`. Rewrite using `[if_pos h, if_pos (by omega)]`.

Rewrite using `[if_neg h, if_neg (by omega)]`. Simplify using `only [ptEntry, pperm, pval, his, false_and, if_false, hjs, and_false]`. Rewrite using `[if_neg (by omega)]`.
-/
theorem ptEntry_eq (bs : List (K × ℕ)) (i j : ℕ) (hi : i < (bs.map Prod.snd).sum) :
    ptEntry bs i j = if j = pperm bs i then pval bs i else 0 := by
  induction bs generalizing i j with
  | nil => simp at hi
  | cons b bs ih =>
    obtain ⟨t, s⟩ := b
    simp only [List.map_cons, List.sum_cons] at hi
    by_cases his : i < s
    · by_cases hjs : j < s
      · simp only [ptEntry, pperm, pval, his, hjs, and_self, if_true]
        by_cases h : i + j + 1 = s
        · rw [if_pos h, if_pos (by omega)]
        · rw [if_neg h, if_neg (by omega)]
      · have hn : ¬ (s ≤ i ∧ s ≤ j) := by omega
        simp only [ptEntry, pperm, pval, his, hjs, and_false, if_false, if_true, hn]
        rw [if_neg (by omega)]
    · by_cases hjs : s ≤ j
      · have hsi : s ≤ i := by omega
        simp only [ptEntry, pperm, pval, his, false_and, if_false, hsi, hjs, and_self, if_true]
        rw [ih (i - s) (j - s) (by omega)]
        by_cases h : j - s = pperm bs (i - s)
        · rw [if_pos h, if_pos (by omega)]
        · rw [if_neg h, if_neg (by omega)]
      · simp only [ptEntry, pperm, pval, his, false_and, if_false, hjs, and_false]
        rw [if_neg (by omega)]

/- English proof (translation)
Proceed by induction on `bs generalizing i with`. Consider the case `nil => simp at hi`. Consider the case `cons b bs ih`. Take `⟨t, s⟩` from `b`. Simplify using `only [List.map_cons, List.sum_cons] at hi ⊢`.

Establish `hs : 1 ≤ s` using `hpos (t, s) (by simp)`. Establish `hpos' : ∀ b ∈ bs, 1 ≤ b.2` using `fun b hb => hpos b (by simp [hb])`. Simplify using `only [pperm]`. Use `split_ifs with h`. Use linear arithmetic over natural numbers and integers.

Use `ih hpos' (i - s) (by omega)` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem pperm_lt (bs : List (K × ℕ)) (hpos : ∀ b ∈ bs, 1 ≤ b.2) (i : ℕ) (hi : i < (bs.map Prod.snd).sum) :
    pperm bs i < (bs.map Prod.snd).sum := by
  induction bs generalizing i with
  | nil => simp at hi
  | cons b bs ih =>
    obtain ⟨t, s⟩ := b
    simp only [List.map_cons, List.sum_cons] at hi ⊢
    have hs : 1 ≤ s := hpos (t, s) (by simp)
    have hpos' : ∀ b ∈ bs, 1 ≤ b.2 := fun b hb => hpos b (by simp [hb])
    simp only [pperm]
    split_ifs with h
    · omega
    · have := ih hpos' (i - s) (by omega)
      omega

/- English proof (translation)
Proceed by induction on `bs generalizing i with`. Consider the case `nil => simp at hi`. Consider the case `cons b bs ih`. Take `⟨t, s⟩` from `b`. Simplify using `only [List.map_cons, List.sum_cons] at hi`.

Establish `hpos' : ∀ b ∈ bs, 1 ≤ b.2` using `fun b hb => hpos b (by simp [hb])`. Distinguish the cases in `h : i < s`. Simplify using `only [pperm, h, if_true]`. Rewrite using `[if_pos (by omega)]`. Use linear arithmetic over natural numbers and integers.

Simplify using `only [pperm, h, if_false]`. Rewrite using `[if_neg (by omega), Nat.add_sub_cancel_left, ih hpos' (i - s) (by omega)]`. Use linear arithmetic over natural numbers and integers.
-/
theorem pperm_pperm (bs : List (K × ℕ)) (hpos : ∀ b ∈ bs, 1 ≤ b.2) (i : ℕ) (hi : i < (bs.map Prod.snd).sum) :
    pperm bs (pperm bs i) = i := by
  induction bs generalizing i with
  | nil => simp at hi
  | cons b bs ih =>
    obtain ⟨t, s⟩ := b
    simp only [List.map_cons, List.sum_cons] at hi
    have hpos' : ∀ b ∈ bs, 1 ≤ b.2 := fun b hb => hpos b (by simp [hb])
    by_cases h : i < s
    · simp only [pperm, h, if_true]
      rw [if_pos (by omega)]
      omega
    · simp only [pperm, h, if_false]
      rw [if_neg (by omega), Nat.add_sub_cancel_left, ih hpos' (i - s) (by omega)]
      omega

/- English proof (translation)
Proceed by induction on `bs generalizing i with`. Consider the case `nil => simp at hi`. Consider the case `cons b bs ih`. Take `⟨t, s⟩` from `b`. Simplify using `only [List.map_cons, List.sum_cons] at hi`.

Establish `ht' : ∀ b ∈ bs, b.1 ≠ 0` using `fun b hb => ht b (by simp [hb])`. Simplify using `only [pval]`. Use `split_ifs with h`. Conclude with `ht (t, s) (by simp)`. Conclude with `ih ht' (i - s) (by omega)`.
-/
theorem pval_ne (bs : List (K × ℕ)) (ht : ∀ b ∈ bs, b.1 ≠ 0) (i : ℕ) (hi : i < (bs.map Prod.snd).sum) :
    pval bs i ≠ 0 := by
  induction bs generalizing i with
  | nil => simp at hi
  | cons b bs ih =>
    obtain ⟨t, s⟩ := b
    simp only [List.map_cons, List.sum_cons] at hi
    have ht' : ∀ b ∈ bs, b.1 ≠ 0 := fun b hb => ht b (by simp [hb])
    simp only [pval]
    split_ifs with h
    · exact ht (t, s) (by simp)
    · exact ih ht' (i - s) (by omega)

/- English proof (translation)
Proceed by induction on `bs generalizing cs with`. Consider the case `nil`. Consider the cases of `cs with`. Consider the case `nil => rfl`. Consider the case `cons c cs`.

Establish `: 1 ≤ c.2` using `hc c (by simp)`. Simplify using `only [List.map_nil, List.sum_nil, List.map_cons, List.sum_cons] at hsum`. Use linear arithmetic over natural numbers and integers. Consider the case `cons b bs ih`. Consider the cases of `cs with`.

Consider the case `nil`. Establish `: 1 ≤ b.2` using `hb b (by simp)`. Simplify using `only [List.map_nil, List.sum_nil, List.map_cons, List.sum_cons] at hsum`. Use linear arithmetic over natural numbers and integers. Consider the case `cons c cs`.

Take `⟨t, s⟩` from `b`. Take `⟨t', s'⟩` from `c`. Establish `hs : 1 ≤ s` using `hb (t, s) (by simp)`. Establish `hs' : 1 ≤ s'` using `hc (t', s') (by simp)`. Establish `hb' : ∀ b ∈ bs, 1 ≤ b.2` using `fun b h => hb b (by simp [h])`.

Establish `hc' : ∀ c ∈ cs, 1 ≤ c.2` using `fun c h => hc c (by simp [h])`. Simplify using `only [List.map_cons, List.sum_cons] at hsum hp hv`. Establish `h0` using `hp 0 (by omega)`. Establish `v0` using `hv 0 (by omega)`. Simplify using `only [pperm, pval, show 0 < s by omega, show 0 < s' by omega, if_true] at h0 v0`.

Establish `hss : s = s'` using `by omega`. Substitute `hss` using the available equality. Substitute `v0` using the available equality. Establish `htail : bs = cs`. Use `ih cs hb' hc' (by omega) (fun i hi => ?_) (fun i hi => ?_)` and prove the remaining obligations.

Use `hp (s + i) (by omega)` as an intermediate fact. Simplify using `only [pperm, show ¬ (s + i < s) by omega, if_false, Nat.add_sub_cancel_left] at this`. Use linear arithmetic over natural numbers and integers. Use `hv (s + i) (by omega)` as an intermediate fact. Simplify `this` using `only [pval, show ¬ (s + i < s) by omega, if_false, Nat.add_sub_cancel_left]`.

Rewrite using `[htail]`.
-/
theorem blocks_eq_of (bs : List (K × ℕ)) (cs : List (K × ℕ)) (hb : ∀ b ∈ bs, 1 ≤ b.2) (hc : ∀ c ∈ cs, 1 ≤ c.2)
    (hsum : (bs.map Prod.snd).sum = (cs.map Prod.snd).sum)
    (hp : ∀ i < (bs.map Prod.snd).sum, pperm bs i = pperm cs i)
    (hv : ∀ i < (bs.map Prod.snd).sum, pval bs i = pval cs i) : bs = cs := by
  induction bs generalizing cs with
  | nil =>
    cases cs with
    | nil => rfl
    | cons c cs =>
      have : 1 ≤ c.2 := hc c (by simp)
      simp only [List.map_nil, List.sum_nil, List.map_cons, List.sum_cons] at hsum
      omega
  | cons b bs ih =>
    cases cs with
    | nil =>
      have : 1 ≤ b.2 := hb b (by simp)
      simp only [List.map_nil, List.sum_nil, List.map_cons, List.sum_cons] at hsum
      omega
    | cons c cs =>
      obtain ⟨t, s⟩ := b
      obtain ⟨t', s'⟩ := c
      have hs : 1 ≤ s := hb (t, s) (by simp)
      have hs' : 1 ≤ s' := hc (t', s') (by simp)
      have hb' : ∀ b ∈ bs, 1 ≤ b.2 := fun b h => hb b (by simp [h])
      have hc' : ∀ c ∈ cs, 1 ≤ c.2 := fun c h => hc c (by simp [h])
      simp only [List.map_cons, List.sum_cons] at hsum hp hv
      have h0 := hp 0 (by omega)
      have v0 := hv 0 (by omega)
      simp only [pperm, pval, show 0 < s by omega, show 0 < s' by omega, if_true] at h0 v0
      have hss : s = s' := by omega
      subst hss
      subst v0
      have htail : bs = cs := by
        refine ih cs hb' hc' (by omega) (fun i hi => ?_) (fun i hi => ?_)
        · have := hp (s + i) (by omega)
          simp only [pperm, show ¬ (s + i < s) by omega, if_false, Nat.add_sub_cancel_left] at this
          omega
        · have := hv (s + i) (by omega)
          simpa only [pval, show ¬ (s + i < s) by omega, if_false, Nat.add_sub_cancel_left] using this
      rw [htail]

def pinv (p : Point K N) (a : Fin N) : Fin N :=
  ⟨pperm p.1 a.val, by
    have := pperm_lt p.1 (fun b hb => (p.2.1 b hb).2) a.val (by rw [p.2.2]; exact a.isLt)
    rwa [p.2.2] at this⟩

/- English proof (translation)
Apply `Fin.ext` to reduce the goal to its premises. Conclude with `pperm_pperm p.1 (fun b hb => (p.2.1 b hb).2) a.val (by rw [p.2.2]; exact a.isLt)`.
-/
theorem pinv_pinv (p : Point K N) (a : Fin N) : pinv p (pinv p a) = a := by
  apply Fin.ext
  exact pperm_pperm p.1 (fun b hb => (p.2.1 b hb).2) a.val (by rw [p.2.2]; exact a.isLt)

/- English proof (translation)
Use function extensionality and compare the values at `a b`. Simplify using `only [ptMat, mono, pinv]`. Rewrite using `[ptEntry_eq p.1 a.val b.val (by rw [p.2.2]; exact a.isLt)]`. Use `congr 1`. Simplify using `[Fin.ext_iff]`.
-/
theorem ptMat_eq_mono (p : Point K N) : ptMat p = mono (pinv p) (fun a => pval p.1 a.val) := by
  funext a b
  simp only [ptMat, mono, pinv]
  rw [ptEntry_eq p.1 a.val b.val (by rw [p.2.2]; exact a.isLt)]
  congr 1
  simp [Fin.ext_iff]

/- English proof (translation)
Take `⟨L₁, U₁, hL₁, hU₁, e₁⟩` from `hp`. Take `⟨L₂, U₂, hL₂, hU₂, e₂⟩` from `hq`. Rewrite `e₁`, `e₂` using `[ptMat_eq_mono]`. Take `⟨hπ, hc⟩` from `mono_uniq (pinv_pinv p) (pinv_pinv q) (fun a => pval_ne q.1 (fun b hb => (q.2.1 b hb).1) a.val (by rw [q.2.2]; exact a.isLt)) hL₁ hL₂ hU₁ hU₂ (e₁.symm.trans e₂)`. Apply `Subtype.ext` to reduce the goal to its premises.

Use `blocks_eq_of p.1 q.1 (fun b hb => (p.2.1 b hb).2) (fun b hb => (q.2.1 b hb).2) (by rw [p.2.2, q.2.2]) (fun i hi => ?_) (fun i hi => ?_)` and prove the remaining obligations. Rewrite `hi` using `[p.2.2]`. Use `congrArg Fin.val (congrFun hπ ⟨i, hi⟩)` as an intermediate fact. Simplify `this` using `[pinv]`. Rewrite `hi` using `[p.2.2]`.

Simplify using `using congrFun hc ⟨i, hi⟩`.
-/
theorem isInCell_uniq {Z : Matrix (Fin N) (Fin N) K} {p q : Point K N} (hp : IsInCell Z p) (hq : IsInCell Z q) :
    p = q := by
  obtain ⟨L₁, U₁, hL₁, hU₁, e₁⟩ := hp
  obtain ⟨L₂, U₂, hL₂, hU₂, e₂⟩ := hq
  rw [ptMat_eq_mono] at e₁ e₂
  obtain ⟨hπ, hc⟩ := mono_uniq (pinv_pinv p) (pinv_pinv q)
    (fun a => pval_ne q.1 (fun b hb => (q.2.1 b hb).1) a.val (by rw [q.2.2]; exact a.isLt))
    hL₁ hL₂ hU₁ hU₂ (e₁.symm.trans e₂)
  apply Subtype.ext
  refine blocks_eq_of p.1 q.1 (fun b hb => (p.2.1 b hb).2) (fun b hb => (q.2.1 b hb).2) (by rw [p.2.2, q.2.2])
    (fun i hi => ?_) (fun i hi => ?_)
  · rw [p.2.2] at hi
    have := congrArg Fin.val (congrFun hπ ⟨i, hi⟩)
    simpa [pinv] using this
  · rw [p.2.2] at hi
    simpa using congrFun hc ⟨i, hi⟩

end Pt

end Formalism.L2.SG.PtCell
