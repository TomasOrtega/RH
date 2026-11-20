import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsMirClass
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsConjRenumber

noncomputable section

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

namespace GlobalTheory.GLm.FirstPattern

def front (N k s : ℕ) (h : k + s ≤ N) : Equiv.Perm (Fin N) where
  toFun a := ⟨if (a : ℕ) < k then s + a else if (a : ℕ) < k + s then a - k else a, by
    have := a.2; split_ifs <;> omega⟩
  invFun a := ⟨if (a : ℕ) < s then k + a else if (a : ℕ) < k + s then a - s else a, by
    have := a.2; split_ifs <;> omega⟩
  left_inv a := by
    apply Fin.ext
    simp only
    split_ifs <;> omega
  right_inv a := by
    apply Fin.ext
    simp only
    split_ifs <;> omega

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem front_val (N k s : ℕ) (h : k + s ≤ N) (a : Fin N) :
    ((front N k s h a : Fin N) : ℕ) = if (a : ℕ) < k then s + a else if (a : ℕ) < k + s then a - k else a := rfl

/- English proof (translation)
Simplify using `only [phI, IsW, Fin.lt_def, front_val]`. Apply the tactic sequence `split_ifs <;> omega`.
-/
theorem phI_front (N k s : ℕ) (h : k + s ≤ N) (a b : Fin N) :
    phI k s 0 (front N k s h a) (front N k s h b) ↔ (a : ℕ) < b ∧ ¬ ((a : ℕ) < k ∧ (b : ℕ) = k) := by
  simp only [phI, IsW, Fin.lt_def, front_val]
  split_ifs <;> omega

/- English proof (translation)
Simplify using `only [eeI, IsW, front_val]`. Apply the tactic sequence `split_ifs <;> omega`.
-/
theorem eeI_front (N k s : ℕ) (h : k + s ≤ N) (a b : Fin N) :
    eeI k s (front N k s h a) (front N k s h b) ↔ (b : ℕ) = a + 1 ∧ (b : ℕ) ≠ k := by
  simp only [eeI, IsW, front_val]
  split_ifs <;> omega

/- English proof (translation)
Take `rfl : P = P'` from `funext fun M => propext (hP M)`. Unfold `eDat`. Use `congr 1`. Use `Finset.sum_congr rfl fun u hu => ?_` and prove the remaining obligations. Rewrite using `[hφ _ (Finset.mem_filter.1 hu).2]`.
-/
theorem eDat_congr (g N : ℕ) [NeZero g] (P P' : Mt g N → Prop) (φ φ' : Mt g N → ZMod g)
    (ψ : AddChar (ZMod g) ℂ) (hP : ∀ M, P M ↔ P' M) (hφ : ∀ M, P' M → φ M = φ' M) :
    eDat g N P φ ψ = eDat g N P' φ' ψ := by
  obtain rfl : P = P' := funext fun M => propext (hP M)
  unfold eDat
  congr 1
  refine Finset.sum_congr rfl fun u hu => ?_
  rw [hφ _ (Finset.mem_filter.1 hu).2]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `⟨fun a b => ⟨fun hab => ?_, fun hab => ?_⟩, fun a ha => ?_⟩` and prove the remaining obligations. Establish `hab' : (b : ℕ) < a` using `hab`. Rewrite using `[h a b (by omega), Matrix.one_apply_ne hab.ne']`.

Substitute `hab` using the available equality. Rewrite using `[h a a (by omega), Matrix.one_apply_eq]`. Establish `haN : a < N` using `by omega`. Rewrite using `[entN, dif_pos ⟨haN, hk⟩, h _ _ (by simp [ha]), Matrix.one_apply_ne]`. Introduce `e`.

Use `congrArg Fin.val e` as an intermediate fact. Simplify using `only at this`. Use linear arithmetic over natural numbers and integers. Introduce and unpack `⟨hU, hz⟩ a b hab`. Break down `lt_trichotomy a b with h | h | h` into its components or cases.

Establish `h' : (a : ℕ) < b` using `h`. Establish `h2 : (a : ℕ) < k ∧ (b : ℕ) = k`. Assume the negation of the conclusion as `hh`. Conclude with `hab ⟨h', hh⟩`. Use `hz a h2.1` as an intermediate fact.

Rewrite `this` using `[entN, dif_pos ⟨a.2, hk⟩]`. Establish `hb : b = ⟨k, hk⟩` using `Fin.ext h2.2`. Rewrite using `[Matrix.one_apply_ne h.ne, hb]`. Conclude with `this`. Rewrite using `[(hU a b).2 h, h, Matrix.one_apply_eq]`.

Rewrite using `[(hU a b).1 h, Matrix.one_apply_ne h.ne']`.
-/
theorem inPat_iff {g : ℕ} [Fact g.Prime] (N k : ℕ) (hk : k < N) (M : Mt g N) :
    InPat (fun a b : Fin N => (a : ℕ) < b ∧ ¬ ((a : ℕ) < k ∧ (b : ℕ) = k)) M ↔
      IsUniUp M ∧ ∀ a, a < k → entN M a k = 0 := by
  constructor
  · intro h
    refine ⟨fun a b => ⟨fun hab => ?_, fun hab => ?_⟩, fun a ha => ?_⟩
    · have hab' : (b : ℕ) < a := hab
      rw [h a b (by omega), Matrix.one_apply_ne hab.ne']
    · subst hab
      rw [h a a (by omega), Matrix.one_apply_eq]
    · have haN : a < N := by omega
      rw [entN, dif_pos ⟨haN, hk⟩, h _ _ (by simp [ha]), Matrix.one_apply_ne]
      intro e
      have := congrArg Fin.val e
      simp only at this
      omega
  · rintro ⟨hU, hz⟩ a b hab
    rcases lt_trichotomy a b with h | h | h
    · have h' : (a : ℕ) < b := h
      have h2 : (a : ℕ) < k ∧ (b : ℕ) = k := by
        by_contra hh
        exact hab ⟨h', hh⟩
      have := hz a h2.1
      rw [entN, dif_pos ⟨a.2, hk⟩] at this
      have hb : b = ⟨k, hk⟩ := Fin.ext h2.2
      rw [Matrix.one_apply_ne h.ne, hb]
      exact this
    · rw [(hU a b).2 h, h, Matrix.one_apply_eq]
    · rw [(hU a b).1 h, Matrix.one_apply_ne h.ne']

/- English proof (translation)
Establish `h1 : ∀ a : Fin N, (∑ b : Fin N, if ((b : ℕ) = a + 1 ∧ (b : ℕ) ≠ k) then M a b else 0) = entN M a (a + 1)`. Introduce `a`. Distinguish the cases in `ha : (a : ℕ) + 1 < N`. Rewrite using `[Finset.sum_eq_single (⟨a + 1, ha⟩ : Fin N)]`. Distinguish the cases in `hk : (a : ℕ) + 1 = k`.

Rewrite using `[if_neg (by simp [hk]), hk, hz a (by omega)]`. Rewrite using `[if_pos (by simp [hk]), entN, dif_pos ⟨a.2, ha⟩]`. Introduce `b _ hb`. Rewrite using `[if_neg]`. Introduce and unpack `⟨e, -⟩`.

Conclude with `hb (Fin.ext e)`. Simplify using the standard rewrite rules. Rewrite using `[entN, dif_neg (by omega)]`. Use `Finset.sum_eq_zero fun b _ => if_neg ?_` and prove the remaining obligations. Use `b.2` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Establish `h2 : ∑ i ∈ Finset.range (N - 1), entN M i (i + 1) = ∑ i ∈ Finset.range N, entN M i (i + 1)`. Use `Finset.sum_subset (Finset.range_subset_range.2 (Nat.sub_le _ _)) fun i _ hi => ?_` and prove the remaining obligations. Rewrite `hi` using `[Finset.mem_range]`. Rewrite using `[entN, dif_neg (by omega)]`.

Rewrite using `[h2, Finset.sum_range, sumAt]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[← h1 a]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Reduce the equality to equality of the corresponding arguments.
-/
theorem sumAt_eq {g : ℕ} [Fact g.Prime] (N k : ℕ) (M : Mt g N) (hz : ∀ a, a < k → entN M a k = 0) :
    sumAt (fun a b : Fin N => (b : ℕ) = a + 1 ∧ (b : ℕ) ≠ k) M =
      ∑ i ∈ Finset.range (N - 1), entN M i (i + 1) := by
  have h1 : ∀ a : Fin N, (∑ b : Fin N, if ((b : ℕ) = a + 1 ∧ (b : ℕ) ≠ k) then M a b else 0) =
      entN M a (a + 1) := by
    intro a
    by_cases ha : (a : ℕ) + 1 < N
    · rw [Finset.sum_eq_single (⟨a + 1, ha⟩ : Fin N)]
      · by_cases hk : (a : ℕ) + 1 = k
        · rw [if_neg (by simp [hk]), hk, hz a (by omega)]
        · rw [if_pos (by simp [hk]), entN, dif_pos ⟨a.2, ha⟩]
      · intro b _ hb
        rw [if_neg]
        rintro ⟨e, -⟩
        exact hb (Fin.ext e)
      · simp
    · rw [entN, dif_neg (by omega)]
      refine Finset.sum_eq_zero fun b _ => if_neg ?_
      have := b.2
      omega
  have h2 : ∑ i ∈ Finset.range (N - 1), entN M i (i + 1) = ∑ i ∈ Finset.range N, entN M i (i + 1) := by
    refine Finset.sum_subset (Finset.range_subset_range.2 (Nat.sub_le _ _)) fun i _ hi => ?_
    rw [Finset.mem_range] at hi
    rw [entN, dif_neg (by omega)]
  rw [h2, Finset.sum_range, sumAt]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← h1 a]
  refine Finset.sum_congr rfl fun b _ => ?_
  congr

/- English proof (translation)
Introduce `g _ ψ N k s hN χ hχ`. Establish `h : k + s ≤ N` using `by omega`. Rewrite using `[← GlobalTheory.GLm.tr_ePat_renumber g ψ N (phI k s 0) (eeI k s) (front N k s h) χ hχ]`. Use `congr 1`. Establish `e1 : (fun a b => phI k s 0 (front N k s h a) (front N k s h b)) = fun a b : Fin N => (a : ℕ) < b ∧ ¬ ((a : ℕ) < k ∧ (b : ℕ) = k)`.

Use function extensionality and compare the values at `fun a => funext fun b => propext (phI_front N k s h a b)`. Establish `e2 : (fun a b => eeI k s (front N k s h a) (front N k s h b)) = fun a b : Fin N => (b : ℕ) = a + 1 ∧ (b : ℕ) ≠ k`. Use function extensionality and compare the values at `fun a => funext fun b => propext (eeI_front N k s h a b)`. Rewrite using `[e1, e2, ePat, eJ']`. Conclude with `eDat_congr g N _ _ _ _ ψ (inPat_iff N k (by omega)) fun M hM => sumAt_eq N k M hM.2`.
-/
theorem tr_first_pattern : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) (N k s : ℕ), N = k + 2 * s + 1 →
    ∀ χ : Gn g N → ℂ, IsClass χ → tr (ePat g N (phI k s 0) (eeI k s) ψ) χ = tr (eJ' g N k ψ) χ := by
  intro g _ ψ N k s hN χ hχ
  have h : k + s ≤ N := by omega
  rw [← GlobalTheory.GLm.tr_ePat_renumber g ψ N (phI k s 0) (eeI k s) (front N k s h) χ hχ]
  congr 1
  have e1 : (fun a b => phI k s 0 (front N k s h a) (front N k s h b)) =
      fun a b : Fin N => (a : ℕ) < b ∧ ¬ ((a : ℕ) < k ∧ (b : ℕ) = k) :=
    funext fun a => funext fun b => propext (phI_front N k s h a b)
  have e2 : (fun a b => eeI k s (front N k s h a) (front N k s h b)) =
      fun a b : Fin N => (b : ℕ) = a + 1 ∧ (b : ℕ) ≠ k :=
    funext fun a => funext fun b => propext (eeI_front N k s h a b)
  rw [e1, e2, ePat, eJ']
  exact eDat_congr g N _ _ _ _ ψ (inPat_iff N k (by omega)) fun M hM => sumAt_eq N k M hM.2

end GlobalTheory.GLm.FirstPattern
