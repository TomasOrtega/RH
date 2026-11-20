import Mathlib
import Formalism.LocalToGlobal.Columns.OcbLevIsSym
import Formalism.LocalToGlobal.Columns.RecLevelSymF

open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Fix

variable {κ : Type} [CommRing κ]

/- English proof (translation)
Take `⟨hB, h0⟩` from `mem_HPar.mp hM`. Establish `hkr : k < r` using `by omega`. Distinguish the cases in `hi : i.val < r`. Take `⟨h1, h2, h3⟩` from `(mem_HPsymF_iff (show k + rS ≤ r by omega)).mp h0`. Establish `e : ∀ a b : Fin r, ((blk0 n κ h (List.replicate j t) ⟨M, hB⟩ : GL (Fin r) κ) : Matrix (Fin r) (Fin r) κ) a b = (M : Matrix (Fin n) (Fin n) κ) (Fin.castLE h a) (Fin.castLE h b)` using `fun a b => rfl`.

Establish `ei : i = Fin.castLE h ⟨i.val, hi⟩` using `Fin.ext rfl`. Establish `ek : (⟨k, hk⟩ : Fin n) = Fin.castLE h ⟨k, hkr⟩` using `Fin.ext rfl`. Rewrite using `[ei, ek, ← e]`. Distinguish the cases in `hik : i.val = k`. Rewrite using `[if_pos (by simpa using hik)]`.

Establish `: (⟨i.val, hi⟩ : Fin r) = ⟨k, hkr⟩` using `Fin.ext hik`. Rewrite using `[this]`. Conclude with `h2 _`. Rewrite using `[if_neg (by simpa using hik)]`. Distinguish the cases in `hrs : rS = 0`.

Substitute `hrs` using the available equality. Distinguish the cases in `hik' : i.val < k`. Conclude with `h3 ⟨i.val, hi⟩ ⟨k, hkr⟩ hik' (by simp)`. Apply `h1` to reduce the goal to its premises. Simplify using `only [symIdx]`.

Apply the tactic sequence `split_ifs <;> omega`. Apply `h1` to reduce the goal to its premises. Simplify using `only [symIdx]`. Apply the tactic sequence `split_ifs <;> omega`. Rewrite using `[if_neg (by omega)]`.

Apply `hB` to reduce the goal to its premises. Use `show coarse r (List.replicate j t) k < coarse r (List.replicate j t) i.val`. Rewrite using `[coarse_of_lt hkr, coarse_of_le (by omega)]`. Use linear arithmetic over natural numbers and integers.
-/
theorem sl_HJsym_col_k {n r k t j rS : ℕ} (h : r ≤ n) (hr : r = k + 2 * rS + 1) {M : GL (Fin n) κ}
    (hM : M ∈ HJsym κ n k r t j rS h) (i : Fin n) (hk : k < n) :
    (M : Matrix (Fin n) (Fin n) κ) i ⟨k, hk⟩ = if i.val = k then 1 else 0 := by
  obtain ⟨hB, h0⟩ := mem_HPar.mp hM
  have hkr : k < r := by omega
  by_cases hi : i.val < r
  · obtain ⟨h1, h2, h3⟩ := (mem_HPsymF_iff (show k + rS ≤ r by omega)).mp h0
    have e : ∀ a b : Fin r, ((blk0 n κ h (List.replicate j t) ⟨M, hB⟩ : GL (Fin r) κ) : Matrix (Fin r) (Fin r) κ) a b =
        (M : Matrix (Fin n) (Fin n) κ) (Fin.castLE h a) (Fin.castLE h b) := fun a b => rfl
    have ei : i = Fin.castLE h ⟨i.val, hi⟩ := Fin.ext rfl
    have ek : (⟨k, hk⟩ : Fin n) = Fin.castLE h ⟨k, hkr⟩ := Fin.ext rfl
    rw [ei, ek, ← e]
    by_cases hik : i.val = k
    · rw [if_pos (by simpa using hik)]
      have : (⟨i.val, hi⟩ : Fin r) = ⟨k, hkr⟩ := Fin.ext hik
      rw [this]
      exact h2 _
    · rw [if_neg (by simpa using hik)]
      by_cases hrs : rS = 0
      · subst hrs
        by_cases hik' : i.val < k
        · exact h3 ⟨i.val, hi⟩ ⟨k, hkr⟩ hik' (by simp)
        · apply h1
          simp only [symIdx]
          split_ifs <;> omega
      · apply h1
        simp only [symIdx]
        split_ifs <;> omega
  · rw [if_neg (by omega)]
    apply hB
    show coarse r (List.replicate j t) k < coarse r (List.replicate j t) i.val
    rw [coarse_of_lt hkr, coarse_of_le (by omega)]
    omega

end Fix

/- English proof (translation)
Introduce `X Pr R Ch m2 hm h hh w`. Establish `hj : m2 + 1 + 1 = R.m` using `by omega`. Establish `hw : h w ∈ (colLevSym Ch (m2 + 1) w).H` using `LevFam.mem_at _ ⟨h, hh⟩ w`. Rewrite `hw` using `[colLevSym_pred Ch hj]`. Establish `hk : R.k < R.N (m2 + 1)`.

Use `r_le_N_of_le (R := R) hj.ge` as an intermediate fact. Use `r_eq_sym R` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Use function extensionality and compare the values at `i`. Use `show ∑ l, ((h w : GL (Fin (R.N (m2 + 1))) (𝓞 X.E ⧸ w.1.asIdeal)) : Matrix _ _ (𝓞 X.E ⧸ w.1.asIdeal)) i l * Loc.eN (𝓞 X.E ⧸ w.1.asIdeal) (R.N (m2 + 1)) R.k l = Loc.eN (𝓞 X.E ⧸ w.1.asIdeal) (R.N (m2 + 1)) R.k i`.

Rewrite using `[Finset.sum_eq_single ⟨R.k, hk⟩]`. Rewrite using `[sl_HJsym_col_k (r_le_N_of_le (R := R) hj.ge) (r_eq_sym R) hw i hk]`. Simplify using `[Loc.eN]`. Introduce `l _ hl`. Establish `: l.val ≠ R.k` using `fun e => hl (Fin.ext e)`.

Simplify using `[Loc.eN, this]`. Introduce `hn`. Conclude with `absurd (Finset.mem_univ _) hn`.
-/
theorem lastLevel_fixes_basisVector_holds : FixESym := by
  intro X Pr R Ch m2 hm h hh w
  have hj : m2 + 1 + 1 = R.m := by omega
  have hw : h w ∈ (colLevSym Ch (m2 + 1) w).H := LevFam.mem_at _ ⟨h, hh⟩ w
  rw [colLevSym_pred Ch hj] at hw
  have hk : R.k < R.N (m2 + 1) := by
    have := r_le_N_of_le (R := R) hj.ge
    have := r_eq_sym R
    omega
  funext i
  show ∑ l, ((h w : GL (Fin (R.N (m2 + 1))) (𝓞 X.E ⧸ w.1.asIdeal)) : Matrix _ _ (𝓞 X.E ⧸ w.1.asIdeal)) i l *
      Loc.eN (𝓞 X.E ⧸ w.1.asIdeal) (R.N (m2 + 1)) R.k l = Loc.eN (𝓞 X.E ⧸ w.1.asIdeal) (R.N (m2 + 1)) R.k i
  rw [Finset.sum_eq_single ⟨R.k, hk⟩]
  · rw [sl_HJsym_col_k (r_le_N_of_le (R := R) hj.ge) (r_eq_sym R) hw i hk]
    simp [Loc.eN]
  · intro l _ hl
    have : l.val ≠ R.k := fun e => hl (Fin.ext e)
    simp [Loc.eN, this]
  · intro hn
    exact absurd (Finset.mem_univ _) hn

section EntY

variable {κ : Type} [CommRing κ]

def slAllowY (k rS r t P P' : ℕ) : Prop :=
  if P' < r then P < r ∧ ¬ symIdx k rS P' < symIdx k rS P ∧ ¬ (P < k ∧ P' = k + rS)
  else P < r ∨ (P - r) / t ≤ (P' - r) / t

/- English proof (translation)
Establish `hc : ∀ x : Fin n, coarse r (List.replicate j t) x.val = if x.val < r then 0 else (x.val - r) / t + 1` using `fun x => coarse_rep ht (by omega)`. Prove the components needed by the constructor for the conclusion. Introduce `hM`. Take `⟨hB, h0⟩` from `mem_HPar.mp hM`. Take `⟨h1, h2, h3⟩` from `(mem_HPsymF_iff hkr).mp h0`.

Establish `e : ∀ a b : Fin r, ((blk0 n κ h (List.replicate j t) ⟨M, hB⟩ : GL (Fin r) κ) : Matrix (Fin r) (Fin r) κ) a b = (M : Matrix (Fin n) (Fin n) κ) (Fin.castLE h a) (Fin.castLE h b)` using `fun a b => rfl`. Establish `hlow : ∀ P P' : Fin n, P'.val < r → ¬ P.val < r → (M : Matrix (Fin n) (Fin n) κ) P P' = 0`. Introduce `P P' hP' hP`. Apply `hB` to reduce the goal to its premises. Use `show coarse r (List.replicate j t) P'.val < coarse r (List.replicate j t) P.val`.

Rewrite using `[hc, hc, if_pos hP', if_neg hP]`. Conclude with `Nat.succ_pos _`. Use `⟨fun P hP => ?_, fun P P' hne hnz => ?_⟩` and prove the remaining obligations. Use `h2 ⟨P.val, hP⟩` as an intermediate fact. Rewrite `this` using `[e]`.

Conclude with `this`. Unfold `slAllowY split_ifs with hP'`. Establish `hP : P.val < r`. Assume the negation of the conclusion as `hP`. Conclude with `hnz (hlow P P' hP' hP)`.

Use `⟨hP, fun hlt => hnz ?_, fun ⟨a, b⟩ => hnz ?_⟩` and prove the remaining obligations. Use `h1 ⟨P.val, hP⟩ ⟨P'.val, hP'⟩ hlt` as an intermediate fact. Rewrite `this` using `[e]`. Conclude with `this`. Use `h3 ⟨P.val, hP⟩ ⟨P'.val, hP'⟩ a b` as an intermediate fact.

Rewrite `this` using `[e]`. Conclude with `this`. Assume the negation of the conclusion as `hc2 push Not at hc2`. Apply `hnz` to reduce the goal to its premises. Apply `hB` to reduce the goal to its premises.

Use `show coarse r (List.replicate j t) P'.val < coarse r (List.replicate j t) P.val`. Rewrite using `[hc, hc, if_neg hP', if_neg (by omega)]`. Generalize the expression as in `(P.val - r) / t = A at *`. Generalize the expression as in `(P'.val - r) / t = B at *`. Use linear arithmetic over natural numbers and integers.

Introduce and unpack `⟨hd, ho⟩`. Establish `hB : M ∈ blockUT n κ r (List.replicate j t)`. Introduce `P P' hlt`. Establish `hlt' : coarse r (List.replicate j t) P'.val < coarse r (List.replicate j t) P.val` using `hlt`. Assume the negation of the conclusion as `hnz`.

Establish `hne : P ≠ P'` using `fun e => by rw [e] at hlt'; exact lt_irrefl _ hlt'`. Use `ho P P' hne hnz` as an intermediate fact. Rewrite `hlt'` using `[hc, hc]`. Unfold `slAllowY at this`. Generalize the expression as in `(P.val - r) / t = A at *`.

Generalize the expression as in `(P'.val - r) / t = B at *`. Apply the tactic sequence `split_ifs at this hlt' <;> omega`. Use `mem_HPar.mpr ⟨hB, (mem_HPsymF_iff hkr).mpr ⟨fun a b hab => ?_, fun a => ?_, fun a b ha hb => ?_⟩⟩` and prove the remaining obligations. Use `show (M : Matrix (Fin n) (Fin n) κ) (Fin.castLE h a) (Fin.castLE h b) = 0`. Assume the negation of the conclusion as `hnz`.

Establish `hne : Fin.castLE h a ≠ Fin.castLE h b` using `fun e => by`. Establish `: a = b` using `Fin.castLE_injective h e`. Rewrite `hab` using `[this]`. Conclude with `lt_irrefl _ hab`. Use `ho _ _ hne hnz` as an intermediate fact.

Unfold `slAllowY at this`. Rewrite `this` using `[if_pos (show (Fin.castLE h b).val < r from b.2)]`. Conclude with `this.2.1 hab`. Conclude with `hd (Fin.castLE h a) a.2`. Use `show (M : Matrix (Fin n) (Fin n) κ) (Fin.castLE h a) (Fin.castLE h b) = 0`.

Assume the negation of the conclusion as `hnz`. Establish `hne : Fin.castLE h a ≠ Fin.castLE h b` using `fun e => by`. Use `congrArg Fin.val e` as an intermediate fact. Simplify using `only [Fin.val_castLE] at this`. Use linear arithmetic over natural numbers and integers.

Use `ho _ _ hne hnz` as an intermediate fact. Unfold `slAllowY at this`. Rewrite `this` using `[if_pos (show (Fin.castLE h b).val < r from b.2)]`. Conclude with `this.2.2 ⟨ha, hb⟩`.
-/
theorem sl_mem_HJsym_iff {n r k t j rS : ℕ} (h : r ≤ n) (hkr : k + rS ≤ r) (ht : 0 < t) (hn : n ≤ r + j * t)
    (M : GL (Fin n) κ) :
    M ∈ HJsym κ n k r t j rS h ↔ (∀ P : Fin n, P.val < r → (M : Matrix (Fin n) (Fin n) κ) P P = 1) ∧
      ∀ P P' : Fin n, P ≠ P' → (M : Matrix (Fin n) (Fin n) κ) P P' ≠ 0 → slAllowY k rS r t P.val P'.val := by
  have hc : ∀ x : Fin n, coarse r (List.replicate j t) x.val = if x.val < r then 0 else (x.val - r) / t + 1 :=
    fun x => coarse_rep ht (by omega)
  constructor
  · intro hM
    obtain ⟨hB, h0⟩ := mem_HPar.mp hM
    obtain ⟨h1, h2, h3⟩ := (mem_HPsymF_iff hkr).mp h0
    have e : ∀ a b : Fin r, ((blk0 n κ h (List.replicate j t) ⟨M, hB⟩ : GL (Fin r) κ) : Matrix (Fin r) (Fin r) κ) a b =
        (M : Matrix (Fin n) (Fin n) κ) (Fin.castLE h a) (Fin.castLE h b) := fun a b => rfl
    have hlow : ∀ P P' : Fin n, P'.val < r → ¬ P.val < r → (M : Matrix (Fin n) (Fin n) κ) P P' = 0 := by
      intro P P' hP' hP
      apply hB
      show coarse r (List.replicate j t) P'.val < coarse r (List.replicate j t) P.val
      rw [hc, hc, if_pos hP', if_neg hP]
      exact Nat.succ_pos _
    refine ⟨fun P hP => ?_, fun P P' hne hnz => ?_⟩
    · have := h2 ⟨P.val, hP⟩
      rw [e] at this
      exact this
    · unfold slAllowY
      split_ifs with hP'
      · have hP : P.val < r := by
          by_contra hP
          exact hnz (hlow P P' hP' hP)
        refine ⟨hP, fun hlt => hnz ?_, fun ⟨a, b⟩ => hnz ?_⟩
        · have := h1 ⟨P.val, hP⟩ ⟨P'.val, hP'⟩ hlt
          rw [e] at this
          exact this
        · have := h3 ⟨P.val, hP⟩ ⟨P'.val, hP'⟩ a b
          rw [e] at this
          exact this
      · by_contra hc2
        push Not at hc2
        apply hnz
        apply hB
        show coarse r (List.replicate j t) P'.val < coarse r (List.replicate j t) P.val
        rw [hc, hc, if_neg hP', if_neg (by omega)]
        generalize (P.val - r) / t = A at *
        generalize (P'.val - r) / t = B at *
        omega
  · rintro ⟨hd, ho⟩
    have hB : M ∈ blockUT n κ r (List.replicate j t) := by
      intro P P' hlt
      have hlt' : coarse r (List.replicate j t) P'.val < coarse r (List.replicate j t) P.val := hlt
      by_contra hnz
      have hne : P ≠ P' := fun e => by rw [e] at hlt'; exact lt_irrefl _ hlt'
      have := ho P P' hne hnz
      rw [hc, hc] at hlt'
      unfold slAllowY at this
      generalize (P.val - r) / t = A at *
      generalize (P'.val - r) / t = B at *
      split_ifs at this hlt' <;> omega
    refine mem_HPar.mpr ⟨hB, (mem_HPsymF_iff hkr).mpr ⟨fun a b hab => ?_, fun a => ?_, fun a b ha hb => ?_⟩⟩
    · show (M : Matrix (Fin n) (Fin n) κ) (Fin.castLE h a) (Fin.castLE h b) = 0
      by_contra hnz
      have hne : Fin.castLE h a ≠ Fin.castLE h b := fun e => by
        have : a = b := Fin.castLE_injective h e
        rw [this] at hab
        exact lt_irrefl _ hab
      have := ho _ _ hne hnz
      unfold slAllowY at this
      rw [if_pos (show (Fin.castLE h b).val < r from b.2)] at this
      exact this.2.1 hab
    · exact hd (Fin.castLE h a) a.2
    · show (M : Matrix (Fin n) (Fin n) κ) (Fin.castLE h a) (Fin.castLE h b) = 0
      by_contra hnz
      have hne : Fin.castLE h a ≠ Fin.castLE h b := fun e => by
        have := congrArg Fin.val e
        simp only [Fin.val_castLE] at this
        omega
      have := ho _ _ hne hnz
      unfold slAllowY at this
      rw [if_pos (show (Fin.castLE h b).val < r from b.2)] at this
      exact this.2.2 ⟨ha, hb⟩

/- English proof (translation)
Unfold `slAllowY ocbXAllow symIdx`. Apply the tactic sequence `by_cases h1 : p < k <;> by_cases h2 : p' < k <;> simp only [h1, h2, if_true, if_false, Nat.add_sub_add_right] <;>`. Apply the tactic sequence `generalize (p - (k + j)) / t = A <;> generalize (p' - (k + j)) / t = B <;> split_ifs <;> (try simp only [true_and, false_and, or_false]) <;> omega`.
-/
theorem sl_allow_iff {k rS j t c p p' : ℕ} (hc : c + j = 2 * rS + 1) (hne : p ≠ p') :
    slAllowY k rS (k + j + c) t (if p < k then p else p + c) (if p' < k then p' else p' + c) ↔ ocbXAllow k rS j t p p' := by
  unfold slAllowY ocbXAllow symIdx
  by_cases h1 : p < k <;> by_cases h2 : p' < k <;> simp only [h1, h2, if_true, if_false, Nat.add_sub_add_right] <;>
    generalize (p - (k + j)) / t = A <;> generalize (p' - (k + j)) / t = B <;> split_ifs <;> (try simp only [true_and, false_and, or_false]) <;> omega

end EntY

section InsPat

variable {κ : Type} [CommRing κ]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem sl_insEquiv_symm_val {N c k N' : ℕ} (hk : k ≤ N) (hN : N' = N + c) (p : Fin N) :
    ((insEquiv N c k N' hk hN).symm (Sum.inl p)).val = if p.val < k then p.val else p.val + c := rfl

/- English proof (translation)
Unfold `ocbM`. Rewrite using `[dif_pos ⟨p.2, p'.2⟩]`.
-/
theorem sl_ocbM {N : ℕ} (M : GL (Fin N) κ) (p p' : Fin N) : ocbM M p.val p'.val = (M : Matrix (Fin N) (Fin N) κ) p p' := by
  unfold ocbM
  rw [dif_pos ⟨p.2, p'.2⟩]

/- English proof (translation)
Rewrite using `[sl_mem_HJsym_iff h (by omega) ht (by subst hN' hr hNd; omega)]`. Establish `hv : ∀ P : Fin N', ∀ p : Fin N, insEquiv N c k N' hk hN' P = Sum.inl p → P.val = if p.val < k then p.val else p.val + c`. Introduce `P p hP`. Rewrite using `[← sl_insEquiv_symm_val hk hN' p, ← hP, Equiv.symm_apply_apply]`. Establish `hq : ∀ P : Fin N', ∀ q : Fin c, insEquiv N c k N' hk hN' P = Sum.inr q → P.val = k + q.val`.

Introduce `P q hP`. Use `congrArg Fin.val ((Equiv.symm_apply_eq _).mpr hP.symm)` as an intermediate fact. Rewrite using `[← this]`. Both sides reduce to the same expression. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨hd, ho⟩`. Use `⟨fun p hp => ?_, fun p p' hp hp' hne hnz => ?_⟩` and prove the remaining obligations. Establish `hpN : p < N` using `by omega`. Apply the tactic sequence `have := hd ((insEquiv N c k N' hk hN').symm (Sum.inl ⟨p, hpN⟩)) (by rw [sl_insEquiv_symm_val]; dsimp only; split_ifs <;> omega)`. Rewrite `this` using `[insGL_val, Equiv.apply_symm_apply, Matrix.fromBlocks_apply₁₁]`.

Rewrite using `[sl_ocbM M ⟨p, hpN⟩ ⟨p, hpN⟩]`. Conclude with `this`. Establish `hne' : (insEquiv N c k N' hk hN').symm (Sum.inl ⟨p, hp⟩) ≠ (insEquiv N c k N' hk hN').symm (Sum.inl ⟨p', hp'⟩)` using `fun e => hne (congrArg Fin.val (Sum.inl_injective ((insEquiv N c k N' hk hN').symm.injective e)))`. Use `ho _ _ hne' (by` as an intermediate fact. Rewrite using `[insGL_val, Equiv.apply_symm_apply, Equiv.apply_symm_apply, Matrix.fromBlocks_apply₁₁]`.

Rewrite `hnz` using `[sl_ocbM M ⟨p, hp⟩ ⟨p', hp'⟩]`. Conclude with `hnz)`. Rewrite `this` using `[sl_insEquiv_symm_val, sl_insEquiv_symm_val, hr]`. Conclude with `(sl_allow_iff hc hne).mp this`. Introduce and unpack `⟨hd, ho⟩`.

Use `⟨fun P hP => ?_, fun P P' hne hnz => ?_⟩` and prove the remaining obligations. Rewrite using `[insGL_val]`. Break down `hP1 : insEquiv N c k N' hk hN' P with p | q` into its components or cases. Rewrite using `[Matrix.fromBlocks_apply₁₁]`. Establish `e` using `hv P p hP1`.

Apply the tactic sequence `have := hd p.val (by split_ifs at e <;> omega)`. Rewrite `this` using `[sl_ocbM]`. Conclude with `this`. Rewrite using `[Matrix.fromBlocks_apply₂₂, Matrix.one_apply_eq]`. Rewrite `hnz` using `[insGL_val]`.

Apply the tactic sequence `rcases hP1 : insEquiv N c k N' hk hN' P with p | q <;> rcases hP2 : insEquiv N c k N' hk hN' P' with p' | q' <;>`. Rewrite `hnz` using `[hP1, hP2]`. Rewrite `hnz` using `[Matrix.fromBlocks_apply₁₁]`. Establish `hpp : p.val ≠ p'.val` using `fun e => hne (by`. Establish `: p = p'` using `Fin.ext e`.

Rewrite using `[← (insEquiv N c k N' hk hN').symm_apply_apply P, ← (insEquiv N c k N' hk hN').symm_apply_apply P', hP1, hP2, this])`. Use `ho p.val p'.val p.2 p'.2 hpp (by rw [sl_ocbM]; exact hnz)` as an intermediate fact. Rewrite using `[hv P p hP1, hv P' p' hP2, hr]`. Conclude with `(sl_allow_iff hc hpp).mpr this`. Rewrite `hnz` using `[Matrix.fromBlocks_apply₁₂]`.

Conclude with `absurd rfl hnz`. Rewrite `hnz` using `[Matrix.fromBlocks_apply₂₁]`. Conclude with `absurd rfl hnz`. Rewrite `hnz` using `[Matrix.fromBlocks_apply₂₂]`. Establish `hqq : q ≠ q'` using `fun e => hne (by`.

Rewrite using `[← (insEquiv N c k N' hk hN').symm_apply_apply P, ← (insEquiv N c k N' hk hN').symm_apply_apply P', hP1, hP2, e])`. Conclude with `absurd (Matrix.one_apply_ne hqq) hnz`.
-/
theorem sl_insGL_pat {N c k j t rS r N' : ℕ} (hk : k ≤ N) (hN' : N' = N + c) (h : r ≤ N') (hr : r = k + j + c)
    (hNd : N = k + j + j * t) (hc : c + j = 2 * rS + 1) (ht : 0 < t) (M : GL (Fin N) κ) :
    insGL κ N c k N' hk hN' M ∈ HJsym κ N' k r t j rS h ↔ ocbXPat k rS j t M := by
  rw [sl_mem_HJsym_iff h (by omega) ht (by subst hN' hr hNd; omega)]
  have hv : ∀ P : Fin N', ∀ p : Fin N, insEquiv N c k N' hk hN' P = Sum.inl p →
      P.val = if p.val < k then p.val else p.val + c := by
    intro P p hP
    rw [← sl_insEquiv_symm_val hk hN' p, ← hP, Equiv.symm_apply_apply]
  have hq : ∀ P : Fin N', ∀ q : Fin c, insEquiv N c k N' hk hN' P = Sum.inr q → P.val = k + q.val := by
    intro P q hP
    have := congrArg Fin.val ((Equiv.symm_apply_eq _).mpr hP.symm)
    rw [← this]
    rfl
  constructor
  · rintro ⟨hd, ho⟩
    refine ⟨fun p hp => ?_, fun p p' hp hp' hne hnz => ?_⟩
    · have hpN : p < N := by omega
      have := hd ((insEquiv N c k N' hk hN').symm (Sum.inl ⟨p, hpN⟩))
        (by rw [sl_insEquiv_symm_val]; dsimp only; split_ifs <;> omega)
      rw [insGL_val, Equiv.apply_symm_apply, Matrix.fromBlocks_apply₁₁] at this
      rw [sl_ocbM M ⟨p, hpN⟩ ⟨p, hpN⟩]
      exact this
    · have hne' : (insEquiv N c k N' hk hN').symm (Sum.inl ⟨p, hp⟩) ≠ (insEquiv N c k N' hk hN').symm (Sum.inl ⟨p', hp'⟩) :=
        fun e => hne (congrArg Fin.val (Sum.inl_injective ((insEquiv N c k N' hk hN').symm.injective e)))
      have := ho _ _ hne' (by
        rw [insGL_val, Equiv.apply_symm_apply, Equiv.apply_symm_apply, Matrix.fromBlocks_apply₁₁]
        rw [sl_ocbM M ⟨p, hp⟩ ⟨p', hp'⟩] at hnz
        exact hnz)
      rw [sl_insEquiv_symm_val, sl_insEquiv_symm_val, hr] at this
      exact (sl_allow_iff hc hne).mp this
  · rintro ⟨hd, ho⟩
    refine ⟨fun P hP => ?_, fun P P' hne hnz => ?_⟩
    · rw [insGL_val]
      rcases hP1 : insEquiv N c k N' hk hN' P with p | q
      · rw [Matrix.fromBlocks_apply₁₁]
        have e := hv P p hP1
        have := hd p.val (by split_ifs at e <;> omega)
        rw [sl_ocbM] at this
        exact this
      · rw [Matrix.fromBlocks_apply₂₂, Matrix.one_apply_eq]
    · rw [insGL_val] at hnz
      rcases hP1 : insEquiv N c k N' hk hN' P with p | q <;> rcases hP2 : insEquiv N c k N' hk hN' P' with p' | q' <;>
        rw [hP1, hP2] at hnz
      · rw [Matrix.fromBlocks_apply₁₁] at hnz
        have hpp : p.val ≠ p'.val := fun e => hne (by
          have : p = p' := Fin.ext e
          rw [← (insEquiv N c k N' hk hN').symm_apply_apply P, ← (insEquiv N c k N' hk hN').symm_apply_apply P', hP1, hP2, this])
        have := ho p.val p'.val p.2 p'.2 hpp (by rw [sl_ocbM]; exact hnz)
        rw [hv P p hP1, hv P' p' hP2, hr]
        exact (sl_allow_iff hc hpp).mpr this
      · rw [Matrix.fromBlocks_apply₁₂] at hnz
        exact absurd rfl hnz
      · rw [Matrix.fromBlocks_apply₂₁] at hnz
        exact absurd rfl hnz
      · rw [Matrix.fromBlocks_apply₂₂] at hnz
        have hqq : q ≠ q' := fun e => hne (by
          rw [← (insEquiv N c k N' hk hN').symm_apply_apply P, ← (insEquiv N c k N' hk hN').symm_apply_apply P', hP1, hP2, e])
        exact absurd (Matrix.one_apply_ne hqq) hnz

end InsPat

section EndPat

variable {κ : Type} [CommRing κ]

/- English proof (translation)
Substitute `hn` using the available equality. Establish `hf : ∀ x : Fin n, fine (n + 0) [] x.val = x.val` using `fun x => fine_self_lt (by omega)`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hB, hd⟩`. Use `⟨fun p hp => ?_, fun p p' hp hp' hne hnz => ?_⟩` and prove the remaining obligations.

Rewrite using `[sl_ocbM M ⟨p, by omega⟩ ⟨p, by omega⟩]`. Conclude with `hd ⟨p, by omega⟩ hp`. Unfold `ocbXAllow`. Rewrite using `[if_pos (by omega)]`. Use `left`.

Assume the negation of the conclusion as `hlt`. Apply `hnz` to reduce the goal to its premises. Rewrite using `[sl_ocbM M ⟨p, hp⟩ ⟨p', hp'⟩]`. Apply `hB` to reduce the goal to its premises. Use `show fine (n + 0) [] p' < fine (n + 0) [] p`.

Rewrite using `[hf ⟨p', hp'⟩, hf ⟨p, hp⟩]`. Use `show p' < p`. Use linear arithmetic over natural numbers and integers. Introduce and unpack `⟨hd, ho⟩`. Use `⟨fun i j hij => ?_, fun i hi => ?_⟩` and prove the remaining obligations.

Establish `hij' : fine (n + 0) [] j.val < fine (n + 0) [] i.val` using `hij`. Rewrite `hij'` using `[hf, hf]`. Assume the negation of the conclusion as `hnz`. Use `ho i.val j.val i.2 j.2 (fun e => by omega) (by rw [sl_ocbM]; exact hnz)` as an intermediate fact. Unfold `ocbXAllow at this`.

Rewrite `this` using `[if_pos (by omega)]`. Use linear arithmetic over natural numbers and integers. Use `hd i.val hi` as an intermediate fact. Rewrite `this` using `[sl_ocbM]`. Conclude with `this`.
-/
theorem mem_level_zero_iff_pattern {n k rS t : ℕ} (hn : n = k) (M : GL (Fin n) κ) : M ∈ HX κ n k t 0 ↔ ocbXPat k rS 0 t M := by
  subst hn
  have hf : ∀ x : Fin n, fine (n + 0) [] x.val = x.val := fun x => fine_self_lt (by omega)
  constructor
  · rintro ⟨hB, hd⟩
    refine ⟨fun p hp => ?_, fun p p' hp hp' hne hnz => ?_⟩
    · rw [sl_ocbM M ⟨p, by omega⟩ ⟨p, by omega⟩]
      exact hd ⟨p, by omega⟩ hp
    · unfold ocbXAllow
      rw [if_pos (by omega)]
      left
      by_contra hlt
      apply hnz
      rw [sl_ocbM M ⟨p, hp⟩ ⟨p', hp'⟩]
      apply hB
      show fine (n + 0) [] p' < fine (n + 0) [] p
      rw [hf ⟨p', hp'⟩, hf ⟨p, hp⟩]
      show p' < p
      omega
  · rintro ⟨hd, ho⟩
    refine ⟨fun i j hij => ?_, fun i hi => ?_⟩
    · have hij' : fine (n + 0) [] j.val < fine (n + 0) [] i.val := hij
      rw [hf, hf] at hij'
      by_contra hnz
      have := ho i.val j.val i.2 j.2 (fun e => by omega) (by rw [sl_ocbM]; exact hnz)
      unfold ocbXAllow at this
      rw [if_pos (by omega)] at this
      omega
    · have := hd i.val hi
      rw [sl_ocbM] at this
      exact this

/- English proof (translation)
Rewrite using `[sl_mem_HJsym_iff h (by omega) ht (by omega)]`. Apply the tactic sequence `have hsimp : ∀ x, (if x < k then x else x + 0) = x := fun x => by split_ifs <;> rfl`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hd, ho⟩`. Use `⟨fun p hp => ?_, fun p p' hp hp' hne hnz => ?_⟩` and prove the remaining obligations.

Rewrite using `[sl_ocbM M ⟨p, by omega⟩ ⟨p, by omega⟩]`. Conclude with `hd ⟨p, by omega⟩ (show p < r by omega)`. Use `ho ⟨p, hp⟩ ⟨p', hp'⟩ (fun e => hne (congrArg Fin.val e)) (by rw [← sl_ocbM]; exact hnz)` as an intermediate fact. Establish `h2` using `(sl_allow_iff (k := k) (rS := rS) (j := j) (t := t) (c := 0) (by omega) hne).mp`. Rewrite `h2` using `[hsimp, hsimp, Nat.add_zero, ← hr]`.

Conclude with `h2 this`. Introduce and unpack `⟨hd, ho⟩`. Use `⟨fun P hP => ?_, fun P P' hne hnz => ?_⟩` and prove the remaining obligations. Use `hd P.val (by omega)` as an intermediate fact. Rewrite `this` using `[sl_ocbM]`.

Conclude with `this`. Establish `hne' : P.val ≠ P'.val` using `fun e => hne (Fin.ext e)`. Use `ho P.val P'.val P.2 P'.2 hne' (by rw [sl_ocbM]; exact hnz)` as an intermediate fact. Establish `h2` using `(sl_allow_iff (k := k) (rS := rS) (j := j) (t := t) (c := 0) (by omega) hne').mpr this`. Rewrite `h2` using `[hsimp, hsimp, Nat.add_zero, ← hr]`.

Conclude with `h2`.
-/
theorem sl_HJsym_top_pat {N k j t rS r : ℕ} (h : r ≤ N) (hr : r = k + j) (hNd : N = k + j + j * t) (hc : j = 2 * rS + 1)
    (ht : 0 < t) (M : GL (Fin N) κ) : M ∈ HJsym κ N k r t j rS h ↔ ocbXPat k rS j t M := by
  rw [sl_mem_HJsym_iff h (by omega) ht (by omega)]
  have hsimp : ∀ x, (if x < k then x else x + 0) = x := fun x => by split_ifs <;> rfl
  constructor
  · rintro ⟨hd, ho⟩
    refine ⟨fun p hp => ?_, fun p p' hp hp' hne hnz => ?_⟩
    · rw [sl_ocbM M ⟨p, by omega⟩ ⟨p, by omega⟩]
      exact hd ⟨p, by omega⟩ (show p < r by omega)
    · have := ho ⟨p, hp⟩ ⟨p', hp'⟩ (fun e => hne (congrArg Fin.val e)) (by rw [← sl_ocbM]; exact hnz)
      have h2 := (sl_allow_iff (k := k) (rS := rS) (j := j) (t := t) (c := 0) (by omega) hne).mp
      rw [hsimp, hsimp, Nat.add_zero, ← hr] at h2
      exact h2 this
  · rintro ⟨hd, ho⟩
    refine ⟨fun P hP => ?_, fun P P' hne hnz => ?_⟩
    · have := hd P.val (by omega)
      rw [sl_ocbM] at this
      exact this
    · have hne' : P.val ≠ P'.val := fun e => hne (Fin.ext e)
      have := ho P.val P'.val P.2 P'.2 hne' (by rw [sl_ocbM]; exact hnz)
      have h2 := (sl_allow_iff (k := k) (rS := rS) (j := j) (t := t) (c := 0) (by omega) hne').mpr this
      rw [hsimp, hsimp, Nat.add_zero, ← hr] at h2
      exact h2

end EndPat

/- English proof (translation)
Introduce `j hj w hbar`. Establish `hr` using `r_eq_sym R`. Establish `hrm : R.r = R.k + R.m - 1` using `rfl`. Establish `hN` using `N_eq_blocks R j`. Break down `Nat.eq_zero_or_pos j with rfl | hj0` into its components or cases.

Rewrite using `[colLevSym_zero] show hbar ∈ (colLev Ch 0 w).H ↔ _`. Unfold `colLev`. Rewrite using `[if_pos (by omega)]`. Conclude with `mem_level_zero_iff_pattern (by simp [Ranks.N]) hbar`. Distinguish the cases in `htop : j + 1 = R.m`.

Rewrite using `[colLevSym_pred Ch htop]`. Conclude with `sl_HJsym_top_pat _ (by omega) hN (by omega) (t_pos R) hbar`. Establish `h1 : j + 1 < R.m` using `by omega`. Rewrite using `[colLevSym_mid_H Ch (by omega) h1 w, Subgroup.mem_comap]`. Conclude with `sl_insGL_pat _ rfl _ (by omega) hN (by omega) (t_pos R) hbar`.
-/
theorem sl_ocbH {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (m2 : ℕ) (hm : R.m = m2 + 2) :
    ∀ j, j ≤ m2 + 1 → ∀ (w : {w // w ∈ Pr.vGs}) (hbar : GL (Fin (R.N j)) (𝓞 X.E ⧸ w.1.asIdeal)),
      hbar ∈ (colLevSym Ch j w).H ↔ ocbXPat R.k R.rS j R.t hbar := by
  intro j hj w hbar
  have hr := r_eq_sym R
  have hrm : R.r = R.k + R.m - 1 := rfl
  have hN := N_eq_blocks R j
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · rw [colLevSym_zero]
    show hbar ∈ (colLev Ch 0 w).H ↔ _
    unfold colLev
    rw [if_pos (by omega)]
    exact mem_level_zero_iff_pattern (by simp [Ranks.N]) hbar
  · by_cases htop : j + 1 = R.m
    · rw [colLevSym_pred Ch htop]
      exact sl_HJsym_top_pat _ (by omega) hN (by omega) (t_pos R) hbar
    · have h1 : j + 1 < R.m := by omega
      rw [colLevSym_mid_H Ch (by omega) h1 w, Subgroup.mem_comap]
      exact sl_insGL_pat _ rfl _ (by omega) hN (by omega) (t_pos R) hbar

section LamEnt

variable {κ K : Type} [CommRing κ] [Field K]

/- English proof (translation)
Unfold `supSum`. Rewrite using `[← Fin.sum_univ_eq_sum_range (fun i => if i + 1 < a ∧ i ∈ S then (if h : i + 1 < n then A ⟨i, by omega⟩ ⟨i + 1, h⟩ else 0) else 0) n]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Distinguish the cases in `hc : i.val + 1 < a ∧ i.val ∈ S`. Rewrite using `[if_pos hc]`.

Distinguish the cases in `hi1 : i.val + 1 < n`. Rewrite using `[dif_pos hi1, Finset.sum_eq_single ⟨i.val + 1, hi1⟩]`. Rewrite using `[if_pos ⟨rfl, hc.1, hc.2⟩]`. Introduce `b _ hb`. Rewrite using `[if_neg]`.

Introduce and unpack `⟨h1, -, -⟩`. Conclude with `hb (Fin.ext h1.symm)`. Introduce `hh`. Conclude with `absurd (Finset.mem_univ _) hh`. Rewrite using `[dif_neg hi1]`.

Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `b _`. Rewrite using `[if_neg]`. Introduce and unpack `⟨h1, -, -⟩`. Use `b.2` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Rewrite using `[if_neg hc]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `b _`. Rewrite using `[if_neg]`.

Introduce and unpack `⟨h1, h2, h3⟩`. Conclude with `hc ⟨by omega, h3⟩`.
-/
theorem sl_supSum_eq {n a : ℕ} (S : Finset ℕ) (A : Matrix (Fin n) (Fin n) κ) :
    supSum a S A = ∑ i ∈ Finset.range n,
      if i + 1 < a ∧ i ∈ S then (if h : i + 1 < n then A ⟨i, by omega⟩ ⟨i + 1, h⟩ else 0) else 0 := by
  unfold supSum
  rw [← Fin.sum_univ_eq_sum_range (fun i => if i + 1 < a ∧ i ∈ S then (if h : i + 1 < n then A ⟨i, by omega⟩ ⟨i + 1, h⟩ else 0)
    else 0) n]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hc : i.val + 1 < a ∧ i.val ∈ S
  · rw [if_pos hc]
    by_cases hi1 : i.val + 1 < n
    · rw [dif_pos hi1, Finset.sum_eq_single ⟨i.val + 1, hi1⟩]
      · rw [if_pos ⟨rfl, hc.1, hc.2⟩]
      · intro b _ hb
        rw [if_neg]
        rintro ⟨h1, -, -⟩
        exact hb (Fin.ext h1.symm)
      · intro hh
        exact absurd (Finset.mem_univ _) hh
    · rw [dif_neg hi1]
      apply Finset.sum_eq_zero
      intro b _
      rw [if_neg]
      rintro ⟨h1, -, -⟩
      have := b.2
      omega
  · rw [if_neg hc]
    apply Finset.sum_eq_zero
    intro b _
    rw [if_neg]
    rintro ⟨h1, h2, h3⟩
    exact hc ⟨by omega, h3⟩

/- English proof (translation)
Rewrite using `[← Finset.sum_filter]`. Use `congr 1`. Use extensionality with `i`. Simplify using `only [Finset.mem_filter, Finset.mem_range]`. Use linear arithmetic over natural numbers and integers.
-/
theorem sl_sum_range_ite (n b : ℕ) (hb : b ≤ n) (f : ℕ → κ) :
    ∑ i ∈ Finset.range n, (if i < b then f i else 0) = ∑ i ∈ Finset.range b, f i := by
  rw [← Finset.sum_filter]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

/- English proof (translation)
Establish `e : ∀ i ∈ Finset.range r, (if i + 1 < r ∧ i + 1 ≠ k then Y i (i + 1) else 0) = (if i < k - 1 then Mx i (i + 1) else 0) + (if k + c ≤ i ∧ i + 1 < r then Mx (i - c) (i - c + 1) else 0)`. Introduce `i _`. Distinguish the cases in `h1 : i < k - 1`. Rewrite using `[if_pos (by omega), if_pos h1, if_neg (by omega), add_zero, hY1 i (by omega)]`. Distinguish the cases in `h2 : k + c ≤ i ∧ i + 1 < r`.

Rewrite using `[if_pos (by omega), if_neg h1, if_pos h2, zero_add, hY3 i h2.1]`. Rewrite using `[if_neg h1, if_neg h2, add_zero]`. Distinguish the cases in `h3 : i + 1 < r ∧ i + 1 ≠ k`. Rewrite using `[if_pos h3, hY2 i (by omega) (by omega)]`. Rewrite using `[if_neg h3]`.

Rewrite using `[Finset.sum_congr rfl e, Finset.sum_add_distrib, sl_sum_range_ite r (k - 1) (by omega)]`. Use `congr 1`. Rewrite using `[← Finset.sum_filter]`. Establish `hf : (Finset.range r).filter (fun i => k + c ≤ i ∧ i + 1 < r) = Finset.Ico (k + c) (k + c + (j - 1))`. Use extensionality with `i`.

Simplify using `only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[hf, Finset.sum_Ico_eq_sum_range, show k + c + (j - 1) - (k + c) = j - 1 by omega]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[show k + c + i - c = k + i by omega]`.
-/
theorem sl_sup_ins {r k c j : ℕ} (hr : r = k + j + c) (Y Mx : ℕ → ℕ → κ)
    (hY1 : ∀ i, i + 1 < k → Y i (i + 1) = Mx i (i + 1)) (hY2 : ∀ i, k ≤ i → i < k + c → Y i (i + 1) = 0)
    (hY3 : ∀ i, k + c ≤ i → Y i (i + 1) = Mx (i - c) (i - c + 1)) :
    ∑ i ∈ Finset.range r, (if i + 1 < r ∧ i + 1 ≠ k then Y i (i + 1) else 0) =
      ∑ i ∈ Finset.range (k - 1), Mx i (i + 1) + ∑ i ∈ Finset.range (j - 1), Mx (k + i) (k + i + 1) := by
  have e : ∀ i ∈ Finset.range r, (if i + 1 < r ∧ i + 1 ≠ k then Y i (i + 1) else 0) =
      (if i < k - 1 then Mx i (i + 1) else 0) + (if k + c ≤ i ∧ i + 1 < r then Mx (i - c) (i - c + 1) else 0) := by
    intro i _
    by_cases h1 : i < k - 1
    · rw [if_pos (by omega), if_pos h1, if_neg (by omega), add_zero, hY1 i (by omega)]
    · by_cases h2 : k + c ≤ i ∧ i + 1 < r
      · rw [if_pos (by omega), if_neg h1, if_pos h2, zero_add, hY3 i h2.1]
      · rw [if_neg h1, if_neg h2, add_zero]
        by_cases h3 : i + 1 < r ∧ i + 1 ≠ k
        · rw [if_pos h3, hY2 i (by omega) (by omega)]
        · rw [if_neg h3]
  rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, sl_sum_range_ite r (k - 1) (by omega)]
  congr 1
  rw [← Finset.sum_filter]
  have hf : (Finset.range r).filter (fun i => k + c ≤ i ∧ i + 1 < r) = Finset.Ico (k + c) (k + c + (j - 1)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [hf, Finset.sum_Ico_eq_sum_range, show k + c + (j - 1) - (k + c) = j - 1 by omega]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show k + c + i - c = k + i by omega]

end LamEnt

section DetBlk

variable {κ K : Type} [CommRing κ] [Field K]

/- English proof (translation)
Establish `h1 : (s + 1) * t ≤ j * t` using `Nat.mul_le_mul_right t hs`. Rewrite `h1` using `[Nat.add_mul, one_mul]`. Rewrite using `[coarse_rep ht (by omega), if_neg (by omega), add_assoc, Nat.add_sub_cancel_left, show s * t + a = a + s * t from add_comm _ _, Nat.add_mul_div_right a s ht, Nat.div_eq_of_lt ha, zero_add]`.
-/
theorem sl_coarse_blk {r t j s a : ℕ} (ht : 0 < t) (hs : s < j) (ha : a < t) :
    coarse r (List.replicate j t) (r + s * t + a) = s + 1 := by
  have h1 : (s + 1) * t ≤ j * t := Nat.mul_le_mul_right t hs
  rw [Nat.add_mul, one_mul] at h1
  rw [coarse_rep ht (by omega), if_neg (by omega), add_assoc, Nat.add_sub_cancel_left,
    show s * t + a = a + s * t from add_comm _ _, Nat.add_mul_div_right a s ht, Nat.div_eq_of_lt ha, zero_add]

def blockPositionsEquiv {n r t j s : ℕ} (ht : 0 < t) (hn : n = r + j * t) (hs : s < j) :
    Fin t ≃ {i : Fin n // coarse r (List.replicate j t) i.val = s + 1} :=
  Equiv.ofBijective (fun a => ⟨⟨r + s * t + a.val, by
      have h1 : (s + 1) * t ≤ j * t := Nat.mul_le_mul_right t hs
      rw [Nat.add_mul, one_mul] at h1
      have := a.2
      omega⟩, sl_coarse_blk ht hs a.2⟩) (by
    constructor
    · intro a b hab
      have := congrArg (fun x : {i : Fin n // coarse r (List.replicate j t) i.val = s + 1} => x.1.val) hab
      simp only at this
      exact Fin.ext (by omega)
    · rintro ⟨i, hi⟩
      have hc := coarse_rep (r := r) (j := j) ht (show i.val ≤ r + j * t by have := i.2; omega)
      rw [hi] at hc
      by_cases hir : i.val < r
      · rw [if_pos hir] at hc
        omega
      · rw [if_neg hir] at hc
        have hd : (i.val - r) / t = s := by omega
        have h1 := Nat.div_mul_le_self (i.val - r) t
        have h2 := Nat.lt_div_mul_add (a := i.val - r) ht
        rw [hd] at h1 h2
        refine ⟨⟨i.val - r - s * t, by omega⟩, Subtype.ext (Fin.ext ?_)⟩
        show r + s * t + (i.val - r - s * t) = i.val
        omega)

/- English proof (translation)
Rewrite using `[← Matrix.det_submatrix_equiv_self (blockPositionsEquiv ht hn hs)]`. Both sides reduce to the same expression.
-/
theorem sl_blk_det {n r t j s : ℕ} (ht : 0 < t) (hn : n = r + j * t) (hs : s < j) (A : Matrix (Fin n) (Fin n) κ) :
    (A.toSquareBlock (fun i => coarse r (List.replicate j t) i.val) (s + 1)).det =
      (Matrix.of fun a b : Fin t => A (blockPositionsEquiv ht hn hs a).1 (blockPositionsEquiv ht hn hs b).1).det := by
  rw [← Matrix.det_submatrix_equiv_self (blockPositionsEquiv ht hn hs)]
  rfl

/- English proof (translation)
Unfold `ocbChiK`. Rewrite using `[dif_pos u.isUnit]`. Use `congr 2`. Conclude with `Units.ext rfl`.
-/
theorem sl_ocbChiK_unit (χ : κˣ →* Kˣ) (u : κˣ) : ocbChiK χ (u : κ) = ((χ u : Kˣ) : K) := by
  unfold ocbChiK
  rw [dif_pos u.isUnit]
  congr 2
  exact Units.ext rfl

end DetBlk

section InsEnt

variable {κ : Type} [CommRing κ] {N c k N' : ℕ} (hk : k ≤ N) (hN' : N' = N + c)

/- English proof (translation)
Establish `: a = (insEquiv N c k N' hk hN').symm (Sum.inl p)` using `Fin.ext (by rw [sl_insEquiv_symm_val]; exact h)`. Rewrite using `[this, Equiv.apply_symm_apply]`.
-/
theorem sl_insEquiv_of_val (p : Fin N) (a : Fin N') (h : a.val = if p.val < k then p.val else p.val + c) :
    insEquiv N c k N' hk hN' a = Sum.inl p := by
  have : a = (insEquiv N c k N' hk hN').symm (Sum.inl p) := Fin.ext (by rw [sl_insEquiv_symm_val]; exact h)
  rw [this, Equiv.apply_symm_apply]

/- English proof (translation)
Establish `: a = (insEquiv N c k N' hk hN').symm (Sum.inr q)` using `Fin.ext h`. Rewrite using `[this, Equiv.apply_symm_apply]`.
-/
theorem sl_insEquiv_of_val_r (q : Fin c) (a : Fin N') (h : a.val = k + q.val) :
    insEquiv N c k N' hk hN' a = Sum.inr q := by
  have : a = (insEquiv N c k N' hk hN').symm (Sum.inr q) := Fin.ext h
  rw [this, Equiv.apply_symm_apply]

/- English proof (translation)
Apply the tactic sequence `have b1 : (if p < k then p else p + c) < N' := by split_ifs <;> omega`. Apply the tactic sequence `have b2 : (if p' < k then p' else p' + c) < N' := by split_ifs <;> omega`. Unfold `ocbM`. Rewrite using `[dif_pos ⟨b1, b2⟩, dif_pos ⟨hp, hp'⟩, insGL_val, sl_insEquiv_of_val hk hN' ⟨p, hp⟩ _ rfl, sl_insEquiv_of_val hk hN' ⟨p', hp'⟩ _ rfl, Matrix.fromBlocks_apply₁₁]`.
-/
theorem sl_ocbM_ins (M : GL (Fin N) κ) (p p' : ℕ) (hp : p < N) (hp' : p' < N) :
    ocbM (insGL κ N c k N' hk hN' M) (if p < k then p else p + c) (if p' < k then p' else p' + c) = ocbM M p p' := by
  have b1 : (if p < k then p else p + c) < N' := by split_ifs <;> omega
  have b2 : (if p' < k then p' else p' + c) < N' := by split_ifs <;> omega
  unfold ocbM
  rw [dif_pos ⟨b1, b2⟩, dif_pos ⟨hp, hp'⟩, insGL_val, sl_insEquiv_of_val hk hN' ⟨p, hp⟩ _ rfl,
    sl_insEquiv_of_val hk hN' ⟨p', hp'⟩ _ rfl, Matrix.fromBlocks_apply₁₁]

/- English proof (translation)
Unfold `ocbM`. Use `split_ifs with hb`. Rewrite using `[insGL_val, sl_insEquiv_of_val_r hk hN' ⟨i - k, by omega⟩ ⟨i, hb.1⟩ (by dsimp only; omega)]`. Distinguish the cases in `h1 : i' < k`. Rewrite using `[sl_insEquiv_of_val hk hN' ⟨i', by omega⟩ ⟨i', hb.2⟩ (by dsimp only; rw [if_pos h1])]`.

Both sides reduce to the same expression. Distinguish the cases in `h2 : i' < k + c`. Rewrite using `[sl_insEquiv_of_val_r hk hN' ⟨i' - k, by omega⟩ ⟨i', hb.2⟩ (by dsimp only; omega), Matrix.fromBlocks_apply₂₂]`. Conclude with `Matrix.one_apply_ne fun e => hne (by have := congrArg Fin.val e; simp only at this; omega)`. Apply the tactic sequence `rw [sl_insEquiv_of_val hk hN' ⟨i' - c, by omega⟩ ⟨i', hb.2⟩ (by dsimp only; split_ifs <;> omega)]`.

Both sides reduce to the same expression. Both sides reduce to the same expression.
-/
theorem sl_ocbM_ins_row (M : GL (Fin N) κ) (i i' : ℕ) (hi1 : k ≤ i) (hi2 : i < k + c) (hne : i ≠ i') :
    ocbM (insGL κ N c k N' hk hN' M) i i' = 0 := by
  unfold ocbM
  split_ifs with hb
  · rw [insGL_val, sl_insEquiv_of_val_r hk hN' ⟨i - k, by omega⟩ ⟨i, hb.1⟩ (by dsimp only; omega)]
    by_cases h1 : i' < k
    · rw [sl_insEquiv_of_val hk hN' ⟨i', by omega⟩ ⟨i', hb.2⟩ (by dsimp only; rw [if_pos h1])]
      rfl
    · by_cases h2 : i' < k + c
      · rw [sl_insEquiv_of_val_r hk hN' ⟨i' - k, by omega⟩ ⟨i', hb.2⟩ (by dsimp only; omega), Matrix.fromBlocks_apply₂₂]
        exact Matrix.one_apply_ne fun e => hne (by have := congrArg Fin.val e; simp only at this; omega)
      · rw [sl_insEquiv_of_val hk hN' ⟨i' - c, by omega⟩ ⟨i', hb.2⟩ (by dsimp only; split_ifs <;> omega)]
        rfl
  · rfl

/- English proof (translation)
Unfold `ocbM`. Distinguish the cases in `hb : i < N' ∧ i' < N'`. Apply the tactic sequence `rw [dif_pos hb, dif_pos ⟨by omega, by omega⟩, insGL_val, sl_insEquiv_of_val hk hN' ⟨i - c, by omega⟩ ⟨i, hb.1⟩ (by dsimp only; split_ifs <;> omega), sl_insEquiv_of_val hk hN' ⟨i' - c, by omega⟩ ⟨i', hb.2⟩ (by dsimp only; split_ifs <;> omega), Matrix.fromBlocks_apply₁₁]`. Rewrite using `[dif_neg hb, dif_neg (by omega)]`.
-/
theorem sl_ocbM_ins_late (M : GL (Fin N) κ) (i i' : ℕ) (hi : k + c ≤ i) (hi' : k + c ≤ i') :
    ocbM (insGL κ N c k N' hk hN' M) i i' = ocbM M (i - c) (i' - c) := by
  unfold ocbM
  by_cases hb : i < N' ∧ i' < N'
  · rw [dif_pos hb, dif_pos ⟨by omega, by omega⟩, insGL_val,
      sl_insEquiv_of_val hk hN' ⟨i - c, by omega⟩ ⟨i, hb.1⟩ (by dsimp only; split_ifs <;> omega),
      sl_insEquiv_of_val hk hN' ⟨i' - c, by omega⟩ ⟨i', hb.2⟩ (by dsimp only; split_ifs <;> omega), Matrix.fromBlocks_apply₁₁]
  · rw [dif_neg hb, dif_neg (by omega)]

end InsEnt

section LamAsm

variable {κ K : Type} [CommRing κ] [Field K]

/- English proof (translation)
Substitute `hn` using the available equality. Unfold `lamX lamGen ocbXLam`. Rewrite using `[MonoidHom.mul_apply, Units.val_mul, supChar_val, MonoidHom.comp_apply, detChar_apply, List.length_replicate]`. Simplify using `only [Finset.range_zero, Finset.prod_empty, Units.val_one, mul_one, Nat.zero_sub, Finset.sum_empty, add_zero]`. Use `congr 1`.

Rewrite using `[sl_supSum_eq, ← sl_sum_range_ite n (n - 1) (by omega)]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Unfold `SX`. Simplify using `only [Finset.mem_filter, Finset.mem_range]`. Distinguish the cases in `hc : i < n - 1`.

Rewrite using `[if_pos ⟨by omega, by omega, Or.inl (by omega)⟩, if_pos hc, dif_pos (by omega)]`. Unfold `ocbM`. Rewrite using `[dif_pos ⟨by omega, by omega⟩]`. Rewrite using `[if_neg (by omega), if_neg hc]`.
-/
theorem character_level_zero_entries (ψ : AddChar κ K) (χ : ℕ → κˣ →* Kˣ) {n k m t : ℕ} (hn : n = k) (M : ↥(HX κ n k t 0)) :
    ((lamX ψ χ n k m t 0 M : Kˣ) : K) = ocbXLam ψ χ k 0 t M.1 := by
  subst hn
  unfold lamX lamGen ocbXLam
  rw [MonoidHom.mul_apply, Units.val_mul, supChar_val, MonoidHom.comp_apply, detChar_apply, List.length_replicate]
  simp only [Finset.range_zero, Finset.prod_empty, Units.val_one, mul_one, Nat.zero_sub, Finset.sum_empty, add_zero]
  congr 1
  rw [sl_supSum_eq, ← sl_sum_range_ite n (n - 1) (by omega)]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold SX
  simp only [Finset.mem_filter, Finset.mem_range]
  by_cases hc : i < n - 1
  · rw [if_pos ⟨by omega, by omega, Or.inl (by omega)⟩, if_pos hc, dif_pos (by omega)]
    unfold ocbM
    rw [dif_pos ⟨by omega, by omega⟩]
  · rw [if_neg (by omega), if_neg hc]

/- English proof (translation)
Unfold `lamJsym lamPar ocbXLam`. Rewrite using `[MonoidHom.mul_apply, Units.val_mul, MonoidHom.comp_apply, MonoidHom.comp_apply, chiSymF_val hr0, detChar_apply, Units.coe_prod, List.length_replicate]`. Use `congr 1`. Use `congr 1`. Rewrite using `[sl_supSum_eq, ← sl_sup_ins hr (ocbM M.1) (ocbM Mx) hY1 hY2 hY3]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Unfold `SPsymF`. Simplify using `only [Finset.mem_filter, Finset.mem_range]`. Distinguish the cases in `hc : i + 1 < r ∧ i + 1 ≠ k`. Rewrite using `[if_pos ⟨hc.1, by omega, hc.2⟩, if_pos hc, dif_pos hc.1]`.

Unfold `ocbM`. Rewrite using `[dif_pos ⟨by omega, by omega⟩]`. Both sides reduce to the same expression. Rewrite using `[if_neg (fun hh => hc ⟨hh.1, hh.2.2⟩), if_neg hc]`. Use `Finset.prod_congr rfl fun s hs => ?_` and prove the remaining obligations.

Establish `hs' : s < j` using `Finset.mem_range.mp hs`. Rewrite using `[← sl_ocbChiK_unit, blkDet_val, sl_blk_det ht hn hs']`. Use `congr 2`. Use extensionality with `a b`. Rewrite using `[Matrix.of_apply, Matrix.of_apply, ← hB s hs' a.1 b.1]`.

Unfold `ocbM`. Rewrite using `[dif_pos ⟨(blockPositionsEquiv ht hn hs' a).1.2, (blockPositionsEquiv ht hn hs' b).1.2⟩]`. Both sides reduce to the same expression.
-/
theorem sl_lamJsym_ent (ψ : AddChar κ K) (χ : ℕ → κˣ →* Kˣ) {n k r t j rS c N : ℕ} (h : r ≤ n) (hr0 : r = k + 2 * rS + 1)
    (hr : r = k + j + c) (hn : n = r + j * t) (ht : 0 < t) (M : ↥(HJsym κ n k r t j rS h)) (Mx : GL (Fin N) κ)
    (hY1 : ∀ i, i + 1 < k → ocbM M.1 i (i + 1) = ocbM Mx i (i + 1))
    (hY2 : ∀ i, k ≤ i → i < k + c → ocbM M.1 i (i + 1) = 0)
    (hY3 : ∀ i, k + c ≤ i → ocbM M.1 i (i + 1) = ocbM Mx (i - c) (i - c + 1))
    (hB : ∀ s, s < j → ∀ a b : ℕ, ocbM M.1 (r + s * t + a) (r + s * t + b) = ocbM Mx (k + j + s * t + a) (k + j + s * t + b)) :
    ((lamJsym ψ χ n k r t j rS h M : Kˣ) : K) = ocbXLam ψ χ k j t Mx := by
  unfold lamJsym lamPar ocbXLam
  rw [MonoidHom.mul_apply, Units.val_mul, MonoidHom.comp_apply, MonoidHom.comp_apply, chiSymF_val hr0, detChar_apply,
    Units.coe_prod, List.length_replicate]
  congr 1
  · congr 1
    rw [sl_supSum_eq, ← sl_sup_ins hr (ocbM M.1) (ocbM Mx) hY1 hY2 hY3]
    refine Finset.sum_congr rfl fun i _ => ?_
    unfold SPsymF
    simp only [Finset.mem_filter, Finset.mem_range]
    by_cases hc : i + 1 < r ∧ i + 1 ≠ k
    · rw [if_pos ⟨hc.1, by omega, hc.2⟩, if_pos hc, dif_pos hc.1]
      unfold ocbM
      rw [dif_pos ⟨by omega, by omega⟩]
      rfl
    · rw [if_neg (fun hh => hc ⟨hh.1, hh.2.2⟩), if_neg hc]
  · refine Finset.prod_congr rfl fun s hs => ?_
    have hs' : s < j := Finset.mem_range.mp hs
    rw [← sl_ocbChiK_unit, blkDet_val, sl_blk_det ht hn hs']
    congr 2
    ext a b
    rw [Matrix.of_apply, Matrix.of_apply, ← hB s hs' a.1 b.1]
    unfold ocbM
    rw [dif_pos ⟨(blockPositionsEquiv ht hn hs' a).1.2, (blockPositionsEquiv ht hn hs' b).1.2⟩]
    rfl

end LamAsm

/- English proof (translation)
Introduce `X Pr R Ch m2 hm`. Use `⟨sl_ocbH Ch m2 hm, fun j hj w hbar => ?_⟩` and prove the remaining obligations. Establish `hr` using `r_eq_sym R`. Establish `hrm : R.r = R.k + R.m - 1` using `rfl`. Establish `hN` using `N_eq_blocks R j`.

Establish `hpsi : psi0P Ch w.1 = Ch.psi0 w`. Unfold `psi0P`. Rewrite using `[dif_pos w.2]`. Establish `hchi : chiP Ch w.1 = extChi (fun s => Ch.chi s w)`. Unfold `chiP`.

Rewrite using `[dif_pos w.2]`. Both sides reduce to the same expression. Rewrite using `[hpsi, hchi]`. Break down `Nat.eq_zero_or_pos j with rfl | hj0` into its components or cases. Establish `key : ∀ l : Lev (𝓞 X.E ⧸ w.1.asIdeal) X.K (R.N 0), l = ⟨HX _ (R.N 0) R.k R.t 0, lamX (Ch.psi0 w) (extChi fun s => Ch.chi s w) (R.N 0) R.k R.m R.t 0⟩ → ∀ M : ↥l.H, ((l.lam M : X.Kˣ) : X.K) = ocbXLam (Ch.psi0 w) (extChi fun s => Ch.chi s w) R.k 0 R.t M.1`.

Introduce `l hl M`. Substitute `hl` using the available equality. Conclude with `character_level_zero_entries _ _ (by simp [Ranks.N]) M`. Conclude with `key _ (by unfold colLevSym; rw [if_pos rfl]; unfold colLev; rw [if_pos (by omega)]) hbar`. Distinguish the cases in `htop : j + 1 = R.m`.

Establish `hNp` using `N_pred_eq htop`. Establish `key : ∀ l : Lev (𝓞 X.E ⧸ w.1.asIdeal) X.K (R.N j), l = ⟨HJsym _ (R.N j) R.k R.r R.t j R.rS (r_le_N_of_le htop.ge), lamJsym (Ch.psi0 w) (extChi fun s => Ch.chi s w) (R.N j) R.k R.r R.t j R.rS (r_le_N_of_le htop.ge)⟩ → ∀ M : ↥l.H, ((l.lam M : X.Kˣ) : X.K) = ocbXLam (Ch.psi0 w) (ext …`. Introduce `l hl M`. Substitute `hl` using the available equality. Use `sl_lamJsym_ent _ _ _ hr (c := 0) (by omega) hNp (t_pos R) M M.1 (fun i _ => rfl) (fun i h1 h2 => by omega) (fun i _ => by simp) (fun s _ a b => ?_)` and prove the remaining obligations.

Rewrite using `[show R.r + s * R.t + a = R.k + j + s * R.t + a by omega, show R.r + s * R.t + b = R.k + j + s * R.t + b by omega]`. Conclude with `key _ (by rw [colLevSym_pred Ch htop]; rfl) hbar`. Establish `h1 : j + 1 < R.m` using `by omega`. Establish `hM : insGL (𝓞 X.E ⧸ w.1.asIdeal) (R.N j) (R.m - 1 - j) R.k (R.N j + (R.m - 1 - j)) (colK_le_N R j) rfl hbar.1 ∈ HJsym (𝓞 X.E ⧸ w.1.asIdeal) (R.N j + (R.m - 1 - j)) R.k R.r R.t j R.rS (r_le_Y (by omega))`. Establish `key : ∀ x, x ∈ (colLevSym Ch j w).H → insGL (𝓞 X.E ⧸ w.1.asIdeal) (R.N j) (R.m - 1 - j) R.k (R.N j + (R.m - 1 - j)) (colK_le_N R j) rfl x ∈ HJsym (𝓞 X.E ⧸ w.1.asIdeal) (R.N j + (R.m - 1 - j)) R.k R.r R.t j R.rS (r_le_Y (by omega))`.

Introduce `x hx`. Rewrite `hx` using `[colLevSym_mid_H Ch (by omega) h1 w]`. Conclude with `hx`. Conclude with `key hbar.1 hbar.2`. Rewrite using `[colLevSym_mid_lam Ch (by omega) h1 w hbar hM]`.

Establish `hk` using `colK_le_N R j`. Use `sl_lamJsym_ent _ _ _ hr (c := R.m - 1 - j) (by omega) (by omega) (t_pos R) ⟨_, hM⟩ hbar.1 (fun i hi => ?_) (fun i i1 i2 => sl_ocbM_ins_row (c := R.m - 1 - j) hk rfl hbar.1 i (i + 1) i1 i2 (by omega)) (fun i hi => ?_) (fun s hs a b => ?_)` and prove the remaining obligations. Use `sl_ocbM_ins (c := R.m - 1 - j) hk rfl hbar.1 i (i + 1) (by omega) (by omega)` as an intermediate fact. Rewrite `this` using `[if_pos (by omega), if_pos (by omega)]`. Then use the resulting hypothesis. Use `show ocbM (insGL _ _ _ _ _ hk rfl hbar.1) i (i + 1) = _`.

Rewrite using `[sl_ocbM_ins_late (c := R.m - 1 - j) hk rfl hbar.1 i (i + 1) hi (by omega), show i + 1 - (R.m - 1 - j) = i - (R.m - 1 - j) + 1 by omega]`. Use `show ocbM (insGL _ _ _ _ _ hk rfl hbar.1) _ _ = _`. Rewrite using `[sl_ocbM_ins_late (c := R.m - 1 - j) hk rfl hbar.1 _ _ (by omega) (by omega), show R.r + s * R.t + a - (R.m - 1 - j) = R.k + j + s * R.t + a by omega, show R.r + s * R.t + b - (R.m - 1 - j) = R.k + j + s * R.t + b by omega]`.
-/
theorem closedLevels_by_entries_holds : OcbLevIsSym := by
  intro X Pr R Ch m2 hm
  refine ⟨sl_ocbH Ch m2 hm, fun j hj w hbar => ?_⟩
  have hr := r_eq_sym R
  have hrm : R.r = R.k + R.m - 1 := rfl
  have hN := N_eq_blocks R j
  have hpsi : psi0P Ch w.1 = Ch.psi0 w := by
    unfold psi0P
    rw [dif_pos w.2]
  have hchi : chiP Ch w.1 = extChi (fun s => Ch.chi s w) := by
    unfold chiP
    rw [dif_pos w.2]
    rfl
  rw [hpsi, hchi]
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · have key : ∀ l : Lev (𝓞 X.E ⧸ w.1.asIdeal) X.K (R.N 0),
        l = ⟨HX _ (R.N 0) R.k R.t 0, lamX (Ch.psi0 w) (extChi fun s => Ch.chi s w) (R.N 0) R.k R.m R.t 0⟩ →
        ∀ M : ↥l.H, ((l.lam M : X.Kˣ) : X.K) = ocbXLam (Ch.psi0 w) (extChi fun s => Ch.chi s w) R.k 0 R.t M.1 := by
      intro l hl M
      subst hl
      exact character_level_zero_entries _ _ (by simp [Ranks.N]) M
    exact key _ (by unfold colLevSym; rw [if_pos rfl]; unfold colLev; rw [if_pos (by omega)]) hbar
  · by_cases htop : j + 1 = R.m
    · have hNp := N_pred_eq htop
      have key : ∀ l : Lev (𝓞 X.E ⧸ w.1.asIdeal) X.K (R.N j),
          l = ⟨HJsym _ (R.N j) R.k R.r R.t j R.rS (r_le_N_of_le htop.ge),
            lamJsym (Ch.psi0 w) (extChi fun s => Ch.chi s w) (R.N j) R.k R.r R.t j R.rS (r_le_N_of_le htop.ge)⟩ →
          ∀ M : ↥l.H, ((l.lam M : X.Kˣ) : X.K) = ocbXLam (Ch.psi0 w) (extChi fun s => Ch.chi s w) R.k j R.t M.1 := by
        intro l hl M
        subst hl
        refine sl_lamJsym_ent _ _ _ hr (c := 0) (by omega) hNp (t_pos R) M M.1 (fun i _ => rfl) (fun i h1 h2 => by omega)
          (fun i _ => by simp) (fun s _ a b => ?_)
        rw [show R.r + s * R.t + a = R.k + j + s * R.t + a by omega, show R.r + s * R.t + b = R.k + j + s * R.t + b by omega]
      exact key _ (by rw [colLevSym_pred Ch htop]; rfl) hbar
    · have h1 : j + 1 < R.m := by omega
      have hM : insGL (𝓞 X.E ⧸ w.1.asIdeal) (R.N j) (R.m - 1 - j) R.k (R.N j + (R.m - 1 - j)) (colK_le_N R j) rfl hbar.1 ∈
          HJsym (𝓞 X.E ⧸ w.1.asIdeal) (R.N j + (R.m - 1 - j)) R.k R.r R.t j R.rS (r_le_Y (by omega)) := by
        have key : ∀ x, x ∈ (colLevSym Ch j w).H → insGL (𝓞 X.E ⧸ w.1.asIdeal) (R.N j) (R.m - 1 - j) R.k (R.N j + (R.m - 1 - j))
            (colK_le_N R j) rfl x ∈ HJsym (𝓞 X.E ⧸ w.1.asIdeal) (R.N j + (R.m - 1 - j)) R.k R.r R.t j R.rS (r_le_Y (by omega)) := by
          intro x hx
          rw [colLevSym_mid_H Ch (by omega) h1 w] at hx
          exact hx
        exact key hbar.1 hbar.2
      rw [colLevSym_mid_lam Ch (by omega) h1 w hbar hM]
      have hk := colK_le_N R j
      refine sl_lamJsym_ent _ _ _ hr (c := R.m - 1 - j) (by omega) (by omega) (t_pos R) ⟨_, hM⟩ hbar.1
        (fun i hi => ?_) (fun i i1 i2 => sl_ocbM_ins_row (c := R.m - 1 - j) hk rfl hbar.1 i (i + 1) i1 i2 (by omega))
        (fun i hi => ?_) (fun s hs a b => ?_)
      · have := sl_ocbM_ins (c := R.m - 1 - j) hk rfl hbar.1 i (i + 1) (by omega) (by omega)
        rwa [if_pos (by omega), if_pos (by omega)] at this
      · show ocbM (insGL _ _ _ _ _ hk rfl hbar.1) i (i + 1) = _
        rw [sl_ocbM_ins_late (c := R.m - 1 - j) hk rfl hbar.1 i (i + 1) hi (by omega), show i + 1 - (R.m - 1 - j) = i - (R.m - 1 - j) + 1 by omega]
      · show ocbM (insGL _ _ _ _ _ hk rfl hbar.1) _ _ = _
        rw [sl_ocbM_ins_late (c := R.m - 1 - j) hk rfl hbar.1 _ _ (by omega) (by omega),
          show R.r + s * R.t + a - (R.m - 1 - j) = R.k + j + s * R.t + a by omega,
          show R.r + s * R.t + b - (R.m - 1 - j) = R.k + j + s * R.t + b by omega]

end Formalism.L2.Col
