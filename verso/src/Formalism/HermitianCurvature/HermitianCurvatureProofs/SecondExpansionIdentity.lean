import Formalism.HermitianCurvature.HermitianCurvatureProofs.FirstExpansionIdentity

open Matrix Finset

namespace Formalism.FourierDecayAlt.P.SignAntidiagonal

open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants

/- English proof (translation)
Establish `e : (Matrix.of fun a b => star (M a b)) = M.conjTranspose.transpose`. Use extensionality with `a b`. Simplify using `[Matrix.conjTranspose_apply]`. Rewrite using `[e, Matrix.det_transpose, Matrix.det_conjTranspose]`.
-/
theorem det_star {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    (Matrix.of fun a b => star (M a b)).det = star M.det := by
  have e : (Matrix.of fun a b => star (M a b)) = M.conjTranspose.transpose := by
    ext a b
    simp [Matrix.conjTranspose_apply]
  rw [e, Matrix.det_transpose, Matrix.det_conjTranspose]

/- English proof (translation)
Simplify using `only [sR]`. Rewrite using `[keyS_esI]`. Both sides reduce to the same expression.
-/
theorem keyS_sR (k r m : ℕ) (hm : m ≤ r) (l : Fin m) : keyS k r (sR k r m hm l) = l.val := by
  simp only [sR]
  rw [keyS_esI]
  rfl

/- English proof (translation)
Establish `hsv : ∀ l : Fin i0, (sR k r i0 hi0 l).val = 2 * r + k - l.val`. Introduce `l`. Simplify using `[sR, Formalism.QuantumDeterminants.esI]`. Establish `he : StrictMono (fun l => keyS k r (sR k r i0 hi0 l))`. Introduce `a b hab`.

Simplify using `only [keyS_sR]`. Conclude with `hab`. Establish `hX : ∀ (a : Fin i0) (p : Fin (2 * r + k + 1)), p ∉ Set.range (sR k r i0 hi0) → y (Fin.castLE hi0 a) p = 0`. Introduce `a p hp`. Conclude with `hz _ p a.isLt hp`.

Establish `hu : ∀ c : Fin i0 → Fin (2 * r + k + 1), StrictMono (fun l => keyS k r (c l)) → (∀ l, c l ∈ Set.range (sR k r i0 hi0)) → c = sR k r i0 hi0`. Introduce `c hc hS`. Conclude with `uniq_key (keyS k r) (keyS_inj k r) (sR k r i0 hi0) c he hc hS`. Establish `hs` using `sum_single (M := A) (fun B : Fin i0 → Fin (2 * r + k + 1) => StrictMono (fun l => keyS k r (B l))) (fun a p => y (Fin.castLE hi0 a) p) (Set.range (sR k r i0 hi0)) hX (sR k r i0 hi0) he hu (fun B => qminor E B (sR k r i0 hi0) (ell + (i0 : ℂ) - 1))`. Establish `hdet : (Matrix.of fun a l : Fin i0 => y (Fin.castLE hi0 a) (sR k r i0 hi0 l)).det = star h.det`.

Rewrite using `[← det_star]`. Use `congr 1`. Use extensionality with `a b`. Conclude with `hh a b`. Unfold `AAv`.

Rewrite using `[← hdet]`. Use `hs using 1` and compare the differences between its conclusion and the goal.
-/
theorem AAv_head {A : Type} [Ring A] [Algebra ℂ A] (k r : ℕ) (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A)
    (y : Fin r → Fin (2 * r + k + 1) → ℂ) (i0 : ℕ) (hi0 : i0 ≤ r) (h : Matrix (Fin i0) (Fin i0) ℂ) (ell : ℂ)
    (hz : ∀ (a : Fin r) (p : Fin (2 * r + k + 1)), a.val < i0 → p ∉ Set.range (sR k r i0 hi0) → y a p = 0)
    (hh : ∀ a b : Fin i0, y (Fin.castLE hi0 a) (sR k r i0 hi0 b) = star (h a b)) :
    AAv k r E y i0 hi0 ell = star h.det • qminor E (sR k r i0 hi0) (sR k r i0 hi0) (ell + (i0 : ℂ) - 1) := by
  classical
  have hsv : ∀ l : Fin i0, (sR k r i0 hi0 l).val = 2 * r + k - l.val := by
    intro l
    simp [sR, Formalism.QuantumDeterminants.esI]
  have he : StrictMono (fun l => keyS k r (sR k r i0 hi0 l)) := by
    intro a b hab
    simp only [keyS_sR]
    exact hab
  have hX : ∀ (a : Fin i0) (p : Fin (2 * r + k + 1)), p ∉ Set.range (sR k r i0 hi0) →
      y (Fin.castLE hi0 a) p = 0 := by
    intro a p hp
    exact hz _ p a.isLt hp
  have hu : ∀ c : Fin i0 → Fin (2 * r + k + 1), StrictMono (fun l => keyS k r (c l)) →
      (∀ l, c l ∈ Set.range (sR k r i0 hi0)) → c = sR k r i0 hi0 := by
    intro c hc hS
    exact uniq_key (keyS k r) (keyS_inj k r) (sR k r i0 hi0) c he hc hS
  have hs := sum_single (M := A) (fun B : Fin i0 → Fin (2 * r + k + 1) => StrictMono (fun l => keyS k r (B l)))
    (fun a p => y (Fin.castLE hi0 a) p) (Set.range (sR k r i0 hi0)) hX (sR k r i0 hi0) he hu
    (fun B => qminor E B (sR k r i0 hi0) (ell + (i0 : ℂ) - 1))
  have hdet : (Matrix.of fun a l : Fin i0 => y (Fin.castLE hi0 a) (sR k r i0 hi0 l)).det = star h.det := by
    rw [← det_star]
    congr 1
    ext a b
    exact hh a b
  unfold AAv
  rw [← hdet]
  convert hs using 1

/- English proof (translation)
Introduce `A _ _ M _ _ k r z' E La y i0 s h t ell hs hj hG hR hh ht hy`. Take `⟨s', rfl⟩ : ∃ s', s = s' + 1` from `⟨s - 1, by omega⟩`. Establish `hm : i0 + s' ≤ r` using `by omega`. Establish `hm' : i0 + s' + 1 ≤ r` using `by omega`. Rewrite using `[AAv_congr k r E y (show i0 + (s' + 1) - 1 = i0 + s' by omega) _ hm]`.

Use `set e2 : Fin (i0 + s') → Fin (2 * r + k + 1) := fun l => sR k r (i0 + s' + 1) hm' ((⟨i0, by omega⟩ : Fin (i0 + s' + 1)).succAbove l) with he2def`. Establish `he2v : ∀ l, (e2 l).val = 2 * r + k - ((⟨i0, by omega⟩ : Fin (i0 + s' + 1)).succAbove l).val`. Introduce `l`. Simplify using `[e2, sR, esI]`. Establish `he2k : ∀ l, keyS k r (e2 l) = ((⟨i0, by omega⟩ : Fin (i0 + s' + 1)).succAbove l).val`.

Introduce `l`. Simplify using `only [e2]`. Rewrite using `[keyS_sR]`. Establish `he2 : StrictMono (fun l => keyS k r (e2 l))`. Introduce `a b hab`.

Simplify using `only [he2k]`. Conclude with `Fin.strictMono_succAbove _ hab`. Establish `hAA : AAv k r E y (i0 + s') hm ell = star (h.det * t ^ s' * sgnW s') • qminor E e2 (sR k r (i0 + s') hm) (ell + ((i0 + s' : ℕ) : ℂ) - 1)`. Unfold `AAv`. Rewrite using `[sum_single (fun B => StrictMono (fun l => keyS k r (B l))) (fun a p => y (Fin.castLE hm a) p) (Set.range e2) ?_ e2 he2 ?_]`.

Use `congr 1`. Establish `hp` using `minors_first_case i0 s' h t ⟨i0, by omega⟩`. Rewrite `hp` using `[if_pos rfl]`. Rewrite using `[← hp, ← det_star]`. Use `congr 1`.

Use extensionality with `a l`. Simplify using `only [Matrix.of_apply]`. Establish `hl` using `((⟨i0, by omega⟩ : Fin (i0 + s' + 1)).succAbove l).isLt`. Rewrite using `[hy _ _ (by simp; omega), if_pos (by rw [he2v]; omega), he2v]`. Apply the tactic sequence `congr 2 <;> (try simp) <;> omega`.

Introduce `a p hp`. Rewrite using `[hy _ _ (by simp; omega)]`. Use `split_ifs with h1`. Distinguish the cases in `hpi : 2 * r + k - p.val = i0`. Rewrite using `[hpi, zb_col_zero i0 s' h t _ (by simp), star_zero]`.

It suffices to derive a contradiction. Apply `hp` to reduce the goal to its premises. Apply the tactic sequence `refine ⟨⟨if 2 * r + k - p.val < i0 then 2 * r + k - p.val else 2 * r + k - p.val - 1, by split_ifs <;> omega⟩, ?_⟩`. Apply the tactic sequence `ext; rw [he2v, succAbove_val]; simp only; split_ifs <;> omega`. Both sides reduce to the same expression.

Introduce `c hc hS`. Conclude with `uniq_key (keyS k r) (keyS_inj k r) _ _ he2 hc hS`. Establish `hhead : AAv k r E y i0 (by omega) ell = star h.det • qminor E (sR k r i0 (by omega)) (sR k r i0 (by omega)) (ell + (i0 : ℂ) - 1)`. Apply `AAv_head` to reduce the goal to its premises. Introduce `a p ha hp`.

Rewrite using `[hy _ _ (by omega)]`. Use `split_ifs with hc`. Establish `hx : ¬ (2 * r + k - p.val < i0)`. Introduce `hlt`. Apply `hp` to reduce the goal to its premises.

Conclude with `⟨⟨2 * r + k - p.val, hlt⟩, by ext; simp [sR, esI]; omega⟩`. Unfold `Zb`. Rewrite using `[dif_pos ha, dif_neg hx, star_zero]`. Both sides reduce to the same expression. Introduce `a b`.

Establish `hb` using `b.isLt`. Rewrite using `[hy _ _ (by simp; omega)]`. Rewrite using `[if_pos (by simp [sR, esI]; omega)]`. Establish `hsv : (sR k r i0 (by omega) b).val = 2 * r + k - b.val` using `by simp [sR, esI]`. Establish `hav : (Fin.castLE (by omega : i0 ≤ r) a).val = a.val` using `by simp`.

Unfold `Zb`. Rewrite using `[hav, hsv]`. Rewrite using `[dif_pos a.isLt, dif_pos (by omega)]`. Use `congr 2`. Apply `Fin.ext` to reduce the goal to its premises.

Simplify using `only [Fin.val_mk]`. Use linear arithmetic over natural numbers and integers. Establish `hP` using `third_peeling_identity A k r z' E hG (i0 + s') hm' ⟨i0, by omega⟩ ell`. Establish `hLa : La (qminor E e2 (sR k r (i0 + s') hm) (ell + ((i0 + s' : ℕ) : ℂ) - 1)) = La (qminor E (sR k r i0 (by omega)) (sR k r i0 (by omega)) (ell + (i0 : ℂ) - 1))` using `la_congr hR hP`. Rewrite using `[hAA, hhead, map_smul, map_smul, hLa, (derivative_leading_zb i0 (s' + 1) h t).1, (derivative_leading_zb i0 (s' + 1) h t).2, smul_smul, smul_smul, smul_smul]`.

Use `congr 1`. Simplify using `only [star_mul', star_pow, star_sgnW, sgnW_succ, Nat.add_sub_cancel, star_neg, star_one]`. Rewrite using `[scal_E (star h.det) (star t) (sgnW s') ((-1) ^ s') s' (star_ne_zero.mpr hh) (star_ne_zero.mpr ht) (sgnW_sq s') (neg_one_sq' s')]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem second_expansion_identity : ExpansionDualColumn := by
  intro A _ _ M _ _ k r z' E La y i0 s h t ell hs hj hG hR hh ht hy
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  have hm : i0 + s' ≤ r := by omega
  have hm' : i0 + s' + 1 ≤ r := by omega
  rw [AAv_congr k r E y (show i0 + (s' + 1) - 1 = i0 + s' by omega) _ hm]
  set e2 : Fin (i0 + s') → Fin (2 * r + k + 1) :=
    fun l => sR k r (i0 + s' + 1) hm' ((⟨i0, by omega⟩ : Fin (i0 + s' + 1)).succAbove l) with he2def
  have he2v : ∀ l, (e2 l).val = 2 * r + k - ((⟨i0, by omega⟩ : Fin (i0 + s' + 1)).succAbove l).val := by
    intro l; simp [e2, sR, esI]
  have he2k : ∀ l, keyS k r (e2 l) = ((⟨i0, by omega⟩ : Fin (i0 + s' + 1)).succAbove l).val := by
    intro l; simp only [e2]; rw [keyS_sR]
  have he2 : StrictMono (fun l => keyS k r (e2 l)) := by
    intro a b hab
    simp only [he2k]; exact Fin.strictMono_succAbove _ hab
  have hAA : AAv k r E y (i0 + s') hm ell =
      star (h.det * t ^ s' * sgnW s') • qminor E e2 (sR k r (i0 + s') hm) (ell + ((i0 + s' : ℕ) : ℂ) - 1) := by
    unfold AAv
    rw [sum_single (fun B => StrictMono (fun l => keyS k r (B l))) (fun a p => y (Fin.castLE hm a) p)
      (Set.range e2) ?_ e2 he2 ?_]
    · congr 1
      have hp := minors_first_case i0 s' h t ⟨i0, by omega⟩
      rw [if_pos rfl] at hp
      rw [← hp, ← det_star]
      congr 1
      ext a l
      simp only [Matrix.of_apply]
      have hl := ((⟨i0, by omega⟩ : Fin (i0 + s' + 1)).succAbove l).isLt
      rw [hy _ _ (by simp; omega), if_pos (by rw [he2v]; omega), he2v]
      congr 2 <;> (try simp) <;> omega
    · intro a p hp
      rw [hy _ _ (by simp; omega)]
      split_ifs with h1
      · by_cases hpi : 2 * r + k - p.val = i0
        · rw [hpi, zb_col_zero i0 s' h t _ (by simp), star_zero]
        · exfalso; apply hp
          refine ⟨⟨if 2 * r + k - p.val < i0 then 2 * r + k - p.val else 2 * r + k - p.val - 1,
            by split_ifs <;> omega⟩, ?_⟩
          ext; rw [he2v, succAbove_val]; simp only; split_ifs <;> omega
      · rfl
    · intro c hc hS; exact uniq_key (keyS k r) (keyS_inj k r) _ _ he2 hc hS
  have hhead : AAv k r E y i0 (by omega) ell =
      star h.det • qminor E (sR k r i0 (by omega)) (sR k r i0 (by omega)) (ell + (i0 : ℂ) - 1) := by
    apply AAv_head
    · intro a p ha hp
      rw [hy _ _ (by omega)]
      split_ifs with hc
      · have hx : ¬ (2 * r + k - p.val < i0) := by
          intro hlt; apply hp
          exact ⟨⟨2 * r + k - p.val, hlt⟩, by ext; simp [sR, esI]; omega⟩
        unfold Zb; rw [dif_pos ha, dif_neg hx, star_zero]
      · rfl
    · intro a b
      have hb := b.isLt
      rw [hy _ _ (by simp; omega)]
      rw [if_pos (by simp [sR, esI]; omega)]
      have hsv : (sR k r i0 (by omega) b).val = 2 * r + k - b.val := by simp [sR, esI]
      have hav : (Fin.castLE (by omega : i0 ≤ r) a).val = a.val := by simp
      unfold Zb
      rw [hav, hsv]
      rw [dif_pos a.isLt, dif_pos (by omega)]
      congr 2
      apply Fin.ext; simp only [Fin.val_mk]; omega
  have hP := third_peeling_identity A k r z' E hG (i0 + s') hm' ⟨i0, by omega⟩ ell
  have hLa : La (qminor E e2 (sR k r (i0 + s') hm) (ell + ((i0 + s' : ℕ) : ℂ) - 1)) =
      La (qminor E (sR k r i0 (by omega)) (sR k r i0 (by omega)) (ell + (i0 : ℂ) - 1)) := la_congr hR hP
  rw [hAA, hhead, map_smul, map_smul, hLa, (derivative_leading_zb i0 (s' + 1) h t).1, (derivative_leading_zb i0 (s' + 1) h t).2,
    smul_smul, smul_smul, smul_smul]
  congr 1
  simp only [star_mul', star_pow, star_sgnW, sgnW_succ, Nat.add_sub_cancel, star_neg, star_one]
  rw [scal_E (star h.det) (star t) (sgnW s') ((-1) ^ s') s' (star_ne_zero.mpr hh) (star_ne_zero.mpr ht)
    (sgnW_sq s') (neg_one_sq' s')]
  ring

end Formalism.FourierDecayAlt.P.SignAntidiagonal
