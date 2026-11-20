import Formalism.HermitianCurvature.HermitianCurvatureProofs.ScalarInverseSimplification

open Matrix Finset

namespace Formalism.FourierDecayAlt.P.SignAntidiagonal

open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants

/- English proof (translation)
Distinguish the cases in `hp : r ≤ p.val ∧ p.val ≤ r + k`. Rewrite using `[Finset.sum_eq_single ⟨p.val - r, by omega⟩]`. Establish `: p = wI k r ⟨p.val - r, by omega⟩` using `by ext; simp [wI]; omega`. Rewrite using `[if_pos this, mul_one, ← this]`. Introduce `b _ hb`.

Rewrite using `[if_neg, mul_zero]`. Introduce `h`. Apply `hb` to reduce the goal to its premises. Use `ext`. Simplify using `only [h, wI]`.

Use linear arithmetic over natural numbers and integers. Simplify using the standard rewrite rules. Rewrite using `[hv p (by omega)]; symm`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `w _`.

Rewrite using `[if_neg, mul_zero]`. Introduce `h`. Apply `hp` to reduce the goal to its premises. Rewrite using `[h]`. Simplify using `only [wI]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem vec_wsum (k r : ℕ) (v : Fin (2 * r + k + 1) → ℂ) (hv : inWb k r v) (p : Fin (2 * r + k + 1)) :
    v p = ∑ w : Fin (k + 1), v (wI k r w) * (if p = wI k r w then 1 else 0) := by
  by_cases hp : r ≤ p.val ∧ p.val ≤ r + k
  · rw [Finset.sum_eq_single ⟨p.val - r, by omega⟩]
    · have : p = wI k r ⟨p.val - r, by omega⟩ := by ext; simp [wI]; omega
      rw [if_pos this, mul_one, ← this]
    · intro b _ hb
      rw [if_neg, mul_zero]
      intro h; apply hb; ext; simp only [h, wI]; omega
    · simp
  · rw [hv p (by omega)]; symm
    apply Finset.sum_eq_zero
    intro w _
    rw [if_neg, mul_zero]
    intro h; apply hp; rw [h]; simp only [wI]; omega

/- English proof (translation)
Use `w.isLt` as an intermediate fact. Unfold `keyS wI; simp only; rw [if_neg (by omega)]`.
-/
theorem keyS_wI (k r : ℕ) (w : Fin (k + 1)) : keyS k r (wI k r w) = r + w.val + r := by
  have := w.isLt
  unfold keyS wI; simp only; rw [if_neg (by omega)]

/- English proof (translation)
Introduce `A _ _ M _ _ k r z' yb E La y i0 s h t ell hs hj hG hR hh ht hz' hyb hzy hya hyi0`. Take `⟨s'', rfl⟩ : ∃ s'', s = s'' + 2` from `⟨s - 2, by omega⟩`. Take `rfl : r = i0 + s'' + 1` from `by omega`. Use `set i : Fin (i0 + s'' + 1) := ⟨i0, by omega⟩ with hidef`. Use `set f : Fin (i0 + s'') → Fin (2 * (i0 + s'' + 1) + k + 1) := fun l => sR k (i0 + s'' + 1) (i0 + s'' + 1) le_rfl (i.succAbove l) with hfdef`.

Establish `hfv : ∀ l, (f l).val = 2 * (i0 + s'' + 1) + k - (i.succAbove l).val` using `by intro l; simp [f, sR, esI]`. Establish `hfk : ∀ l, keyS k _ (f l) = (i.succAbove l).val` using `by intro l; simp only [f]; rw [keyS_sR]`. Use `set ew : Fin (k + 1) → Fin (i0 + s'' + 1) → Fin (2 * (i0 + s'' + 1) + k + 1) := fun w => Fin.snoc (α := fun _ => Fin (2 * (i0 + s'' + 1) + k + 1)) f (wI k (i0 + s'' + 1) w) with hewdef`. Establish `hew : ∀ w, StrictMono (fun l => keyS k _ (ew w l))`. Introduce `w`.

Establish `e : (fun l => keyS k _ (ew w l)) = Fin.snoc (α` using `fun _ => ℕ) (fun l => keyS k (i0 + s'' + 1) (f l)) (keyS k (i0 + s'' + 1) (wI k (i0 + s'' + 1) w)) := by`. Use function extensionality and compare the values at `l`. Proceed by induction on `l using Fin.lastCases with`. Consider the case `last => simp [ew]`. Consider the case `cast l => simp [ew]`.

Rewrite using `[e]`. Apply `strictMono_snoc` to reduce the goal to its premises. Introduce `a b hab`. Simplify using `only [hfk]`. Conclude with `Fin.strictMono_succAbove _ hab`.

Introduce `l`. Rewrite using `[hfk, keyS_wI]`. Use `(i.succAbove l).isLt` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hew_last : ∀ w (j : Fin (i0 + s'' + 1)), ew w j = wI k _ w ↔ j = Fin.last _`.

Introduce `w j`. Prove the components needed by the constructor for the conclusion. Introduce `hj`. Assume the negation of the conclusion as `hne`. Take `⟨l, rfl⟩` from `Fin.exists_castSucc_eq.mpr hne`.

Use `congrArg Fin.val hj` as an intermediate fact. Simplify using `only [ew, Fin.snoc_castSucc] at this`. Rewrite `this` using `[hfv]`. Simplify using `[wI] at this`. Use `(i.succAbove l).isLt` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Introduce and unpack `rfl`. Simplify using `[ew]`. Establish `hdet : ∀ w, (Matrix.of fun a l => if a = i then (if ew w l = wI k _ w then (1 : ℂ) else 0) else y (Fin.castLE le_rfl a) (ew w l)).det = (-1) ^ s'' * star (h.det * t ^ s'' * sgnW s'')`. Introduce `w`.

Rewrite using `[Matrix.det_succ_row _ i, Finset.sum_eq_single (Fin.last _)]`. Simplify using `only [Matrix.of_apply, (hew_last w (Fin.last _)).mpr rfl, if_true, mul_one, Fin.succAbove_last]`. Establish `hsub : (Matrix.of fun a l => if a = i then (if ew w l = wI k _ w then (1 : ℂ) else 0) else y (Fin.castLE le_rfl a) (ew w l)).submatrix i.succAbove Fin.castSucc = (starRingEnd ℂ).mapMatrix (Matrix.of fun a b : Fin (i0 + s'') => Zb i0 (s'' + 2) h t ((⟨i0, by omega⟩ : Fin (i0 + s'' …`. Use extensionality with `a b`. Simplify using `only [Matrix.submatrix_apply, Matrix.of_apply]`.

Rewrite using `[if_neg (Fin.succAbove_ne i a)]`. Simplify using `only [ew, Fin.snoc_castSucc]`. Establish `hb` using `(i.succAbove b).isLt`. Establish `hbne : (i.succAbove b).val ≠ i0` using `fun h' => Fin.succAbove_ne i b (Fin.ext h')`. Establish `hane : (i.succAbove a).val ≠ i0` using `fun h' => Fin.succAbove_ne i a (Fin.ext h')`.

Rewrite using `[hya _ _ (by simpa using hane), if_pos ⟨by rw [hfv]; omega, by rw [hfv]; omega⟩, hfv]`. Rewrite using `[show 2 * (i0 + s'' + 1) + k - (2 * (i0 + s'' + 1) + k - (i.succAbove b).val) = (i.succAbove b).val by omega]`. Simplify using `[i]`. Rewrite using `[hsub, ← RingHom.map_det, third_polynomial_expansion, starRingEnd_apply]`. Simplify using `only [Fin.val_last]`.

Rewrite using `[show i.val + (i0 + s'') = (i0 + i0) + s'' by simp [i]; ring, pow_add, ← two_mul, pow_mul]`. Evaluate the numerical expressions. Introduce `j _ hj`. Simplify using `only [Matrix.of_apply, if_pos rfl]`. Rewrite using `[if_neg (fun h' => hj ((hew_last w j).mp h'))]`.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Establish `harg : ell + (((i0 + s'' + 1 : ℕ)) : ℂ) - 1 = ell + ((i0 + s'' : ℕ) : ℂ)` using `by push_cast; ring`. Establish `hAA : AAv k (i0 + s'' + 1) E y (i0 + s'' + 1) le_rfl ell = ((-1) ^ s'' * star (h.det * t ^ s'' * sgnW s'')) • ∑ w, yb (wI k _ w) • qminor E (ew w) (sR k _ (i0 + s'' + 1) le_rfl) (ell + ((i0 + s'' : ℕ) : ℂ))`. Unfold `AAv`.

Rewrite using `[harg]`. Rewrite using `[sum_lin (fun B => StrictMono (fun l => keyS k _ (B l))) (fun a p => y (Fin.castLE le_rfl a) p) i (fun w => yb (wI k _ w)) (fun w p => if p = wI k _ w then 1 else 0) (fun p => by rw [hyi0 _ (by simp [i])]; exact vec_wsum k _ yb hyb p)]`. Rewrite using `[Finset.smul_sum]`. Use `congr 1`. Use extensionality with `w`.

Rewrite using `[sum_single (fun B => StrictMono (fun l => keyS k _ (B l))) (fun a p => if a = i then (if p = wI k _ w then (1 : ℂ) else 0) else y (Fin.castLE le_rfl a) p) (Set.range (ew w)) ?_ (ew w) (hew w) ?_, hdet w, smul_comm]`. Introduce `a p hp`. Distinguish the cases in `ha : a = i`. Rewrite using `[if_pos ha, if_neg]; intro hpw; apply hp; exact ⟨Fin.last _, by rw [hpw]; simp [ew]⟩`. Rewrite using `[if_neg ha]`.

Establish `hane : a.val ≠ i0` using `fun h' => ha (Fin.ext h')`. Rewrite using `[hya _ _ (by simpa using hane)]`. Rewrite using `[if_neg]`. Introduce and unpack `⟨hp1, hp2⟩`. Apply `hp` to reduce the goal to its premises.

Apply the tactic sequence `refine ⟨Fin.castSucc ⟨if 2 * (i0 + s'' + 1) + k - p.val < i0 then 2 * (i0 + s'' + 1) + k - p.val else 2 * (i0 + s'' + 1) + k - p.val - 1, by split_ifs <;> omega⟩, ?_⟩`. Apply the tactic sequence `ext; simp only [ew, Fin.snoc_castSucc]; rw [hfv, succAbove_val]; simp only [i]; split_ifs <;> omega`. Introduce `c hc hS`. Conclude with `uniq_key (keyS k _) (keyS_inj k _) _ _ (hew w) hc hS`. Establish `hhead : AAv k (i0 + s'' + 1) E y i0 (by omega) ell = star h.det • qminor E (sR k _ i0 (by omega)) (sR k _ i0 (by omega)) (ell + (i0 : ℂ) - 1)`.

Apply `AAv_head` to reduce the goal to its premises. Introduce `a p ha hp`. Rewrite using `[hya _ _ (by omega)]`. Use `split_ifs with hc`. Establish `hx : ¬ (2 * (i0 + s'' + 1) + k - p.val < i0)`.

Introduce `hlt`. Apply `hp` to reduce the goal to its premises. Conclude with `⟨⟨2 * (i0 + s'' + 1) + k - p.val, hlt⟩, by ext; simp [sR, esI]; omega⟩`. Unfold `Zb`. Rewrite using `[dif_pos ha, dif_neg hx, star_zero]`.

Both sides reduce to the same expression. Introduce `a b`. Establish `hb` using `b.isLt`. Rewrite using `[hya _ _ (by simp; omega)]`. Rewrite using `[if_pos (by simp [sR, esI]; omega)]`.

Establish `hsv : (sR k (i0 + s'' + 1) i0 (by omega) b).val = 2 * (i0 + s'' + 1) + k - b.val` using `by simp [sR, esI]`. Establish `hav : (Fin.castLE (by omega : i0 ≤ i0 + s'' + 1) a).val = a.val` using `by simp`. Unfold `Zb`. Rewrite using `[hav, hsv]`. Rewrite using `[dif_pos a.isLt, dif_pos (by omega)]`.

Use `congr 2`. Apply `Fin.ext` to reduce the goal to its premises. Simplify using `only`. Use linear arithmetic over natural numbers and integers. Establish `hP` using `fourth_peeling_identity A k (i0 + s'') z' yb E hG i ell hz' hyb`.

Establish `hLa : (∑ w, yb (wI k _ w) • La (qminor E (ew w) (sR k _ (i0 + s'' + 1) le_rfl) (ell + ((i0 + s'' : ℕ) : ℂ)))) = star t • La (qminor E (sR k _ i0 (by omega)) (sR k _ i0 (by omega)) (ell + (i0 : ℂ) - 1))`. Use `la_congr hR hP` as an intermediate fact. Rewrite `this` using `[map_sum]`. Simplify using `only [map_smul] at this`. Rewrite `this` using `[herm_swap, hzy]`.

Conclude with `this`. Establish `hD : Dlead i0 (s'' + 2) h t (i0 + s'' + 1 + 1) = h.det * t ^ (s'' + 2) * -sgnW s''`. Rewrite using `[show i0 + s'' + 1 + 1 = i0 + (s'' + 2) by omega, (derivative_leading_zb i0 (s'' + 2) h t).2, sign_alternates_add_two]`. Rewrite using `[hAA, hhead, map_smul, map_smul, map_sum]`. Simplify using `only [map_smul]`.

Rewrite using `[hLa, hD, (derivative_leading_zb i0 (s'' + 2) h t).1, smul_smul, smul_smul, smul_smul, smul_smul]`. Use `congr 1`. Rewrite using `[show s'' + 2 - 1 = s'' + 1 by omega]`. Simplify using `only [star_mul', star_pow, star_neg, star_sgnW]`. Establish `h1` using `star_ne_zero.mpr hh`.

Establish `h2` using `star_ne_zero.mpr ht`. Apply the tactic sequence `rcases mul_self_eq_one_iff.mp (sgnW_sq s'') with h3 | h3 <;> rw [h3] <;> field_simp <;> ring`.
-/
theorem fourth_expansion_identity : ExpansionDualCovector := by
  intro A _ _ M _ _ k r z' yb E La y i0 s h t ell hs hj hG hR hh ht hz' hyb hzy hya hyi0
  obtain ⟨s'', rfl⟩ : ∃ s'', s = s'' + 2 := ⟨s - 2, by omega⟩
  obtain rfl : r = i0 + s'' + 1 := by omega
  set i : Fin (i0 + s'' + 1) := ⟨i0, by omega⟩ with hidef
  set f : Fin (i0 + s'') → Fin (2 * (i0 + s'' + 1) + k + 1) :=
    fun l => sR k (i0 + s'' + 1) (i0 + s'' + 1) le_rfl (i.succAbove l) with hfdef
  have hfv : ∀ l, (f l).val = 2 * (i0 + s'' + 1) + k - (i.succAbove l).val := by intro l; simp [f, sR, esI]
  have hfk : ∀ l, keyS k _ (f l) = (i.succAbove l).val := by intro l; simp only [f]; rw [keyS_sR]
  set ew : Fin (k + 1) → Fin (i0 + s'' + 1) → Fin (2 * (i0 + s'' + 1) + k + 1) :=
    fun w => Fin.snoc (α := fun _ => Fin (2 * (i0 + s'' + 1) + k + 1)) f (wI k (i0 + s'' + 1) w) with hewdef
  have hew : ∀ w, StrictMono (fun l => keyS k _ (ew w l)) := by
    intro w
    have e : (fun l => keyS k _ (ew w l)) = Fin.snoc (α := fun _ => ℕ) (fun l => keyS k (i0 + s'' + 1) (f l)) (keyS k (i0 + s'' + 1) (wI k (i0 + s'' + 1) w)) := by
      funext l
      induction l using Fin.lastCases with
      | last => simp [ew]
      | cast l => simp [ew]
    rw [e]
    apply strictMono_snoc
    · intro a b hab; simp only [hfk]; exact Fin.strictMono_succAbove _ hab
    · intro l; rw [hfk, keyS_wI]; have := (i.succAbove l).isLt; omega
  have hew_last : ∀ w (j : Fin (i0 + s'' + 1)), ew w j = wI k _ w ↔ j = Fin.last _ := by
    intro w j
    constructor
    · intro hj
      by_contra hne
      obtain ⟨l, rfl⟩ := Fin.exists_castSucc_eq.mpr hne
      have := congrArg Fin.val hj
      simp only [ew, Fin.snoc_castSucc] at this
      rw [hfv] at this; simp [wI] at this; have := (i.succAbove l).isLt; omega
    · rintro rfl; simp [ew]
  have hdet : ∀ w, (Matrix.of fun a l => if a = i then (if ew w l = wI k _ w then (1 : ℂ) else 0)
      else y (Fin.castLE le_rfl a) (ew w l)).det = (-1) ^ s'' * star (h.det * t ^ s'' * sgnW s'') := by
    intro w
    rw [Matrix.det_succ_row _ i, Finset.sum_eq_single (Fin.last _)]
    · simp only [Matrix.of_apply, (hew_last w (Fin.last _)).mpr rfl, if_true, mul_one, Fin.succAbove_last]
      have hsub : (Matrix.of fun a l => if a = i then (if ew w l = wI k _ w then (1 : ℂ) else 0)
          else y (Fin.castLE le_rfl a) (ew w l)).submatrix i.succAbove Fin.castSucc =
          (starRingEnd ℂ).mapMatrix (Matrix.of fun a b : Fin (i0 + s'') => Zb i0 (s'' + 2) h t
            ((⟨i0, by omega⟩ : Fin (i0 + s'' + 1)).succAbove a).val ((⟨i0, by omega⟩ : Fin (i0 + s'' + 1)).succAbove b).val) := by
        ext a b
        simp only [Matrix.submatrix_apply, Matrix.of_apply]
        rw [if_neg (Fin.succAbove_ne i a)]
        simp only [ew, Fin.snoc_castSucc]
        have hb := (i.succAbove b).isLt
        have hbne : (i.succAbove b).val ≠ i0 := fun h' => Fin.succAbove_ne i b (Fin.ext h')
        have hane : (i.succAbove a).val ≠ i0 := fun h' => Fin.succAbove_ne i a (Fin.ext h')
        rw [hya _ _ (by simpa using hane), if_pos ⟨by rw [hfv]; omega, by rw [hfv]; omega⟩, hfv]
        rw [show 2 * (i0 + s'' + 1) + k - (2 * (i0 + s'' + 1) + k - (i.succAbove b).val) = (i.succAbove b).val by omega]
        simp [i]
      rw [hsub, ← RingHom.map_det, third_polynomial_expansion, starRingEnd_apply]
      simp only [Fin.val_last]
      rw [show i.val + (i0 + s'') = (i0 + i0) + s'' by simp [i]; ring, pow_add, ← two_mul, pow_mul]
      norm_num
    · intro j _ hj
      simp only [Matrix.of_apply, if_pos rfl]
      rw [if_neg (fun h' => hj ((hew_last w j).mp h'))]; simp
    · simp
  have harg : ell + (((i0 + s'' + 1 : ℕ)) : ℂ) - 1 = ell + ((i0 + s'' : ℕ) : ℂ) := by push_cast; ring
  have hAA : AAv k (i0 + s'' + 1) E y (i0 + s'' + 1) le_rfl ell =
      ((-1) ^ s'' * star (h.det * t ^ s'' * sgnW s'')) • ∑ w, yb (wI k _ w) •
        qminor E (ew w) (sR k _ (i0 + s'' + 1) le_rfl) (ell + ((i0 + s'' : ℕ) : ℂ)) := by
    unfold AAv
    rw [harg]
    rw [sum_lin (fun B => StrictMono (fun l => keyS k _ (B l))) (fun a p => y (Fin.castLE le_rfl a) p) i
      (fun w => yb (wI k _ w)) (fun w p => if p = wI k _ w then 1 else 0)
      (fun p => by rw [hyi0 _ (by simp [i])]; exact vec_wsum k _ yb hyb p)]
    rw [Finset.smul_sum]
    congr 1; ext w
    rw [sum_single (fun B => StrictMono (fun l => keyS k _ (B l))) (fun a p => if a = i then (if p = wI k _ w then (1 : ℂ) else 0)
      else y (Fin.castLE le_rfl a) p) (Set.range (ew w)) ?_ (ew w) (hew w) ?_, hdet w, smul_comm]
    · intro a p hp
      by_cases ha : a = i
      · rw [if_pos ha, if_neg]; intro hpw; apply hp; exact ⟨Fin.last _, by rw [hpw]; simp [ew]⟩
      · rw [if_neg ha]
        have hane : a.val ≠ i0 := fun h' => ha (Fin.ext h')
        rw [hya _ _ (by simpa using hane)]
        rw [if_neg]
        rintro ⟨hp1, hp2⟩
        apply hp
        refine ⟨Fin.castSucc ⟨if 2 * (i0 + s'' + 1) + k - p.val < i0 then 2 * (i0 + s'' + 1) + k - p.val
          else 2 * (i0 + s'' + 1) + k - p.val - 1, by split_ifs <;> omega⟩, ?_⟩
        ext; simp only [ew, Fin.snoc_castSucc]; rw [hfv, succAbove_val]; simp only [i]; split_ifs <;> omega
    · intro c hc hS; exact uniq_key (keyS k _) (keyS_inj k _) _ _ (hew w) hc hS
  have hhead : AAv k (i0 + s'' + 1) E y i0 (by omega) ell =
      star h.det • qminor E (sR k _ i0 (by omega)) (sR k _ i0 (by omega)) (ell + (i0 : ℂ) - 1) := by
    apply AAv_head
    · intro a p ha hp
      rw [hya _ _ (by omega)]
      split_ifs with hc
      · have hx : ¬ (2 * (i0 + s'' + 1) + k - p.val < i0) := by
          intro hlt; apply hp
          exact ⟨⟨2 * (i0 + s'' + 1) + k - p.val, hlt⟩, by ext; simp [sR, esI]; omega⟩
        unfold Zb; rw [dif_pos ha, dif_neg hx, star_zero]
      · rfl
    · intro a b
      have hb := b.isLt
      rw [hya _ _ (by simp; omega)]
      rw [if_pos (by simp [sR, esI]; omega)]
      have hsv : (sR k (i0 + s'' + 1) i0 (by omega) b).val = 2 * (i0 + s'' + 1) + k - b.val := by simp [sR, esI]
      have hav : (Fin.castLE (by omega : i0 ≤ i0 + s'' + 1) a).val = a.val := by simp
      unfold Zb
      rw [hav, hsv]
      rw [dif_pos a.isLt, dif_pos (by omega)]
      congr 2
      apply Fin.ext; simp only; omega
  have hP := fourth_peeling_identity A k (i0 + s'') z' yb E hG i ell hz' hyb
  have hLa : (∑ w, yb (wI k _ w) • La (qminor E (ew w) (sR k _ (i0 + s'' + 1) le_rfl) (ell + ((i0 + s'' : ℕ) : ℂ)))) =
      star t • La (qminor E (sR k _ i0 (by omega)) (sR k _ i0 (by omega)) (ell + (i0 : ℂ) - 1)) := by
    have := la_congr hR hP
    rw [map_sum] at this
    simp only [map_smul] at this
    rw [herm_swap, hzy] at this
    exact this
  have hD : Dlead i0 (s'' + 2) h t (i0 + s'' + 1 + 1) = h.det * t ^ (s'' + 2) * -sgnW s'' := by
    rw [show i0 + s'' + 1 + 1 = i0 + (s'' + 2) by omega, (derivative_leading_zb i0 (s'' + 2) h t).2, sign_alternates_add_two]
  rw [hAA, hhead, map_smul, map_smul, map_sum]
  simp only [map_smul]
  rw [hLa, hD, (derivative_leading_zb i0 (s'' + 2) h t).1, smul_smul, smul_smul, smul_smul, smul_smul]
  congr 1
  rw [show s'' + 2 - 1 = s'' + 1 by omega]
  simp only [star_mul', star_pow, star_neg, star_sgnW]
  have h1 := star_ne_zero.mpr hh
  have h2 := star_ne_zero.mpr ht
  rcases mul_self_eq_one_iff.mp (sgnW_sq s'') with h3 | h3 <;> rw [h3] <;> field_simp <;> ring

end Formalism.FourierDecayAlt.P.SignAntidiagonal
