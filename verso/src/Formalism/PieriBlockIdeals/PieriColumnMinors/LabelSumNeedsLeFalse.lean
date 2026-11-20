import Mathlib
import Formalism.PieriBlockIdeals.Statement

noncomputable section

open Finset

namespace Formalism.CohomologicalDescent

open Classical

/- English proof (translation)
Assume the negation of the conclusion as `hlt`. Use `push Not at hlt`. Establish `hdvd : (l : ℤ) ^ 2 ∣ n`. Establish `h2 : (l : ℤ) ^ 2 ∣ (l : ℤ) ^ vl l n` using `pow_dvd_pow _ (by omega)`. Use `h2.trans ?_` and prove the remaining obligations.

Establish `h3 : l ^ padicValNat l n.natAbs ∣ n.natAbs` using `pow_padicValNat_dvd`. Establish `h4 : ((l ^ padicValNat l n.natAbs : ℕ) : ℤ) ∣ ((n.natAbs : ℕ) : ℤ)` using `Int.natCast_dvd_natCast.mpr h3`. Rewrite `h4` using `[Int.natAbs_of_nonneg h0.le]`. Simplify `h4` using `[vl, padicValInt]`. Use `Int.le_of_dvd h0 hdvd` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma label_vl_le_one {l : ℕ} (_hl : l.Prime) {n : ℤ} (h0 : 0 < n) (h1 : n < (l : ℤ) ^ 2) :
    vl l n ≤ 1 := by
  by_contra hlt
  push Not at hlt
  have hdvd : (l : ℤ) ^ 2 ∣ n := by
    have h2 : (l : ℤ) ^ 2 ∣ (l : ℤ) ^ vl l n := pow_dvd_pow _ (by omega)
    refine h2.trans ?_
    have h3 : l ^ padicValNat l n.natAbs ∣ n.natAbs := pow_padicValNat_dvd
    have h4 : ((l ^ padicValNat l n.natAbs : ℕ) : ℤ) ∣ ((n.natAbs : ℕ) : ℤ) :=
      Int.natCast_dvd_natCast.mpr h3
    rw [Int.natAbs_of_nonneg h0.le] at h4
    simpa [vl, padicValInt] using h4
  have := Int.le_of_dvd h0 hdvd
  linarith

/- English proof (translation)
Use `split_ifs with hd`. Conclude with `label_vl_le_one hl h0 h1` after adjusting the coercions. Establish `h : vl l n = 0` using `padicValInt.eq_zero_of_not_dvd hd`. Simplify using `[h]`.
-/
lemma label_vl_le_ind {l : ℕ} (hl : l.Prime) {n : ℤ} (h0 : 0 < n) (h1 : n < (l : ℤ) ^ 2) :
    (vl l n : ℝ) ≤ if (l : ℤ) ∣ n then 1 else 0 := by
  split_ifs with hd
  · exact_mod_cast label_vl_le_one hl h0 h1
  · have h : vl l n = 0 := padicValInt.eq_zero_of_not_dvd hd
    simp [h]

/- English proof (translation)
Rewrite using `[Finset.sum_filter]`. Use `Finset.sum_le_sum fun x hx => ?_` and prove the remaining obligations. Establish `h` using `label_vl_le_ind hl (hr x hx).1 (hr x hx).2`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma label_sum_le_filter {l : ℕ} (hl : l.Prime) (s : Finset ℤ) (mB : ℤ) (c : ℤ → ℝ)
    (hc : ∀ x ∈ s, 0 ≤ c x) (hr : ∀ x ∈ s, 0 < x - mB ∧ x - mB < (l : ℤ) ^ 2) :
    ∑ x ∈ s, c x * (vl l (x - mB) : ℝ) ≤ ∑ x ∈ s.filter (fun x => (l : ℤ) ∣ x - mB), c x := by
  rw [Finset.sum_filter]
  refine Finset.sum_le_sum fun x hx => ?_
  have h := label_vl_le_ind hl (hr x hx).1 (hr x hx).2
  calc c x * (vl l (x - mB) : ℝ) ≤ c x * (if (l : ℤ) ∣ x - mB then 1 else 0) :=
        mul_le_mul_of_nonneg_left h (hc x hx)
    _ = if (l : ℤ) ∣ x - mB then c x else 0 := by split_ifs <;> simp

/- English proof (translation)
Establish `hl : (0 : ℤ) < l` using `by exact_mod_cast hl0`. Establish `hq0 : 0 ≤ (xp - xm) / (l : ℤ)` using `Int.ediv_nonneg (by linarith) hl.le`. Establish `hcard : ((Finset.Icc xm xp).filter (fun x => (l : ℤ) ∣ x - mB)).card ≤ (Finset.Icc (0 : ℤ) ((xp - xm) / (l : ℤ))).card`. Use `Finset.card_le_card_of_injOn (fun x => (x - xm) / (l : ℤ)) ?_ ?_` and prove the remaining obligations. Introduce `x hx`.

Simplify using `only [Finset.coe_Icc, Finset.coe_filter, Set.mem_Icc, Set.mem_ofPred_eq, Finset.mem_Icc] at hx ⊢`. Conclude with `⟨Int.ediv_nonneg (by linarith) hl.le, Int.ediv_le_ediv hl (by linarith)⟩`. Introduce `x hx y hy hxy`. Simplify using `only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_Icc] at hx hy`. Establish `hxy' : (x - xm) / (l : ℤ) = (y - xm) / (l : ℤ)` using `hxy`.

Establish `hmod : (x - xm) % (l : ℤ) = (y - xm) % (l : ℤ)`. Rewrite using `[Int.emod_eq_emod_iff_emod_sub_eq_zero]`. Apply `Int.emod_eq_zero_of_dvd` to reduce the goal to its premises. Establish `e : (x - xm) - (y - xm) = (x - mB) - (y - mB)` using `by ring`. Rewrite using `[e]`.

Conclude with `dvd_sub hx.2 hy.2`. Establish `e1 : (l : ℤ) * ((x - xm) / (l : ℤ)) + (x - xm) % (l : ℤ) = x - xm`. Conclude with `Int.mul_ediv_add_emod _ _`. Establish `e2 : (l : ℤ) * ((y - xm) / (l : ℤ)) + (y - xm) % (l : ℤ) = y - xm`. Conclude with `Int.mul_ediv_add_emod _ _`.

Rewrite `e1` using `[hxy', hmod]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hIcc : ((Finset.Icc (0 : ℤ) ((xp - xm) / (l : ℤ))).card : ℤ) = (xp - xm) / (l : ℤ) + 1`. Rewrite using `[Int.card_Icc, Int.toNat_of_nonneg (by omega)]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hqr : (((xp - xm) / (l : ℤ) : ℤ) : ℝ) ≤ ((xp - xm : ℤ) : ℝ) / l`. Rewrite using `[le_div_iff₀ (by exact_mod_cast hl0 : (0 : ℝ) < l)]`. Use `Int.ediv_mul_le (xp - xm) (ne_of_gt hl)` as an intermediate fact. Conclude with `this` after adjusting the coercions. Establish `hc : ((((Finset.Icc xm xp).filter (fun x => (l : ℤ) ∣ x - mB)).card : ℕ) : ℤ) ≤ (xp - xm) / (l : ℤ) + 1`.

Rewrite using `[← hIcc]`. Conclude with `hcard` after adjusting the coercions. Establish `hcR : ((((Finset.Icc xm xp).filter (fun x => (l : ℤ) ∣ x - mB)).card : ℕ) : ℝ) ≤ (((xp - xm) / (l : ℤ) : ℤ) : ℝ) + 1`. Conclude with `hc` after adjusting the coercions. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma label_card_le {l : ℕ} (hl0 : 0 < l) (xm xp mB : ℤ) (hx : xm ≤ xp) :
    ((((Finset.Icc xm xp).filter (fun x => (l : ℤ) ∣ x - mB)).card : ℕ) : ℝ)
      ≤ ((xp - xm : ℤ) : ℝ) / l + 1 := by
  have hl : (0 : ℤ) < l := by exact_mod_cast hl0
  have hq0 : 0 ≤ (xp - xm) / (l : ℤ) := Int.ediv_nonneg (by linarith) hl.le
  have hcard : ((Finset.Icc xm xp).filter (fun x => (l : ℤ) ∣ x - mB)).card ≤
      (Finset.Icc (0 : ℤ) ((xp - xm) / (l : ℤ))).card := by
    refine Finset.card_le_card_of_injOn (fun x => (x - xm) / (l : ℤ)) ?_ ?_
    · intro x hx
      simp only [Finset.coe_Icc, Finset.coe_filter, Set.mem_Icc, Set.mem_ofPred_eq,
        Finset.mem_Icc] at hx ⊢
      exact ⟨Int.ediv_nonneg (by linarith) hl.le, Int.ediv_le_ediv hl (by linarith)⟩
    · intro x hx y hy hxy
      simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_Icc] at hx hy
      have hxy' : (x - xm) / (l : ℤ) = (y - xm) / (l : ℤ) := hxy
      have hmod : (x - xm) % (l : ℤ) = (y - xm) % (l : ℤ) := by
        rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]
        apply Int.emod_eq_zero_of_dvd
        have e : (x - xm) - (y - xm) = (x - mB) - (y - mB) := by ring
        rw [e]
        exact dvd_sub hx.2 hy.2
      have e1 : (l : ℤ) * ((x - xm) / (l : ℤ)) + (x - xm) % (l : ℤ) = x - xm := by
        exact Int.mul_ediv_add_emod _ _
      have e2 : (l : ℤ) * ((y - xm) / (l : ℤ)) + (y - xm) % (l : ℤ) = y - xm := by
        exact Int.mul_ediv_add_emod _ _
      rw [hxy', hmod] at e1
      linarith
  have hIcc : ((Finset.Icc (0 : ℤ) ((xp - xm) / (l : ℤ))).card : ℤ) = (xp - xm) / (l : ℤ) + 1 := by
    rw [Int.card_Icc, Int.toNat_of_nonneg (by omega)]
    ring
  have hqr : (((xp - xm) / (l : ℤ) : ℤ) : ℝ) ≤ ((xp - xm : ℤ) : ℝ) / l := by
    rw [le_div_iff₀ (by exact_mod_cast hl0 : (0 : ℝ) < l)]
    have := Int.ediv_mul_le (xp - xm) (ne_of_gt hl)
    exact_mod_cast this
  have hc : ((((Finset.Icc xm xp).filter (fun x => (l : ℤ) ∣ x - mB)).card : ℕ) : ℤ) ≤
      (xp - xm) / (l : ℤ) + 1 := by
    rw [← hIcc]
    exact_mod_cast hcard
  have hcR : ((((Finset.Icc xm xp).filter (fun x => (l : ℤ) ∣ x - mB)).card : ℕ) : ℝ) ≤
      (((xp - xm) / (l : ℤ) : ℤ) : ℝ) + 1 := by
    exact_mod_cast hc
  linarith

/- English proof (translation)
Establish `hne : ({d : ℕ | 1 ≤ d ∧ (l : ℤ) ∣ D - (d : ℤ)} : Set ℕ).Nonempty`. Use `⟨D.toNat + l, ?_⟩` and prove the remaining obligations. Simplify using `only [Set.mem_ofPred_eq]`. Use `⟨by omega, ?_⟩` and prove the remaining obligations. Establish `e : D - ((D.toNat + l : ℕ) : ℤ) = -(l : ℤ)`.

Use `push_cast`. Rewrite using `[Int.toNat_of_nonneg hD]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `(dvd_neg).mpr dvd_rfl`.

Unfold `d0`. Conclude with `Nat.sInf_mem hne`.
-/
lemma leastCongruentPos_mem {l : ℕ} (hl : 0 < l) (D : ℤ) (hD : 0 ≤ D) :
    1 ≤ d0 l D ∧ (l : ℤ) ∣ D - (d0 l D : ℤ) := by
  have hne : ({d : ℕ | 1 ≤ d ∧ (l : ℤ) ∣ D - (d : ℤ)} : Set ℕ).Nonempty := by
    refine ⟨D.toNat + l, ?_⟩
    simp only [Set.mem_ofPred_eq]
    refine ⟨by omega, ?_⟩
    have e : D - ((D.toNat + l : ℕ) : ℤ) = -(l : ℤ) := by
      push_cast
      rw [Int.toNat_of_nonneg hD]
      ring
    rw [e]
    exact (dvd_neg).mpr dvd_rfl
  unfold d0
  exact Nat.sInf_mem hne

/- English proof (translation)
Unfold `d0`. Conclude with `Nat.sInf_le ⟨h1, hd⟩`.
-/
lemma leastCongruentPos_le {l : ℕ} (D : ℤ) (d : ℕ) (h1 : 1 ≤ d) (hd : (l : ℤ) ∣ D - d) : d0 l D ≤ d := by
  unfold d0
  exact Nat.sInf_le ⟨h1, hd⟩

/- English proof (translation)
Establish `hl : (0 : ℝ) < l` using `by exact_mod_cast hl0`. Establish `hhR : (0 : ℝ) < h` using `by exact_mod_cast (by omega : 0 < h)`. Break down `Nat.eq_zero_or_pos (h / l) with h0 | hpos` into its components or cases. Rewrite using `[h0, harmonic_zero, Rat.cast_zero]`. Establish `hx : (0 : ℝ) < (h : ℝ) / l` using `div_pos hhR hl`.

Establish `h1` using `Real.one_sub_inv_le_log_of_pos hx`. Establish `hinv : ((h : ℝ) / l)⁻¹ ≤ 2`. Rewrite using `[inv_div, div_le_iff₀ hhR]`. Conclude with `hlh` after adjusting the coercions. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `h1` using `harmonic_le_one_add_log (h / l)`. Establish `h2 : Real.log ((h / l : ℕ) : ℝ) ≤ Real.log ((h : ℝ) / l)` using `Real.log_le_log (by exact_mod_cast hpos) Nat.cast_div_le`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma label_harm_le {l h : ℕ} (hl0 : 0 < l) (hlh : l ≤ 2 * h) :
    ((harmonic (h / l) : ℚ) : ℝ) ≤ 1 + Real.log ((h : ℝ) / (l : ℝ)) := by
  have hl : (0 : ℝ) < l := by exact_mod_cast hl0
  have hhR : (0 : ℝ) < h := by exact_mod_cast (by omega : 0 < h)
  rcases Nat.eq_zero_or_pos (h / l) with h0 | hpos
  · rw [h0, harmonic_zero, Rat.cast_zero]
    have hx : (0 : ℝ) < (h : ℝ) / l := div_pos hhR hl
    have h1 := Real.one_sub_inv_le_log_of_pos hx
    have hinv : ((h : ℝ) / l)⁻¹ ≤ 2 := by
      rw [inv_div, div_le_iff₀ hhR]
      exact_mod_cast hlh
    linarith
  · have h1 := harmonic_le_one_add_log (h / l)
    have h2 : Real.log ((h / l : ℕ) : ℝ) ≤ Real.log ((h : ℝ) / l) :=
      Real.log_le_log (by exact_mod_cast hpos) Nat.cast_div_le
    linarith

/- English proof (translation)
Use `show padicValInt l n = 0`. Apply `padicValInt.eq_zero_of_not_dvd` to reduce the goal to its premises. Introduce `hd`. Use `Int.le_of_dvd h0 hd` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma label_vl_zero_small {l : ℕ} {n : ℤ} (h0 : 0 < n) (h1 : n < l) : vl l n = 0 := by
  show padicValInt l n = 0
  apply padicValInt.eq_zero_of_not_dvd
  intro hd
  have := Int.le_of_dvd h0 hd
  linarith

/- English proof (translation)
Establish `hlpos : 0 < l` using `hl.pos`. Establish `hlZ : (0 : ℤ) < l` using `by exact_mod_cast hlpos`. Establish `hlR : (0 : ℝ) < l` using `by exact_mod_cast hlpos`. Establish `hhZ : (h : ℤ) < (l : ℤ) ^ 2` using `by exact_mod_cast hh`. Establish `hm0 : (0 : ℝ) ≤ min (k : ℝ) (t : ℝ)` using `le_min (Nat.cast_nonneg _) (Nat.cast_nonneg _)`.

Take `⟨hd01, hd0dvd⟩` from `leastCongruentPos_mem hlpos (xm - mB) (by omega)`. Take `⟨d0, hd0⟩ : ∃ d0, d0 = Formalism.CohomologicalDescent.d0 l (xm - mB)` from `⟨_, rfl⟩`. Rewrite `hd01`, `hd0dvd`, the goal using `[← hd0]`. Take `⟨A, hA⟩ : ∃ A : ℝ, A = if ((d0 : ℕ) : ℤ) < xm - mB then min (min (k : ℝ) (t : ℝ)) (i / (d0 : ℝ)) else 0` from `⟨_, rfl⟩`. Rewrite using `[← hA]`.

Establish `hA0 : 0 ≤ A`. Rewrite using `[hA]`. Use `split_ifs`. Conclude with `le_min hm0 (div_nonneg hi (Nat.cast_nonneg _))`. Conclude with `le_refl 0`.

Take `⟨F, hF⟩ : ∃ F : ℕ → ℝ, ∀ j, F j = if j = 0 then A else i / ((l : ℝ) * (j : ℝ))` from `⟨_, fun _ => rfl⟩`. Establish `hF0 : ∀ j, 0 ≤ F j`. Introduce `j`. Rewrite using `[hF]`. Use `split_ifs`.

Conclude with `hA0`. Conclude with `div_nonneg hi (mul_nonneg hlR.le (Nat.cast_nonneg _))`. Establish `hc : ∀ ct ∈ Finset.Ioo mB xm, 0 ≤ min (min (k : ℝ) (t : ℝ)) (i / ((xm - ct : ℤ) : ℝ))`. Introduce `ct hct`. Rewrite `hct` using `[Finset.mem_Ioo]`.

Establish `hpos : (0 : ℝ) < ((xm - ct : ℤ) : ℝ)` using `by exact_mod_cast (by omega : (0 : ℤ) < xm - ct)`. Conclude with `le_min hm0 (div_nonneg hi hpos.le)`. Establish `hr : ∀ ct ∈ Finset.Ioo mB xm, 0 < ct - mB ∧ ct - mB < (l : ℤ) ^ 2`. Introduce `ct hct`. Rewrite `hct` using `[Finset.mem_Ioo]`.

Conclude with `⟨by omega, by linarith [hct.2]⟩`. Establish `step1` using `label_sum_le_filter hl (Finset.Ioo mB xm) mB (fun ct => min (min (k : ℝ) (t : ℝ)) (i / ((xm - ct : ℤ) : ℝ))) hc hr`. Use `le_trans step1 ?_` and prove the remaining obligations. Take `⟨S, hS⟩ : ∃ S, S = (Finset.Ioo mB xm).filter (fun x => (l : ℤ) ∣ x - mB)` from `⟨_, rfl⟩`. Rewrite using `[← hS]`.

Establish `key : ∀ ct ∈ S, (l : ℤ) ∣ xm - ct - d0 ∧ (d0 : ℤ) ≤ xm - ct ∧ mB < ct ∧ ct < xm`. Introduce `ct hct`. Rewrite `hct` using `[hS, Finset.mem_filter, Finset.mem_Ioo]`. Take `⟨⟨h1, h2⟩, h3⟩` from `hct`. Use `⟨?_, ?_, h1, h2⟩` and prove the remaining obligations.

Establish `e : xm - ct - (d0 : ℤ) = (xm - mB - d0) - (ct - mB)` using `by ring`. Rewrite using `[e]`. Conclude with `dvd_sub hd0dvd h3`. Establish `hnn : ((xm - ct).toNat : ℤ) = xm - ct` using `Int.toNat_of_nonneg (by omega)`. Establish `e : xm - mB - (((xm - ct).toNat : ℕ) : ℤ) = ct - mB`.

Rewrite using `[hnn]`. Expand and normalize the polynomial expressions, which then agree. Establish `hle` using `leastCongruentPos_le (l := l) (xm - mB) (xm - ct).toNat (by omega) (by rw [e]; exact h3)`. Rewrite `hle` using `[← hd0]`. Establish `hle' : (d0 : ℤ) ≤ ((xm - ct).toNat : ℤ)` using `by exact_mod_cast hle`.

Rewrite `hle'` using `[hnn]`. Conclude with `hle'`. Take `⟨g, hg⟩ : ∃ g : ℤ → ℕ, ∀ ct, g ct = ((xm - ct - d0) / (l : ℤ)).toNat` from `⟨_, fun _ => rfl⟩`. Establish `hgZ : ∀ ct ∈ S, (l : ℤ) * (g ct : ℤ) = xm - ct - d0`. Introduce `ct hct`.

Take `⟨hdv, hle, -, -⟩` from `key ct hct`. Rewrite using `[hg, Int.toNat_of_nonneg (Int.ediv_nonneg (by omega) hlZ.le)]`. Conclude with `Int.mul_ediv_cancel' hdv`. Establish `hterm : ∀ ct ∈ S, min (min (k : ℝ) (t : ℝ)) (i / ((xm - ct : ℤ) : ℝ)) ≤ F (g ct)`. Introduce `ct hct`.

Take `⟨-, hle, h1, h2⟩` from `key ct hct`. Establish `he` using `hgZ ct hct`. Rewrite using `[hF]`. Use `split_ifs with h0`. Rewrite `he` using `[h0]`.

Establish `hd : xm - ct = (d0 : ℤ)` using `by push_cast at he; linarith`. Establish `hlt : ((d0 : ℕ) : ℤ) < xm - mB` using `by omega`. Rewrite using `[hA, if_pos hlt]`. Establish `hdR : ((xm - ct : ℤ) : ℝ) = (d0 : ℝ)` using `by rw [hd]; norm_cast`. Rewrite using `[hdR]`.

Establish `hd0nn : (0 : ℤ) ≤ (d0 : ℤ)` using `by positivity`. Establish `hle' : (l : ℤ) * (g ct : ℤ) ≤ xm - ct` using `by linarith`. Establish `hprodR : (l : ℝ) * (g ct : ℝ) ≤ ((xm - ct : ℤ) : ℝ)` using `by exact_mod_cast hle'`. Establish `hgR : (0 : ℝ) < (g ct : ℝ)` using `by exact_mod_cast Nat.pos_of_ne_zero h0`. Establish `hprodpos : (0 : ℝ) < (l : ℝ) * (g ct : ℝ)` using `mul_pos hlR hgR`.

Conclude with `(min_le_right _ _).trans (div_le_div_of_nonneg_left hi hprodpos hprodR)`. Establish `hmaps : ∀ ct ∈ S, g ct ∈ Finset.range (h / l + 1)`. Introduce `ct hct`. Take `⟨-, hle, h1, h2⟩` from `key ct hct`. Establish `he` using `hgZ ct hct`.

Rewrite using `[Finset.mem_range, Nat.lt_add_one_iff, Nat.le_div_iff_mul_le hlpos]`. Establish `hz : ((g ct * l : ℕ) : ℤ) ≤ (h : ℤ)`. Use `push_cast`. Establish `hd0nn : (0 : ℤ) ≤ (d0 : ℤ)` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion.

Conclude with `hz` after adjusting the coercions. Establish `hinj : ∀ a ∈ S, ∀ b ∈ S, g a = g b → a = b`. Introduce `a ha b hb hab`. Establish `h1` using `hgZ a ha`. Establish `h2` using `hgZ b hb`.

Rewrite `h1` using `[hab]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hH : ∑ j ∈ Finset.range (h / l), F (j + 1) = (i / l) * ((harmonic (h / l) : ℚ) : ℝ)`. Simplify using `only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[hF, if_neg (by omega)]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Establish `hlog` using `label_harm_le hlpos hlh`. Establish `hil : 0 ≤ i / (l : ℝ)` using `div_nonneg hi hlR.le`.

Establish `hmul` using `mul_le_mul_of_nonneg_left hlog hil`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.sum_image]`. Introduce `a ha b hb hab`. Conclude with `hinj a ha b hb hab`.

Use `_ ≤ ∑ j ∈ Finset.range (h / l + 1), F j := Finset.sum_le_sum_of_subset_of_nonneg (Finset.image_subset_iff.mpr hmaps) (fun j _ _ => hF0 j)`. Use `_ = ∑ j ∈ Finset.range (h / l), F (j + 1) + F 0 := Finset.sum_range_succ' _ _`. Use `_ = (i / l) * ((harmonic (h / l) : ℚ) : ℝ) + A := by rw [hH, hF 0, if_pos rfl]`. Use `_ ≤ A + (i / (l : ℝ)) * (1 + Real.log ((h : ℝ) / (l : ℝ))) := by linarith`.
-/
lemma label_second {l k t h : ℕ} {i : ℝ} {xm mB : ℤ} (hl : l.Prime) (hi : 0 ≤ i)
    (hmB : 0 ≤ mB) (hmx : mB < xm) (hxh : xm ≤ (h : ℤ)) (hh : h < l ^ 2) (hlh : l ≤ 2 * h) :
    ∑ ct ∈ Finset.Ioo mB xm,
      min (min (k : ℝ) (t : ℝ)) (i / ((xm - ct : ℤ) : ℝ)) * (vl l (ct - mB) : ℝ)
    ≤ (if ((d0 l (xm - mB) : ℕ) : ℤ) < xm - mB then
        min (min (k : ℝ) (t : ℝ)) (i / (d0 l (xm - mB) : ℝ)) else 0) +
      (i / (l : ℝ)) * (1 + Real.log ((h : ℝ) / (l : ℝ))) := by
  have hlpos : 0 < l := hl.pos
  have hlZ : (0 : ℤ) < l := by exact_mod_cast hlpos
  have hlR : (0 : ℝ) < l := by exact_mod_cast hlpos
  have hhZ : (h : ℤ) < (l : ℤ) ^ 2 := by exact_mod_cast hh
  have hm0 : (0 : ℝ) ≤ min (k : ℝ) (t : ℝ) := le_min (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  obtain ⟨hd01, hd0dvd⟩ := leastCongruentPos_mem hlpos (xm - mB) (by omega)
  obtain ⟨d0, hd0⟩ : ∃ d0, d0 = Formalism.CohomologicalDescent.d0 l (xm - mB) := ⟨_, rfl⟩
  rw [← hd0] at hd01 hd0dvd ⊢
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = if ((d0 : ℕ) : ℤ) < xm - mB then
      min (min (k : ℝ) (t : ℝ)) (i / (d0 : ℝ)) else 0 := ⟨_, rfl⟩
  rw [← hA]
  have hA0 : 0 ≤ A := by
    rw [hA]
    split_ifs
    · exact le_min hm0 (div_nonneg hi (Nat.cast_nonneg _))
    · exact le_refl 0
  obtain ⟨F, hF⟩ : ∃ F : ℕ → ℝ, ∀ j, F j = if j = 0 then A else i / ((l : ℝ) * (j : ℝ)) :=
    ⟨_, fun _ => rfl⟩
  have hF0 : ∀ j, 0 ≤ F j := by
    intro j
    rw [hF]
    split_ifs
    · exact hA0
    · exact div_nonneg hi (mul_nonneg hlR.le (Nat.cast_nonneg _))
  have hc : ∀ ct ∈ Finset.Ioo mB xm, 0 ≤ min (min (k : ℝ) (t : ℝ)) (i / ((xm - ct : ℤ) : ℝ)) := by
    intro ct hct
    rw [Finset.mem_Ioo] at hct
    have hpos : (0 : ℝ) < ((xm - ct : ℤ) : ℝ) := by exact_mod_cast (by omega : (0 : ℤ) < xm - ct)
    exact le_min hm0 (div_nonneg hi hpos.le)
  have hr : ∀ ct ∈ Finset.Ioo mB xm, 0 < ct - mB ∧ ct - mB < (l : ℤ) ^ 2 := by
    intro ct hct
    rw [Finset.mem_Ioo] at hct
    exact ⟨by omega, by linarith [hct.2]⟩
  have step1 := label_sum_le_filter hl (Finset.Ioo mB xm) mB
    (fun ct => min (min (k : ℝ) (t : ℝ)) (i / ((xm - ct : ℤ) : ℝ))) hc hr
  refine le_trans step1 ?_
  obtain ⟨S, hS⟩ : ∃ S, S = (Finset.Ioo mB xm).filter (fun x => (l : ℤ) ∣ x - mB) := ⟨_, rfl⟩
  rw [← hS]
  have key : ∀ ct ∈ S, (l : ℤ) ∣ xm - ct - d0 ∧ (d0 : ℤ) ≤ xm - ct ∧ mB < ct ∧ ct < xm := by
    intro ct hct
    rw [hS, Finset.mem_filter, Finset.mem_Ioo] at hct
    obtain ⟨⟨h1, h2⟩, h3⟩ := hct
    refine ⟨?_, ?_, h1, h2⟩
    · have e : xm - ct - (d0 : ℤ) = (xm - mB - d0) - (ct - mB) := by ring
      rw [e]
      exact dvd_sub hd0dvd h3
    · have hnn : ((xm - ct).toNat : ℤ) = xm - ct := Int.toNat_of_nonneg (by omega)
      have e : xm - mB - (((xm - ct).toNat : ℕ) : ℤ) = ct - mB := by
        rw [hnn]
        ring
      have hle := leastCongruentPos_le (l := l) (xm - mB) (xm - ct).toNat (by omega)
        (by rw [e]; exact h3)
      rw [← hd0] at hle
      have hle' : (d0 : ℤ) ≤ ((xm - ct).toNat : ℤ) := by exact_mod_cast hle
      rw [hnn] at hle'
      exact hle'
  obtain ⟨g, hg⟩ : ∃ g : ℤ → ℕ, ∀ ct, g ct = ((xm - ct - d0) / (l : ℤ)).toNat :=
    ⟨_, fun _ => rfl⟩
  have hgZ : ∀ ct ∈ S, (l : ℤ) * (g ct : ℤ) = xm - ct - d0 := by
    intro ct hct
    obtain ⟨hdv, hle, -, -⟩ := key ct hct
    rw [hg, Int.toNat_of_nonneg (Int.ediv_nonneg (by omega) hlZ.le)]
    exact Int.mul_ediv_cancel' hdv
  have hterm : ∀ ct ∈ S, min (min (k : ℝ) (t : ℝ)) (i / ((xm - ct : ℤ) : ℝ)) ≤ F (g ct) := by
    intro ct hct
    obtain ⟨-, hle, h1, h2⟩ := key ct hct
    have he := hgZ ct hct
    rw [hF]
    split_ifs with h0
    · rw [h0] at he
      have hd : xm - ct = (d0 : ℤ) := by push_cast at he; linarith
      have hlt : ((d0 : ℕ) : ℤ) < xm - mB := by omega
      rw [hA, if_pos hlt]
      have hdR : ((xm - ct : ℤ) : ℝ) = (d0 : ℝ) := by rw [hd]; norm_cast
      rw [hdR]
    · have hd0nn : (0 : ℤ) ≤ (d0 : ℤ) := by positivity
      have hle' : (l : ℤ) * (g ct : ℤ) ≤ xm - ct := by linarith
      have hprodR : (l : ℝ) * (g ct : ℝ) ≤ ((xm - ct : ℤ) : ℝ) := by exact_mod_cast hle'
      have hgR : (0 : ℝ) < (g ct : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero h0
      have hprodpos : (0 : ℝ) < (l : ℝ) * (g ct : ℝ) := mul_pos hlR hgR
      exact (min_le_right _ _).trans (div_le_div_of_nonneg_left hi hprodpos hprodR)
  have hmaps : ∀ ct ∈ S, g ct ∈ Finset.range (h / l + 1) := by
    intro ct hct
    obtain ⟨-, hle, h1, h2⟩ := key ct hct
    have he := hgZ ct hct
    rw [Finset.mem_range, Nat.lt_add_one_iff, Nat.le_div_iff_mul_le hlpos]
    have hz : ((g ct * l : ℕ) : ℤ) ≤ (h : ℤ) := by
      push_cast
      have hd0nn : (0 : ℤ) ≤ (d0 : ℤ) := by positivity
      linarith
    exact_mod_cast hz
  have hinj : ∀ a ∈ S, ∀ b ∈ S, g a = g b → a = b := by
    intro a ha b hb hab
    have h1 := hgZ a ha
    have h2 := hgZ b hb
    rw [hab] at h1
    linarith
  have hH : ∑ j ∈ Finset.range (h / l), F (j + 1) = (i / l) * ((harmonic (h / l) : ℚ) : ℝ) := by
    simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hF, if_neg (by omega)]
    push_cast
    field_simp
  have hlog := label_harm_le hlpos hlh
  have hil : 0 ≤ i / (l : ℝ) := div_nonneg hi hlR.le
  have hmul := mul_le_mul_of_nonneg_left hlog hil
  calc ∑ x ∈ S, min (min (k : ℝ) (t : ℝ)) (i / ((xm - x : ℤ) : ℝ))
      ≤ ∑ x ∈ S, F (g x) := Finset.sum_le_sum hterm
    _ = ∑ j ∈ S.image g, F j := by
        rw [Finset.sum_image]
        intro a ha b hb hab
        exact hinj a ha b hb hab
    _ ≤ ∑ j ∈ Finset.range (h / l + 1), F j :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.image_subset_iff.mpr hmaps)
          (fun j _ _ => hF0 j)
    _ = ∑ j ∈ Finset.range (h / l), F (j + 1) + F 0 := Finset.sum_range_succ' _ _
    _ = (i / l) * ((harmonic (h / l) : ℚ) : ℝ) + A := by rw [hH, hF 0, if_pos rfl]
    _ ≤ A + (i / (l : ℝ)) * (1 + Real.log ((h : ℝ) / (l : ℝ))) := by linarith

/- English proof (translation)
Introduce `l k t h i xm xp mB hl hi hmB hmx hxx hxh hh hlh`. Unfold `labelLHS labelSumBound`. Establish `hlpos : 0 < l` using `hl.pos`. Establish `hhZ : (h : ℤ) < (l : ℤ) ^ 2` using `by exact_mod_cast hh`. Establish `hk : (0 : ℝ) ≤ k` using `Nat.cast_nonneg _`.

Establish `hA` using `label_sum_le_filter hl (Finset.Icc xm xp) mB (fun _ => (k : ℝ)) (fun _ _ => hk) (fun x hx => by`. Rewrite `hx` using `[Finset.mem_Icc]`. Conclude with `⟨by omega, by linarith [hx.2]⟩)`. Rewrite `hA` using `[Finset.sum_const, nsmul_eq_mul]`. Establish `hB : ((((Finset.Icc xm xp).filter (fun x => (l : ℤ) ∣ x - mB)).card : ℕ) : ℝ) ≤ ((xp - xm : ℤ) : ℝ) / l + IlInd l xm xp mB`.

Unfold `IlInd`. Use `split_ifs with hex`. Conclude with `label_card_le hlpos xm xp mB hxx`. Establish `hempty : (Finset.Icc xm xp).filter (fun x => (l : ℤ) ∣ x - mB) = ∅`. Rewrite using `[Finset.filter_eq_empty_iff]`.

Introduce `x hx hd`. Rewrite `hx` using `[Finset.mem_Icc]`. Conclude with `hex ⟨x, hx.1, hx.2, hd⟩`. Rewrite using `[hempty, Finset.card_empty, Nat.cast_zero, add_zero]`. Apply `div_nonneg` to reduce the goal to its premises.

Conclude with `(by omega : (0 : ℤ) ≤ xp - xm)` after adjusting the coercions. Conclude with `Nat.cast_nonneg _`. Establish `hC` using `label_second (k := k) (t := t) hl hi hmB hmx (by omega) hh hlh`. Establish `hkB` using `mul_le_mul_of_nonneg_left hB hk`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem labelSumLe_holds : LabelSum := by
  intro l k t h i xm xp mB hl hi hmB hmx hxx hxh hh hlh
  unfold labelLHS labelSumBound
  have hlpos : 0 < l := hl.pos
  have hhZ : (h : ℤ) < (l : ℤ) ^ 2 := by exact_mod_cast hh
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hA := label_sum_le_filter hl (Finset.Icc xm xp) mB (fun _ => (k : ℝ))
    (fun _ _ => hk) (fun x hx => by
      rw [Finset.mem_Icc] at hx
      exact ⟨by omega, by linarith [hx.2]⟩)
  rw [Finset.sum_const, nsmul_eq_mul] at hA
  have hB : ((((Finset.Icc xm xp).filter (fun x => (l : ℤ) ∣ x - mB)).card : ℕ) : ℝ) ≤
      ((xp - xm : ℤ) : ℝ) / l + IlInd l xm xp mB := by
    unfold IlInd
    split_ifs with hex
    · exact label_card_le hlpos xm xp mB hxx
    · have hempty : (Finset.Icc xm xp).filter (fun x => (l : ℤ) ∣ x - mB) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro x hx hd
        rw [Finset.mem_Icc] at hx
        exact hex ⟨x, hx.1, hx.2, hd⟩
      rw [hempty, Finset.card_empty, Nat.cast_zero, add_zero]
      apply div_nonneg
      · exact_mod_cast (by omega : (0 : ℤ) ≤ xp - xm)
      · exact Nat.cast_nonneg _
  have hC := label_second (k := k) (t := t) hl hi hmB hmx (by omega) hh hlh
  have hkB := mul_le_mul_of_nonneg_left hB hk
  linarith

end Formalism.CohomologicalDescent
