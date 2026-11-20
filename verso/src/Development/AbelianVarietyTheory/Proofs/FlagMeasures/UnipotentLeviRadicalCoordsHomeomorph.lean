import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicLeviEmbeddingHomomorphismProperties
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicStabilizerRadicalStructure
import Formalism.FormalDegreeBessel.FinalG

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.NCoord

variable {k r : ℕ}

/- English proof (translation)
Simplify using `[eI]`.
-/
private theorem eI_val_flag_measures (a : Fin r) : (eI k r a).val = a.val := by
  simp [eI]

/- English proof (translation)
Simplify using `[wI]`.
-/
private theorem wI_val_flag_measures (j : Fin (k + 1)) : (wI k r j).val = r + j.val := by
  simp [wI]

/- English proof (translation)
Simplify using `[esI]`.
-/
private theorem esI_val_flag_measures (a : Fin r) : (esI k r a).val = 2 * r + k - a.val := by
  simp [esI]

/- English proof (translation)
Take `⟨n, hn⟩` from `i`. Distinguish the cases in `h1 : n < r`. Use `left`. Conclude with `⟨⟨n, h1⟩, Fin.ext (by rw [eI_val_flag_measures])⟩`. Use `right`.

Distinguish the cases in `h2 : n ≤ r + k`. Use `left`. Conclude with `⟨⟨n - r, by omega⟩, Fin.ext (by rw [wI_val_flag_measures]; simp only; omega)⟩`. Use `right`. Conclude with `⟨⟨2 * r + k - n, by omega⟩, Fin.ext (by rw [esI_val_flag_measures]; simp only; omega)⟩`.
-/
theorem idx_cases (i : Fin (2 * r + k + 1)) :
    (∃ a, i = eI k r a) ∨ (∃ j, i = wI k r j) ∨ ∃ a, i = esI k r a := by
  obtain ⟨n, hn⟩ := i
  by_cases h1 : n < r
  · left
    exact ⟨⟨n, h1⟩, Fin.ext (by rw [eI_val_flag_measures])⟩
  · right
    by_cases h2 : n ≤ r + k
    · left
      exact ⟨⟨n - r, by omega⟩, Fin.ext (by rw [wI_val_flag_measures]; simp only; omega)⟩
    · right
      exact ⟨⟨2 * r + k - n, by omega⟩, Fin.ext (by rw [esI_val_flag_measures]; simp only; omega)⟩

/- English proof (translation)
Set `e : Fin r ⊕ Fin (k + 1) ⊕ Fin r → Fin (2 * r + k + 1)` to `Sum.elim (eI k r) (Sum.elim (wI k r) (esI k r))`. Establish `hbij : Function.Bijective e`. Prove the components needed by the constructor for the conclusion. Apply the tactic sequence `rintro (a | a | a) (b | b | b) h <;>`. Apply the tactic sequence `simp only [e, Sum.elim_inl, Sum.elim_inr, Fin.ext_iff, eI_val_flag_measures, wI_val_flag_measures, esI_val_flag_measures, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq] at h ⊢ <;>`.

Use the proof step `(have := a.2; have := b.2; omega)`. Introduce `i`. Break down `idx_cases i with ⟨a, rfl⟩ | ⟨a, rfl⟩ | ⟨a, rfl⟩` into its components or cases. Conclude with `⟨Sum.inl a, rfl⟩`. Conclude with `⟨Sum.inr (Sum.inl a), rfl⟩`.

Conclude with `⟨Sum.inr (Sum.inr a), rfl⟩`. Rewrite using `[← hbij.sum_comp f, Fintype.sum_sum_type, Fintype.sum_sum_type, add_assoc]`. Both sides reduce to the same expression.
-/
theorem sum_three (f : Fin (2 * r + k + 1) → ℂ) :
    ∑ i, f i = ∑ a, f (eI k r a) + ∑ j, f (wI k r j) + ∑ a, f (esI k r a) := by
  let e : Fin r ⊕ Fin (k + 1) ⊕ Fin r → Fin (2 * r + k + 1) :=
    Sum.elim (eI k r) (Sum.elim (wI k r) (esI k r))
  have hbij : Function.Bijective e := by
    constructor
    · rintro (a | a | a) (b | b | b) h <;>
        simp only [e, Sum.elim_inl, Sum.elim_inr, Fin.ext_iff, eI_val_flag_measures, wI_val_flag_measures, esI_val_flag_measures,
          Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq] at h ⊢ <;>
        (have := a.2; have := b.2; omega)
    · intro i
      rcases idx_cases i with ⟨a, rfl⟩ | ⟨a, rfl⟩ | ⟨a, rfl⟩
      · exact ⟨Sum.inl a, rfl⟩
      · exact ⟨Sum.inr (Sum.inl a), rfl⟩
      · exact ⟨Sum.inr (Sum.inr a), rfl⟩
  rw [← hbij.sum_comp f, Fintype.sum_sum_type, Fintype.sum_sum_type, add_assoc]
  rfl

/- English proof (translation)
Simplify using `only [mulVec, dotProduct]`. Rewrite using `[sum_three]`. Simplify using `[Rad.H_ee, Rad.H_ew, Rad.H_es]`.
-/
theorem H_e (v : Fin (2 * r + k + 1) → ℂ) (a : Fin r) : (Hpk k r *ᵥ v) (eI k r a) = v (esI k r a) := by
  simp only [mulVec, dotProduct]
  rw [sum_three]
  simp [Rad.H_ee, Rad.H_ew, Rad.H_es]

/- English proof (translation)
Simplify using `only [mulVec, dotProduct]`. Rewrite using `[sum_three]`. Simplify using `[Rad.H_se, Rad.H_sw, Rad.H_ss]`.
-/
theorem H_es (v : Fin (2 * r + k + 1) → ℂ) (a : Fin r) : (Hpk k r *ᵥ v) (esI k r a) = v (eI k r a) := by
  simp only [mulVec, dotProduct]
  rw [sum_three]
  simp [Rad.H_se, Rad.H_sw, Rad.H_ss]

/- English proof (translation)
Simplify using `only [mulVec, dotProduct]`. Rewrite using `[sum_three]`. Simplify using `[Rad.H_we, Rad.H_ww, Rad.H_ws, Hb, Rad.sg, Matrix.diagonal_apply, ite_mul]`.
-/
theorem H_w (v : Fin (2 * r + k + 1) → ℂ) (j : Fin (k + 1)) :
    (Hpk k r *ᵥ v) (wI k r j) = (Hb k *ᵥ fun l => v (wI k r l)) j := by
  simp only [mulVec, dotProduct]
  rw [sum_three]
  simp [Rad.H_we, Rad.H_ww, Rad.H_ws, Hb, Rad.sg, Matrix.diagonal_apply, ite_mul]

/- English proof (translation)
Simplify using `only [herm, dotProduct, Pi.star_apply]`. Rewrite using `[sum_three]`. Simplify using `only [H_e, H_w, H_es]`.
-/
theorem herm_three (v w : Fin (2 * r + k + 1) → ℂ) : herm (Hpk k r) v w =
    ∑ a, star (w (eI k r a)) * v (esI k r a) + herm (Hb k) (fun l => v (wI k r l)) (fun l => w (wI k r l)) +
      ∑ a, star (w (esI k r a)) * v (eI k r a) := by
  simp only [herm, dotProduct, Pi.star_apply]
  rw [sum_three]
  simp only [H_e, H_w, H_es]

/- English proof (translation)
Establish `h : gᴴ * Hpk k r * g = Hpk k r` using `hg`. Use `conv_rhs => rw [← h]`. Simplify using `only [herm, dotProduct, mulVec, Matrix.mul_apply, conjTranspose_apply, Pi.star_apply, Finset.mul_sum, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem herm_col {g : Mat k r} (hg : g ∈ GG k r) (i j : Fin (2 * r + k + 1)) :
    herm (Hpk k r) (fun l => g l j) (fun l => g l i) = Hpk k r i j := by
  have h : gᴴ * Hpk k r * g = Hpk k r := hg
  conv_rhs => rw [← h]
  simp only [herm, dotProduct, mulVec, Matrix.mul_apply, conjTranspose_apply, Pi.star_apply,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

/- English proof (translation)
Simplify using `only [bvec, mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero]`. Simplify using the standard rewrite rules.
-/
theorem col_eq (g : Mat k r) (i j : Fin (2 * r + k + 1)) : (g *ᵥ bvec j) i = g i j := by
  simp only [bvec, mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero]
  simp

/- English proof (translation)
Simplify using `only [Rad.herm_Hb, star_sum, star_mul', star_star, Rad.star_sg]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem herm_b_star (v w : Fin (k + 1) → ℂ) : star (herm (Hb k) v w) = herm (Hb k) w v := by
  simp only [Rad.herm_Hb, star_sum, star_mul', star_star, Rad.star_sg]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

def Bof (p : Mat k r) : Fin r → Fin (k + 1) → ℂ := fun b j => p (wI k r j) (esI k r b)

def Sof (p : Mat k r) : Matrix (Fin r) (Fin r) ℂ := fun a b =>
  p (eI k r a) (esI k r b) + herm (Hb k) (Bof p b) (Bof p a) / 2

/- English proof (translation)
Use function extensionality and compare the values at `b j`. Simplify using `only [Bof, Rad.pEl_ws]`.
-/
theorem Bof_pEl (B : Fin r → Fin (k + 1) → ℂ) (S : Matrix (Fin r) (Fin r) ℂ) : Bof (pEl k r B S) = B := by
  funext b j
  simp only [Bof, Rad.pEl_ws]

/- English proof (translation)
Use function extensionality and compare the values at `a b`. Simplify using `only [Sof, Bof_pEl, Rad.pEl_es, sub_add_cancel]`.
-/
theorem Sof_pEl (B : Fin r → Fin (k + 1) → ℂ) (S : Matrix (Fin r) (Fin r) ℂ) : Sof (pEl k r B S) = S := by
  funext a b
  simp only [Sof, Bof_pEl, Rad.pEl_es, sub_add_cancel]

/- English proof (translation)
Simplify using `only [herm, bvec, dotProduct, Pi.star_apply]`. Rewrite using `[Finset.sum_eq_single x]`. Simplify using the standard rewrite rules. Introduce `l _ hl`. Simplify using `[hl]`.

Simplify using the standard rewrite rules.
-/
private theorem herm_Hpk_bvec_eq_mulVec_apply (v : Fin (2 * r + k + 1) → ℂ) (x : Fin (2 * r + k + 1)) :
    herm (Hpk k r) v (bvec x) = (Hpk k r *ᵥ v) x := by
  simp only [herm, bvec, dotProduct, Pi.star_apply]
  rw [Finset.sum_eq_single x]
  · simp
  · intro l _ hl
    simp [hl]
  · simp

/- English proof (translation)
Take `⟨hU, -, hmid⟩` from `hp`. Establish `hU' : p ∈ GG k r` using `hU`. Establish `hcolE : ∀ a, (fun l => p l (eI k r a)) = bvec (eI k r a)`. Introduce `a`. Use function extensionality and compare the values at `l`.

Rewrite using `[he]`. Simplify using `[bvec, Pi.single_apply]`. Establish `hw : ∀ i j : Fin (k + 1), p (wI k r i) (wI k r j) = if i = j then 1 else 0`. Introduce `i j`. Rewrite using `[hmid _ _ (by rw [wI_val_flag_measures]; omega) (by rw [wI_val_flag_measures]; have := j.2; omega) (by rw [wI_val_flag_measures]; omega)]`.

Simplify using `only [Rad.wI_inj]`. Establish `hsw : ∀ (a : Fin r) (j : Fin (k + 1)), p (esI k r a) (wI k r j) = 0`. Introduce `a j`. Rewrite using `[hmid _ _ (by rw [wI_val_flag_measures]; omega) (by rw [wI_val_flag_measures]; have := j.2; omega) (by rw [esI_val_flag_measures]; have := a.2; omega), if_neg (Rad.esI_ne_wI _ _)]`. Establish `hss : ∀ a b : Fin r, p (esI k r a) (esI k r b) = if a = b then 1 else 0`.

Introduce `a b`. Establish `h` using `herm_col hU' (eI k r a) (esI k r b)`. Rewrite `h` using `[hcolE, herm_Hpk_bvec_eq_mulVec_apply, H_e, Rad.H_es]`. Conclude with `h`. Establish `hst01 : ∀ c a : Fin r, star (if c = a then (1 : ℂ) else 0) = if c = a then 1 else 0`.

Apply the tactic sequence `intro c a; split_ifs <;> simp`. Establish `hmidw : ∀ j : Fin (k + 1), (fun l => p (wI k r l) (wI k r j)) = bvec j`. Introduce `j`. Use function extensionality and compare the values at `l`. Rewrite using `[hw]`.

Simplify using `[bvec, Pi.single_apply]`. Establish `hew : ∀ (b : Fin r) (j : Fin (k + 1)), p (eI k r b) (wI k r j) = -(star (Bof p b j) * Rad.sg k j)`. Introduce `b j`. Establish `h` using `herm_col hU' (wI k r j) (esI k r b)`. Rewrite `h` using `[herm_three, Rad.H_ws, hmidw, ← herm_b_star, Rad.herm_bvec]`.

Simplify using `only [hss, hsw, star_zero, zero_mul, Finset.sum_const_zero, add_zero, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h`. Establish `h2` using `congrArg star h`. Simplify using `only [star_add, star_mul', star_star, Rad.star_sg, star_zero] at h2`. Simplify using `only [Bof]`. Take the linear combination `h2`.

Establish `hrel : ∀ a b : Fin r, star (p (eI k r b) (esI k r a)) + herm (Hb k) (Bof p b) (Bof p a) + p (eI k r a) (esI k r b) = 0`. Introduce `a b`. Establish `h` using `herm_col hU' (esI k r a) (esI k r b)`. Rewrite `h` using `[herm_three, Rad.H_ss]`. Simplify using `only [hss, hst01, mul_ite, ite_mul, mul_one, one_mul, mul_zero, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h`.

Conclude with `h`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use extensionality with `a b`. Establish `h` using `hrel a b`. Establish `hs` using `herm_b_star (Bof p a) (Bof p b)`.

Simplify using `only [conjTranspose_apply, Matrix.neg_apply, Sof, star_add, star_div₀, hs]`. Establish `h2 : star (2 : ℂ) = 2` using `by simp`. Rewrite using `[h2]`. Take the linear combination `h`. Use extensionality with `i j`.

Apply the tactic sequence `rcases idx_cases i with ⟨a, rfl⟩ | ⟨a, rfl⟩ | ⟨a, rfl⟩ <;>`. Break down `idx_cases j with ⟨b, rfl⟩ | ⟨b, rfl⟩ | ⟨b, rfl⟩` into its components or cases. Rewrite using `[he, Rad.pEl_ee]`. Simplify using `only [Rad.eI_inj]`. Rewrite using `[hew, Rad.pEl_ew]`.

Rewrite using `[Rad.pEl_es]`. Simplify using `only [Sof]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[he, Rad.pEl_we, if_neg (Rad.wI_ne_eI _ _)]`. Rewrite using `[hw, Rad.pEl_ww]`.

Rewrite using `[Rad.pEl_ws]`. Both sides reduce to the same expression. Rewrite using `[he, Rad.pEl_se, if_neg (Rad.esI_ne_eI _ _)]`. Rewrite using `[hsw, Rad.pEl_sw]`. Rewrite using `[hss, Rad.pEl_ss]`.
-/
theorem rad_eq {p : Mat k r} (hp : p ∈ Nset k r) (he : ∀ a i, p i (eI k r a) = if i = eI k r a then 1 else 0) :
    (Sof p)ᴴ = -Sof p ∧ p = pEl k r (Bof p) (Sof p) := by
  obtain ⟨hU, -, hmid⟩ := hp
  have hU' : p ∈ GG k r := hU
  have hcolE : ∀ a, (fun l => p l (eI k r a)) = bvec (eI k r a) := by
    intro a; funext l; rw [he]; simp [bvec, Pi.single_apply]
  have hw : ∀ i j : Fin (k + 1), p (wI k r i) (wI k r j) = if i = j then 1 else 0 := by
    intro i j
    rw [hmid _ _ (by rw [wI_val_flag_measures]; omega) (by rw [wI_val_flag_measures]; have := j.2; omega) (by rw [wI_val_flag_measures]; omega)]
    simp only [Rad.wI_inj]
  have hsw : ∀ (a : Fin r) (j : Fin (k + 1)), p (esI k r a) (wI k r j) = 0 := by
    intro a j
    rw [hmid _ _ (by rw [wI_val_flag_measures]; omega) (by rw [wI_val_flag_measures]; have := j.2; omega)
      (by rw [esI_val_flag_measures]; have := a.2; omega), if_neg (Rad.esI_ne_wI _ _)]
  have hss : ∀ a b : Fin r, p (esI k r a) (esI k r b) = if a = b then 1 else 0 := by
    intro a b
    have h := herm_col hU' (eI k r a) (esI k r b)
    rw [hcolE, herm_Hpk_bvec_eq_mulVec_apply, H_e, Rad.H_es] at h
    exact h
  have hst01 : ∀ c a : Fin r, star (if c = a then (1 : ℂ) else 0) = if c = a then 1 else 0 := by
    intro c a; split_ifs <;> simp
  have hmidw : ∀ j : Fin (k + 1), (fun l => p (wI k r l) (wI k r j)) = bvec j := by
    intro j; funext l; rw [hw]; simp [bvec, Pi.single_apply]
  have hew : ∀ (b : Fin r) (j : Fin (k + 1)),
      p (eI k r b) (wI k r j) = -(star (Bof p b j) * Rad.sg k j) := by
    intro b j
    have h := herm_col hU' (wI k r j) (esI k r b)
    rw [herm_three, Rad.H_ws, hmidw, ← herm_b_star, Rad.herm_bvec] at h
    simp only [hss, hsw, star_zero, zero_mul, Finset.sum_const_zero, add_zero, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
    have h2 := congrArg star h
    simp only [star_add, star_mul', star_star, Rad.star_sg, star_zero] at h2
    simp only [Bof]
    linear_combination h2
  have hrel : ∀ a b : Fin r, star (p (eI k r b) (esI k r a)) + herm (Hb k) (Bof p b) (Bof p a)
      + p (eI k r a) (esI k r b) = 0 := by
    intro a b
    have h := herm_col hU' (esI k r a) (esI k r b)
    rw [herm_three, Rad.H_ss] at h
    simp only [hss, hst01, mul_ite, ite_mul, mul_one, one_mul, mul_zero, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
    exact h
  refine ⟨?_, ?_⟩
  · ext a b
    have h := hrel a b
    have hs := herm_b_star (Bof p a) (Bof p b)
    simp only [conjTranspose_apply, Matrix.neg_apply, Sof, star_add, star_div₀, hs]
    have h2 : star (2 : ℂ) = 2 := by simp
    rw [h2]
    linear_combination h
  · ext i j
    rcases idx_cases i with ⟨a, rfl⟩ | ⟨a, rfl⟩ | ⟨a, rfl⟩ <;>
    rcases idx_cases j with ⟨b, rfl⟩ | ⟨b, rfl⟩ | ⟨b, rfl⟩
    · rw [he, Rad.pEl_ee]; simp only [Rad.eI_inj]
    · rw [hew, Rad.pEl_ew]
    · rw [Rad.pEl_es]; simp only [Sof]; ring
    · rw [he, Rad.pEl_we, if_neg (Rad.wI_ne_eI _ _)]
    · rw [hw, Rad.pEl_ww]
    · rw [Rad.pEl_ws]; rfl
    · rw [he, Rad.pEl_se, if_neg (Rad.esI_ne_eI _ _)]
    · rw [hsw, Rad.pEl_sw]
    · rw [hss, Rad.pEl_ss]

def xOf (n : Mat k r) : UT r → ℂ := fun p => n (eI k r p.1.1) (eI k r p.1.2)

def qOf (p : Mat k r) : PPar k r := (Bof p, fun x => Sof p x.1.1 x.1.2, fun a => (Sof p a a).im)

def cOf (n : Mat k r) : (UT r → ℂ) × PPar k r := (xOf n, qOf (uEmb k r (upper (xOf n))⁻¹ * n))

/- English proof (translation)
Take `⟨B, s, t⟩` from `q`. Use `Prod.ext (Bof_pEl B _) (Prod.ext ?_ ?_)` and prove the remaining obligations. Use function extensionality and compare the values at `x show Sof (pEl k r B (skewM s t)) x.1.1 x.1.2 = s x`. Rewrite using `[Sof_pEl]`. Simplify using `only [skewM, dif_pos x.2]`.

Use function extensionality and compare the values at `a show (Sof (pEl k r B (skewM s t)) a a).im = t a`. Rewrite using `[Sof_pEl]`. Simplify using `[skewM]`.
-/
theorem qOf_pOf (q : PPar k r) : qOf (pOf k r q) = q := by
  obtain ⟨B, s, t⟩ := q
  refine Prod.ext (Bof_pEl B _) (Prod.ext ?_ ?_)
  · funext x
    show Sof (pEl k r B (skewM s t)) x.1.1 x.1.2 = s x
    rw [Sof_pEl]
    simp only [skewM, dif_pos x.2]
  · funext a
    show (Sof (pEl k r B (skewM s t)) a a).im = t a
    rw [Sof_pEl]
    simp [skewM]

/- English proof (translation)
Establish `h : (eI k r a).val < r ∧ (eI k r b).val < r`. Rewrite using `[eI_val_flag_measures, eI_val_flag_measures]`. Conclude with `⟨a.2, b.2⟩`. Simplify using `only [uEmb, dif_pos h]`. Apply the tactic sequence `all_goals rfl`.
-/
theorem uEmb_col (u : Matrix (Fin r) (Fin r) ℂ) (a b : Fin r) : uEmb k r u (eI k r a) (eI k r b) = u a b := by
  have h : (eI k r a).val < r ∧ (eI k r b).val < r := by
    rw [eI_val_flag_measures, eI_val_flag_measures]; exact ⟨a.2, b.2⟩
  simp only [uEmb, dif_pos h]
  all_goals rfl

/- English proof (translation)
Introduce `a b hab`. Establish `hab' : b < a` using `hab`. Simplify using `only [upper, dif_neg (not_lt.mpr hab'.le), if_neg (ne_of_gt hab')]`.
-/
private theorem upper_blockTriangular (x : UT r → ℂ) : (upper x).BlockTriangular id := by
  intro a b hab
  have hab' : b < a := hab
  simp only [upper, dif_neg (not_lt.mpr hab'.le), if_neg (ne_of_gt hab')]

/- English proof (translation)
Rewrite using `[Matrix.det_of_isUpperTriangular (upper_blockTriangular x)]`. Use `Finset.prod_eq_one fun a _ => ?_` and prove the remaining obligations. Simplify using `[upper]`.
-/
private theorem det_upper_eq_one (x : UT r → ℂ) : (upper x).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular (upper_blockTriangular x)]
  refine Finset.prod_eq_one fun a _ => ?_
  simp [upper]

/- English proof (translation)
Establish `hU : IsUnit (upper x).det` using `by rw [det_upper_eq_one]; exact isUnit_one`. Set `_` to `(upper x).invertibleOfIsUnitDet hU`. Establish `ht` using `Matrix.blockTriangular_inv_of_blockTriangular (upper_blockTriangular x)`. Establish `hd : ∀ a, (upper x)⁻¹ a a = 1`. Introduce `a`.

Establish `h` using `congrFun (congrFun (Matrix.nonsing_inv_mul (upper x) hU) a) a`. Rewrite `h` using `[Matrix.mul_apply, Finset.sum_eq_single a]`. Establish `hdiag : upper x a a = 1` using `by simp [upper]`. Rewrite `h` using `[hdiag, mul_one, Matrix.one_apply_eq]`. Conclude with `h`.

Introduce `c _ hc`. Break down `lt_or_gt_of_ne hc with hlt | hlt` into its components or cases. Rewrite using `[ht hlt, zero_mul]`. Rewrite using `[upper_blockTriangular x hlt, mul_zero]`. Simplify using the standard rewrite rules.

Use `⟨fun p => (upper x)⁻¹ p.1.1 p.1.2, ?_⟩` and prove the remaining obligations. Use extensionality with `a b`. Use `show (upper x)⁻¹ a b = (if h : a < b then (upper x)⁻¹ a b else if a = b then 1 else 0)`. Use `split_ifs with h1 h2`. Both sides reduce to the same expression.

Substitute `h2` using the available equality. Conclude with `hd a`. Conclude with `ht (lt_of_le_of_ne (not_lt.mp h1) (Ne.symm h2))`.
-/
private theorem exists_upper_eq_inv_upper (x : UT r → ℂ) : ∃ y : UT r → ℂ, (upper x)⁻¹ = upper y := by
  have hU : IsUnit (upper x).det := by rw [det_upper_eq_one]; exact isUnit_one
  let _ := (upper x).invertibleOfIsUnitDet hU
  have ht := Matrix.blockTriangular_inv_of_blockTriangular (upper_blockTriangular x)
  have hd : ∀ a, (upper x)⁻¹ a a = 1 := by
    intro a
    have h := congrFun (congrFun (Matrix.nonsing_inv_mul (upper x) hU) a) a
    rw [Matrix.mul_apply, Finset.sum_eq_single a] at h
    · have hdiag : upper x a a = 1 := by simp [upper]
      rw [hdiag, mul_one, Matrix.one_apply_eq] at h
      exact h
    · intro c _ hc
      rcases lt_or_gt_of_ne hc with hlt | hlt
      · rw [ht hlt, zero_mul]
      · rw [upper_blockTriangular x hlt, mul_zero]
    · simp
  refine ⟨fun p => (upper x)⁻¹ p.1.1 p.1.2, ?_⟩
  ext a b
  show (upper x)⁻¹ a b = (if h : a < b then (upper x)⁻¹ a b else if a = b then 1 else 0)
  split_ifs with h1 h2
  · rfl
  · subst h2; exact hd a
  · exact ht (lt_of_le_of_ne (not_lt.mp h1) (Ne.symm h2))

/- English proof (translation)
Establish `hU : IsUnit (upper x).det` using `by rw [det_upper_eq_one]; exact isUnit_one`. Take `⟨y, hy⟩` from `exists_upper_eq_inv_upper x`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← UEmb.uEmb_mul, Matrix.nonsing_inv_mul _ hU, UEmb.uEmb_one]`. Rewrite using `[← UEmb.uEmb_mul, Matrix.mul_nonsing_inv _ hU, UEmb.uEmb_one]`.

Rewrite using `[hy]`. Conclude with `UEmb.upper_mem y`.
-/
theorem uEmb_inv_mul (x : UT r → ℂ) : uEmb k r (upper x)⁻¹ * uEmb k r (upper x) = 1 ∧
    uEmb k r (upper x) * uEmb k r (upper x)⁻¹ = 1 ∧ uEmb k r (upper x)⁻¹ ∈ Nset k r := by
  have hU : IsUnit (upper x).det := by rw [det_upper_eq_one]; exact isUnit_one
  obtain ⟨y, hy⟩ := exists_upper_eq_inv_upper x
  refine ⟨?_, ?_, ?_⟩
  · rw [← UEmb.uEmb_mul, Matrix.nonsing_inv_mul _ hU, UEmb.uEmb_one]
  · rw [← UEmb.uEmb_mul, Matrix.mul_nonsing_inv _ hU, UEmb.uEmb_one]
  · rw [hy]; exact UEmb.upper_mem y

/- English proof (translation)
Break down `idx_cases c with ⟨a, rfl⟩ | ⟨a, rfl⟩ | ⟨a, rfl⟩` into its components or cases. Simplify using `only [Rad.pEl_ee, Rad.eI_inj]`. Rewrite using `[Rad.pEl_we, if_neg (Rad.wI_ne_eI _ _)]`. Rewrite using `[Rad.pEl_se, if_neg (Rad.esI_ne_eI _ _)]`.
-/
private theorem pEl_apply_eI (B : Fin r → Fin (k + 1) → ℂ) (S : Matrix (Fin r) (Fin r) ℂ) (b : Fin r)
    (c : Fin (2 * r + k + 1)) : pEl k r B S c (eI k r b) = if c = eI k r b then 1 else 0 := by
  rcases idx_cases c with ⟨a, rfl⟩ | ⟨a, rfl⟩ | ⟨a, rfl⟩
  · simp only [Rad.pEl_ee, Rad.eI_inj]
  · rw [Rad.pEl_we, if_neg (Rad.wI_ne_eI _ _)]
  · rw [Rad.pEl_se, if_neg (Rad.esI_ne_eI _ _)]

/- English proof (translation)
Take `⟨s, p⟩` from `q`. Establish `hx : xOf (uEmb k r (upper s) * pOf k r p) = s`. Use function extensionality and compare the values at `x`. Simplify using `only [xOf, pOf, Matrix.mul_apply, pEl_apply_eI, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, uEmb_col]`. Simplify using `only [upper, dif_pos x.2]`.

Simplify using `only [cOf]`. Rewrite using `[hx, ← Matrix.mul_assoc, (uEmb_inv_mul s).1, Matrix.one_mul, qOf_pOf]`.
-/
theorem cOf_coord (q : (UT r → ℂ) × PPar k r) : cOf (uEmb k r (upper q.1) * pOf k r q.2) = q := by
  obtain ⟨s, p⟩ := q
  have hx : xOf (uEmb k r (upper s) * pOf k r p) = s := by
    funext x
    simp only [xOf, pOf, Matrix.mul_apply, pEl_apply_eI, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, uEmb_col]
    simp only [upper, dif_pos x.2]
  simp only [cOf]
  rw [hx, ← Matrix.mul_assoc, (uEmb_inv_mul s).1, Matrix.one_mul, qOf_pOf]

/- English proof (translation)
Establish `hb` using `b.2`. Establish `h1 : ¬ (i.val < r ∧ (eI k r b).val < r)` using `by rw [eI_val_flag_measures]; omega`. Establish `h2 : ¬ (r + k < i.val ∧ r + k < (eI k r b).val)` using `by rw [eI_val_flag_measures]; omega`. Establish `h3 : i ≠ eI k r b` using `by intro h; rw [h, eI_val_flag_measures] at hi; omega`. Simplify using `only [uEmb, dif_neg h1, dif_neg h2, if_neg h3]`.
-/
private theorem uEmb_apply_eI_eq_zero_of_le (u : Matrix (Fin r) (Fin r) ℂ) (b : Fin r) (i : Fin (2 * r + k + 1))
    (hi : r ≤ i.val) : uEmb k r u i (eI k r b) = 0 := by
  have hb := b.2
  have h1 : ¬ (i.val < r ∧ (eI k r b).val < r) := by rw [eI_val_flag_measures]; omega
  have h2 : ¬ (r + k < i.val ∧ r + k < (eI k r b).val) := by rw [eI_val_flag_measures]; omega
  have h3 : i ≠ eI k r b := by intro h; rw [h, eI_val_flag_measures] at hi; omega
  simp only [uEmb, dif_neg h1, dif_neg h2, if_neg h3]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Rewrite using `[col_eq, col_eq]`. Take `⟨-, h1, -⟩` from `hn`. Break down `idx_cases i with ⟨a, rfl⟩ | ⟨a, rfl⟩ | ⟨a, rfl⟩` into its components or cases. Rewrite using `[uEmb_col]`.

Distinguish the cases in `hab : a < b`. Simplify using `only [upper, dif_pos hab, xOf]`. Establish `hba : b.val ≤ a.val` using `Fin.not_lt.mp hab`. Rewrite using `[h1 b (eI k r a) (by rw [eI_val_flag_measures]; exact hba)]`. Simplify using `only [upper, dif_neg hab, Rad.eI_inj]`.

Rewrite using `[h1 b _ (by rw [wI_val_flag_measures]; have := b.2; omega), if_neg (Rad.wI_ne_eI _ _), uEmb_apply_eI_eq_zero_of_le _ _ _ (by rw [wI_val_flag_measures]; omega)]`. Rewrite using `[h1 b _ (by rw [esI_val_flag_measures]; have := b.2; have := a.2; omega), if_neg (Rad.esI_ne_eI _ _), uEmb_apply_eI_eq_zero_of_le _ _ _ (by rw [esI_val_flag_measures]; have := a.2; omega)]`.
-/
theorem col_e {n : Mat k r} (hn : n ∈ Nset k r) (b : Fin r) :
    n *ᵥ bvec (eI k r b) = uEmb k r (upper (xOf n)) *ᵥ bvec (eI k r b) := by
  funext i
  rw [col_eq, col_eq]
  obtain ⟨-, h1, -⟩ := hn
  rcases idx_cases i with ⟨a, rfl⟩ | ⟨a, rfl⟩ | ⟨a, rfl⟩
  · rw [uEmb_col]
    by_cases hab : a < b
    · simp only [upper, dif_pos hab, xOf]
    · have hba : b.val ≤ a.val := Fin.not_lt.mp hab
      rw [h1 b (eI k r a) (by rw [eI_val_flag_measures]; exact hba)]
      simp only [upper, dif_neg hab, Rad.eI_inj]
  · rw [h1 b _ (by rw [wI_val_flag_measures]; have := b.2; omega), if_neg (Rad.wI_ne_eI _ _),
      uEmb_apply_eI_eq_zero_of_le _ _ _ (by rw [wI_val_flag_measures]; omega)]
  · rw [h1 b _ (by rw [esI_val_flag_measures]; have := b.2; have := a.2; omega), if_neg (Rad.esI_ne_eI _ _),
      uEmb_apply_eI_eq_zero_of_le _ _ _ (by rw [esI_val_flag_measures]; have := a.2; omega)]

/- English proof (translation)
Take `⟨ha0, ha1, ha2⟩` from `ha`. Take `⟨hb0, hb1, hb2⟩` from `hb`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Use `show (a * b)ᴴ * Hpk k r * (a * b) = Hpk k r`. Establish `ha0' : aᴴ * Hpk k r * a = Hpk k r` using `ha0`.

Establish `hb0' : bᴴ * Hpk k r * b = Hpk k r` using `hb0`. Rewrite using `[conjTranspose_mul]`. Combine the equalities or inequalities in the displayed calculation. Introduce `c i hci`. Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single (eI k r c)]`.

Rewrite using `[hb1 c _ (by rw [eI_val_flag_measures]), if_pos rfl, mul_one]`. Conclude with `ha1 c i hci`. Introduce `l _ hl`. Distinguish the cases in `hlc : c.val ≤ l.val`. Rewrite using `[hb1 c l hlc, if_neg hl, mul_zero]`.

Establish `hlr : l.val < r` using `by have := c.2; omega`. Establish `hle : eI k r ⟨l.val, hlr⟩ = l` using `Fin.ext (eI_val_flag_measures _)`. Establish `hx` using `ha1 ⟨l.val, hlr⟩ i (by show l.val ≤ i.val; omega)`. Rewrite `hx` using `[hle]`. Rewrite using `[hx, if_neg (by intro h; rw [h] at hci; omega), zero_mul]`.

Simplify using the standard rewrite rules. Introduce `i j hj1 hj2 hi`. Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single j]`. Rewrite using `[hb2 j j hj1 hj2 hj1, if_pos rfl, mul_one]`. Conclude with `ha2 i j hj1 hj2 hi`.

Introduce `l _ hl`. Distinguish the cases in `hlr : r ≤ l.val`. Rewrite using `[hb2 l j hj1 hj2 hlr, if_neg hl, mul_zero]`. Establish `hlr' : l.val < r` using `by omega`. Establish `hle : eI k r ⟨l.val, hlr'⟩ = l` using `Fin.ext (eI_val_flag_measures _)`.

Establish `hx` using `ha1 ⟨l.val, hlr'⟩ i (by show l.val ≤ i.val; omega)`. Rewrite `hx` using `[hle]`. Rewrite using `[hx, if_neg (by intro h; rw [h] at hi; omega), zero_mul]`. Simplify using the standard rewrite rules.
-/
private theorem mul_mem_Nset {a b : Mat k r} (ha : a ∈ Nset k r) (hb : b ∈ Nset k r) :
    a * b ∈ Nset k r := by
  obtain ⟨ha0, ha1, ha2⟩ := ha
  obtain ⟨hb0, hb1, hb2⟩ := hb
  refine ⟨?_, ?_, ?_⟩
  · show (a * b)ᴴ * Hpk k r * (a * b) = Hpk k r
    have ha0' : aᴴ * Hpk k r * a = Hpk k r := ha0
    have hb0' : bᴴ * Hpk k r * b = Hpk k r := hb0
    rw [conjTranspose_mul]
    calc bᴴ * aᴴ * Hpk k r * (a * b) = bᴴ * (aᴴ * Hpk k r * a) * b := by simp only [Matrix.mul_assoc]
      _ = Hpk k r := by rw [ha0', hb0']
  · intro c i hci
    rw [Matrix.mul_apply, Finset.sum_eq_single (eI k r c)]
    · rw [hb1 c _ (by rw [eI_val_flag_measures]), if_pos rfl, mul_one]
      exact ha1 c i hci
    · intro l _ hl
      by_cases hlc : c.val ≤ l.val
      · rw [hb1 c l hlc, if_neg hl, mul_zero]
      · have hlr : l.val < r := by have := c.2; omega
        have hle : eI k r ⟨l.val, hlr⟩ = l := Fin.ext (eI_val_flag_measures _)
        have hx := ha1 ⟨l.val, hlr⟩ i (by show l.val ≤ i.val; omega)
        rw [hle] at hx
        rw [hx, if_neg (by intro h; rw [h] at hci; omega), zero_mul]
    · simp
  · intro i j hj1 hj2 hi
    rw [Matrix.mul_apply, Finset.sum_eq_single j]
    · rw [hb2 j j hj1 hj2 hj1, if_pos rfl, mul_one]
      exact ha2 i j hj1 hj2 hi
    · intro l _ hl
      by_cases hlr : r ≤ l.val
      · rw [hb2 l j hj1 hj2 hlr, if_neg hl, mul_zero]
      · have hlr' : l.val < r := by omega
        have hle : eI k r ⟨l.val, hlr'⟩ = l := Fin.ext (eI_val_flag_measures _)
        have hx := ha1 ⟨l.val, hlr'⟩ i (by show l.val ≤ i.val; omega)
        rw [hle] at hx
        rw [hx, if_neg (by intro h; rw [h] at hi; omega), zero_mul]
    · simp

/- English proof (translation)
Take `⟨hVU, hUV, hV⟩` from `uEmb_inv_mul (k := k) (xOf n)`. Establish `hpN : uEmb k r (upper (xOf n))⁻¹ * n ∈ Nset k r` using `mul_mem_Nset hV hn`. Establish `he : ∀ (a : Fin r) (i : Fin (2 * r + k + 1)), (uEmb k r (upper (xOf n))⁻¹ * n) i (eI k r a) = if i = eI k r a then 1 else 0`. Introduce `a i`. Establish `h2 : (uEmb k r (upper (xOf n))⁻¹ * n) *ᵥ bvec (eI k r a) = bvec (eI k r a)`.

Rewrite using `[← Matrix.mulVec_mulVec, col_e hn, Matrix.mulVec_mulVec, hVU, Matrix.one_mulVec]`. Establish `h3` using `congrFun h2 i`. Rewrite `h3` using `[col_eq]`. Rewrite using `[h3]`. Simplify using `[bvec, Pi.single_apply]`.

Take `⟨hS, hpe⟩` from `rad_eq hpN he`. Take `⟨st, hst, -⟩` from `Rad.skewM_unique _ hS`. Use `⟨(xOf n, (Bof (uEmb k r (upper (xOf n))⁻¹ * n), st.1, st.2)), ?_⟩` and prove the remaining obligations. Use `show uEmb k r (upper (xOf n)) * pEl k r (Bof (uEmb k r (upper (xOf n))⁻¹ * n)) (skewM st.1 st.2) = n`. Rewrite using `[← hst, ← hpe, ← Matrix.mul_assoc, hUV, Matrix.one_mul]`.
-/
theorem exists_coord {n : Mat k r} (hn : n ∈ Nset k r) :
    ∃ q : (UT r → ℂ) × PPar k r, uEmb k r (upper q.1) * pOf k r q.2 = n := by
  obtain ⟨hVU, hUV, hV⟩ := uEmb_inv_mul (k := k) (xOf n)
  have hpN : uEmb k r (upper (xOf n))⁻¹ * n ∈ Nset k r := mul_mem_Nset hV hn
  have he : ∀ (a : Fin r) (i : Fin (2 * r + k + 1)),
      (uEmb k r (upper (xOf n))⁻¹ * n) i (eI k r a) = if i = eI k r a then 1 else 0 := by
    intro a i
    have h2 : (uEmb k r (upper (xOf n))⁻¹ * n) *ᵥ bvec (eI k r a) = bvec (eI k r a) := by
      rw [← Matrix.mulVec_mulVec, col_e hn, Matrix.mulVec_mulVec, hVU, Matrix.one_mulVec]
    have h3 := congrFun h2 i
    rw [col_eq] at h3
    rw [h3]
    simp [bvec, Pi.single_apply]
  obtain ⟨hS, hpe⟩ := rad_eq hpN he
  obtain ⟨st, hst, -⟩ := Rad.skewM_unique _ hS
  refine ⟨(xOf n, (Bof (uEmb k r (upper (xOf n))⁻¹ * n), st.1, st.2)), ?_⟩
  show uEmb k r (upper (xOf n)) * pEl k r (Bof (uEmb k r (upper (xOf n))⁻¹ * n)) (skewM st.1 st.2) = n
  rw [← hst, ← hpe, ← Matrix.mul_assoc, hUV, Matrix.one_mul]

/- English proof (translation)
Use `continuous_matrix fun a b => ?_` and prove the remaining obligations. Distinguish the cases in `h : a < b`. Simplify using `only [upper, dif_pos h]`. Conclude with `continuous_apply _`. Simplify using `only [upper, dif_neg h]`.

Conclude with `continuous_const`.
-/
theorem cont_upper (r : ℕ) : Continuous (upper : (UT r → ℂ) → Matrix (Fin r) (Fin r) ℂ) := by
  refine continuous_matrix fun a b => ?_
  by_cases h : a < b
  · simp only [upper, dif_pos h]
    exact continuous_apply _
  · simp only [upper, dif_neg h]
    exact continuous_const

/- English proof (translation)
Conclude with `det_upper_eq_one x`.
-/
theorem det_upper (x : UT r → ℂ) : (upper x).det = 1 := by
  exact det_upper_eq_one x

/- English proof (translation)
Establish `h : (fun x : UT r → ℂ => (upper x)⁻¹) = fun x => (upper x).adjugate`. Use function extensionality and compare the values at `x`. Rewrite using `[Matrix.inv_def, det_upper, Ring.inverse_one, one_smul]`. Rewrite using `[h]`. Conclude with `(cont_upper r).matrix_adjugate`.
-/
theorem cont_upper_inv (r : ℕ) : Continuous fun x : UT r → ℂ => (upper x)⁻¹ := by
  have h : (fun x : UT r → ℂ => (upper x)⁻¹) = fun x => (upper x).adjugate := by
    funext x
    rw [Matrix.inv_def, det_upper, Ring.inverse_one, one_smul]
  rw [h]
  exact (cont_upper r).matrix_adjugate

/- English proof (translation)
Use `continuous_matrix fun i j => ?_` and prove the remaining obligations. Distinguish the cases in `h1 : i.val < r ∧ j.val < r`. Simplify using `only [uEmb, dif_pos h1]`. Conclude with `hf.matrix_elem _ _`. Distinguish the cases in `h2 : r + k < i.val ∧ r + k < j.val`.

Simplify using `only [uEmb, dif_neg h1, dif_pos h2]`. Conclude with `(hf'.matrix_elem _ _).star`. Simplify using `only [uEmb, dif_neg h1, dif_neg h2]`. Conclude with `continuous_const`.
-/
private theorem continuous_uEmb_of_continuous_inv {X : Type*} [TopologicalSpace X] (k r : ℕ) {f : X → Matrix (Fin r) (Fin r) ℂ}
    (hf : Continuous f) (hf' : Continuous fun x => (f x)⁻¹) : Continuous fun x => uEmb k r (f x) := by
  refine continuous_matrix fun i j => ?_
  by_cases h1 : i.val < r ∧ j.val < r
  · simp only [uEmb, dif_pos h1]
    exact hf.matrix_elem _ _
  by_cases h2 : r + k < i.val ∧ r + k < j.val
  · simp only [uEmb, dif_neg h1, dif_pos h2]
    exact (hf'.matrix_elem _ _).star
  · simp only [uEmb, dif_neg h1, dif_neg h2]
    exact continuous_const

/- English proof (translation)
Conclude with `continuous_uEmb_of_continuous_inv k r (cont_upper r) (cont_upper_inv r)`.
-/
theorem cont_uEmb (k r : ℕ) : Continuous fun x : UT r → ℂ => uEmb k r (upper x) := by
  exact continuous_uEmb_of_continuous_inv k r (cont_upper r) (cont_upper_inv r)

/- English proof (translation)
Use `continuous_uEmb_of_continuous_inv k r (cont_upper_inv r) ?_` and prove the remaining obligations. Establish `h : (fun x : UT r → ℂ => ((upper x)⁻¹)⁻¹) = upper`. Use function extensionality and compare the values at `x`. Conclude with `Matrix.nonsing_inv_nonsing_inv _ (by rw [det_upper]; exact isUnit_one)`. Rewrite using `[h]`.

Conclude with `cont_upper r`.
-/
theorem cont_uEmb_inv (k r : ℕ) : Continuous fun x : UT r → ℂ => uEmb k r (upper x)⁻¹ := by
  refine continuous_uEmb_of_continuous_inv k r (cont_upper_inv r) ?_
  have h : (fun x : UT r → ℂ => ((upper x)⁻¹)⁻¹) = upper := by
    funext x
    exact Matrix.nonsing_inv_nonsing_inv _ (by rw [det_upper]; exact isUnit_one)
  rw [h]
  exact cont_upper r

/- English proof (translation)
Distinguish the cases in `h1 : a < b`. Simplify using `only [skewM, dif_pos h1]`. Conclude with `(continuous_apply _).comp hs`. Distinguish the cases in `h2 : b < a`. Simplify using `only [skewM, dif_neg h1, dif_pos h2]`.

Conclude with `((continuous_apply _).comp hs).star.neg`. Simplify using `only [skewM, dif_neg h1, dif_neg h2]`. Conclude with `(Complex.continuous_ofReal.comp ((continuous_apply a).comp ht)).mul continuous_const`.
-/
private theorem continuous_skewM_apply {X : Type*} [TopologicalSpace X] {s : X → UT r → ℂ} {t : X → Fin r → ℝ}
    (hs : Continuous s) (ht : Continuous t) (a b : Fin r) : Continuous fun x => skewM (s x) (t x) a b := by
  by_cases h1 : a < b
  · simp only [skewM, dif_pos h1]
    exact (continuous_apply _).comp hs
  by_cases h2 : b < a
  · simp only [skewM, dif_neg h1, dif_pos h2]
    exact ((continuous_apply _).comp hs).star.neg
  · simp only [skewM, dif_neg h1, dif_neg h2]
    exact (Complex.continuous_ofReal.comp ((continuous_apply a).comp ht)).mul continuous_const

/- English proof (translation)
Simplify using `only [Rad.herm_Hb]`. Conclude with `continuous_finsetSum _ fun j _ => ((continuous_apply j).comp hg).star.mul (continuous_const.mul ((continuous_apply j).comp hf))`.
-/
private theorem continuous_herm_Hb {X : Type*} [TopologicalSpace X] {f g : X → Fin (k + 1) → ℂ}
    (hf : Continuous f) (hg : Continuous g) : Continuous fun x => herm (Hb k) (f x) (g x) := by
  simp only [Rad.herm_Hb]
  exact continuous_finsetSum _ fun j _ =>
    ((continuous_apply j).comp hg).star.mul (continuous_const.mul ((continuous_apply j).comp hf))

/- English proof (translation)
Use `continuous_matrix fun i j => ?_` and prove the remaining obligations. Establish `hB : ∀ a, Continuous fun q : PPar k r => q.1 a` using `fun a => (continuous_apply a).comp continuous_fst`. Establish `hs : Continuous fun q : PPar k r => q.2.1` using `continuous_fst.comp continuous_snd`. Establish `ht : Continuous fun q : PPar k r => q.2.2` using `continuous_snd.comp continuous_snd`. Apply the tactic sequence `rcases idx_cases i with ⟨a, rfl⟩ | ⟨a, rfl⟩ | ⟨a, rfl⟩ <;>`.

Apply the tactic sequence `rcases idx_cases j with ⟨b, rfl⟩ | ⟨b, rfl⟩ | ⟨b, rfl⟩ <;>`. Simplify using `only [pOf, Rad.pEl_ee, Rad.pEl_ew, Rad.pEl_es, Rad.pEl_we, Rad.pEl_ww, Rad.pEl_ws, Rad.pEl_se, Rad.pEl_sw, Rad.pEl_ss]`. Apply the tactic sequence `all_goals first`. Consider the case `exact continuous_const`. Consider the case `exact (((continuous_apply b).comp (hB a)).star.mul continuous_const).neg`.

Consider the case `exact (continuous_skewM_apply hs ht a b).sub ((continuous_herm_Hb (hB b) (hB a)).div_const 2)`. Consider the case `exact (continuous_apply a).comp (hB b)`.
-/
theorem cont_pOf (k r : ℕ) : Continuous (pOf k r) := by
  refine continuous_matrix fun i j => ?_
  have hB : ∀ a, Continuous fun q : PPar k r => q.1 a := fun a => (continuous_apply a).comp continuous_fst
  have hs : Continuous fun q : PPar k r => q.2.1 := continuous_fst.comp continuous_snd
  have ht : Continuous fun q : PPar k r => q.2.2 := continuous_snd.comp continuous_snd
  rcases idx_cases i with ⟨a, rfl⟩ | ⟨a, rfl⟩ | ⟨a, rfl⟩ <;>
  rcases idx_cases j with ⟨b, rfl⟩ | ⟨b, rfl⟩ | ⟨b, rfl⟩ <;>
  simp only [pOf, Rad.pEl_ee, Rad.pEl_ew, Rad.pEl_es, Rad.pEl_we, Rad.pEl_ww, Rad.pEl_ws,
    Rad.pEl_se, Rad.pEl_sw, Rad.pEl_ss]
  all_goals first
    | exact continuous_const
    | exact (((continuous_apply b).comp (hB a)).star.mul continuous_const).neg
    | exact (continuous_skewM_apply hs ht a b).sub ((continuous_herm_Hb (hB b) (hB a)).div_const 2)
    | exact (continuous_apply a).comp (hB b)

/- English proof (translation)
Establish `hB : Continuous fun p : Mat k r => Bof p`. Use `continuous_pi fun b => continuous_pi fun j => ?_` and prove the remaining obligations. Simplify using `only [Bof]`. Conclude with `continuous_id.matrix_elem _ _`. Establish `hS : ∀ a b, Continuous fun p : Mat k r => Sof p a b`.

Introduce `a b`. Simplify using `only [Sof]`. Conclude with `(continuous_id.matrix_elem _ _).add ((continuous_herm_Hb ((continuous_apply b).comp hB) ((continuous_apply a).comp hB)).div_const 2)`. Conclude with `hB.prodMk ((continuous_pi fun x => hS _ _).prodMk (continuous_pi fun a => Complex.continuous_im.comp (hS a a)))`.
-/
theorem cont_qOf (k r : ℕ) : Continuous (qOf : Mat k r → PPar k r) := by
  have hB : Continuous fun p : Mat k r => Bof p := by
    refine continuous_pi fun b => continuous_pi fun j => ?_
    simp only [Bof]
    exact continuous_id.matrix_elem _ _
  have hS : ∀ a b, Continuous fun p : Mat k r => Sof p a b := by
    intro a b
    simp only [Sof]
    exact (continuous_id.matrix_elem _ _).add
      ((continuous_herm_Hb ((continuous_apply b).comp hB) ((continuous_apply a).comp hB)).div_const 2)
  exact hB.prodMk ((continuous_pi fun x => hS _ _).prodMk
    (continuous_pi fun a => Complex.continuous_im.comp (hS a a)))

/- English proof (translation)
Establish `hx : Continuous fun n : Mat k r => xOf n`. Use `continuous_pi fun p => ?_` and prove the remaining obligations. Simplify using `only [xOf]`. Conclude with `continuous_id.matrix_elem _ _`. Use `show Continuous fun n : Mat k r => (xOf n, qOf (uEmb k r (upper (xOf n))⁻¹ * n))`.

Conclude with `hx.prodMk ((cont_qOf k r).comp (((cont_uEmb_inv k r).comp hx).mul continuous_id))`.
-/
theorem cont_cOf (k r : ℕ) : Continuous (cOf : Mat k r → _) := by
  have hx : Continuous fun n : Mat k r => xOf n := by
    refine continuous_pi fun p => ?_
    simp only [xOf]
    exact continuous_id.matrix_elem _ _
  show Continuous fun n : Mat k r => (xOf n, qOf (uEmb k r (upper (xOf n))⁻¹ * n))
  exact hx.prodMk ((cont_qOf k r).comp (((cont_uEmb_inv k r).comp hx).mul continuous_id))

/- English proof (translation)
The claim follows from `(((Rad.radical k r).1 q.1 (skewM q.2.1 q.2.2)).2.2.2 (Rad.skewM_skew _ _)).1`.
-/
private theorem pOf_mem_Nset (q : PPar k r) : pOf k r q ∈ Nset k r :=
  (((Rad.radical k r).1 q.1 (skewM q.2.1 q.2.2)).2.2.2 (Rad.skewM_skew _ _)).1

/- English proof (translation)
Introduce `k r`. Use `⟨⟨fun q _ => ?_, fun q _ q' _ h => ?_, fun n hn => ?_⟩, ?_, cOf, cont_cOf k r, cOf_coord⟩` and prove the remaining obligations. Conclude with `mul_mem_Nset (UEmb.upper_mem q.1) (pOf_mem_Nset q.2)`. Combine the equalities or inequalities in the displayed calculation. Take `⟨q, hq⟩` from `exists_coord hn`.

Conclude with `⟨q, Set.mem_univ _, hq⟩`. Conclude with `((cont_uEmb k r).comp continuous_fst).mul ((cont_pOf k r).comp continuous_snd)`.
-/
theorem coord_homeo : ∀ k r : ℕ, Set.BijOn (fun q : (UT r → ℂ) × PPar k r => uEmb k r (upper q.1) * pOf k r q.2) Set.univ (Nset k r) ∧ Continuous (fun q : (UT r → ℂ) × PPar k r => uEmb k r (upper q.1) * pOf k r q.2) ∧ ∃ c : Mat k r → (UT r → ℂ) × PPar k r, Continuous c ∧ ∀ q : (UT r → ℂ) × PPar k r, c (uEmb k r (upper q.1) * pOf k r q.2) = q := by
  intro k r
  refine ⟨⟨fun q _ => ?_, fun q _ q' _ h => ?_, fun n hn => ?_⟩, ?_, cOf, cont_cOf k r, cOf_coord⟩
  · exact mul_mem_Nset (UEmb.upper_mem q.1) (pOf_mem_Nset q.2)
  · calc q = cOf (uEmb k r (upper q.1) * pOf k r q.2) := (cOf_coord q).symm
      _ = cOf (uEmb k r (upper q'.1) * pOf k r q'.2) := congrArg cOf h
      _ = q' := cOf_coord q'
  · obtain ⟨q, hq⟩ := exists_coord hn
    exact ⟨q, Set.mem_univ _, hq⟩
  · exact ((cont_uEmb k r).comp continuous_fst).mul ((cont_pOf k r).comp continuous_snd)

end GlobalTheory.Amp.NCoord
