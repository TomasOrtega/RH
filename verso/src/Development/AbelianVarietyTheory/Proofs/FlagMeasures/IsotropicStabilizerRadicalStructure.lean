import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.Rad

variable {k r : ℕ}

/- English proof (translation)
Distinguish the cases in `h : i.val < r`. Conclude with `h1 ⟨i.val, h⟩`. Distinguish the cases in `h' : i.val ≤ r + k`. Establish `: i = wI k r ⟨i.val - r, by omega⟩` using `Fin.ext (by simp [wI]; omega)`. Rewrite using `[this]`.

Conclude with `h2 _`. Establish `: i = esI k r ⟨2 * r + k - i.val, by omega⟩` using `Fin.ext (by simp [esI]; omega)`. Rewrite using `[this]`. Conclude with `h3 _`.
-/
theorem cases3 {P : Fin (2 * r + k + 1) → Prop} (h1 : ∀ a, P (eI k r a)) (h2 : ∀ j, P (wI k r j))
    (h3 : ∀ b, P (esI k r b)) (i : Fin (2 * r + k + 1)) : P i := by
  by_cases h : i.val < r
  · exact h1 ⟨i.val, h⟩
  · by_cases h' : i.val ≤ r + k
    · have : i = wI k r ⟨i.val - r, by omega⟩ := Fin.ext (by simp [wI]; omega)
      rw [this]; exact h2 _
    · have : i = esI k r ⟨2 * r + k - i.val, by omega⟩ := Fin.ext (by simp [esI]; omega)
      rw [this]; exact h3 _

/- English proof (translation)
Simplify using `[eI, Fin.ext_iff]`.
-/
theorem eI_inj (a b : Fin r) : eI k r a = eI k r b ↔ a = b := by
  simp [eI, Fin.ext_iff]
/- English proof (translation)
Simplify using `[wI, Fin.ext_iff]`.
-/
theorem wI_inj (a b : Fin (k + 1)) : wI k r a = wI k r b ↔ a = b := by
  simp [wI, Fin.ext_iff]
/- English proof (translation)
Use `a.2` as an intermediate fact. Use `b.2` as an intermediate fact. Simplify using `only [esI, Fin.ext_iff]`. Use linear arithmetic over natural numbers and integers.
-/
theorem esI_inj (a b : Fin r) : esI k r a = esI k r b ↔ a = b := by
  have := a.2; have := b.2
  simp only [esI, Fin.ext_iff]; omega
/- English proof (translation)
Use `a.2` as an intermediate fact. Simplify using `only [eI, wI, Fin.ext_iff, ne_eq]`. Use linear arithmetic over natural numbers and integers.
-/
theorem eI_ne_wI (a : Fin r) (b : Fin (k + 1)) : eI k r a ≠ wI k r b := by
  have := a.2
  simp only [eI, wI, Fin.ext_iff, ne_eq]; omega
/- English proof (translation)
Use `a.2` as an intermediate fact. Use `b.2` as an intermediate fact. Simplify using `only [eI, esI, Fin.ext_iff, ne_eq]`. Use linear arithmetic over natural numbers and integers.
-/
theorem eI_ne_esI (a b : Fin r) : eI k r a ≠ esI k r b := by
  have := a.2; have := b.2
  simp only [eI, esI, Fin.ext_iff, ne_eq]; omega
/- English proof (translation)
Use `a.2` as an intermediate fact. Use `b.2` as an intermediate fact. Simplify using `only [wI, esI, Fin.ext_iff, ne_eq]`. Use linear arithmetic over natural numbers and integers.
-/
theorem wI_ne_esI (a : Fin (k + 1)) (b : Fin r) : wI k r a ≠ esI k r b := by
  have := a.2; have := b.2
  simp only [wI, esI, Fin.ext_iff, ne_eq]; omega
/- English proof (translation)
The claim follows from `(eI_ne_wI b a).symm`.
-/
theorem wI_ne_eI (a : Fin (k + 1)) (b : Fin r) : wI k r a ≠ eI k r b := (eI_ne_wI b a).symm
/- English proof (translation)
The claim follows from `(eI_ne_esI b a).symm`.
-/
theorem esI_ne_eI (a b : Fin r) : esI k r a ≠ eI k r b := (eI_ne_esI b a).symm
/- English proof (translation)
The claim follows from `(wI_ne_esI b a).symm`.
-/
theorem esI_ne_wI (a : Fin r) (b : Fin (k + 1)) : esI k r a ≠ wI k r b := (wI_ne_esI b a).symm

/- English proof (translation)
Set `e : (Fin r ⊕ Fin (k + 1)) ⊕ Fin r → Fin (2 * r + k + 1)` to `Sum.elim (Sum.elim (eI k r) (wI k r)) (esI k r)`. Establish `he : Function.Bijective e`. Prove the components needed by the constructor for the conclusion. Apply the tactic sequence `rintro ((a | a) | a) ((b | b) | b) h <;>`. Apply the tactic sequence `simp [e, eI_inj, wI_inj, esI_inj, eI_ne_wI, eI_ne_esI, wI_ne_esI, wI_ne_eI, esI_ne_eI, esI_ne_wI] at h ⊢ <;>`.

Conclude with `h`. Introduce `i`. Proceed by induction on `i using cases3 with`. Consider the case `h1 a => exact ⟨.inl (.inl a), rfl⟩`. Consider the case `h2 a => exact ⟨.inl (.inr a), rfl⟩`.

Consider the case `h3 a => exact ⟨.inr a, rfl⟩`. Rewrite using `[← he.sum_comp f]`. Simplify using `[e, Fintype.sum_sum_type]`.
-/
theorem sum3 (f : Fin (2 * r + k + 1) → ℂ) :
    ∑ i, f i = ∑ a, f (eI k r a) + ∑ j, f (wI k r j) + ∑ b, f (esI k r b) := by
  let e : (Fin r ⊕ Fin (k + 1)) ⊕ Fin r → Fin (2 * r + k + 1) :=
    Sum.elim (Sum.elim (eI k r) (wI k r)) (esI k r)
  have he : Function.Bijective e := by
    constructor
    · rintro ((a | a) | a) ((b | b) | b) h <;>
        simp [e, eI_inj, wI_inj, esI_inj, eI_ne_wI, eI_ne_esI, wI_ne_esI, wI_ne_eI, esI_ne_eI, esI_ne_wI] at h ⊢ <;>
        exact h
    · intro i
      induction i using cases3 with
      | h1 a => exact ⟨.inl (.inl a), rfl⟩
      | h2 a => exact ⟨.inl (.inr a), rfl⟩
      | h3 a => exact ⟨.inr a, rfl⟩
  rw [← he.sum_comp f]
  simp [e, Fintype.sum_sum_type]

def sg (k : ℕ) (j : Fin (k + 1)) : ℂ := if j = Fin.last k then -1 else 1

/- English proof (translation)
Apply the tactic sequence `unfold sg; split_ifs <;> simp`.
-/
theorem star_sg (j : Fin (k + 1)) : star (sg k j) = sg k j := by
  unfold sg; split_ifs <;> simp

/- English proof (translation)
Simplify using `[herm, Hb, dotProduct, Matrix.mulVec_diagonal, sg]`.
-/
theorem herm_Hb (v w : Fin (k + 1) → ℂ) : herm (Hb k) v w = ∑ j, star (w j) * (sg k j * v j) := by
  simp [herm, Hb, dotProduct, Matrix.mulVec_diagonal, sg]

/- English proof (translation)
Apply the tactic sequence `rw [herm_Hb, Finset.sum_eq_single j] <;> simp +contextual [bvec]`.
-/
theorem herm_bvec (j : Fin (k + 1)) (w : Fin (k + 1) → ℂ) : herm (Hb k) (bvec j) w = star (w j) * sg k j := by
  rw [herm_Hb, Finset.sum_eq_single j] <;> simp +contextual [bvec]

/- English proof (translation)
Simplify using `[Hb, Matrix.diagonal_apply, sg]`.
-/
theorem Hb_apply (i j : Fin (k + 1)) : Hb k i j = if i = j then sg k i else 0 := by
  simp [Hb, Matrix.diagonal_apply, sg]

section entries
variable (B : Fin r → Fin (k + 1) → ℂ) (S : Matrix (Fin r) (Fin r) ℂ) (a b : Fin r) (i j : Fin (k + 1))

/- English proof (translation)
Use `a.2` as an intermediate fact. Use `b.2` as an intermediate fact. Unfold `pEl`. Apply the tactic sequence `split_ifs <;> first | rfl | (exfalso; simp only [eI, wI, esI, Fin.ext_iff] at *; omega)`.
-/
theorem pEl_ee : pEl k r B S (eI k r a) (eI k r b) = if a = b then 1 else 0 := by
  have := a.2; have := b.2
  unfold pEl
  split_ifs <;> first | rfl | (exfalso; simp only [eI, wI, esI, Fin.ext_iff] at *; omega)
/- English proof (translation)
Use `a.2` as an intermediate fact. Use `j.2` as an intermediate fact. Unfold `pEl; rw [if_neg (eI_ne_wI _ _), dif_pos (by simp only [eI, wI]; omega), herm_bvec]`. Simplify using `[eI, wI]`.
-/
theorem pEl_ew : pEl k r B S (eI k r a) (wI k r j) = -(star (B a j) * sg k j) := by
  have := a.2; have := j.2
  unfold pEl; rw [if_neg (eI_ne_wI _ _), dif_pos (by simp only [eI, wI]; omega), herm_bvec]
  simp [eI, wI]
/- English proof (translation)
Use `a.2` as an intermediate fact. Use `b.2` as an intermediate fact. Establish `hb : ∀ h, (⟨2 * r + k - (esI k r b).val, h⟩ : Fin r) = b` using `fun h => Fin.ext (by simp only [esI]; omega)`. Unfold `pEl; rw [if_neg (eI_ne_esI _ _), dif_neg (by simp only [eI, esI]; omega), dif_neg (by simp only [eI, esI]; omega), dif_pos (by simp only [eI, esI]; omega)]`. Simplify using `only [hb]`.

Both sides reduce to the same expression.
-/
theorem pEl_es : pEl k r B S (eI k r a) (esI k r b) = S a b - herm (Hb k) (B b) (B a) / 2 := by
  have := a.2; have := b.2
  have hb : ∀ h, (⟨2 * r + k - (esI k r b).val, h⟩ : Fin r) = b := fun h => Fin.ext (by simp only [esI]; omega)
  unfold pEl; rw [if_neg (eI_ne_esI _ _), dif_neg (by simp only [eI, esI]; omega),
    dif_neg (by simp only [eI, esI]; omega), dif_pos (by simp only [eI, esI]; omega)]
  simp only [hb]; rfl
/- English proof (translation)
Use `i.2` as an intermediate fact. Use `b.2` as an intermediate fact. Unfold `pEl`. Rewrite using `[if_neg (wI_ne_eI _ _)]`. Apply the tactic sequence `split_ifs <;> first | rfl | (exfalso; simp only [eI, wI, esI, Fin.ext_iff] at *; omega)`.
-/
theorem pEl_we : pEl k r B S (wI k r i) (eI k r b) = 0 := by
  have := i.2; have := b.2
  unfold pEl; rw [if_neg (wI_ne_eI _ _)]
  split_ifs <;> first | rfl | (exfalso; simp only [eI, wI, esI, Fin.ext_iff] at *; omega)
/- English proof (translation)
Use `i.2` as an intermediate fact. Use `j.2` as an intermediate fact. Unfold `pEl`. Apply the tactic sequence `split_ifs <;> first | rfl | (exfalso; simp only [eI, wI, esI, Fin.ext_iff] at *; omega)`.
-/
theorem pEl_ww : pEl k r B S (wI k r i) (wI k r j) = if i = j then 1 else 0 := by
  have := i.2; have := j.2
  unfold pEl
  split_ifs <;> first | rfl | (exfalso; simp only [eI, wI, esI, Fin.ext_iff] at *; omega)
/- English proof (translation)
Use `i.2` as an intermediate fact. Use `b.2` as an intermediate fact. Establish `hb : ∀ h, (⟨2 * r + k - (esI k r b).val, h⟩ : Fin r) = b` using `fun h => Fin.ext (by simp only [esI]; omega)`. Unfold `pEl; rw [if_neg (wI_ne_esI _ _), dif_neg (by simp only [wI, esI]; omega), dif_pos (by simp only [wI, esI]; omega)]`. Simplify using `only [hb]`.

Simplify using `[wI]`.
-/
theorem pEl_ws : pEl k r B S (wI k r i) (esI k r b) = B b i := by
  have := i.2; have := b.2
  have hb : ∀ h, (⟨2 * r + k - (esI k r b).val, h⟩ : Fin r) = b := fun h => Fin.ext (by simp only [esI]; omega)
  unfold pEl; rw [if_neg (wI_ne_esI _ _), dif_neg (by simp only [wI, esI]; omega),
    dif_pos (by simp only [wI, esI]; omega)]
  simp only [hb]; simp [wI]
/- English proof (translation)
Use `a.2` as an intermediate fact. Use `b.2` as an intermediate fact. Unfold `pEl`. Rewrite using `[if_neg (esI_ne_eI _ _)]`. Apply the tactic sequence `split_ifs <;> first | rfl | (exfalso; simp only [eI, wI, esI, Fin.ext_iff] at *; omega)`.
-/
theorem pEl_se : pEl k r B S (esI k r a) (eI k r b) = 0 := by
  have := a.2; have := b.2
  unfold pEl; rw [if_neg (esI_ne_eI _ _)]
  split_ifs <;> first | rfl | (exfalso; simp only [eI, wI, esI, Fin.ext_iff] at *; omega)
/- English proof (translation)
Use `a.2` as an intermediate fact. Use `j.2` as an intermediate fact. Unfold `pEl`. Rewrite using `[if_neg (esI_ne_wI _ _)]`. Apply the tactic sequence `split_ifs <;> first | rfl | (exfalso; simp only [eI, wI, esI, Fin.ext_iff] at *; omega)`.
-/
theorem pEl_sw : pEl k r B S (esI k r a) (wI k r j) = 0 := by
  have := a.2; have := j.2
  unfold pEl; rw [if_neg (esI_ne_wI _ _)]
  split_ifs <;> first | rfl | (exfalso; simp only [eI, wI, esI, Fin.ext_iff] at *; omega)
/- English proof (translation)
Use `a.2` as an intermediate fact. Use `b.2` as an intermediate fact. Unfold `pEl`. Apply the tactic sequence `split_ifs <;> first | rfl | (exfalso; simp only [eI, wI, esI, Fin.ext_iff] at *; omega)`.
-/
theorem pEl_ss : pEl k r B S (esI k r a) (esI k r b) = if a = b then 1 else 0 := by
  have := a.2; have := b.2
  unfold pEl
  split_ifs <;> first | rfl | (exfalso; simp only [eI, wI, esI, Fin.ext_iff] at *; omega)

/- English proof (translation)
Use `a.2` as an intermediate fact. Use `b.2` as an intermediate fact. Unfold `Hpk`. Apply the tactic sequence `split_ifs with h1 h2 h3 h4 <;> simp only [eI] at * <;> first | rfl | omega`.
-/
theorem H_ee : Hpk k r (eI k r a) (eI k r b) = 0 := by
  have := a.2; have := b.2
  unfold Hpk
  split_ifs with h1 h2 h3 h4 <;> simp only [eI] at * <;> first | rfl | omega
/- English proof (translation)
Use `a.2` as an intermediate fact. Use `j.2` as an intermediate fact. Unfold `Hpk`. Apply the tactic sequence `split_ifs with h1 h2 h3 h4 <;> simp only [eI, wI] at * <;> first | rfl | omega`.
-/
theorem H_ew : Hpk k r (eI k r a) (wI k r j) = 0 := by
  have := a.2; have := j.2
  unfold Hpk
  split_ifs with h1 h2 h3 h4 <;> simp only [eI, wI] at * <;> first | rfl | omega
/- English proof (translation)
Use `a.2` as an intermediate fact. Use `b.2` as an intermediate fact. Unfold `Hpk`. Apply the tactic sequence `split_ifs with h1 h2 h3 h4 <;> simp only [eI, esI, Fin.ext_iff] at * <;> first | rfl | omega`.
-/
theorem H_es : Hpk k r (eI k r a) (esI k r b) = if a = b then 1 else 0 := by
  have := a.2; have := b.2
  unfold Hpk
  split_ifs with h1 h2 h3 h4 <;> simp only [eI, esI, Fin.ext_iff] at * <;> first | rfl | omega
/- English proof (translation)
Use `i.2` as an intermediate fact. Use `b.2` as an intermediate fact. Unfold `Hpk`. Apply the tactic sequence `split_ifs with h1 h2 h3 h4 <;> simp only [eI, wI, Fin.ext_iff] at * <;> first | rfl | omega`.
-/
theorem H_we : Hpk k r (wI k r i) (eI k r b) = 0 := by
  have := i.2; have := b.2
  unfold Hpk
  split_ifs with h1 h2 h3 h4 <;> simp only [eI, wI, Fin.ext_iff] at * <;> first | rfl | omega
/- English proof (translation)
Use `i.2` as an intermediate fact. Use `j.2` as an intermediate fact. Unfold `Hpk sg`. Apply the tactic sequence `split_ifs with h1 h2 h3 h4 <;> simp only [wI, Fin.ext_iff, Fin.val_last] at * <;> first | rfl | omega`.
-/
theorem H_ww : Hpk k r (wI k r i) (wI k r j) = if i = j then sg k i else 0 := by
  have := i.2; have := j.2
  unfold Hpk sg
  split_ifs with h1 h2 h3 h4 <;> simp only [wI, Fin.ext_iff, Fin.val_last] at * <;> first | rfl | omega
/- English proof (translation)
Use `i.2` as an intermediate fact. Use `b.2` as an intermediate fact. Unfold `Hpk`. Apply the tactic sequence `split_ifs with h1 h2 h3 h4 <;> simp only [esI, wI, Fin.ext_iff] at * <;> first | rfl | omega`.
-/
theorem H_ws : Hpk k r (wI k r i) (esI k r b) = 0 := by
  have := i.2; have := b.2
  unfold Hpk
  split_ifs with h1 h2 h3 h4 <;> simp only [esI, wI, Fin.ext_iff] at * <;> first | rfl | omega
/- English proof (translation)
Use `a.2` as an intermediate fact. Use `b.2` as an intermediate fact. Unfold `Hpk`. Apply the tactic sequence `split_ifs with h1 h2 h3 h4 <;> simp only [eI, esI, Fin.ext_iff] at * <;> first | rfl | omega`.
-/
theorem H_se : Hpk k r (esI k r a) (eI k r b) = if a = b then 1 else 0 := by
  have := a.2; have := b.2
  unfold Hpk
  split_ifs with h1 h2 h3 h4 <;> simp only [eI, esI, Fin.ext_iff] at * <;> first | rfl | omega
/- English proof (translation)
Use `a.2` as an intermediate fact. Use `j.2` as an intermediate fact. Unfold `Hpk`. Apply the tactic sequence `split_ifs with h1 h2 h3 h4 <;> simp only [esI, wI, Fin.ext_iff] at * <;> first | rfl | omega`.
-/
theorem H_sw : Hpk k r (esI k r a) (wI k r j) = 0 := by
  have := a.2; have := j.2
  unfold Hpk
  split_ifs with h1 h2 h3 h4 <;> simp only [esI, wI, Fin.ext_iff] at * <;> first | rfl | omega
/- English proof (translation)
Use `a.2` as an intermediate fact. Use `b.2` as an intermediate fact. Unfold `Hpk`. Apply the tactic sequence `split_ifs with h1 h2 h3 h4 <;> simp only [esI, Fin.ext_iff] at * <;> first | rfl | omega`.
-/
theorem H_ss : Hpk k r (esI k r a) (esI k r b) = 0 := by
  have := a.2; have := b.2
  unfold Hpk
  split_ifs with h1 h2 h3 h4 <;> simp only [esI, Fin.ext_iff] at * <;> first | rfl | omega

variable (m : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)

/- English proof (translation)
Use `i.2` as an intermediate fact. Use `j.2` as an intermediate fact. Unfold `mEmb; rw [dif_pos (by simp only [wI]; omega)]; simp [wI]`.
-/
theorem m_ww : mEmb k r m (wI k r i) (wI k r j) = m i j := by
  have := i.2; have := j.2
  unfold mEmb; rw [dif_pos (by simp only [wI]; omega)]; simp [wI]
/- English proof (translation)
Use `a.2` as an intermediate fact. Unfold `mEmb; rw [dif_neg (by simp only [eI]; omega)]`.
-/
theorem m_e (x : Fin (2 * r + k + 1)) : mEmb k r m (eI k r a) x = if eI k r a = x then 1 else 0 := by
  have := a.2
  unfold mEmb; rw [dif_neg (by simp only [eI]; omega)]
/- English proof (translation)
Use `a.2` as an intermediate fact. Unfold `mEmb; rw [dif_neg (by simp only [esI]; omega)]`.
-/
theorem middleSpaceLeviEmbedding_apply_es_row (x : Fin (2 * r + k + 1)) : mEmb k r m (esI k r a) x = if esI k r a = x then 1 else 0 := by
  have := a.2
  unfold mEmb; rw [dif_neg (by simp only [esI]; omega)]
/- English proof (translation)
Use `b.2` as an intermediate fact. Unfold `mEmb; rw [dif_neg (by simp only [eI]; omega), if_neg (wI_ne_eI _ _)]`.
-/
theorem m_we : mEmb k r m (wI k r i) (eI k r b) = 0 := by
  have := b.2
  unfold mEmb; rw [dif_neg (by simp only [eI]; omega), if_neg (wI_ne_eI _ _)]
/- English proof (translation)
Use `b.2` as an intermediate fact. Unfold `mEmb; rw [dif_neg (by simp only [esI]; omega), if_neg (wI_ne_esI _ _)]`.
-/
theorem m_ws : mEmb k r m (wI k r i) (esI k r b) = 0 := by
  have := b.2
  unfold mEmb; rw [dif_neg (by simp only [esI]; omega), if_neg (wI_ne_esI _ _)]

end entries

/- English proof (translation)
Simplify using `only [herm_Hb, star_sum, star_mul', star_star, star_sg]`. Conclude with `Finset.sum_congr rfl fun _ _ => by ring`.
-/
theorem herm_star (v w : Fin (k + 1) → ℂ) : star (herm (Hb k) v w) = herm (Hb k) w v := by
  simp only [herm_Hb, star_sum, star_mul', star_star, star_sg]
  exact Finset.sum_congr rfl fun _ _ => by ring

/- English proof (translation)
Simplify using `[herm, Matrix.mulVec_add]`.
-/
theorem herm_add_left (v v' w : Fin (k + 1) → ℂ) :
    herm (Hb k) (v + v') w = herm (Hb k) v w + herm (Hb k) v' w := by
  simp [herm, Matrix.mulVec_add]

/- English proof (translation)
Simplify using `[herm]`.
-/
theorem herm_add_right (v w w' : Fin (k + 1) → ℂ) :
    herm (Hb k) v (w + w') = herm (Hb k) v w + herm (Hb k) v w' := by
  simp [herm]

/- English proof (translation)
Simplify using `[herm, Matrix.mulVec_neg]`.
-/
theorem herm_neg_left (v w : Fin (k + 1) → ℂ) : herm (Hb k) (-v) w = -herm (Hb k) v w := by
  simp [herm, Matrix.mulVec_neg]

/- English proof (translation)
Simplify using `[herm]`.
-/
theorem herm_neg_right (v w : Fin (k + 1) → ℂ) : herm (Hb k) v (-w) = -herm (Hb k) v w := by
  simp [herm]

/- English proof (translation)
Use extensionality with `x y`. Rewrite using `[Matrix.mul_apply, sum3]`. Apply the tactic sequence `induction x using cases3 <;> induction y using cases3 <;>`. Simplify using `[pEl_ee, pEl_ew, pEl_es, pEl_we, pEl_ww, pEl_ws, pEl_se, pEl_sw, pEl_ss]`. Expand and normalize the polynomial expressions, which then agree.

Name the introduced variables `a b`. Simplify using `only [herm_add_left, herm_add_right]`. Establish `: herm (Hb k) (B' b) (B a) = ∑ j, (starRingEnd ℂ) (B a j) * sg k j * B' b j`. Rewrite using `[herm_Hb]; exact Finset.sum_congr rfl fun _ _ => by simp [mul_assoc]`. Rewrite using `[← this]`.

Expand and normalize the polynomial expressions, which then agree. Expand and normalize the polynomial expressions, which then agree.
-/
theorem pEl_mul (B B' : Fin r → Fin (k + 1) → ℂ) (S S' : Matrix (Fin r) (Fin r) ℂ) :
    pEl k r B S * pEl k r B' S' = pEl k r (B + B')
      (S + S' + Matrix.of fun a b => (herm (Hb k) (B b) (B' a) - herm (Hb k) (B' b) (B a)) / 2) := by
  ext x y
  rw [Matrix.mul_apply, sum3]
  induction x using cases3 <;> induction y using cases3 <;>
    simp [pEl_ee, pEl_ew, pEl_es, pEl_we, pEl_ww, pEl_ws, pEl_se, pEl_sw, pEl_ss]
  · ring
  · rename_i a b
    simp only [herm_add_left, herm_add_right]
    have : herm (Hb k) (B' b) (B a) = ∑ j, (starRingEnd ℂ) (B a j) * sg k j * B' b j := by
      rw [herm_Hb]; exact Finset.sum_congr rfl fun _ _ => by simp [mul_assoc]
    rw [← this]; ring
  · ring

/- English proof (translation)
Use extensionality with `x y`. Apply the tactic sequence `induction x using cases3 <;> induction y using cases3 <;>`. Simplify using `[pEl_ee, pEl_ew, pEl_es, pEl_we, pEl_ww, pEl_ws, pEl_se, pEl_sw, pEl_ss, Matrix.one_apply, herm, eI_inj, wI_inj, esI_inj, eI_ne_wI, eI_ne_esI, wI_ne_esI, wI_ne_eI, esI_ne_eI, esI_ne_wI]`.
-/
theorem pEl_zero : pEl k r 0 0 = 1 := by
  ext x y
  induction x using cases3 <;> induction y using cases3 <;>
    simp [pEl_ee, pEl_ew, pEl_es, pEl_we, pEl_ww, pEl_ws, pEl_se, pEl_sw, pEl_ss, Matrix.one_apply, herm,
      eI_inj, wI_inj, esI_inj, eI_ne_wI, eI_ne_esI, wI_ne_esI, wI_ne_eI, esI_ne_eI, esI_ne_wI]

/- English proof (translation)
Apply `Matrix.inv_eq_right_inv` to reduce the goal to its premises. Rewrite using `[pEl_mul, ← pEl_zero]`. Use `congr 1`. Simplify using the standard rewrite rules. Use extensionality with `a b`.

Simplify using `[herm_neg_left, herm_neg_right]`.
-/
theorem pEl_inv (B : Fin r → Fin (k + 1) → ℂ) (S : Matrix (Fin r) (Fin r) ℂ) :
    (pEl k r B S)⁻¹ = pEl k r (-B) (-S) := by
  apply Matrix.inv_eq_right_inv
  rw [pEl_mul, ← pEl_zero]
  congr 1
  · simp
  · ext a b; simp [herm_neg_left, herm_neg_right]

/- English proof (translation)
Use `show _ = _`. Use extensionality with `x y`. Simplify using `only [Matrix.mul_apply, sum3, Matrix.conjTranspose_apply]`. Apply the tactic sequence `induction x using cases3 <;> induction y using cases3 <;>`. Simplify using `[pEl_ee, pEl_ew, pEl_es, pEl_we, pEl_ww, pEl_ws, pEl_se, pEl_sw, pEl_ss, H_ee, H_ew, H_es, H_we, H_ww, H_ws, H_se, H_sw, H_ss, apply_ite (starRingEnd ℂ)]`.

Simplify using `only [eq_comm]`. Name the introduced variables `i j`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Both sides reduce to the same expression.

Rewrite using `[if_neg h, if_neg (Ne.symm h)]`. Name the introduced variables `j b`. Establish `: (starRingEnd ℂ) (sg k j) = sg k j` using `star_sg j`. Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `only [eq_comm]`. Name the introduced variables `a b`. Establish `h1 : herm (Hb k) (B b) (B a) = ∑ j, (starRingEnd ℂ) (B a j) * sg k j * B b j`. Rewrite using `[herm_Hb]; exact Finset.sum_congr rfl fun _ _ => by simp [mul_assoc]`. Establish `h2 : (starRingEnd ℂ) (herm (Hb k) (B a) (B b)) = herm (Hb k) (B b) (B a)` using `herm_star _ _`.

Establish `h3 : (starRingEnd ℂ) (S b a) = -S a b` using `congrFun (congrFun hS a) b`. Rewrite using `[← h1, h2, h3]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem pEl_mem_UH (B : Fin r → Fin (k + 1) → ℂ) (S : Matrix (Fin r) (Fin r) ℂ) (hS : Sᴴ = -S) :
    pEl k r B S ∈ UH (Hpk k r) := by
  show _ = _
  ext x y
  simp only [Matrix.mul_apply, sum3, Matrix.conjTranspose_apply]
  induction x using cases3 <;> induction y using cases3 <;>
    simp [pEl_ee, pEl_ew, pEl_es, pEl_we, pEl_ww, pEl_ws, pEl_se, pEl_sw, pEl_ss,
      H_ee, H_ew, H_es, H_we, H_ww, H_ws, H_se, H_sw, H_ss, apply_ite (starRingEnd ℂ)]
  · simp only [eq_comm]
  · rename_i i j
    by_cases h : i = j
    · subst h; rfl
    · rw [if_neg h, if_neg (Ne.symm h)]
  · rename_i j b
    have : (starRingEnd ℂ) (sg k j) = sg k j := star_sg j
    rw [this]; ring
  · simp only [eq_comm]
  · rename_i a b
    have h1 : herm (Hb k) (B b) (B a) = ∑ j, (starRingEnd ℂ) (B a j) * sg k j * B b j := by
      rw [herm_Hb]; exact Finset.sum_congr rfl fun _ _ => by simp [mul_assoc]
    have h2 : (starRingEnd ℂ) (herm (Hb k) (B a) (B b)) = herm (Hb k) (B b) (B a) := herm_star _ _
    have h3 : (starRingEnd ℂ) (S b a) = -S a b := congrFun (congrFun hS a) b
    rw [← h1, h2, h3]; ring

/- English proof (translation)
Use extensionality with `x y`. Rewrite using `[Matrix.mul_apply, sum3]`. Apply the tactic sequence `induction x using cases3 <;> induction y using cases3 <;>`. Simplify using `[m_ww, m_e, middleSpaceLeviEmbedding_apply_es_row, m_we, m_ws, Matrix.mul_apply, eI_inj, wI_inj, esI_inj, eI_ne_wI, eI_ne_esI, wI_ne_esI, wI_ne_eI, esI_ne_eI, esI_ne_wI]`.
-/
theorem mEmb_mul (m m' : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    mEmb k r m * mEmb k r m' = mEmb k r (m * m') := by
  ext x y
  rw [Matrix.mul_apply, sum3]
  induction x using cases3 <;> induction y using cases3 <;>
    simp [m_ww, m_e, middleSpaceLeviEmbedding_apply_es_row, m_we, m_ws, Matrix.mul_apply,
      eI_inj, wI_inj, esI_inj, eI_ne_wI, eI_ne_esI, wI_ne_esI, wI_ne_eI, esI_ne_eI, esI_ne_wI]

/- English proof (translation)
Use extensionality with `x y`. Apply the tactic sequence `induction x using cases3 <;> induction y using cases3 <;>`. Simplify using `[m_ww, m_e, middleSpaceLeviEmbedding_apply_es_row, m_we, m_ws, Matrix.one_apply, eI_inj, wI_inj, esI_inj, eI_ne_wI, eI_ne_esI, wI_ne_esI, wI_ne_eI, esI_ne_eI, esI_ne_wI]`.
-/
theorem mEmb_one : mEmb k r 1 = 1 := by
  ext x y
  induction x using cases3 <;> induction y using cases3 <;>
    simp [m_ww, m_e, middleSpaceLeviEmbedding_apply_es_row, m_we, m_ws, Matrix.one_apply,
      eI_inj, wI_inj, esI_inj, eI_ne_wI, eI_ne_esI, wI_ne_esI, wI_ne_eI, esI_ne_eI, esI_ne_wI]

/- English proof (translation)
Use `show _ = _`. Establish `hm' : mᴴ * Hb k * m = Hb k` using `hm`. Use extensionality with `x y`. Simplify using `only [Matrix.mul_apply, sum3, Matrix.conjTranspose_apply]`. Apply the tactic sequence `induction x using cases3 <;> induction y using cases3 <;>`.

Simplify using `[m_ww, m_e, middleSpaceLeviEmbedding_apply_es_row, m_we, m_ws, H_ee, H_ew, H_es, H_we, H_ww, H_ws, H_se, H_sw, H_ss, apply_ite (starRingEnd ℂ), eI_inj, wI_inj, esI_inj, eI_ne_wI, eI_ne_esI, wI_ne_esI, wI_ne_eI, esI_ne_eI, esI_ne_wI]`. Simplify using `only [eq_comm]`. Name the introduced variables `i j`. Use `congrFun (congrFun hm' i) j` as an intermediate fact. Simplify `this` using `[Matrix.mul_apply, Hb_apply]`.

Simplify using `only [eq_comm]`.
-/
theorem mEmb_mem (m : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (hm : m ∈ UH (Hb k)) : mEmb k r m ∈ GG k r := by
  show _ = _
  have hm' : mᴴ * Hb k * m = Hb k := hm
  ext x y
  simp only [Matrix.mul_apply, sum3, Matrix.conjTranspose_apply]
  induction x using cases3 <;> induction y using cases3 <;>
    simp [m_ww, m_e, middleSpaceLeviEmbedding_apply_es_row, m_we, m_ws, H_ee, H_ew, H_es, H_we, H_ww, H_ws, H_se, H_sw, H_ss,
      apply_ite (starRingEnd ℂ),
      eI_inj, wI_inj, esI_inj, eI_ne_wI, eI_ne_esI, wI_ne_esI, wI_ne_eI, esI_ne_eI, esI_ne_wI]
  · simp only [eq_comm]
  · rename_i i j
    have := congrFun (congrFun hm' i) j
    simpa [Matrix.mul_apply, Hb_apply] using this
  · simp only [eq_comm]

/- English proof (translation)
Establish `hm' : mᴴ * Hb k * m = Hb k` using `hm`. Establish `hH : Hb k * Hb k = 1`. Unfold `Hb`. Rewrite using `[Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Apply the tactic sequence `congr 1; funext j; split_ifs <;> simp`.

Establish `h1 : (Hb k * mᴴ * Hb k) * m = 1`. Rewrite using `[← hH]`. Use `nth_rewrite 4 [← hm']`. Simplify using `only [Matrix.mul_assoc]`. Establish `hu : IsUnit m.det` using `Matrix.isUnit_det_of_left_inverse h1`.

Apply `Matrix.inv_eq_right_inv` to reduce the goal to its premises. Rewrite using `[mEmb_mul, Matrix.mul_nonsing_inv _ hu, mEmb_one]`.
-/
theorem mEmb_inv (m : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (hm : m ∈ UH (Hb k)) :
    (mEmb k r m)⁻¹ = mEmb k r m⁻¹ := by
  have hm' : mᴴ * Hb k * m = Hb k := hm
  have hH : Hb k * Hb k = 1 := by
    unfold Hb; rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext j; split_ifs <;> simp
  have h1 : (Hb k * mᴴ * Hb k) * m = 1 := by
    rw [← hH]; nth_rewrite 4 [← hm']; simp only [Matrix.mul_assoc]
  have hu : IsUnit m.det := Matrix.isUnit_det_of_left_inverse h1
  apply Matrix.inv_eq_right_inv
  rw [mEmb_mul, Matrix.mul_nonsing_inv _ hu, mEmb_one]

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [Matrix.conjTranspose_apply, Matrix.neg_apply, skewM]`. Break down `lt_trichotomy a b with h | h | h` into its components or cases. Simplify using `[h, h.not_gt]`. Substitute `h` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[h, h.not_gt]`.
-/
theorem skewM_skew (s : UT r → ℂ) (t : Fin r → ℝ) : (skewM s t)ᴴ = -skewM s t := by
  ext a b
  simp only [Matrix.conjTranspose_apply, Matrix.neg_apply, skewM]
  rcases lt_trichotomy a b with h | h | h
  · simp [h, h.not_gt]
  · subst h; simp
  · simp [h, h.not_gt]

/- English proof (translation)
Establish `hs : ∀ a b, star (S b a) = -S a b` using `fun a b => congrFun (congrFun hS a) b`. Use `⟨(fun q => S q.1.1 q.1.2, fun a => (S a a).im), ?_, ?_⟩` and prove the remaining obligations. Use extensionality with `a b`. Simplify using `only [skewM]`. Break down `lt_trichotomy a b with h | h | h` into its components or cases.

Simplify using `[h]`. Substitute `h` using the available equality. Use `congrArg Complex.re (hs a a)` as an intermediate fact. Simplify using `only [lt_irrefl, dite_false]`. Apply the tactic sequence `apply Complex.ext <;> simp at this ⊢`.

Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[dif_neg h.not_gt, dif_pos h, hs, neg_neg]`. Introduce and unpack `⟨s, t⟩ rfl`. Use extensionality with `q`. Simplify using `[skewM, q.2]`.

Simplify using `[skewM]`.
-/
theorem skewM_unique (S : Matrix (Fin r) (Fin r) ℂ) (hS : Sᴴ = -S) :
    ∃! p : (UT r → ℂ) × (Fin r → ℝ), S = skewM p.1 p.2 := by
  have hs : ∀ a b, star (S b a) = -S a b := fun a b => congrFun (congrFun hS a) b
  refine ⟨(fun q => S q.1.1 q.1.2, fun a => (S a a).im), ?_, ?_⟩
  · ext a b
    simp only [skewM]
    rcases lt_trichotomy a b with h | h | h
    · simp [h]
    · subst h
      have := congrArg Complex.re (hs a a)
      simp only [lt_irrefl, dite_false]
      apply Complex.ext <;> simp at this ⊢
      linarith
    · rw [dif_neg h.not_gt, dif_pos h, hs, neg_neg]
  · rintro ⟨s, t⟩ rfl
    ext q
    · simp [skewM, q.2]
    · simp [skewM]

/- English proof (translation)
Simplify using `[bvec]`.
-/
theorem mulVec_bvec (g : Mat k r) (y x : Fin (2 * r + k + 1)) : (g *ᵥ bvec y) x = g x y := by
  simp [bvec]

/- English proof (translation)
Simplify using `[bvec, Pi.single_apply]`.
-/
theorem bvec_apply (y x : Fin (2 * r + k + 1)) : bvec y x = if x = y then 1 else 0 := by
  simp [bvec, Pi.single_apply]

/- English proof (translation)
Introduce `k r`. Use `⟨fun B S => ⟨fun a => ?_, fun j => ?_, fun b => ?_, fun hS => ⟨⟨pEl_mem_UH B S hS, ?_, ?_⟩, pEl_inv B S⟩⟩, skewM_skew, skewM_unique, pEl_mul, fun m hm => ⟨mEmb_mem m hm, mEmb_inv m hm⟩⟩` and prove the remaining obligations. Use function extensionality and compare the values at `x`. Rewrite using `[mulVec_bvec, bvec_apply]`. Apply the tactic sequence `induction x using cases3 <;> simp [pEl_ee, pEl_we, pEl_se, eI_inj, wI_ne_eI, esI_ne_eI]`.

Use function extensionality and compare the values at `x`. Rewrite using `[mulVec_bvec]`. Simplify using `only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, bvec_apply, herm_bvec]`. Apply the tactic sequence `induction x using cases3 <;>`. Simplify using `[pEl_ew, pEl_ww, pEl_sw, eI_inj, wI_inj, wI_ne_eI, esI_ne_eI, eI_ne_wI, esI_ne_wI]`.

Use function extensionality and compare the values at `x`. Rewrite using `[mulVec_bvec]`. Simplify using `only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, bvec_apply]`. Apply the tactic sequence `induction x using cases3 <;>`. Simplify using `[pEl_es, pEl_ws, pEl_ss, eI_inj, wI_inj, esI_inj, wI_ne_eI, esI_ne_eI, eI_ne_wI, esI_ne_wI, eI_ne_esI, wI_ne_esI]`.

Introduce `a x _`. Apply the tactic sequence `induction x using cases3 <;> simp [pEl_ee, pEl_we, pEl_se, eI_inj, wI_ne_eI, esI_ne_eI]`. Introduce `x y h1 h2 h3`. Proceed by induction on `x using cases3 with`. Consider the case `h1 a => exact absurd a.2 (by simp only [eI] at h3; omega)`.

Consider the case `h2 i`. Proceed by induction on `y using cases3 with`. Consider the case `h1 a => exact absurd a.2 (by simp only [eI] at h1; omega)`. Consider the case `h2 j => simp [pEl_ww, wI_inj]`. Consider the case `h3 a => exact absurd a.2 (by simp only [esI] at h2; omega)`.

Consider the case `h3 b`. Proceed by induction on `y using cases3 with`. Consider the case `h1 a => exact absurd a.2 (by simp only [eI] at h1; omega)`. Consider the case `h2 j => simp [pEl_sw, esI_ne_wI]`. Consider the case `h3 a => exact absurd a.2 (by simp only [esI] at h2; omega)`.
-/
theorem radical : ∀ k r : ℕ, (∀ (B : Fin r → Fin (k + 1) → ℂ) (S : Matrix (Fin r) (Fin r) ℂ), (∀ a : Fin r, pEl k r B S *ᵥ bvec (eI k r a) = bvec (eI k r a)) ∧ (∀ j : Fin (k + 1), pEl k r B S *ᵥ bvec (wI k r j) = bvec (wI k r j) - ∑ b, herm (Hb k) (bvec j) (B b) • bvec (eI k r b)) ∧ (∀ b : Fin r, pEl k r B S *ᵥ bvec (esI k r b) = bvec (esI k r b) + (∑ j, B b j • bvec (wI k r j)) + ∑ a, (S a b - herm (Hb k) (B b) (B a) / 2) • bvec (eI k r a)) ∧ (Sᴴ = -S → pEl k r B S ∈ Nset k r ∧ (pEl k r B S)⁻¹ = pEl k r (-B) (-S))) ∧ (∀ (s : UT r → ℂ) (t : Fin r → ℝ), (skewM s t)ᴴ = -skewM s t) ∧ (∀ S : Matrix (Fin r) (Fin r) ℂ, Sᴴ = -S → ∃! p : (UT r → ℂ) × (Fin r → ℝ), S = skewM p.1 p.2) ∧ (∀ B B' (S S' : Matrix (Fin r) (Fin r) ℂ), pEl k r B S * pEl k r B' S' = pEl k r (B + B') (S + S' + Matrix.of fun a b => (herm (Hb k) (B b) (B' a) - herm (Hb k) (B' b) (B a)) / 2)) ∧ ∀ m ∈ UH (Hb k), mEmb k r m ∈ GG k r ∧ (mEmb k r m)⁻¹ = mEmb k r m⁻¹ := by
  intro k r
  refine ⟨fun B S => ⟨fun a => ?_, fun j => ?_, fun b => ?_, fun hS => ⟨⟨pEl_mem_UH B S hS, ?_, ?_⟩, pEl_inv B S⟩⟩,
    skewM_skew, skewM_unique, pEl_mul, fun m hm => ⟨mEmb_mem m hm, mEmb_inv m hm⟩⟩
  · funext x
    rw [mulVec_bvec, bvec_apply]
    induction x using cases3 <;> simp [pEl_ee, pEl_we, pEl_se, eI_inj, wI_ne_eI, esI_ne_eI]
  · funext x
    rw [mulVec_bvec]
    simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, bvec_apply, herm_bvec]
    induction x using cases3 <;>
      simp [pEl_ew, pEl_ww, pEl_sw, eI_inj, wI_inj, wI_ne_eI, esI_ne_eI, eI_ne_wI, esI_ne_wI]
  · funext x
    rw [mulVec_bvec]
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, bvec_apply]
    induction x using cases3 <;>
      simp [pEl_es, pEl_ws, pEl_ss, eI_inj, wI_inj, esI_inj, wI_ne_eI, esI_ne_eI, eI_ne_wI, esI_ne_wI,
        eI_ne_esI, wI_ne_esI]
  · intro a x _
    induction x using cases3 <;> simp [pEl_ee, pEl_we, pEl_se, eI_inj, wI_ne_eI, esI_ne_eI]
  · intro x y h1 h2 h3
    induction x using cases3 with
    | h1 a => exact absurd a.2 (by simp only [eI] at h3; omega)
    | h2 i =>
      induction y using cases3 with
      | h1 a => exact absurd a.2 (by simp only [eI] at h1; omega)
      | h2 j => simp [pEl_ww, wI_inj]
      | h3 a => exact absurd a.2 (by simp only [esI] at h2; omega)
    | h3 b =>
      induction y using cases3 with
      | h1 a => exact absurd a.2 (by simp only [eI] at h1; omega)
      | h2 j => simp [pEl_sw, esI_ne_wI]
      | h3 a => exact absurd a.2 (by simp only [esI] at h2; omega)

end GlobalTheory.Amp.Rad
