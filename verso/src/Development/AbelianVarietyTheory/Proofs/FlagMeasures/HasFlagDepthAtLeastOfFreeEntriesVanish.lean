import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsVolData

noncomputable section

open Matrix
open Formalism.QuantumDeterminants GlobalTheory.SnMass GlobalTheory.SnMass.VolN

namespace GlobalTheory.SnMass.VolN.DepCoords

variable {k r : ℕ}

def mir (k r : ℕ) (i : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) :=
  if i.val < r ∨ r + k < i.val then ⟨2 * r + k - i.val, by omega⟩ else i

def sg (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℂ := if i.val = r + k then -1 else 1

/- English proof (translation)
Unfold `mir`. Rewrite using `[if_pos h]`.
-/
theorem mir_val_out {i : Fin (2 * r + k + 1)} (h : i.val < r ∨ r + k < i.val) :
    (mir k r i).val = 2 * r + k - i.val := by
  unfold mir
  rw [if_pos h]

/- English proof (translation)
Unfold `mir`. Rewrite using `[if_neg h]`.
-/
theorem mir_val_in {i : Fin (2 * r + k + 1)} (h : ¬ (i.val < r ∨ r + k < i.val)) : mir k r i = i := by
  unfold mir
  rw [if_neg h]

/- English proof (translation)
Establish `hi` using `i.isLt`. Distinguish the cases in `h : i.val < r ∨ r + k < i.val`. Establish `h1` using `mir_val_out h`. Establish `h2 : (mir k r i).val < r ∨ r + k < (mir k r i).val` using `by omega`. Apply `Fin.ext` to reduce the goal to its premises.

Rewrite using `[mir_val_out h2, h1]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[mir_val_in h, mir_val_in h]`.
-/
theorem mir_mir (i : Fin (2 * r + k + 1)) : mir k r (mir k r i) = i := by
  have hi := i.isLt
  by_cases h : i.val < r ∨ r + k < i.val
  · have h1 := mir_val_out h
    have h2 : (mir k r i).val < r ∨ r + k < (mir k r i).val := by omega
    apply Fin.ext
    rw [mir_val_out h2, h1]
    omega
  · rw [mir_val_in h, mir_val_in h]

/- English proof (translation)
Establish `ha` using `a.isLt`. Establish `he : (eI k r a).val = a.val` using `by rfl`. Establish `hs : (esI k r a).val = 2 * r + k - a.val` using `by rfl`. Apply `Fin.ext` to reduce the goal to its premises. Rewrite using `[mir_val_out (by omega), he, hs]`.
-/
theorem mir_eI (a : Fin r) : mir k r (eI k r a) = esI k r a := by
  have ha := a.isLt
  have he : (eI k r a).val = a.val := by rfl
  have hs : (esI k r a).val = 2 * r + k - a.val := by rfl
  apply Fin.ext
  rw [mir_val_out (by omega), he, hs]

/- English proof (translation)
Establish `ha` using `a.isLt`. Establish `he : (eI k r a).val = a.val` using `by rfl`. Establish `hs : (esI k r a).val = 2 * r + k - a.val` using `by rfl`. Apply `Fin.ext` to reduce the goal to its premises. Rewrite using `[mir_val_out (by omega), he, hs]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem mir_esI (a : Fin r) : mir k r (esI k r a) = eI k r a := by
  have ha := a.isLt
  have he : (eI k r a).val = a.val := by rfl
  have hs : (esI k r a).val = 2 * r + k - a.val := by rfl
  apply Fin.ext
  rw [mir_val_out (by omega), he, hs]
  omega

/- English proof (translation)
Establish `hj` using `j.isLt`. Establish `hw : (wI k r j).val = r + j.val` using `by rfl`. Conclude with `mir_val_in (by omega)`.
-/
theorem mir_wI (j : Fin (k + 1)) : mir k r (wI k r j) = wI k r j := by
  have hj := j.isLt
  have hw : (wI k r j).val = r + j.val := by rfl
  exact mir_val_in (by omega)

/- English proof (translation)
Unfold `sg`. Apply the tactic sequence `split_ifs <;> norm_num`.
-/
theorem sg_ne_zero (i : Fin (2 * r + k + 1)) : sg k r i ≠ 0 := by
  unfold sg
  split_ifs <;> norm_num

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem eI_val (a : Fin r) : (eI k r a).val = a.val := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem wI_val (j : Fin (k + 1)) : (wI k r j).val = r + j.val := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem esI_val (a : Fin r) : (esI k r a).val = 2 * r + k - a.val := rfl

/- English proof (translation)
Establish `ha` using `a.isLt`. Establish `h : (eI k r a).val ≠ r + k` using `by rw [eI_val]; omega`. Unfold `sg`. Rewrite using `[if_neg h]`.
-/
theorem sg_eI (a : Fin r) : sg k r (eI k r a) = 1 := by
  have ha := a.isLt
  have h : (eI k r a).val ≠ r + k := by rw [eI_val]; omega
  unfold sg
  rw [if_neg h]

/- English proof (translation)
Establish `ha` using `a.isLt`. Establish `h : (esI k r a).val ≠ r + k` using `by rw [esI_val]; omega`. Unfold `sg`. Rewrite using `[if_neg h]`.
-/
theorem sg_esI (a : Fin r) : sg k r (esI k r a) = 1 := by
  have ha := a.isLt
  have h : (esI k r a).val ≠ r + k := by rw [esI_val]; omega
  unfold sg
  rw [if_neg h]

/- English proof (translation)
Distinguish the cases in `h : i.val < r ∨ r + k < i.val`. Establish `h1` using `mir_val_out h`. Establish `hi` using `i.isLt`. Establish `h2 : (mir k r i).val ≠ r + k` using `by omega`. Establish `h3 : i.val ≠ r + k` using `by omega`.

Unfold `sg`. Rewrite using `[if_neg h2, if_neg h3]`. Rewrite using `[mir_val_in h]`.
-/
theorem sg_mir (i : Fin (2 * r + k + 1)) : sg k r (mir k r i) = sg k r i := by
  by_cases h : i.val < r ∨ r + k < i.val
  · have h1 := mir_val_out h
    have hi := i.isLt
    have h2 : (mir k r i).val ≠ r + k := by omega
    have h3 : i.val ≠ r + k := by omega
    unfold sg
    rw [if_neg h2, if_neg h3]
  · rw [mir_val_in h]

/- English proof (translation)
Establish `hi` using `i.isLt`. Establish `hl` using `l.isLt`. Distinguish the cases in `h : i.val < r ∨ r + k < i.val`. Establish `e : l = mir k r i ↔ i.val + l.val = 2 * r + k`. Rewrite using `[Fin.ext_iff, mir_val_out h]`.

Use linear arithmetic over natural numbers and integers. Establish `s : sg k r i = 1`. Unfold `sg`. Rewrite using `[if_neg (by omega)]`. Rewrite using `[s]`.

Unfold `Hpk`. Simplify using `only [e]`. Simplify using `only [Fin.ext_iff]`. Apply the tactic sequence `split_ifs <;> first | rfl | (exfalso; omega)`. Establish `e : l = mir k r i ↔ i.val = l.val`.

Rewrite using `[mir_val_in h, Fin.ext_iff]`. Conclude with `eq_comm`. Unfold `Hpk sg`. Simplify using `only [e]`. Simplify using `only [Fin.ext_iff]`.

Apply the tactic sequence `split_ifs <;> first | rfl | (exfalso; omega)`.
-/
theorem Hpk_apply (i l : Fin (2 * r + k + 1)) :
    Hpk k r i l = if l = mir k r i then sg k r i else 0 := by
  have hi := i.isLt
  have hl := l.isLt
  by_cases h : i.val < r ∨ r + k < i.val
  · have e : l = mir k r i ↔ i.val + l.val = 2 * r + k := by
      rw [Fin.ext_iff, mir_val_out h]
      omega
    have s : sg k r i = 1 := by
      unfold sg
      rw [if_neg (by omega)]
    rw [s]
    unfold Hpk
    simp only [e]
    simp only [Fin.ext_iff]
    split_ifs <;> first | rfl | (exfalso; omega)
  · have e : l = mir k r i ↔ i.val = l.val := by
      rw [mir_val_in h, Fin.ext_iff]
      exact eq_comm
    unfold Hpk sg
    simp only [e]
    simp only [Fin.ext_iff]
    split_ifs <;> first | rfl | (exfalso; omega)

/- English proof (translation)
Rewrite using `[Hpk_apply]`. Distinguish the cases in `h : l = mir k r j`. Substitute `h` using the available equality. Simplify using `[mir_mir, sg_mir]`. Establish `h' : ¬ j = mir k r l` using `fun h2 => h (by rw [h2, mir_mir])`.

Rewrite using `[if_neg h, if_neg h']`.
-/
theorem Hpk_apply' (l j : Fin (2 * r + k + 1)) :
    Hpk k r l j = if l = mir k r j then sg k r j else 0 := by
  rw [Hpk_apply]
  by_cases h : l = mir k r j
  · subst h
    simp [mir_mir, sg_mir]
  · have h' : ¬ j = mir k r l := fun h2 => h (by rw [h2, mir_mir])
    rw [if_neg h, if_neg h']

/- English proof (translation)
Simplify using `[Matrix.mul_apply, Hpk_apply, ite_mul]`.
-/
theorem H_mul (Y : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (i j : Fin (2 * r + k + 1)) :
    (Hpk k r * Y) i j = sg k r i * Y (mir k r i) j := by
  simp [Matrix.mul_apply, Hpk_apply, ite_mul]

/- English proof (translation)
Simplify using `[Matrix.mul_apply, Hpk_apply', mul_ite]`.
-/
theorem mul_H (Y : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (i j : Fin (2 * r + k + 1)) :
    (Y * Hpk k r) i j = Y i (mir k r j) * sg k r j := by
  simp [Matrix.mul_apply, Hpk_apply', mul_ite]

/- English proof (translation)
Establish `h : xᴴ * Hpk k r * x = Hpk k r` using `hx`. Establish `h2` using `congrFun (congrFun h i) j`. Rewrite `h2` using `[Matrix.mul_apply (M := xᴴ * Hpk k r) (N := x)]`. Simplify using `only [mul_H, Matrix.conjTranspose_apply] at h2`. Conclude with `h2`.
-/
theorem un_entry {x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hx : x ∈ UH (Hpk k r))
    (i j : Fin (2 * r + k + 1)) :
    ∑ l, star (x (mir k r l) i) * sg k r l * x l j = Hpk k r i j := by
  have h : xᴴ * Hpk k r * x = Hpk k r := hx
  have h2 := congrFun (congrFun h i) j
  rw [Matrix.mul_apply (M := xᴴ * Hpk k r) (N := x)] at h2
  simp only [mul_H, Matrix.conjTranspose_apply] at h2
  exact h2

/- English proof (translation)
Establish `h : xᴴ * Hpk k r * x = Hpk k r` using `hx`. Establish `key : (x - 1)ᴴ * Hpk k r + Hpk k r * (x - 1) + (x - 1)ᴴ * Hpk k r * (x - 1) = 0`. Rewrite using `[Matrix.conjTranspose_sub, Matrix.conjTranspose_one]`. Establish `e : (xᴴ - 1) * Hpk k r + Hpk k r * (x - 1) + (xᴴ - 1) * Hpk k r * (x - 1) = xᴴ * Hpk k r * x - Hpk k r` using `by noncomm_ring`. Rewrite using `[e, h, sub_self]`.

Establish `h2` using `congrFun (congrFun key i) j`. Rewrite `h2` using `[Matrix.add_apply, Matrix.add_apply, Matrix.mul_apply (M := (x - 1)ᴴ * Hpk k r) (N := x - 1), mul_H, H_mul]`. Simplify using `only [mul_H, Matrix.conjTranspose_apply, Matrix.zero_apply] at h2`. Conclude with `h2`.
-/
theorem sub_entry {x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hx : x ∈ UH (Hpk k r))
    (i j : Fin (2 * r + k + 1)) :
    star ((x - 1) (mir k r j) i) * sg k r j + sg k r i * (x - 1) (mir k r i) j +
      ∑ l, star ((x - 1) (mir k r l) i) * sg k r l * (x - 1) l j = 0 := by
  have h : xᴴ * Hpk k r * x = Hpk k r := hx
  have key : (x - 1)ᴴ * Hpk k r + Hpk k r * (x - 1) + (x - 1)ᴴ * Hpk k r * (x - 1) = 0 := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one]
    have e : (xᴴ - 1) * Hpk k r + Hpk k r * (x - 1) + (xᴴ - 1) * Hpk k r * (x - 1) =
        xᴴ * Hpk k r * x - Hpk k r := by noncomm_ring
    rw [e, h, sub_self]
  have h2 := congrFun (congrFun key i) j
  rw [Matrix.add_apply, Matrix.add_apply, Matrix.mul_apply (M := (x - 1)ᴴ * Hpk k r) (N := x - 1),
    mul_H, H_mul] at h2
  simp only [mul_H, Matrix.conjTranspose_apply, Matrix.zero_apply] at h2
  exact h2

/- English proof (translation)
Establish `ha` using `a.isLt`. Unfold `pos`. Rewrite using `[eI_val, if_pos ha]`.
-/
theorem pos_eI (a : Fin r) : pos k r (eI k r a) = a.val := by
  have ha := a.isLt
  unfold pos
  rw [eI_val, if_pos ha]

/- English proof (translation)
Establish `hj` using `j.isLt`. Unfold `pos`. Rewrite using `[wI_val, if_neg (by omega), if_pos (by omega)]`.
-/
theorem pos_wI (j : Fin (k + 1)) : pos k r (wI k r j) = r := by
  have hj := j.isLt
  unfold pos
  rw [wI_val, if_neg (by omega), if_pos (by omega)]

/- English proof (translation)
Establish `ha` using `a.isLt`. Unfold `pos`. Rewrite using `[esI_val, if_neg (by omega), if_neg (by omega)]`. Use linear arithmetic over natural numbers and integers.
-/
theorem pos_esI (a : Fin r) : pos k r (esI k r a) = 2 * r - a.val := by
  have ha := a.isLt
  unfold pos
  rw [esI_val, if_neg (by omega), if_neg (by omega)]
  omega

/- English proof (translation)
Establish `hi` using `i.isLt`. Distinguish the cases in `h1 : i.val < r`. Conclude with `Or.inl ⟨⟨i.val, h1⟩, Fin.ext (by rw [eI_val])⟩`. Distinguish the cases in `h2 : i.val ≤ r + k`. Conclude with `Or.inr (Or.inl ⟨⟨i.val - r, by omega⟩, Fin.ext (by rw [wI_val]; dsimp only; omega)⟩)`.

Conclude with `Or.inr (Or.inr ⟨⟨2 * r + k - i.val, by omega⟩, Fin.ext (by rw [esI_val]; dsimp only; omega)⟩)`.
-/
theorem idx_cases (i : Fin (2 * r + k + 1)) :
    (∃ a, i = eI k r a) ∨ (∃ j, i = wI k r j) ∨ ∃ a, i = esI k r a := by
  have hi := i.isLt
  by_cases h1 : i.val < r
  · exact Or.inl ⟨⟨i.val, h1⟩, Fin.ext (by rw [eI_val])⟩
  by_cases h2 : i.val ≤ r + k
  · exact Or.inr (Or.inl ⟨⟨i.val - r, by omega⟩, Fin.ext (by rw [wI_val]; dsimp only; omega)⟩)
  · exact Or.inr (Or.inr ⟨⟨2 * r + k - i.val, by omega⟩, Fin.ext (by rw [esI_val]; dsimp only; omega)⟩)

/- English proof (translation)
Break down `idx_cases i with ⟨a, rfl⟩ | ⟨j, rfl⟩ | ⟨a, rfl⟩` into its components or cases. Use `a.isLt` as an intermediate fact. Rewrite using `[mir_eI, pos_esI, pos_eI]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[mir_wI, pos_wI]`.

Use linear arithmetic over natural numbers and integers. Use `a.isLt` as an intermediate fact. Rewrite using `[mir_esI, pos_eI, pos_esI]`. Use linear arithmetic over natural numbers and integers.
-/
theorem pos_mir (i : Fin (2 * r + k + 1)) : pos k r (mir k r i) + pos k r i = 2 * r := by
  rcases idx_cases i with ⟨a, rfl⟩ | ⟨j, rfl⟩ | ⟨a, rfl⟩
  · have := a.isLt
    rw [mir_eI, pos_esI, pos_eI]
    omega
  · rw [mir_wI, pos_wI]
    omega
  · have := a.isLt
    rw [mir_esI, pos_eI, pos_esI]
    omega

/- English proof (translation)
Unfold `Dep at h ⊢`. Introduce `i j hij`. Conclude with `h i j (by omega)`.
-/
theorem dep_mono {d e : ℕ} {X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (h : Dep k r e X)
    (hde : d ≤ e) : Dep k r d X := by
  unfold Dep at h ⊢
  intro i j hij
  exact h i j (by omega)

/- English proof (translation)
Take `⟨hU, hcol, -⟩` from `hx`. Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Introduce `s hs t hst`. Establish `hsl` using `s.isLt`.

Establish `htl` using `t.isLt`. Establish `hst' : s.val ≤ t.val` using `hst`. Apply the tactic sequence `have e := un_entry hU (eI k r s) (esI k r t)`. Rewrite `e` using `[Hpk_apply, mir_eI, sg_eI]`. Establish `hsum : ∑ l, star (x (mir k r l) (eI k r s)) * sg k r l * x l (esI k r t) = x (esI k r s) (esI k r t)`.

Rewrite using `[Finset.sum_eq_single (esI k r s)]`. Rewrite using `[mir_esI, sg_esI, hcol s (eI k r s) (le_of_eq (eI_val s).symm)]`. Simplify using the standard rewrite rules. Introduce `l _ hl`. Break down `idx_cases l with ⟨a, rfl⟩ | ⟨j, rfl⟩ | ⟨a, rfl⟩` into its components or cases.

Establish `hal` using `a.isLt`. Rewrite using `[mir_eI, hcol s (esI k r a) (by rw [esI_val]; omega)]`. Rewrite using `[if_neg (fun h' => by have := congrArg Fin.val h'; rw [esI_val, eI_val] at this; omega)]`. Simplify using the standard rewrite rules. Establish `hjl` using `j.isLt`.

Rewrite using `[mir_wI, hcol s (wI k r j) (by rw [wI_val]; omega)]`. Rewrite using `[if_neg (fun h' => by have := congrArg Fin.val h'; rw [wI_val, eI_val] at this; omega)]`. Simplify using the standard rewrite rules. Establish `ha : a ≠ s` using `fun h => hl (by rw [h])`. Establish `hav : a.val ≠ s.val` using `fun h => ha (Fin.ext h)`.

Rewrite using `[mir_esI]`. Break down `Nat.lt_or_gt_of_ne hav with h | h` into its components or cases. Rewrite using `[ih a.val (by omega) a rfl t (show a.val ≤ t.val by omega)]`. Rewrite using `[if_neg (fun h' => by have := congrArg Fin.val h'; omega)]`. Simplify using the standard rewrite rules.

Rewrite using `[hcol s (eI k r a) (by rw [eI_val]; omega)]`. Rewrite using `[if_neg (fun h' => by have := congrArg Fin.val h'; rw [eI_val, eI_val] at this; omega)]`. Simplify using the standard rewrite rules. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.

Rewrite `e` using `[hsum]`. Rewrite using `[e]`. Distinguish the cases in `h : s = t`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Establish `h' : ¬ esI k r t = esI k r s` using `fun h' => h (Fin.ext (by`. Use `congrArg Fin.val h'` as an intermediate fact. Rewrite `this` using `[esI_val, esI_val]`. Use the proof step `omega))`. Rewrite using `[if_neg h, if_neg h']`.
-/
theorem row_es {x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hx : x ∈ Nset k r) (n : ℕ) :
    ∀ (s : Fin r), s.val = n → ∀ t : Fin r, s ≤ t →
      x (esI k r s) (esI k r t) = if s = t then 1 else 0 := by
  obtain ⟨hU, hcol, -⟩ := hx
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro s hs t hst
  have hsl := s.isLt
  have htl := t.isLt
  have hst' : s.val ≤ t.val := hst
  have e := un_entry hU (eI k r s) (esI k r t)
  rw [Hpk_apply, mir_eI, sg_eI] at e
  have hsum : ∑ l, star (x (mir k r l) (eI k r s)) * sg k r l * x l (esI k r t) =
      x (esI k r s) (esI k r t) := by
    rw [Finset.sum_eq_single (esI k r s)]
    · rw [mir_esI, sg_esI, hcol s (eI k r s) (le_of_eq (eI_val s).symm)]
      simp
    · intro l _ hl
      rcases idx_cases l with ⟨a, rfl⟩ | ⟨j, rfl⟩ | ⟨a, rfl⟩
      · have hal := a.isLt
        rw [mir_eI, hcol s (esI k r a) (by rw [esI_val]; omega)]
        rw [if_neg (fun h' => by have := congrArg Fin.val h'; rw [esI_val, eI_val] at this; omega)]
        simp
      · have hjl := j.isLt
        rw [mir_wI, hcol s (wI k r j) (by rw [wI_val]; omega)]
        rw [if_neg (fun h' => by have := congrArg Fin.val h'; rw [wI_val, eI_val] at this; omega)]
        simp
      · have ha : a ≠ s := fun h => hl (by rw [h])
        have hav : a.val ≠ s.val := fun h => ha (Fin.ext h)
        rw [mir_esI]
        rcases Nat.lt_or_gt_of_ne hav with h | h
        · rw [ih a.val (by omega) a rfl t (show a.val ≤ t.val by omega)]
          rw [if_neg (fun h' => by have := congrArg Fin.val h'; omega)]
          simp
        · rw [hcol s (eI k r a) (by rw [eI_val]; omega)]
          rw [if_neg (fun h' => by have := congrArg Fin.val h'; rw [eI_val, eI_val] at this; omega)]
          simp
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [hsum] at e
  rw [e]
  by_cases h : s = t
  · subst h
    simp
  · have h' : ¬ esI k r t = esI k r s := fun h' => h (Fin.ext (by
      have := congrArg Fin.val h'
      rw [esI_val, esI_val] at this
      omega))
    rw [if_neg h, if_neg h']

/- English proof (translation)
Establish `hx'` using `hx`. Take `⟨hU, hcol, hmid⟩` from `hx'`. Unfold `Dep`. Introduce `i j hij`. Establish `key : x i j = if i = j then 1 else 0`.

Break down `idx_cases j with ⟨a, rfl⟩ | ⟨l, rfl⟩ | ⟨b, rfl⟩` into its components or cases. Rewrite `hij` using `[pos_eI]`. Apply `hcol a i` to reduce the goal to its premises. Apply the tactic sequence `have : pos k r i ≤ i.val := by unfold pos; split_ifs <;> omega`. Use linear arithmetic over natural numbers and integers.

Rewrite `hij` using `[pos_wI]`. Establish `hi : r ≤ i.val`. Assume the negation of the conclusion as `hc`. Establish `hc' : i.val < r` using `by omega`. Establish `: pos k r i = i.val` using `by unfold pos; rw [if_pos hc']`.

Use linear arithmetic over natural numbers and integers. Establish `hl` using `l.isLt`. Conclude with `hmid i (wI k r l) (by rw [wI_val]; omega) (by rw [wI_val]; omega) hi`. Rewrite `hij` using `[pos_esI]`. Establish `hb` using `b.isLt`.

Break down `idx_cases i with ⟨a, rfl⟩ | ⟨l, rfl⟩ | ⟨a, rfl⟩` into its components or cases. Rewrite `hij` using `[pos_eI]`. Use `a.isLt` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite `hij` using `[pos_wI]`.

Use linear arithmetic over natural numbers and integers. Rewrite `hij` using `[pos_esI]`. Establish `ha` using `a.isLt`. Establish `hab : a ≤ b` using `by show a.val ≤ b.val; omega`. Rewrite using `[row_es hx a.val a rfl b hab]`.

Distinguish the cases in `h : a = b`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Establish `h' : ¬ esI k r a = esI k r b` using `fun h' => h (Fin.ext (by`. Use `congrArg Fin.val h'` as an intermediate fact.

Rewrite `this` using `[esI_val, esI_val]`. Use the proof step `omega))`. Rewrite using `[if_neg h, if_neg h']`. Rewrite using `[Matrix.sub_apply, key, Matrix.one_apply, sub_self]`.
-/
theorem dep_one {x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hx : x ∈ Nset k r) :
    Dep k r 1 (x - 1) := by
  have hx' := hx
  obtain ⟨hU, hcol, hmid⟩ := hx'
  unfold Dep
  intro i j hij
  have key : x i j = if i = j then 1 else 0 := by
    rcases idx_cases j with ⟨a, rfl⟩ | ⟨l, rfl⟩ | ⟨b, rfl⟩
    · rw [pos_eI] at hij
      apply hcol a i
      have : pos k r i ≤ i.val := by unfold pos; split_ifs <;> omega
      omega
    · rw [pos_wI] at hij
      have hi : r ≤ i.val := by
        by_contra hc
        have hc' : i.val < r := by omega
        have : pos k r i = i.val := by unfold pos; rw [if_pos hc']
        omega
      have hl := l.isLt
      exact hmid i (wI k r l) (by rw [wI_val]; omega) (by rw [wI_val]; omega) hi
    · rw [pos_esI] at hij
      have hb := b.isLt
      rcases idx_cases i with ⟨a, rfl⟩ | ⟨l, rfl⟩ | ⟨a, rfl⟩
      · rw [pos_eI] at hij
        have := a.isLt
        omega
      · rw [pos_wI] at hij
        omega
      · rw [pos_esI] at hij
        have ha := a.isLt
        have hab : a ≤ b := by show a.val ≤ b.val; omega
        rw [row_es hx a.val a rfl b hab]
        by_cases h : a = b
        · subst h
          simp
        · have h' : ¬ esI k r a = esI k r b := fun h' => h (Fin.ext (by
            have := congrArg Fin.val h'
            rw [esI_val, esI_val] at this
            omega))
          rw [if_neg h, if_neg h']
  rw [Matrix.sub_apply, key, Matrix.one_apply, sub_self]

/- English proof (translation)
Establish `hd'` using `hd`. Unfold `Dep at hd'`. Apply the tactic sequence `have h := sub_entry hx (mir k r a) b`. Rewrite `h` using `[mir_mir, sg_mir]`. Establish `hs : ∑ l, star ((x - 1) (mir k r l) (mir k r a)) * sg k r l * (x - 1) l b = 0`.

Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `l _`. Distinguish the cases in `hl : pos k r a < pos k r l`. Rewrite using `[hd' l b (by omega)]`. Simplify using the standard rewrite rules.

Establish `h1` using `pos_mir a`. Establish `h2` using `pos_mir l`. Rewrite using `[hd' (mir k r l) (mir k r a) (by omega)]`. Simplify using the standard rewrite rules. Rewrite `h` using `[hs, add_zero]`.

Conclude with `h`.
-/
theorem mirror {x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hx : x ∈ UH (Hpk k r)) {e : ℕ}
    (he : 1 ≤ e) (hd : Dep k r e (x - 1)) {a b : Fin (2 * r + k + 1)} (hab : pos k r b = pos k r a + e) :
    star ((x - 1) (mir k r b) (mir k r a)) * sg k r b + sg k r a * (x - 1) a b = 0 := by
  have hd' := hd
  unfold Dep at hd'
  have h := sub_entry hx (mir k r a) b
  rw [mir_mir, sg_mir] at h
  have hs : ∑ l, star ((x - 1) (mir k r l) (mir k r a)) * sg k r l * (x - 1) l b = 0 := by
    apply Finset.sum_eq_zero
    intro l _
    by_cases hl : pos k r a < pos k r l
    · rw [hd' l b (by omega)]
      simp
    · have h1 := pos_mir a
      have h2 := pos_mir l
      rw [hd' (mir k r l) (mir k r a) (by omega)]
      simp
  rw [hs, add_zero] at h
  exact h

/- English proof (translation)
Establish `h` using `mirror hx he hd hab`. Rewrite `h` using `[hz, star_zero, zero_mul, zero_add]`. Conclude with `(mul_eq_zero.mp h).resolve_left (sg_ne_zero a)`.
-/
theorem mirror_zero {x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hx : x ∈ UH (Hpk k r)) {e : ℕ}
    (he : 1 ≤ e) (hd : Dep k r e (x - 1)) {a b : Fin (2 * r + k + 1)} (hab : pos k r b = pos k r a + e)
    (hz : (x - 1) (mir k r b) (mir k r a) = 0) : (x - 1) a b = 0 := by
  have h := mirror hx he hd hab
  rw [hz, star_zero, zero_mul, zero_add] at h
  exact (mul_eq_zero.mp h).resolve_left (sg_ne_zero a)

/- English proof (translation)
Introduce `h'`. Apply `h` to reduce the goal to its premises. Apply `Fin.ext` to reduce the goal to its premises. Use `congrArg Fin.val h'` as an intermediate fact. Rewrite `this` using `[eI_val, eI_val]`. Then use the resulting hypothesis.
-/
theorem eI_ne {s t : Fin r} (h : s ≠ t) : eI k r s ≠ eI k r t := by
  intro h'
  apply h
  apply Fin.ext
  have := congrArg Fin.val h'
  rwa [eI_val, eI_val] at this

/- English proof (translation)
Introduce `h`. Use `congrArg Fin.val h` as an intermediate fact. Rewrite `this` using `[eI_val, wI_val]`. Use `s.isLt` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem eI_ne_wI (s : Fin r) (l : Fin (k + 1)) : eI k r s ≠ wI k r l := by
  intro h
  have := congrArg Fin.val h
  rw [eI_val, wI_val] at this
  have := s.isLt
  omega

/- English proof (translation)
Introduce `h`. Use `congrArg Fin.val h` as an intermediate fact. Rewrite `this` using `[eI_val, esI_val]`. Use `s.isLt` as an intermediate fact. Use `t.isLt` as an intermediate fact.

Use linear arithmetic over natural numbers and integers.
-/
theorem eI_ne_esI (s t : Fin r) : eI k r s ≠ esI k r t := by
  intro h
  have := congrArg Fin.val h
  rw [eI_val, esI_val] at this
  have := s.isLt
  have := t.isLt
  omega

/- English proof (translation)
Take `⟨hU, -⟩` from `hx`. Establish `hsub : ∀ i j : Fin (2 * r + k + 1), i ≠ j → (x - 1) i j = x i j` using `fun i j h => by`. Rewrite using `[Matrix.sub_apply, Matrix.one_apply_ne h, sub_zero]`. Establish `fU : ∀ a b : Fin r, a < b → b.val - a.val < d + 1 → (x - 1) (eI k r a) (eI k r b) = 0`. Introduce `a b hab hdeg`.

Establish `h` using `hf (Sum.inl ⟨(a, b), hab⟩) hdeg`. Establish `h' : x (eI k r a) (eI k r b) = 0` using `h`. Rewrite using `[hsub _ _ (eI_ne (ne_of_lt hab)), h']`. Establish `fH : ∀ (a : Fin r) (l : Fin (k + 1)), r - a.val < d + 1 → (x - 1) (eI k r a) (wI k r l) = 0`. Introduce `a l hdeg`.

Establish `h` using `hf (Sum.inr (Sum.inl a)) hdeg`. Establish `h' : (fun j => x (eI k r a) (wI k r j)) = (0 : Fin (k + 1) → ℂ)` using `h`. Rewrite using `[hsub _ _ (eI_ne_wI a l)]`. Conclude with `congrFun h' l`. Establish `fC : ∀ a b : Fin r, a < b → 2 * r - a.val - b.val < d + 1 → (x - 1) (eI k r a) (esI k r b) = 0`.

Introduce `a b hab hdeg`. Establish `h` using `hf (Sum.inr (Sum.inr (Sum.inl ⟨(a, b), hab⟩))) hdeg`. Establish `h' : x (eI k r a) (esI k r b) = 0` using `h`. Rewrite using `[hsub _ _ (eI_ne_esI a b), h']`. Establish `fD : ∀ a : Fin r, 2 * r - 2 * a.val = d → (x - 1) (eI k r a) (esI k r a) = 0`.

Introduce `a hdeg`. Establish `ha` using `a.isLt`. Establish `h` using `hf (Sum.inr (Sum.inr (Sum.inr a))) (show 2 * r - 2 * a.val < d + 1 by omega)`. Establish `him : (x (eI k r a) (esI k r a)).im = 0` using `h`. Establish `hab : pos k r (esI k r a) = pos k r (eI k r a) + d`.

Rewrite using `[pos_esI, pos_eI]`. Use linear arithmetic over natural numbers and integers. Establish `hm` using `mirror hU h1 hd hab`. Rewrite `hm` using `[mir_esI, mir_eI, sg_esI, sg_eI, mul_one, one_mul, hsub _ _ (eI_ne_esI a a)]`. Rewrite using `[hsub _ _ (eI_ne_esI a a)]`.

Apply `Complex.ext` to reduce the goal to its premises. Establish `hre` using `congrArg Complex.re hm`. Simplify using `at hre`. Rewrite using `[Complex.zero_re]`. Combine the linear equalities and inequalities to obtain the conclusion.

Rewrite using `[Complex.zero_im]`. Conclude with `him`. Establish `hd'` using `hd`. Unfold `Dep at hd' ⊢`. Introduce `i j hij`.

Distinguish the cases in `hlt : pos k r j < pos k r i + d`. Conclude with `hd' i j hlt`. Establish `heq : pos k r j = pos k r i + d` using `by omega`. Apply the tactic sequence `rcases idx_cases i with ⟨a, rfl⟩ | ⟨l, rfl⟩ | ⟨a, rfl⟩ <;>`. Break down `idx_cases j with ⟨b, rfl⟩ | ⟨m, rfl⟩ | ⟨b, rfl⟩` into its components or cases.

Establish `hn` using `heq`. Rewrite `hn` using `[pos_eI, pos_eI]`. Conclude with `fU a b (show a.val < b.val by omega) (by omega)`. Establish `hn` using `heq`. Rewrite `hn` using `[pos_wI, pos_eI]`.

Conclude with `fH a m (by omega)`. Establish `hn` using `heq`. Rewrite `hn` using `[pos_esI, pos_eI]`. Establish `ha` using `a.isLt`. Establish `hb` using `b.isLt`.

Break down `lt_trichotomy a.val b.val with h | h | h` into its components or cases. Conclude with `fC a b h (by omega)`. Establish `: a = b` using `Fin.ext h`. Substitute `this` using the available equality. Conclude with `fD _ (by omega)`.

Apply `mirror_zero hU h1 hd heq` to reduce the goal to its premises. Rewrite using `[mir_esI, mir_eI]`. Conclude with `fC b a h (by omega)`. Establish `hn` using `heq`. Rewrite `hn` using `[pos_eI, pos_wI]`.

Use `b.isLt` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hn` using `heq`. Rewrite `hn` using `[pos_wI, pos_wI]`. Use linear arithmetic over natural numbers and integers.

Establish `hn` using `heq`. Rewrite `hn` using `[pos_esI, pos_wI]`. Use `b.isLt` as an intermediate fact. Apply `mirror_zero hU h1 hd heq` to reduce the goal to its premises. Rewrite using `[mir_esI, mir_wI]`.

Conclude with `fH b l (by omega)`. Establish `hn` using `heq`. Rewrite `hn` using `[pos_eI, pos_esI]`. Use `a.isLt` as an intermediate fact. Use `b.isLt` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Establish `hn` using `heq`. Rewrite `hn` using `[pos_wI, pos_esI]`. Use `a.isLt` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Establish `hn` using `heq`. Rewrite `hn` using `[pos_esI, pos_esI]`. Use `a.isLt` as an intermediate fact. Use `b.isLt` as an intermediate fact. Apply `mirror_zero hU h1 hd heq` to reduce the goal to its premises.

Rewrite using `[mir_esI, mir_esI]`. Conclude with `fU b a (show b.val < a.val by omega) (by omega)`.
-/
theorem dep_step {x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hx : x ∈ Nset k r) {d : ℕ}
    (h1 : 1 ≤ d) (hd : Dep k r d (x - 1))
    (hf : ∀ β : Bk r, degB r β < d + 1 → cM k r β (Matrix.of.symm x) = 0) : Dep k r (d + 1) (x - 1) := by
  obtain ⟨hU, -⟩ := hx
  have hsub : ∀ i j : Fin (2 * r + k + 1), i ≠ j → (x - 1) i j = x i j := fun i j h => by
    rw [Matrix.sub_apply, Matrix.one_apply_ne h, sub_zero]
  have fU : ∀ a b : Fin r, a < b → b.val - a.val < d + 1 → (x - 1) (eI k r a) (eI k r b) = 0 := by
    intro a b hab hdeg
    have h := hf (Sum.inl ⟨(a, b), hab⟩) hdeg
    have h' : x (eI k r a) (eI k r b) = 0 := h
    rw [hsub _ _ (eI_ne (ne_of_lt hab)), h']
  have fH : ∀ (a : Fin r) (l : Fin (k + 1)), r - a.val < d + 1 → (x - 1) (eI k r a) (wI k r l) = 0 := by
    intro a l hdeg
    have h := hf (Sum.inr (Sum.inl a)) hdeg
    have h' : (fun j => x (eI k r a) (wI k r j)) = (0 : Fin (k + 1) → ℂ) := h
    rw [hsub _ _ (eI_ne_wI a l)]
    exact congrFun h' l
  have fC : ∀ a b : Fin r, a < b → 2 * r - a.val - b.val < d + 1 →
      (x - 1) (eI k r a) (esI k r b) = 0 := by
    intro a b hab hdeg
    have h := hf (Sum.inr (Sum.inr (Sum.inl ⟨(a, b), hab⟩))) hdeg
    have h' : x (eI k r a) (esI k r b) = 0 := h
    rw [hsub _ _ (eI_ne_esI a b), h']
  have fD : ∀ a : Fin r, 2 * r - 2 * a.val = d → (x - 1) (eI k r a) (esI k r a) = 0 := by
    intro a hdeg
    have ha := a.isLt
    have h := hf (Sum.inr (Sum.inr (Sum.inr a))) (show 2 * r - 2 * a.val < d + 1 by omega)
    have him : (x (eI k r a) (esI k r a)).im = 0 := h
    have hab : pos k r (esI k r a) = pos k r (eI k r a) + d := by
      rw [pos_esI, pos_eI]
      omega
    have hm := mirror hU h1 hd hab
    rw [mir_esI, mir_eI, sg_esI, sg_eI, mul_one, one_mul, hsub _ _ (eI_ne_esI a a)] at hm
    rw [hsub _ _ (eI_ne_esI a a)]
    apply Complex.ext
    · have hre := congrArg Complex.re hm
      simp at hre
      rw [Complex.zero_re]
      linarith
    · rw [Complex.zero_im]
      exact him
  have hd' := hd
  unfold Dep at hd' ⊢
  intro i j hij
  by_cases hlt : pos k r j < pos k r i + d
  · exact hd' i j hlt
  have heq : pos k r j = pos k r i + d := by omega
  rcases idx_cases i with ⟨a, rfl⟩ | ⟨l, rfl⟩ | ⟨a, rfl⟩ <;>
    rcases idx_cases j with ⟨b, rfl⟩ | ⟨m, rfl⟩ | ⟨b, rfl⟩
  · have hn := heq
    rw [pos_eI, pos_eI] at hn
    exact fU a b (show a.val < b.val by omega) (by omega)
  · have hn := heq
    rw [pos_wI, pos_eI] at hn
    exact fH a m (by omega)
  · have hn := heq
    rw [pos_esI, pos_eI] at hn
    have ha := a.isLt
    have hb := b.isLt
    rcases lt_trichotomy a.val b.val with h | h | h
    · exact fC a b h (by omega)
    · have : a = b := Fin.ext h
      subst this
      exact fD _ (by omega)
    · apply mirror_zero hU h1 hd heq
      rw [mir_esI, mir_eI]
      exact fC b a h (by omega)
  · have hn := heq
    rw [pos_eI, pos_wI] at hn
    have := b.isLt
    omega
  · have hn := heq
    rw [pos_wI, pos_wI] at hn
    omega
  · have hn := heq
    rw [pos_esI, pos_wI] at hn
    have := b.isLt
    apply mirror_zero hU h1 hd heq
    rw [mir_esI, mir_wI]
    exact fH b l (by omega)
  · have hn := heq
    rw [pos_eI, pos_esI] at hn
    have := a.isLt
    have := b.isLt
    omega
  · have hn := heq
    rw [pos_wI, pos_esI] at hn
    have := a.isLt
    omega
  · have hn := heq
    rw [pos_esI, pos_esI] at hn
    have := a.isLt
    have := b.isLt
    apply mirror_zero hU h1 hd heq
    rw [mir_esI, mir_esI]
    exact fU b a (show b.val < a.val by omega) (by omega)

end GlobalTheory.SnMass.VolN.DepCoords

namespace GlobalTheory.SnMass.VolN

open DepCoords in

/- English proof (translation)
Proceed by induction on `d with`. Consider the case `zero => exact dep_mono (dep_one hx) (Nat.zero_le 1)`. Consider the case `succ n ih`. Break down `Nat.eq_zero_or_pos n with h0 | hpos` into its components or cases. Substitute `h0` using the available equality.

Conclude with `dep_one hx`. Conclude with `dep_step hx hpos (ih (fun β hβ => hf β (by omega))) hf`.
-/
theorem dep_of_free_coords (k r : ℕ) (x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (d : ℕ)
    (hx : x ∈ Nset k r) (hf : ∀ β : Bk r, degB r β < d → cM k r β (Matrix.of.symm x) = 0) :
    Dep k r d (x - 1) := by
  induction d with
  | zero => exact dep_mono (dep_one hx) (Nat.zero_le 1)
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      exact dep_one hx
    · exact dep_step hx hpos (ih (fun β hβ => hf β (by omega))) hf

end GlobalTheory.SnMass.VolN
