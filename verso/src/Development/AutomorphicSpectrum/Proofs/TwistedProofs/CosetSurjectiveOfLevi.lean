import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLeviNormalizesUnipotentRadical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryBlockTriangularLeviPartUnitary

noncomputable section

open Formalism.UG Matrix GlobalTheory.SatakeWeyl GlobalTheory.InertZeta

namespace GlobalTheory.CompanionTheory.InertCoset

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n : ℕ}

def hf (σ : L →+* L) (x y : Fin n → L) : L := ∑ k, σ (x k.rev) * y k

omit [Valued L (WithZero (Multiplicative ℤ))] in
/- English proof (translation)
Unfold `hf`. Rewrite using `[map_sum]`. Use `Fintype.sum_equiv Fin.revPerm _ _ (fun k => ?_)` and prove the remaining obligations. Simplify using `[hσσ, mul_comm]`.
-/
theorem hf_conj (hσσ : ∀ x, σ (σ x) = x) (x y : Fin n → L) : σ (hf σ x y) = hf σ y x := by
  unfold hf
  rw [map_sum]
  refine Fintype.sum_equiv Fin.revPerm _ _ (fun k => ?_)
  simp [hσσ, mul_comm]

omit [Valued L (WithZero (Multiplicative ℤ))] in
/- English proof (translation)
Simplify using `only [hf, Pi.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib]`.
-/
theorem hf_sub_left (x x' y : Fin n → L) : hf σ (x - x') y = hf σ x y - hf σ x' y := by
  simp only [hf, Pi.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib]

omit [Valued L (WithZero (Multiplicative ℤ))] in
/- English proof (translation)
Simplify using `only [hf, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]`.
-/
theorem hf_sub_right (x y y' : Fin n → L) : hf σ x (y - y') = hf σ x y - hf σ x y' := by
  simp only [hf, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

omit [Valued L (WithZero (Multiplicative ℤ))] in
/- English proof (translation)
Simplify using `only [hf, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]`.
-/
theorem hf_add_left (x x' y : Fin n → L) : hf σ (x + x') y = hf σ x y + hf σ x' y := by
  simp only [hf, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

omit [Valued L (WithZero (Multiplicative ℤ))] in
/- English proof (translation)
Simplify using `only [hf, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl (fun k _ => ?_)` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hf_smul (c c' : L) (x y : Fin n → L) : hf σ (c • x) (c' • y) = σ c * c' * hf σ x y := by
  simp only [hf, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  ring

omit [Valued L (WithZero (Multiplicative ℤ))] in
/- English proof (translation)
Unfold `hf`. Rewrite using `[Finset.sum_eq_single a.rev]`. Simplify using the standard rewrite rules. Introduce `b _ hb`. Establish `hba : b.rev ≠ a` using `fun h => hb (by rw [← h, Fin.rev_rev])`.

Simplify using `[Pi.single_apply, hba]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
theorem hf_single_left (a : Fin n) (y : Fin n → L) : hf σ (Pi.single a 1) y = y a.rev := by
  unfold hf
  rw [Finset.sum_eq_single a.rev]
  · simp
  · intro b _ hb
    have hba : b.rev ≠ a := fun h => hb (by rw [← h, Fin.rev_rev])
    simp [Pi.single_apply, hba]
  · intro h
    exact absurd (Finset.mem_univ _) h

def refl (σ : L →+* L) (d : Fin n → L) : Matrix (Fin n) (Fin n) L := 1 + Matrix.of fun i j => d i * σ (d j.rev)

/- English proof (translation)
Simplify using `only [hf, Pi.add_apply, mul_add, Finset.sum_add_distrib]`.
-/
private theorem hform_add_right_orbital_bounds_conclusion (x y y' : Fin n → L) : hf σ x (y + y') = hf σ x y + hf σ x y' := by
  simp only [hf, Pi.add_apply, mul_add, Finset.sum_add_distrib]

/- English proof (translation)
Unfold `hf`. Rewrite using `[Finset.sum_eq_single a]`. Simplify using the standard rewrite rules. Introduce `b _ hb`. Simplify using `[Pi.single_eq_of_ne hb]`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
private theorem hf_single_one_right (x : Fin n → L) (a : Fin n) : hf σ x (Pi.single a 1) = σ (x a.rev) := by
  unfold hf
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · intro h
    exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Distinguish the cases in `h : i.rev = j`. Substitute `h` using the available equality. Establish `hv : (i : ℕ) + (i.rev : ℕ) + 1 = n` using `by rw [Fin.val_rev]; omega`. Use `show (Pi.single i.rev (1 : L) : Fin n → L) i.rev = (if (i : ℕ) + (i.rev : ℕ) + 1 = n then 1 else 0)`. Rewrite using `[if_pos hv, Pi.single_eq_same]`.

Establish `hv : ¬ ((i : ℕ) + (j : ℕ) + 1 = n)`. Introduce `h'`. Apply `h` to reduce the goal to its premises. Use `ext`. Rewrite using `[Fin.val_rev]`.

Use linear arithmetic over natural numbers and integers. Use `show (Pi.single j (1 : L) : Fin n → L) i.rev = (if (i : ℕ) + (j : ℕ) + 1 = n then 1 else 0)`. Rewrite using `[if_neg hv, Pi.single_eq_of_ne h]`.
-/
private theorem single_one_rev_eq_antiJ_apply (i j : Fin n) : (Pi.single j (1 : L) : Fin n → L) i.rev = antiJ L n i j := by
  by_cases h : i.rev = j
  · subst h
    have hv : (i : ℕ) + (i.rev : ℕ) + 1 = n := by rw [Fin.val_rev]; omega
    show (Pi.single i.rev (1 : L) : Fin n → L) i.rev = (if (i : ℕ) + (i.rev : ℕ) + 1 = n then 1 else 0)
    rw [if_pos hv, Pi.single_eq_same]
  · have hv : ¬ ((i : ℕ) + (j : ℕ) + 1 = n) := by
      intro h'
      apply h
      ext
      rw [Fin.val_rev]
      omega
    show (Pi.single j (1 : L) : Fin n → L) i.rev = (if (i : ℕ) + (j : ℕ) + 1 = n then 1 else 0)
    rw [if_neg hv, Pi.single_eq_of_ne h]

/- English proof (translation)
Establish `key : ∀ l, (cT σ A * antiJ L n) i l = σ (A l.rev i)`. Introduce `l`. Simplify using `only [Matrix.mul_apply, antiJ, cT, Matrix.transpose_apply, Matrix.map_apply]`. Rewrite using `[Finset.sum_eq_single l.rev]`. Establish `hl : (l.rev : ℕ) + l + 1 = n` using `by rw [Fin.val_rev]; omega`.

Rewrite using `[if_pos hl, mul_one]`. Introduce `b _ hb`. Establish `hbl : ¬ ((b : ℕ) + l + 1 = n)`. Introduce `h`. Apply `hb` to reduce the goal to its premises.

Use `ext`. Rewrite using `[Fin.val_rev]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[if_neg hbl, mul_zero]`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ _) h`. Rewrite using `[Matrix.mul_apply]`. Simplify using `only [key]`. Both sides reduce to the same expression.
-/
private theorem cT_mul_antiJ_mul_apply_eq_hf_col (A : Matrix (Fin n) (Fin n) L) (i j : Fin n) :
    (cT σ A * antiJ L n * A) i j = hf σ (fun k => A k i) (fun k => A k j) := by
  have key : ∀ l, (cT σ A * antiJ L n) i l = σ (A l.rev i) := by
    intro l
    simp only [Matrix.mul_apply, antiJ, cT, Matrix.transpose_apply, Matrix.map_apply]
    rw [Finset.sum_eq_single l.rev]
    · have hl : (l.rev : ℕ) + l + 1 = n := by rw [Fin.val_rev]; omega
      rw [if_pos hl, mul_one]
    · intro b _ hb
      have hbl : ¬ ((b : ℕ) + l + 1 = n) := by
        intro h
        apply hb
        ext
        rw [Fin.val_rev]
        omega
      rw [if_neg hbl, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [Matrix.mul_apply]
  simp only [key]
  rfl

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[cT_mul_antiJ_mul_apply_eq_hf_col]`. Establish `hcol : ∀ i, (fun k => refl σ d k i) = Pi.single i 1 + σ (d i.rev) • d`. Introduce `i`. Use extensionality with `k`.

Simplify using `[refl, Matrix.one_apply, Pi.single_apply, mul_comm]`. Rewrite using `[hcol i, hcol j, hf_add_left, hf_single_left]`. Establish `h1 : hf σ (σ (d i.rev) • d) (Pi.single j 1 + σ (d j.rev) • d) = σ (σ (d i.rev)) * hf σ d (Pi.single j 1 + σ (d j.rev) • d)`. Simplify using `using hf_smul (σ := σ) (σ (d i.rev)) 1 d (Pi.single j 1 + σ (d j.rev) • d)`. Rewrite using `[h1, hform_add_right_orbital_bounds_conclusion, hf_single_one_right]`.

Establish `h2 : hf σ d (σ (d j.rev) • d) = σ (d j.rev) * hf σ d d`. Simplify using `using hf_smul (σ := σ) 1 (σ (d j.rev)) d d`. Rewrite using `[h2, hd, hσσ]`. Simplify using `only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]`. Rewrite using `[single_one_rev_eq_antiJ_apply]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem refl_unitary (hσσ : ∀ x, σ (σ x) = x) (d : Fin n → L) (hd : hf σ d d = -2) :
    cT σ (refl σ d) * antiJ L n * refl σ d = antiJ L n := by
  ext i j
  rw [cT_mul_antiJ_mul_apply_eq_hf_col]
  have hcol : ∀ i, (fun k => refl σ d k i) = Pi.single i 1 + σ (d i.rev) • d := by
    intro i
    ext k
    simp [refl, Matrix.one_apply, Pi.single_apply, mul_comm]
  rw [hcol i, hcol j, hf_add_left, hf_single_left]
  have h1 : hf σ (σ (d i.rev) • d) (Pi.single j 1 + σ (d j.rev) • d) =
      σ (σ (d i.rev)) * hf σ d (Pi.single j 1 + σ (d j.rev) • d) := by
    simpa using hf_smul (σ := σ) (σ (d i.rev)) 1 d (Pi.single j 1 + σ (d j.rev) • d)
  rw [h1, hform_add_right_orbital_bounds_conclusion, hf_single_one_right]
  have h2 : hf σ d (σ (d j.rev) • d) = σ (d j.rev) * hf σ d d := by
    simpa using hf_smul (σ := σ) 1 (σ (d j.rev)) d d
  rw [h2, hd, hσσ]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [single_one_rev_eq_antiJ_apply]
  ring

omit [Valued L (WithZero (Multiplicative ℤ))] in
/- English proof (translation)
Use extensionality with `i`. Simplify using `only [refl, Matrix.add_mulVec, Matrix.one_mulVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hf]`. Use `congr 1`. Simplify using `only [Matrix.mulVec, dotProduct, Matrix.of_apply]`. Rewrite using `[Finset.sum_mul]`.

Use `Finset.sum_congr rfl (fun j _ => ?_)` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem refl_mulVec (d x : Fin n → L) : refl σ d *ᵥ x = x + hf σ d x • d := by
  ext i
  simp only [refl, Matrix.add_mulVec, Matrix.one_mulVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hf]
  congr 1
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

/- English proof (translation)
Conclude with `Iff.rfl`.
-/
theorem mem_intL' {x : L} : x ∈ intL L ↔ Valued.v x ≤ 1 := by
  exact Iff.rfl

/- English proof (translation)
Set `X : Matrix (Fin m) (Fin m) (intL L)` to `Matrix.of fun i j => ⟨mat A i j, h1 i j⟩`. Set `Y : Matrix (Fin m) (Fin m) (intL L)` to `Matrix.of fun i j => ⟨(((A : GL (Fin m) L)⁻¹ : GL (Fin m) L) : Matrix (Fin m) (Fin m) L) i j, h2 i j⟩`. Establish `hX : (intL L).subtype.mapMatrix X = mat A`. Use extensionality with `i j`. Both sides reduce to the same expression.

Establish `hY : (intL L).subtype.mapMatrix Y = (((A : GL (Fin m) L)⁻¹ : GL (Fin m) L) : Matrix (Fin m) (Fin m) L)`. Use extensionality with `i j`. Both sides reduce to the same expression. Establish `hinj : Function.Injective ((intL L).subtype.mapMatrix : Matrix (Fin m) (Fin m) (intL L) → Matrix (Fin m) (Fin m) L)` using `Matrix.map_injective Subtype.val_injective`. Establish `hXY : X * Y = 1` using `hinj (by rw [map_mul, map_one, hX, hY]; exact (A : GL (Fin m) L).mul_inv)`.

Establish `hYX : Y * X = 1` using `hinj (by rw [map_mul, map_one, hX, hY]; exact (A : GL (Fin m) L).inv_mul)`. Rewrite using `[KU, Subgroup.mem_subgroupOf]`. Use `show (A : GL (Fin m) L) ∈ GU σ m ⊓ (bc (intL L).subtype).range`. Use `Subgroup.mem_inf.2 ⟨A.2, MonoidHom.mem_range.2 ⟨⟨X, Y, hXY, hYX⟩, ?_⟩⟩` and prove the remaining obligations. Apply `Units.ext` to reduce the goal to its premises.

Use extensionality with `i j`. Both sides reduce to the same expression.
-/
private theorem mem_KU_of_mat_and_inv_mem_intL {m : ℕ} (A : GU σ m) (h1 : ∀ i j, mat A i j ∈ intL L)
    (h2 : ∀ i j, (((A : GL (Fin m) L)⁻¹ : GL (Fin m) L) : Matrix (Fin m) (Fin m) L) i j ∈ intL L) :
    A ∈ KU σ m := by
  let X : Matrix (Fin m) (Fin m) (intL L) := Matrix.of fun i j => ⟨mat A i j, h1 i j⟩
  let Y : Matrix (Fin m) (Fin m) (intL L) :=
    Matrix.of fun i j => ⟨(((A : GL (Fin m) L)⁻¹ : GL (Fin m) L) : Matrix (Fin m) (Fin m) L) i j, h2 i j⟩
  have hX : (intL L).subtype.mapMatrix X = mat A := by
    ext i j
    rfl
  have hY : (intL L).subtype.mapMatrix Y = (((A : GL (Fin m) L)⁻¹ : GL (Fin m) L) : Matrix (Fin m) (Fin m) L) := by
    ext i j
    rfl
  have hinj : Function.Injective
      ((intL L).subtype.mapMatrix : Matrix (Fin m) (Fin m) (intL L) → Matrix (Fin m) (Fin m) L) :=
    Matrix.map_injective Subtype.val_injective
  have hXY : X * Y = 1 := hinj (by rw [map_mul, map_one, hX, hY]; exact (A : GL (Fin m) L).mul_inv)
  have hYX : Y * X = 1 := hinj (by rw [map_mul, map_one, hX, hY]; exact (A : GL (Fin m) L).inv_mul)
  rw [KU, Subgroup.mem_subgroupOf]
  show (A : GL (Fin m) L) ∈ GU σ m ⊓ (bc (intL L).subtype).range
  refine Subgroup.mem_inf.2 ⟨A.2, MonoidHom.mem_range.2 ⟨⟨X, Y, hXY, hYX⟩, ?_⟩⟩
  apply Units.ext
  ext i j
  rfl

/- English proof (translation)
Use `set d := e - w with hd_def`. Establish `hwe : hf σ w e = 1` using `by rw [← hf_conj hσσ, hew, map_one]`. Establish `hdd : hf σ d d = -2`. Rewrite using `[hd_def, hf_sub_left, hf_sub_right, hf_sub_right, hee, hew, hwe, hww]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hde : hf σ d e = -1`. Rewrite using `[hd_def, hf_sub_left, hee, hwe]`. Expand and normalize the polynomial expressions, which then agree. Establish `hinv : ∀ x, refl σ d *ᵥ (refl σ d *ᵥ x) = x`. Introduce `x`.

Rewrite using `[refl_mulVec, refl_mulVec, hform_add_right_orbital_bounds_conclusion]`. Establish `h2 : hf σ d (hf σ d x • d) = hf σ d x * hf σ d d`. Simplify using `using hf_smul (σ := σ) 1 (hf σ d x) d d`. Rewrite using `[h2, hdd]`. Use extensionality with `k`.

Simplify using `only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `hRR : refl σ d * refl σ d = 1`. Apply `Matrix.ext_of_mulVec_single` to reduce the goal to its premises. Introduce `i`.

Rewrite using `[← Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]`. Establish `hσint : ∀ x, x ∈ intL L → σ x ∈ intL L` using `fun x hx => mem_intL'.2 (by rw [hσ]; exact mem_intL'.1 hx)`. Establish `hdint : ∀ i, d i ∈ intL L` using `fun i => (intL L).sub_mem (he i) (hw i)`. Establish `hRint : ∀ i j, refl σ d i j ∈ intL L`. Introduce `i j`.

Simplify using `only [refl, Matrix.add_apply, Matrix.of_apply]`. Use `(intL L).add_mem ?_ ((intL L).mul_mem (hdint i) (hσint _ (hdint j.rev)))` and prove the remaining obligations. Rewrite using `[Matrix.one_apply]`. Use `split_ifs`. Conclude with `(intL L).one_mem`.

Conclude with `(intL L).zero_mem`. Set `R : GL (Fin n) L` to `⟨refl σ d, refl σ d, hRR, hRR⟩`. Establish `hRU : R ∈ GU σ n` using `refl_unitary hσσ d hdd`. Use `⟨⟨R, hRU⟩, mem_KU_of_mat_and_inv_mem_intL _ hRint hRint, ?_⟩` and prove the remaining obligations. Use `show refl σ d *ᵥ e = w`.

Rewrite using `[refl_mulVec, hde, hd_def]`. Use extensionality with `k`. Simplify using `only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_K_of_pair (hσσ : ∀ x, σ (σ x) = x) (hσ : ∀ x, Valued.v (σ x) = Valued.v x) {e w : Fin n → L}
    (he : ∀ i, e i ∈ intL L) (hw : ∀ i, w i ∈ intL L) (hee : hf σ e e = 0) (hww : hf σ w w = 0)
    (hew : hf σ e w = 1) : ∃ k ∈ KU σ n, mat k *ᵥ e = w := by
  set d := e - w with hd_def
  have hwe : hf σ w e = 1 := by rw [← hf_conj hσσ, hew, map_one]
  have hdd : hf σ d d = -2 := by
    rw [hd_def, hf_sub_left, hf_sub_right, hf_sub_right, hee, hew, hwe, hww]
    ring
  have hde : hf σ d e = -1 := by
    rw [hd_def, hf_sub_left, hee, hwe]
    ring
  have hinv : ∀ x, refl σ d *ᵥ (refl σ d *ᵥ x) = x := by
    intro x
    rw [refl_mulVec, refl_mulVec, hform_add_right_orbital_bounds_conclusion]
    have h2 : hf σ d (hf σ d x • d) = hf σ d x * hf σ d d := by
      simpa using hf_smul (σ := σ) 1 (hf σ d x) d d
    rw [h2, hdd]
    ext k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hRR : refl σ d * refl σ d = 1 := by
    apply Matrix.ext_of_mulVec_single
    intro i
    rw [← Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  have hσint : ∀ x, x ∈ intL L → σ x ∈ intL L := fun x hx => mem_intL'.2 (by rw [hσ]; exact mem_intL'.1 hx)
  have hdint : ∀ i, d i ∈ intL L := fun i => (intL L).sub_mem (he i) (hw i)
  have hRint : ∀ i j, refl σ d i j ∈ intL L := by
    intro i j
    simp only [refl, Matrix.add_apply, Matrix.of_apply]
    refine (intL L).add_mem ?_ ((intL L).mul_mem (hdint i) (hσint _ (hdint j.rev)))
    rw [Matrix.one_apply]
    split_ifs
    · exact (intL L).one_mem
    · exact (intL L).zero_mem
  let R : GL (Fin n) L := ⟨refl σ d, refl σ d, hRR, hRR⟩
  have hRU : R ∈ GU σ n := refl_unitary hσσ d hdd
  refine ⟨⟨R, hRU⟩, mem_KU_of_mat_and_inv_mem_intL _ hRint hRint, ?_⟩
  show refl σ d *ᵥ e = w
  rw [refl_mulVec, hde, hd_def]
  ext k
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  ring

/- English proof (translation)
Rewrite using `[Pi.single_apply]`. Use `split_ifs`. Conclude with `hc`. Conclude with `(intL L).zero_mem`.
-/
theorem single_mem (a : Fin n) (c : L) (hc : c ∈ intL L) (i : Fin n) : (Pi.single a c : Fin n → L) i ∈ intL L := by
  rw [Pi.single_apply]
  split_ifs
  · exact hc
  · exact (intL L).zero_mem

/- English proof (translation)
Establish `hN0 : (Fin.last (N + 1) : Fin (N + 2)) ≠ 0` using `last_ne_zero`. Establish `he0int : ∀ k, (Pi.single (0 : Fin (N + 2)) (1 : L) : Fin (N + 2) → L) k ∈ intL L` using `single_mem 0 1 (intL L).one_mem`. Establish `haint : ∀ k, (Pi.single a (1 : L) : Fin (N + 2) → L) k ∈ intL L` using `single_mem a 1 (intL L).one_mem`. Establish `hee0 : hf σ (Pi.single (0 : Fin (N + 2)) (1 : L)) (Pi.single 0 1) = 0`. Rewrite using `[hf_single_left, Fin.rev_zero, Pi.single_eq_of_ne hN0]`.

Distinguish the cases in `ha0 : a = 0`. Substitute `ha0` using the available equality. Use `⟨1, Subgroup.one_mem _, ?_⟩` and prove the remaining obligations. Use `show (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) *ᵥ _ = _`. Rewrite using `[Matrix.one_mulVec]`.

Distinguish the cases in `hal : a = Fin.last (N + 1)`. Substitute `hal` using the available equality. Use `exists_K_of_pair hσσ hσ he0int haint hee0 ?_ ?_` and prove the remaining obligations. Rewrite using `[hf_single_left, Fin.rev_last, Pi.single_eq_of_ne (Ne.symm hN0)]`. Rewrite using `[hf_single_left, Fin.rev_zero, Pi.single_eq_same]`.

Establish `hbr : a.rev.rev = a` using `Fin.rev_rev a`. Establish `hb0 : a.rev ≠ 0`. Introduce `h`. Apply `hal` to reduce the goal to its premises. Rewrite using `[← hbr, h, Fin.rev_zero]`.

Establish `hbl : a.rev ≠ Fin.last (N + 1)`. Introduce `h`. Apply `ha0` to reduce the goal to its premises. Rewrite using `[← hbr, h, Fin.rev_last]`. Establish `hba : a.rev ≠ a` using `fun h => ha h.symm`.

Use `set v : Fin (N + 2) → L := Pi.single (Fin.last (N + 1)) 1 + Pi.single a.rev 1 with hv_def`. Establish `hvint : ∀ k, v k ∈ intL L` using `fun k => (intL L).add_mem (single_mem _ 1 (intL L).one_mem k) (single_mem _ 1 (intL L).one_mem k)`. Establish `hvv : hf σ v v = 0`. Rewrite using `[hv_def, hf_add_left, hf_single_left, hf_single_left, Fin.rev_last, hbr]`. Simplify using `only [Pi.add_apply]`.

Rewrite using `[Pi.single_eq_of_ne (Ne.symm hN0), Pi.single_eq_of_ne (Ne.symm hb0), Pi.single_eq_of_ne hal, Pi.single_eq_of_ne (Ne.symm hba)]`. Expand and normalize the polynomial expressions, which then agree. Establish `h0v : hf σ (Pi.single (0 : Fin (N + 2)) (1 : L)) v = 1`. Rewrite using `[hf_single_left, Fin.rev_zero, hv_def, Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hbl), add_zero]`. Establish `hva : hf σ v (Pi.single a 1) = 1`.

Rewrite using `[hf_single_one_right, hv_def, Pi.add_apply, Pi.single_eq_of_ne hbl, Pi.single_eq_same, zero_add, map_one]`. Establish `haa : hf σ (Pi.single a (1 : L)) (Pi.single a 1) = 0`. Rewrite using `[hf_single_left, Pi.single_eq_of_ne hba]`. Take `⟨k1, hk1, hk1v⟩` from `exists_K_of_pair hσσ hσ he0int hvint hee0 hvv h0v`. Take `⟨k2, hk2, hk2v⟩` from `exists_K_of_pair hσσ hσ hvint haint hvv haa hva`.

Use `⟨k2 * k1, Subgroup.mul_mem _ hk2 hk1, ?_⟩` and prove the remaining obligations. Use `show (mat k2 * mat k1) *ᵥ _ = _`. Rewrite using `[← Matrix.mulVec_mulVec, hk1v, hk2v]`.
-/
theorem exists_K_single {N : ℕ} (hσσ : ∀ x, σ (σ x) = x) (hσ : ∀ x, Valued.v (σ x) = Valued.v x)
    (a : Fin (N + 2)) (ha : a ≠ a.rev) :
    ∃ k ∈ KU σ (N + 2), mat k *ᵥ (Pi.single 0 1 : Fin (N + 2) → L) = Pi.single a 1 := by
  have hN0 : (Fin.last (N + 1) : Fin (N + 2)) ≠ 0 := last_ne_zero
  have he0int : ∀ k, (Pi.single (0 : Fin (N + 2)) (1 : L) : Fin (N + 2) → L) k ∈ intL L :=
    single_mem 0 1 (intL L).one_mem
  have haint : ∀ k, (Pi.single a (1 : L) : Fin (N + 2) → L) k ∈ intL L := single_mem a 1 (intL L).one_mem
  have hee0 : hf σ (Pi.single (0 : Fin (N + 2)) (1 : L)) (Pi.single 0 1) = 0 := by
    rw [hf_single_left, Fin.rev_zero, Pi.single_eq_of_ne hN0]
  by_cases ha0 : a = 0
  · subst ha0
    refine ⟨1, Subgroup.one_mem _, ?_⟩
    show (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) *ᵥ _ = _
    rw [Matrix.one_mulVec]
  by_cases hal : a = Fin.last (N + 1)
  · subst hal
    refine exists_K_of_pair hσσ hσ he0int haint hee0 ?_ ?_
    · rw [hf_single_left, Fin.rev_last, Pi.single_eq_of_ne (Ne.symm hN0)]
    · rw [hf_single_left, Fin.rev_zero, Pi.single_eq_same]
  have hbr : a.rev.rev = a := Fin.rev_rev a
  have hb0 : a.rev ≠ 0 := by
    intro h
    apply hal
    rw [← hbr, h, Fin.rev_zero]
  have hbl : a.rev ≠ Fin.last (N + 1) := by
    intro h
    apply ha0
    rw [← hbr, h, Fin.rev_last]
  have hba : a.rev ≠ a := fun h => ha h.symm
  set v : Fin (N + 2) → L := Pi.single (Fin.last (N + 1)) 1 + Pi.single a.rev 1 with hv_def
  have hvint : ∀ k, v k ∈ intL L := fun k =>
    (intL L).add_mem (single_mem _ 1 (intL L).one_mem k) (single_mem _ 1 (intL L).one_mem k)
  have hvv : hf σ v v = 0 := by
    rw [hv_def, hf_add_left, hf_single_left, hf_single_left, Fin.rev_last, hbr]
    simp only [Pi.add_apply]
    rw [Pi.single_eq_of_ne (Ne.symm hN0), Pi.single_eq_of_ne (Ne.symm hb0), Pi.single_eq_of_ne hal,
      Pi.single_eq_of_ne (Ne.symm hba)]
    ring
  have h0v : hf σ (Pi.single (0 : Fin (N + 2)) (1 : L)) v = 1 := by
    rw [hf_single_left, Fin.rev_zero, hv_def, Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hbl),
      add_zero]
  have hva : hf σ v (Pi.single a 1) = 1 := by
    rw [hf_single_one_right, hv_def, Pi.add_apply, Pi.single_eq_of_ne hbl, Pi.single_eq_same, zero_add, map_one]
  have haa : hf σ (Pi.single a (1 : L)) (Pi.single a 1) = 0 := by
    rw [hf_single_left, Pi.single_eq_of_ne hba]
  obtain ⟨k1, hk1, hk1v⟩ := exists_K_of_pair hσσ hσ he0int hvint hee0 hvv h0v
  obtain ⟨k2, hk2, hk2v⟩ := exists_K_of_pair hσσ hσ hvint haint hvv haa hva
  refine ⟨k2 * k1, Subgroup.mul_mem _ hk2 hk1, ?_⟩
  show (mat k2 * mat k1) *ᵥ _ = _
  rw [← Matrix.mulVec_mulVec, hk1v, hk2v]

/- English proof (translation)
Establish `hz0 : z ≠ 0`. Introduce `h`. Rewrite `hz` using `[h, map_zero]`. Conclude with `zero_ne_one hz`. Establish `hσz0 : σ z ≠ 0`.

Introduce `h`. Apply `hz0` to reduce the goal to its premises. Rewrite using `[← hσσ z, h, map_zero]`. Establish `hN0 : (Fin.last (N + 1) : Fin (N + 2)) ≠ 0` using `last_ne_zero`. Set `δ : Fin (N + 2) → L` to `fun i => if i = 0 then z else if i = Fin.last (N + 1) then (σ z)⁻¹ else 1`.

Set `δ' : Fin (N + 2) → L` to `fun i => if i = 0 then z⁻¹ else if i = Fin.last (N + 1) then σ z else 1`. Establish `hδδ' : ∀ i, δ i * δ' i = 1`. Introduce `i`. Simplify using `only [δ, δ']`. Use `split_ifs`.

Conclude with `mul_inv_cancel₀ hz0`. Conclude with `inv_mul_cancel₀ hσz0`. Conclude with `one_mul 1`. Establish `hD1 : Matrix.diagonal δ * Matrix.diagonal δ' = 1`. Rewrite using `[Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`.

Use `congr 1`. Use function extensionality and compare the values at `i`. Conclude with `hδδ' i`. Establish `hD2 : Matrix.diagonal δ' * Matrix.diagonal δ = 1`. Rewrite using `[Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`.

Use `congr 1`. Use function extensionality and compare the values at `i`. Rewrite using `[mul_comm]`. Conclude with `hδδ' i`. Set `D : GL (Fin (N + 2)) L` to `⟨Matrix.diagonal δ, Matrix.diagonal δ', hD1, hD2⟩`.

Establish `hunit : ∀ i, σ (δ i) * δ i.rev = 1`. Introduce `i`. Break down `idx_cases i with rfl | ⟨j, rfl⟩ | rfl` into its components or cases. Simplify using `only [δ, Fin.rev_zero, if_pos rfl, if_neg hN0]`. Conclude with `mul_inv_cancel₀ hσz0`.

Establish `h1 : mid j ≠ 0` using `mid_ne_zero j`. Establish `h2 : mid j ≠ Fin.last (N + 1)` using `mid_ne_last j`. Establish `h3 : (mid j).rev ≠ 0` using `by rw [← mid_rev]; exact mid_ne_zero _`. Establish `h4 : (mid j).rev ≠ Fin.last (N + 1)` using `by rw [← mid_rev]; exact mid_ne_last _`. Simplify using `only [δ, if_neg h1, if_neg h2, if_neg h3, if_neg h4, map_one, one_mul]`.

Simplify using `only [δ, Fin.rev_last, hN0, if_false, if_true, eq_self_iff_true, ↓reduceIte, map_inv₀, hσσ]`. Conclude with `inv_mul_cancel₀ hz0`. Establish `hDU : D ∈ GU σ (N + 2)` using `by show cT σ (Matrix.diagonal δ) * antiJ L (N + 2) * Matrix.diagonal δ = antiJ L (N + 2)`. Use extensionality with `i j`. Rewrite using `[cT_mul_antiJ_mul_apply_eq_hf_col]`.

Establish `hc : ∀ i, (fun k => Matrix.diagonal δ k i) = δ i • Pi.single i 1`. Introduce `i`. Use extensionality with `k`. Distinguish the cases in `hk : k = i`. Substitute `hk` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[Matrix.diagonal_apply_ne _ hk, Pi.single_eq_of_ne hk]`. Rewrite using `[hc i, hc j, hf_smul, hf_single_left, ← single_one_rev_eq_antiJ_apply]`. Distinguish the cases in `h : i.rev = j`. Substitute `h` using the available equality.

Rewrite using `[Pi.single_eq_same, mul_one, hunit i]`. Rewrite using `[Pi.single_eq_of_ne h, mul_zero]`. Establish `hint : ∀ x : L, Valued.v x = 1 → x ∈ intL L` using `fun x hx => mem_intL'.2 (le_of_eq hx)`. Establish `hδint : ∀ i, δ i ∈ intL L`. Introduce `i`.

Simplify using `only [δ]`. Use `split_ifs`. Conclude with `hint _ hz`. Conclude with `hint _ (by rw [map_inv₀, hσ, hz, inv_one])`. Conclude with `(intL L).one_mem`.

Establish `hδ'int : ∀ i, δ' i ∈ intL L`. Introduce `i`. Simplify using `only [δ']`. Use `split_ifs`. Conclude with `hint _ (by rw [map_inv₀, hz, inv_one])`.

Conclude with `hint _ (by rw [hσ, hz])`. Conclude with `(intL L).one_mem`. Establish `hdiag : ∀ (f : Fin (N + 2) → L), (∀ i, f i ∈ intL L) → ∀ i j, Matrix.diagonal f i j ∈ intL L`. Introduce `f hf i j`. Rewrite using `[Matrix.diagonal_apply]`.

Use `split_ifs`. Conclude with `hf i`. Conclude with `(intL L).zero_mem`. Use `⟨⟨D, hDU⟩, mem_KU_of_mat_and_inv_mem_intL _ (hdiag δ hδint) (hdiag δ' hδ'int), ?_⟩` and prove the remaining obligations. Use `show Matrix.diagonal δ *ᵥ _ = _`.

Use extensionality with `k`. Rewrite using `[Matrix.mulVec_diagonal]`. Distinguish the cases in `hk : k = 0`. Substitute `hk` using the available equality. Simplify using `[δ]`.

Simplify using `[Pi.single_eq_of_ne hk]`.
-/
theorem exists_K_unit {N : ℕ} (hσσ : ∀ x, σ (σ x) = x) (hσ : ∀ x, Valued.v (σ x) = Valued.v x) {z : L}
    (hz : Valued.v z = 1) :
    ∃ k ∈ KU σ (N + 2), mat k *ᵥ (Pi.single 0 1 : Fin (N + 2) → L) = z • Pi.single 0 1 := by
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, map_zero] at hz
    exact zero_ne_one hz
  have hσz0 : σ z ≠ 0 := by
    intro h
    apply hz0
    rw [← hσσ z, h, map_zero]
  have hN0 : (Fin.last (N + 1) : Fin (N + 2)) ≠ 0 := last_ne_zero
  let δ : Fin (N + 2) → L := fun i => if i = 0 then z else if i = Fin.last (N + 1) then (σ z)⁻¹ else 1
  let δ' : Fin (N + 2) → L := fun i => if i = 0 then z⁻¹ else if i = Fin.last (N + 1) then σ z else 1
  have hδδ' : ∀ i, δ i * δ' i = 1 := by
    intro i
    simp only [δ, δ']
    split_ifs
    · exact mul_inv_cancel₀ hz0
    · exact inv_mul_cancel₀ hσz0
    · exact one_mul 1
  have hD1 : Matrix.diagonal δ * Matrix.diagonal δ' = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact hδδ' i
  have hD2 : Matrix.diagonal δ' * Matrix.diagonal δ = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    rw [mul_comm]
    exact hδδ' i
  let D : GL (Fin (N + 2)) L := ⟨Matrix.diagonal δ, Matrix.diagonal δ', hD1, hD2⟩
  have hunit : ∀ i, σ (δ i) * δ i.rev = 1 := by
    intro i
    rcases idx_cases i with rfl | ⟨j, rfl⟩ | rfl
    · simp only [δ, Fin.rev_zero, if_pos rfl, if_neg hN0]
      exact mul_inv_cancel₀ hσz0
    · have h1 : mid j ≠ 0 := mid_ne_zero j
      have h2 : mid j ≠ Fin.last (N + 1) := mid_ne_last j
      have h3 : (mid j).rev ≠ 0 := by rw [← mid_rev]; exact mid_ne_zero _
      have h4 : (mid j).rev ≠ Fin.last (N + 1) := by rw [← mid_rev]; exact mid_ne_last _
      simp only [δ, if_neg h1, if_neg h2, if_neg h3, if_neg h4, map_one, one_mul]
    · simp only [δ, Fin.rev_last, hN0, if_false, if_true, eq_self_iff_true, ↓reduceIte, map_inv₀, hσσ]
      exact inv_mul_cancel₀ hz0
  have hDU : D ∈ GU σ (N + 2) := by
    show cT σ (Matrix.diagonal δ) * antiJ L (N + 2) * Matrix.diagonal δ = antiJ L (N + 2)
    ext i j
    rw [cT_mul_antiJ_mul_apply_eq_hf_col]
    have hc : ∀ i, (fun k => Matrix.diagonal δ k i) = δ i • Pi.single i 1 := by
      intro i
      ext k
      by_cases hk : k = i
      · subst hk
        simp
      · simp [Matrix.diagonal_apply_ne _ hk, Pi.single_eq_of_ne hk]
    rw [hc i, hc j, hf_smul, hf_single_left, ← single_one_rev_eq_antiJ_apply]
    by_cases h : i.rev = j
    · subst h
      rw [Pi.single_eq_same, mul_one, hunit i]
    · rw [Pi.single_eq_of_ne h, mul_zero]
  have hint : ∀ x : L, Valued.v x = 1 → x ∈ intL L := fun x hx => mem_intL'.2 (le_of_eq hx)
  have hδint : ∀ i, δ i ∈ intL L := by
    intro i
    simp only [δ]
    split_ifs
    · exact hint _ hz
    · exact hint _ (by rw [map_inv₀, hσ, hz, inv_one])
    · exact (intL L).one_mem
  have hδ'int : ∀ i, δ' i ∈ intL L := by
    intro i
    simp only [δ']
    split_ifs
    · exact hint _ (by rw [map_inv₀, hz, inv_one])
    · exact hint _ (by rw [hσ, hz])
    · exact (intL L).one_mem
  have hdiag : ∀ (f : Fin (N + 2) → L), (∀ i, f i ∈ intL L) → ∀ i j, Matrix.diagonal f i j ∈ intL L := by
    intro f hf i j
    rw [Matrix.diagonal_apply]
    split_ifs
    · exact hf i
    · exact (intL L).zero_mem
  refine ⟨⟨D, hDU⟩, mem_KU_of_mat_and_inv_mem_intL _ (hdiag δ hδint) (hdiag δ' hδ'int), ?_⟩
  show Matrix.diagonal δ *ᵥ _ = _
  ext k
  rw [Matrix.mulVec_diagonal]
  by_cases hk : k = 0
  · subst hk
    simp [δ]
  · simp [Pi.single_eq_of_ne hk]

/- English proof (translation)
Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Establish `hi0 : i₀ = i₀.rev`. Assume the negation of the conclusion as `h`. Conclude with `hcon i₀ h hi`.

Establish `hlt : ∀ k, k ≠ i₀ → Valued.v (σ (w k.rev) * w k) < 1`. Introduce `k hk`. Establish `hkr : k ≠ k.rev`. Introduce `h`. Apply `hk` to reduce the goal to its premises.

Use `ext`. Establish `h1` using `congrArg Fin.val h`. Establish `h2` using `congrArg Fin.val hi0`. Rewrite `h1`, `h2` using `[Fin.val_rev]`. Use linear arithmetic over natural numbers and integers.

Establish `hwk : Valued.v (w k) < 1` using `lt_of_le_of_ne (mem_intL'.1 (hw k)) (hcon k hkr)`. Rewrite using `[map_mul, hσ]`. Combine the equalities or inequalities in the displayed calculation. Establish `hsplit : hf σ w w = σ (w i₀.rev) * w i₀ + ∑ k ∈ Finset.univ.erase i₀, σ (w k.rev) * w k`. Unfold `hf`.

Conclude with `(Finset.add_sum_erase _ _ (Finset.mem_univ i₀)).symm`. Establish `hrest : Valued.v (∑ k ∈ Finset.univ.erase i₀, σ (w k.rev) * w k) < 1` using `Valuation.map_sum_lt _ one_ne_zero (fun k hk => hlt k (Finset.ne_of_mem_erase hk))`. Establish `hterm : Valued.v (σ (w i₀.rev) * w i₀) = 1`. Rewrite using `[map_mul, hσ, ← hi0, hi, one_mul]`. Establish `hv1 : Valued.v (hf σ w w) = 1`.

Rewrite using `[hsplit, Valuation.map_add_eq_of_lt_left _ (by rw [hterm]; exact hrest), hterm]`. Rewrite `hv1` using `[hww, map_zero]`. Conclude with `zero_ne_one hv1`.
-/
theorem exists_unit_coord {w : Fin n → L} (hσ : ∀ x, Valued.v (σ x) = Valued.v x) (hw : ∀ i, w i ∈ intL L)
    (hww : hf σ w w = 0) {i₀ : Fin n} (hi : Valued.v (w i₀) = 1) : ∃ i, i ≠ i.rev ∧ Valued.v (w i) = 1 := by
  by_contra hcon
  push Not at hcon
  have hi0 : i₀ = i₀.rev := by
    by_contra h
    exact hcon i₀ h hi
  have hlt : ∀ k, k ≠ i₀ → Valued.v (σ (w k.rev) * w k) < 1 := by
    intro k hk
    have hkr : k ≠ k.rev := by
      intro h
      apply hk
      ext
      have h1 := congrArg Fin.val h
      have h2 := congrArg Fin.val hi0
      rw [Fin.val_rev] at h1 h2
      omega
    have hwk : Valued.v (w k) < 1 := lt_of_le_of_ne (mem_intL'.1 (hw k)) (hcon k hkr)
    rw [map_mul, hσ]
    calc Valued.v (w k.rev) * Valued.v (w k) ≤ 1 * Valued.v (w k) :=
          mul_le_mul' (mem_intL'.1 (hw _)) le_rfl
      _ < 1 := by rw [one_mul]; exact hwk
  have hsplit : hf σ w w = σ (w i₀.rev) * w i₀ + ∑ k ∈ Finset.univ.erase i₀, σ (w k.rev) * w k := by
    unfold hf
    exact (Finset.add_sum_erase _ _ (Finset.mem_univ i₀)).symm
  have hrest : Valued.v (∑ k ∈ Finset.univ.erase i₀, σ (w k.rev) * w k) < 1 :=
    Valuation.map_sum_lt _ one_ne_zero (fun k hk => hlt k (Finset.ne_of_mem_erase hk))
  have hterm : Valued.v (σ (w i₀.rev) * w i₀) = 1 := by
    rw [map_mul, hσ, ← hi0, hi, one_mul]
  have hv1 : Valued.v (hf σ w w) = 1 := by
    rw [hsplit, Valuation.map_add_eq_of_lt_left _ (by rw [hterm]; exact hrest), hterm]
  rw [hww, map_zero] at hv1
  exact zero_ne_one hv1

/- English proof (translation)
Establish `hh : cT σ (mat h) * antiJ L n * mat h = antiJ L n` using `h.2`. Establish `key : ∀ l, (cT σ (mat h) * antiJ L n) i l = σ (mat h l.rev i)`. Introduce `l`. Simplify using `only [Matrix.mul_apply, antiJ, cT, Matrix.transpose_apply, Matrix.map_apply]`. Rewrite using `[Finset.sum_eq_single l.rev]`.

Establish `hl : (l.rev : ℕ) + l + 1 = n` using `by rw [Fin.val_rev]; omega`. Rewrite using `[if_pos hl, mul_one]`. Introduce `b _ hb`. Establish `hbl : ¬ ((b : ℕ) + l + 1 = n)`. Introduce `h`.

Apply `hb` to reduce the goal to its premises. Use `ext`. Rewrite using `[Fin.val_rev]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[if_neg hbl, mul_zero]`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.mul_apply]`. Simplify using `only [key]`.

Both sides reduce to the same expression. Use `_ = antiJ L n i j := by rw [hh]`.
-/
theorem hf_col (h : GU σ n) (i j : Fin n) :
    hf σ (fun k => mat h k i) (fun k => mat h k j) = antiJ L n i j := by
  have hh : cT σ (mat h) * antiJ L n * mat h = antiJ L n := h.2
  have key : ∀ l, (cT σ (mat h) * antiJ L n) i l = σ (mat h l.rev i) := by
    intro l
    simp only [Matrix.mul_apply, antiJ, cT, Matrix.transpose_apply, Matrix.map_apply]
    rw [Finset.sum_eq_single l.rev]
    · have hl : (l.rev : ℕ) + l + 1 = n := by rw [Fin.val_rev]; omega
      rw [if_pos hl, mul_one]
    · intro b _ hb
      have hbl : ¬ ((b : ℕ) + l + 1 = n) := by
        intro h
        apply hb
        ext
        rw [Fin.val_rev]
        omega
      rw [if_neg hbl, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  calc hf σ (fun k => mat h k i) (fun k => mat h k j) = (cT σ (mat h) * antiJ L n * mat h) i j := by
        rw [Matrix.mul_apply]
        simp only [key]
        rfl
    _ = antiJ L n i j := by rw [hh]

/- English proof (translation)
Establish `hvx : Valued.v x ≠ 0` using `(Valuation.ne_zero_iff _).2 hx`. Take `⟨γ, hγ⟩` from `WithZero.ne_zero_iff_exists.1 hvx`. Use `⟨Multiplicative.toAdd γ, ?_⟩` and prove the remaining obligations. Establish `h1 : WithZero.exp (-1 : ℤ) = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))` using `rfl`. Rewrite using `[map_mul, map_zpow₀, hϖ, ← hγ, h1, ← WithZero.coe_zpow, ← WithZero.coe_mul, ← WithZero.coe_one, WithZero.coe_inj]`.

Apply `Multiplicative.toAdd.injective` to reduce the goal to its premises. Simplify using the standard rewrite rules.
-/
theorem exists_zpow_unit {ϖ x : L} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (hx : x ≠ 0) :
    ∃ s : ℤ, Valued.v (ϖ ^ s * x) = 1 := by
  have hvx : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  obtain ⟨γ, hγ⟩ := WithZero.ne_zero_iff_exists.1 hvx
  refine ⟨Multiplicative.toAdd γ, ?_⟩
  have h1 : WithZero.exp (-1 : ℤ) = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := rfl
  rw [map_mul, map_zpow₀, hϖ, ← hγ, h1, ← WithZero.coe_zpow, ← WithZero.coe_mul, ← WithZero.coe_one, WithZero.coe_inj]
  apply Multiplicative.toAdd.injective
  simp

/- English proof (translation)
Use extensionality with `k`. Simplify using `[Matrix.mulVec, dotProduct, Pi.single_apply]`.
-/
private theorem mulVec_single_one_eq_col (M : Matrix (Fin n) (Fin n) L) (j : Fin n) : M *ᵥ Pi.single j 1 = fun k => M k j := by
  ext k
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

/- English proof (translation)
Take `⟨hσσ, hσ, -, hϖ, -⟩` from `hU`. Use `set u : Fin (N + 2) → L := mat g⁻¹ *ᵥ Pi.single 0 1 with hu_def`. Establish `hgu : mat g *ᵥ u = Pi.single 0 1`. Rewrite using `[hu_def, Matrix.mulVec_mulVec]`. Establish `h1 : mat g * mat g⁻¹ = 1` using `by show mat (g * g⁻¹) = 1`.

Rewrite using `[mul_inv_cancel]`. Both sides reduce to the same expression. Rewrite using `[h1, Matrix.one_mulVec]`. Establish `huu : hf σ u u = 0`. Establish `h` using `hf_col g⁻¹ 0 0`.

Rewrite using `[hu_def, mulVec_single_one_eq_col, h]`. Use `show (if ((0 : Fin (N + 2)) : ℕ) + ((0 : Fin (N + 2)) : ℕ) + 1 = N + 2 then (1 : L) else 0) = 0`. Rewrite using `[if_neg (by simp only [Fin.val_zero]; omega)]`. Take `⟨i₁, -, hi₁⟩` from `Finset.exists_max_image Finset.univ (fun k => Valued.v (u k)) Finset.univ_nonempty`. Establish `hu1 : u i₁ ≠ 0`.

Introduce `h0`. Establish `hall : u = 0`. Use extensionality with `k`. Establish `hk` using `hi₁ k (Finset.mem_univ _)`. Rewrite `hk` using `[h0, map_zero]`.

Conclude with `(Valuation.zero_iff _).1 (le_antisymm hk zero_le')`. Rewrite `hgu` using `[hall, Matrix.mulVec_zero]`. Establish `h2` using `congrFun hgu 0`. Simplify using `at h2`. Take `⟨t, ht⟩` from `exists_zpow_unit hϖ hu1`.

Use `set w : Fin (N + 2) → L := (ϖ ^ t) • u with hw_def`. Establish `hwint : ∀ k, w k ∈ intL L`. Introduce `k`. Apply `mem_intL'.2` to reduce the goal to its premises. Simplify using `only [hw_def, Pi.smul_apply, smul_eq_mul, map_mul]`.

Rewrite `ht` using `[map_mul]`. Combine the equalities or inequalities in the displayed calculation. Establish `hwi₁ : Valued.v (w i₁) = 1`. Simplify `ht` using `[hw_def]`. Establish `hww : hf σ w w = 0`.

Rewrite using `[hw_def, hf_smul, huu, mul_zero]`. Take `⟨i, hi, hwi⟩` from `exists_unit_coord hσ hwint hww hwi₁`. Use `set u0 := w i with hu0`. Establish `hu00 : u0 ≠ 0`. Introduce `h`.

Rewrite `hwi` using `[h, map_zero]`. Conclude with `zero_ne_one hwi`. Use `set z : L := (σ u0)⁻¹ with hz_def`. Establish `hzv : Valued.v z = 1` using `by rw [hz_def, map_inv₀, hσ, hwi, inv_one]`. Use `set e : Fin (N + 2) → L := z • Pi.single i.rev 1 with he_def`.

Establish `heint : ∀ k, e k ∈ intL L`. Introduce `k`. Rewrite using `[he_def, Pi.smul_apply, smul_eq_mul]`. Conclude with `(intL L).mul_mem (mem_intL'.2 (le_of_eq hzv)) (single_mem _ 1 (intL L).one_mem k)`. Establish `hee : hf σ e e = 0`.

Rewrite using `[he_def, hf_smul, hf_single_left, Fin.rev_rev, Pi.single_eq_of_ne hi, mul_zero]`. Establish `hew : hf σ e w = 1`. Establish `h` using `hf_smul (σ := σ) z 1 (Pi.single i.rev 1) w`. Rewrite `h` using `[one_smul, mul_one, hf_single_left, Fin.rev_rev]`. Rewrite using `[he_def, h, hz_def, map_inv₀, hσσ]`.

Conclude with `inv_mul_cancel₀ hu00`. Take `⟨k1, hk1, hk1e⟩` from `exists_K_of_pair hσσ hσ heint hwint hee hww hew`. Establish `hirev : i.rev ≠ i.rev.rev`. Rewrite using `[Fin.rev_rev]`. Conclude with `fun h => hi h.symm`.

Take `⟨k2, hk2, hk2e⟩` from `exists_K_single hσσ hσ i.rev hirev`. Take `⟨k3, hk3, hk3e⟩` from `exists_K_unit (N := N) hσσ hσ hzv`. Use `⟨t, k1 * k2 * k3, Subgroup.mul_mem _ (Subgroup.mul_mem _ hk1 hk2) hk3, ?_⟩` and prove the remaining obligations. Establish `hkv : mat (k1 * k2 * k3) *ᵥ Pi.single 0 1 = w` using `by show (mat k1 * mat k2 * mat k3) *ᵥ _ = _`. Rewrite using `[← Matrix.mulVec_mulVec, hk3e, Matrix.mulVec_smul, ← Matrix.mulVec_mulVec, hk2e, ← Matrix.mulVec_smul, ← he_def, hk1e]`.

Establish `hfinal : mat (g * (k1 * k2 * k3)) *ᵥ Pi.single 0 1 = ϖ ^ t • Pi.single 0 1` using `by show (mat g * mat (k1 * k2 * k3)) *ᵥ _ = _`. Rewrite using `[← Matrix.mulVec_mulVec, hkv, hw_def, Matrix.mulVec_smul, hgu]`. Introduce `j`. Establish `hj` using `congrFun hfinal j`. Rewrite `hj` using `[mulVec_single_one_eq_col]`.

Simplify using `using hj`.
-/
theorem exists_col {ϖ : L} {q N : ℕ} (hU : IsUnramInv ϖ σ q) (g : GU σ (N + 2)) :
    ∃ s : ℤ, ∃ k ∈ KU σ (N + 2), ∀ i, mat (g * k) i 0 = ϖ ^ s * (Pi.single 0 1 : Fin (N + 2) → L) i := by
  obtain ⟨hσσ, hσ, -, hϖ, -⟩ := hU
  set u : Fin (N + 2) → L := mat g⁻¹ *ᵥ Pi.single 0 1 with hu_def
  have hgu : mat g *ᵥ u = Pi.single 0 1 := by
    rw [hu_def, Matrix.mulVec_mulVec]
    have h1 : mat g * mat g⁻¹ = 1 := by
      show mat (g * g⁻¹) = 1
      rw [mul_inv_cancel]
      rfl
    rw [h1, Matrix.one_mulVec]
  have huu : hf σ u u = 0 := by
    have h := hf_col g⁻¹ 0 0
    rw [hu_def, mulVec_single_one_eq_col, h]
    show (if ((0 : Fin (N + 2)) : ℕ) + ((0 : Fin (N + 2)) : ℕ) + 1 = N + 2 then (1 : L) else 0) = 0
    rw [if_neg (by simp only [Fin.val_zero]; omega)]
  obtain ⟨i₁, -, hi₁⟩ := Finset.exists_max_image Finset.univ (fun k => Valued.v (u k)) Finset.univ_nonempty
  have hu1 : u i₁ ≠ 0 := by
    intro h0
    have hall : u = 0 := by
      ext k
      have hk := hi₁ k (Finset.mem_univ _)
      rw [h0, map_zero] at hk
      exact (Valuation.zero_iff _).1 (le_antisymm hk zero_le')
    rw [hall, Matrix.mulVec_zero] at hgu
    have h2 := congrFun hgu 0
    simp at h2
  obtain ⟨t, ht⟩ := exists_zpow_unit hϖ hu1
  set w : Fin (N + 2) → L := (ϖ ^ t) • u with hw_def
  have hwint : ∀ k, w k ∈ intL L := by
    intro k
    apply mem_intL'.2
    simp only [hw_def, Pi.smul_apply, smul_eq_mul, map_mul]
    rw [map_mul] at ht
    calc Valued.v (ϖ ^ t) * Valued.v (u k) ≤ Valued.v (ϖ ^ t) * Valued.v (u i₁) :=
          mul_le_mul' le_rfl (hi₁ k (Finset.mem_univ _))
      _ = 1 := ht
  have hwi₁ : Valued.v (w i₁) = 1 := by
    simpa [hw_def] using ht
  have hww : hf σ w w = 0 := by
    rw [hw_def, hf_smul, huu, mul_zero]
  obtain ⟨i, hi, hwi⟩ := exists_unit_coord hσ hwint hww hwi₁
  set u0 := w i with hu0
  have hu00 : u0 ≠ 0 := by
    intro h
    rw [h, map_zero] at hwi
    exact zero_ne_one hwi
  set z : L := (σ u0)⁻¹ with hz_def
  have hzv : Valued.v z = 1 := by rw [hz_def, map_inv₀, hσ, hwi, inv_one]
  set e : Fin (N + 2) → L := z • Pi.single i.rev 1 with he_def
  have heint : ∀ k, e k ∈ intL L := by
    intro k
    rw [he_def, Pi.smul_apply, smul_eq_mul]
    exact (intL L).mul_mem (mem_intL'.2 (le_of_eq hzv)) (single_mem _ 1 (intL L).one_mem k)
  have hee : hf σ e e = 0 := by
    rw [he_def, hf_smul, hf_single_left, Fin.rev_rev, Pi.single_eq_of_ne hi, mul_zero]
  have hew : hf σ e w = 1 := by
    have h := hf_smul (σ := σ) z 1 (Pi.single i.rev 1) w
    rw [one_smul, mul_one, hf_single_left, Fin.rev_rev] at h
    rw [he_def, h, hz_def, map_inv₀, hσσ]
    exact inv_mul_cancel₀ hu00
  obtain ⟨k1, hk1, hk1e⟩ := exists_K_of_pair hσσ hσ heint hwint hee hww hew
  have hirev : i.rev ≠ i.rev.rev := by
    rw [Fin.rev_rev]
    exact fun h => hi h.symm
  obtain ⟨k2, hk2, hk2e⟩ := exists_K_single hσσ hσ i.rev hirev
  obtain ⟨k3, hk3, hk3e⟩ := exists_K_unit (N := N) hσσ hσ hzv
  refine ⟨t, k1 * k2 * k3, Subgroup.mul_mem _ (Subgroup.mul_mem _ hk1 hk2) hk3, ?_⟩
  have hkv : mat (k1 * k2 * k3) *ᵥ Pi.single 0 1 = w := by
    show (mat k1 * mat k2 * mat k3) *ᵥ _ = _
    rw [← Matrix.mulVec_mulVec, hk3e, Matrix.mulVec_smul, ← Matrix.mulVec_mulVec, hk2e, ← Matrix.mulVec_smul,
      ← he_def, hk1e]
  have hfinal : mat (g * (k1 * k2 * k3)) *ᵥ Pi.single 0 1 = ϖ ^ t • Pi.single 0 1 := by
    show (mat g * mat (k1 * k2 * k3)) *ᵥ _ = _
    rw [← Matrix.mulVec_mulVec, hkv, hw_def, Matrix.mulVec_smul, hgu]
  intro j
  have hj := congrFun hfinal j
  rw [mulVec_single_one_eq_col] at hj
  simpa using hj

section Levi

variable {N : ℕ} {ϖ : L} {a a' : ℤ} {g g' : GU σ N} {m m' : GU σ (N + 2)}

/- English proof (translation)
Take `⟨hm, hm0, hl, hmid⟩` from `h`. Take `⟨hm', hm0', hl', hmid'⟩` from `h'`. Establish `hmz : ∀ i j, blk N i ≠ blk N j → mat m i j = 0` using `hm`. Establish `hmat : mat (m * m') = mat m * mat m'` using `rfl`. Use `⟨Subgroup.mul_mem _ hm hm', ?_, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[hmat, Matrix.mul_apply, sum_idx, Finset.sum_eq_zero (fun j _ => by rw [hmz 0 (mid j) (by simp [blk_zero, blk_mid]), zero_mul]), hmz 0 (Fin.last (N + 1)) (by simp [blk_zero, blk_last]), hm0, hm0', zpow_add₀ h0]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hmat, Matrix.mul_apply, sum_idx, Finset.sum_eq_zero (fun j _ => by rw [hmz (Fin.last (N + 1)) (mid j) (by simp [blk_last, blk_mid]), zero_mul]), hmz (Fin.last (N + 1)) 0 (by simp [blk_zero, blk_last]), hl, hl', neg_add, zpow_add₀ h0]`. Expand and normalize the polynomial expressions, which then agree. Introduce `i j`.

Rewrite using `[hmat, Matrix.mul_apply, sum_idx, hmz (mid i) 0 (by simp [blk_zero, blk_mid]), hmz (mid i) (Fin.last (N + 1)) (by simp [blk_mid, blk_last])]`. Simplify using `only [zero_mul, zero_add, add_zero, hmid, hmid']`. Use `show _ = (mat g * mat g') i j`. Rewrite using `[Matrix.mul_apply]`.
-/
theorem isLeviElt_mul (h0 : ϖ ≠ 0) (h : IsLeviElt ϖ a g m) (h' : IsLeviElt ϖ a' g' m') :
    IsLeviElt ϖ (a + a') (g * g') (m * m') := by
  obtain ⟨hm, hm0, hl, hmid⟩ := h
  obtain ⟨hm', hm0', hl', hmid'⟩ := h'
  have hmz : ∀ i j, blk N i ≠ blk N j → mat m i j = 0 := hm
  have hmat : mat (m * m') = mat m * mat m' := rfl
  refine ⟨Subgroup.mul_mem _ hm hm', ?_, ?_, ?_⟩
  · rw [hmat, Matrix.mul_apply, sum_idx,
      Finset.sum_eq_zero (fun j _ => by rw [hmz 0 (mid j) (by simp [blk_zero, blk_mid]), zero_mul]),
      hmz 0 (Fin.last (N + 1)) (by simp [blk_zero, blk_last]), hm0, hm0', zpow_add₀ h0]
    ring
  · rw [hmat, Matrix.mul_apply, sum_idx,
      Finset.sum_eq_zero (fun j _ => by rw [hmz (Fin.last (N + 1)) (mid j) (by simp [blk_last, blk_mid]), zero_mul]),
      hmz (Fin.last (N + 1)) 0 (by simp [blk_zero, blk_last]), hl, hl', neg_add, zpow_add₀ h0]
    ring
  · intro i j
    rw [hmat, Matrix.mul_apply, sum_idx, hmz (mid i) 0 (by simp [blk_zero, blk_mid]),
      hmz (mid i) (Fin.last (N + 1)) (by simp [blk_mid, blk_last])]
    simp only [zero_mul, zero_add, add_zero, hmid, hmid']
    show _ = (mat g * mat g') i j
    rw [Matrix.mul_apply]

/- English proof (translation)
Take `⟨hm, h0, hl, hmid⟩` from `h`. Take `⟨hm', h0', hl', hmid'⟩` from `h'`. Establish `hmz : ∀ i j, blk N i ≠ blk N j → mat m i j = 0` using `hm`. Establish `hmz' : ∀ i j, blk N i ≠ blk N j → mat m' i j = 0` using `hm'`. Establish `key : ∀ i j, mat m i j = mat m' i j`.

Introduce `i j`. Distinguish the cases in `hij : blk N i = blk N j`. Apply the tactic sequence `rcases idx_cases i with rfl | ⟨i', rfl⟩ | rfl <;> rcases idx_cases j with rfl | ⟨j', rfl⟩ | rfl all_goals first`. Consider the case `(rw [h0, h0'])`. Consider the case `(rw [hmid, hmid'])`.

Consider the case `(rw [hl, hl'])`. Consider the case `(simp [blk_zero, blk_mid, blk_last] at hij)`. Rewrite using `[hmz i j hij, hmz' i j hij]`. Conclude with `Subtype.ext (Units.ext (Matrix.ext key))`.
-/
theorem isLeviElt_unique (h : IsLeviElt ϖ a g m) (h' : IsLeviElt ϖ a g m') : m = m' := by
  obtain ⟨hm, h0, hl, hmid⟩ := h
  obtain ⟨hm', h0', hl', hmid'⟩ := h'
  have hmz : ∀ i j, blk N i ≠ blk N j → mat m i j = 0 := hm
  have hmz' : ∀ i j, blk N i ≠ blk N j → mat m' i j = 0 := hm'
  have key : ∀ i j, mat m i j = mat m' i j := by
    intro i j
    by_cases hij : blk N i = blk N j
    · rcases idx_cases i with rfl | ⟨i', rfl⟩ | rfl <;> rcases idx_cases j with rfl | ⟨j', rfl⟩ | rfl
      all_goals first
        | (rw [h0, h0'])
        | (rw [hmid, hmid'])
        | (rw [hl, hl'])
        | (simp [blk_zero, blk_mid, blk_last] at hij)
    · rw [hmz i j hij, hmz' i j hij]
  exact Subtype.ext (Units.ext (Matrix.ext key))

end Levi

/- English proof (translation)
Rewrite `hA` using `[KU, Subgroup.mem_subgroupOf, intPts]`. Take `⟨-, hr⟩` from `Subgroup.mem_inf.1 hA`. Take `⟨g', hg'⟩` from `MonoidHom.mem_range.1 hr`. Use `show ((A : GL (Fin m) L) : Matrix (Fin m) (Fin m) L) i j ∈ intL L`. Rewrite using `[← hg']`.

Conclude with `((g' : Matrix (Fin m) (Fin m) (intL L)) i j).2`.
-/
private theorem mat_apply_mem_intL_of_mem_KU {m : ℕ} {A : GU σ m} (hA : A ∈ KU σ m) (i j : Fin m) : mat A i j ∈ intL L := by
  rw [KU, Subgroup.mem_subgroupOf, intPts] at hA
  obtain ⟨-, hr⟩ := Subgroup.mem_inf.1 hA
  obtain ⟨g', hg'⟩ := MonoidHom.mem_range.1 hr
  show ((A : GL (Fin m) L) : Matrix (Fin m) (Fin m) L) i j ∈ intL L
  rw [← hg']
  exact ((g' : Matrix (Fin m) (Fin m) (intL L)) i j).2

/- English proof (translation)
Take `⟨heL, he0, hel, hem⟩` from `he`. Establish `hez : ∀ i j, blk N i ≠ blk N j → mat e i j = 0` using `heL`. Distinguish the cases in `hij : blk N i = blk N j`. Apply the tactic sequence `rcases idx_cases i with rfl | ⟨i', rfl⟩ | rfl <;> rcases idx_cases j with rfl | ⟨j', rfl⟩ | rfl all_goals first`. Consider the case `(rw [he0, zpow_zero]; exact (intL L).one_mem)`.

Consider the case `(rw [hem]; exact mat_apply_mem_intL_of_mem_KU hh _ _)`. Consider the case `(rw [hel, neg_zero, zpow_zero]; exact (intL L).one_mem)`. Consider the case `(simp [blk_zero, blk_mid, blk_last] at hij)`. Rewrite using `[hez i j hij]`. Conclude with `(intL L).zero_mem`.
-/
private theorem mat_apply_mem_intL_of_isLeviElt_of_mem_KU {N : ℕ} {ϖ : L} {h : GU σ N} {e : GU σ (N + 2)} (he : IsLeviElt ϖ 0 h e)
    (hh : h ∈ KU σ N) (i j : Fin (N + 2)) : mat e i j ∈ intL L := by
  obtain ⟨heL, he0, hel, hem⟩ := he
  have hez : ∀ i j, blk N i ≠ blk N j → mat e i j = 0 := heL
  by_cases hij : blk N i = blk N j
  · rcases idx_cases i with rfl | ⟨i', rfl⟩ | rfl <;> rcases idx_cases j with rfl | ⟨j', rfl⟩ | rfl
    all_goals first
      | (rw [he0, zpow_zero]; exact (intL L).one_mem)
      | (rw [hem]; exact mat_apply_mem_intL_of_mem_KU hh _ _)
      | (rw [hel, neg_zero, zpow_zero]; exact (intL L).one_mem)
      | (simp [blk_zero, blk_mid, blk_last] at hij)
  · rw [hez i j hij]
    exact (intL L).zero_mem

/- English proof (translation)
Establish `hU'` using `hU`. Take `⟨hσσ, hσ, hσϖ, hϖ, -⟩` from `hU'`. Establish `hϖ0 : ϖ ≠ 0`. Introduce `h`. Rewrite `hϖ` using `[h, map_zero]`.

Conclude with `WithZero.zero_ne_coe hϖ`. Establish `hcol0 : (fun k => mat p k 0) = ϖ ^ s • Pi.single 0 1`. Use function extensionality and compare the values at `k`. Rewrite using `[hp k]`. Both sides reduce to the same expression.

Establish `hσs : σ (ϖ ^ s) = ϖ ^ s` using `by rw [map_zpow₀, hσϖ]`. Establish `hrow : ∀ b, ϖ ^ s * mat p (Fin.last (N + 1)) b = (Pi.single b (1 : L) : Fin (N + 2) → L) (Fin.last (N + 1))`. Introduce `b`. Establish `h` using `hf_col p 0 b`. Rewrite `h` using `[hcol0, ← single_one_rev_eq_antiJ_apply, Fin.rev_zero]`.

Establish `h2` using `hf_smul (σ := σ) (ϖ ^ s) 1 (Pi.single 0 1) (fun k => mat p k b)`. Rewrite `h2` using `[one_smul, mul_one, hf_single_left, Fin.rev_zero, hσs]`. Rewrite using `[← h, h2]`. Establish `hlast0 : ∀ b, b ≠ Fin.last (N + 1) → mat p (Fin.last (N + 1)) b = 0`. Introduce `b hb`.

Establish `h` using `hrow b`. Rewrite `h` using `[Pi.single_eq_of_ne (Ne.symm hb)]`. Conclude with `(mul_eq_zero.1 h).resolve_left (zpow_ne_zero _ hϖ0)`. Establish `hlastlast : mat p (Fin.last (N + 1)) (Fin.last (N + 1)) = ϖ ^ (-s)`. Establish `h` using `hrow (Fin.last (N + 1))`.

Rewrite `h` using `[Pi.single_eq_same]`. Rewrite using `[_root_.zpow_neg]`. Conclude with `eq_inv_of_mul_eq_one_right h`. Establish `hp0 : ∀ i, i ≠ 0 → mat p i 0 = 0` using `fun i hi => by rw [hp i, Pi.single_eq_of_ne hi, mul_zero]`. Establish `htri : (mat p).BlockTriangular (blk N)`.

Introduce `i j hij`. Apply the tactic sequence `rcases idx_cases i with rfl | ⟨i', rfl⟩ | rfl <;> rcases idx_cases j with rfl | ⟨j', rfl⟩ | rfl`. Apply the tactic sequence `all_goals simp only [blk_zero, blk_mid, blk_last] at hij`. Apply the tactic sequence `all_goals first`. Consider the case `omega`.

Consider the case `exact hp0 _ (mid_ne_zero _)`. Consider the case `exact hp0 _ last_ne_zero`. Consider the case `exact hlast0 _ (mid_ne_last _)`. Establish `hrevblk : ∀ a : Fin (N + 2), blk N a.rev = 2 - blk N a`. Introduce `a`.

Break down `idx_cases a with rfl | ⟨i', rfl⟩ | rfl` into its components or cases. Rewrite using `[Fin.rev_zero, blk_last, blk_zero]`. Rewrite using `[← mid_rev, blk_mid, blk_mid]`. Rewrite using `[Fin.rev_last, blk_zero, blk_last]`. Establish `hsym : ∀ a b : Fin (N + 2), blk N a = blk N b → blk N a.rev = blk N b.rev`.

Introduce `a b hab`. Rewrite using `[hrevblk, hrevblk, hab]`. Take `⟨m0, hm0L, hm0eq, hm0r⟩` from `leviPart L σ (N + 2) (blk N) hsym p htri`. Establish `hm0z : ∀ i j, blk N i ≠ blk N j → mat m0 i j = 0` using `hm0L`. Establish `hm0iL : m0⁻¹ ∈ leviU σ (blk N)` using `Subgroup.inv_mem _ hm0L`.

Establish `hm0iz : ∀ i j, blk N i ≠ blk N j → mat m0⁻¹ i j = 0` using `hm0iL`. Establish `hmidprod : ∀ (a b : GU σ (N + 2)), (∀ i j, blk N i ≠ blk N j → mat a i j = 0) → ∀ i j, mat (a * b) (mid i) (mid j) = ∑ k, mat a (mid i) (mid k) * mat b (mid k) (mid j)`. Introduce `a b ha i j`. Use `show (mat a * mat b) (mid i) (mid j) = _`. Rewrite using `[Matrix.mul_apply, sum_idx, ha (mid i) 0 (by rw [blk_mid, blk_zero]; decide), ha (mid i) (Fin.last (N + 1)) (by rw [blk_mid, blk_last]; decide), zero_mul, zero_mul, zero_add, add_zero]`.

Establish `hone : ∀ i j : Fin N, (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) (mid i) (mid j) = (1 : Matrix (Fin N) (Fin N) L) i j`. Introduce `i j`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Rewrite using `[Matrix.one_apply_ne h, Matrix.one_apply_ne (fun h' => h (mid_injective h'))]`. Set `G : Matrix (Fin N) (Fin N) L` to `fun i j => mat m0 (mid i) (mid j)`. Set `G' : Matrix (Fin N) (Fin N) L` to `fun i j => mat m0⁻¹ (mid i) (mid j)`. Establish `hGG' : G * G' = 1`. Use extensionality with `i j`.

Rewrite using `[Matrix.mul_apply]`. Use `show ∑ k, mat m0 (mid i) (mid k) * mat m0⁻¹ (mid k) (mid j) = _`. Rewrite using `[← hmidprod m0 m0⁻¹ hm0z, mul_inv_cancel]`. Conclude with `hone i j`. Establish `hG'G : G' * G = 1`.

Use extensionality with `i j`. Rewrite using `[Matrix.mul_apply]`. Use `show ∑ k, mat m0⁻¹ (mid i) (mid k) * mat m0 (mid k) (mid j) = _`. Rewrite using `[← hmidprod m0⁻¹ m0 hm0iz, inv_mul_cancel]`. Conclude with `hone i j`.

Establish `hGU : cT σ G * antiJ L N * G = antiJ L N`. Use extensionality with `i j`. Rewrite using `[cT_mul_antiJ_mul_apply_eq_hf_col]`. Establish `h` using `hf_col m0 (mid i) (mid j)`. Establish `hJ : antiJ L (N + 2) (mid i) (mid j) = antiJ L N i j` using `by show (if ((mid i : Fin (N + 2)) : ℕ) + ((mid j : Fin (N + 2)) : ℕ) + 1 = N + 2 then (1 : L) else 0) = (if (i : ℕ) + (j : ℕ) + 1 = N then 1 else 0)`.

Rewrite using `[val_mid, val_mid]`. Distinguish the cases in `hc : (i : ℕ) + (j : ℕ) + 1 = N`. Rewrite using `[if_pos (by omega), if_pos hc]`. Rewrite using `[if_neg (by omega), if_neg hc]`. Rewrite `h` using `[hJ]`.

Rewrite using `[← h]`. Use `show ∑ k, σ (G k.rev i) * G k j = ∑ l, σ (mat m0 l.rev (mid i)) * mat m0 l (mid j)`. Rewrite using `[sum_idx, hm0z 0 (mid j) (by rw [blk_zero, blk_mid]; decide), hm0z (Fin.last (N + 1)) (mid j) (by rw [blk_last, blk_mid]; decide), mul_zero, mul_zero, zero_add, add_zero]`. Use `Finset.sum_congr rfl (fun k _ => ?_)` and prove the remaining obligations. Rewrite using `[← mid_rev]`.

Set `g0 : GU σ N` to `⟨⟨G, G', hGG', hG'G⟩, hGU⟩`. Use `⟨QuotientGroup.mk g0, fun m hm => ?_⟩` and prove the remaining obligations. Take `⟨k0, hk0⟩` from `QuotientGroup.mk_out_eq_mul (KU σ N) g0`. Take `⟨e, he⟩` from `hLE L ϖ σ q N hU 0 (k0 : GU σ N)`. Take `⟨e', he'⟩` from `hLE L ϖ σ q N hU 0 ((k0 : GU σ N)⁻¹)`.

Establish `hm0lev : IsLeviElt ϖ s g0 m0`. Use `⟨hm0L, ?_, ?_, fun i j => rfl⟩` and prove the remaining obligations. Rewrite using `[hm0eq 0 0 rfl, hp 0, Pi.single_eq_same, mul_one]`. Rewrite using `[hm0eq _ _ rfl, hlastlast]`. Establish `hprod` using `isLeviElt_mul hϖ0 hm0lev he`.

Rewrite `hprod` using `[add_zero, ← hk0]`. Establish `hmeq : m = m0 * e` using `isLeviElt_unique hm hprod`. Establish `hee' : e * e' = 1`. Establish `h1` using `isLeviElt_mul hϖ0 he he'`. Rewrite `h1` using `[add_zero, mul_inv_cancel]`.

Establish `h2 : IsLeviElt ϖ 0 (1 : GU σ N) (1 : GU σ (N + 2))`. Use `⟨Subgroup.one_mem _, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `show (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) 0 0 = ϖ ^ (0 : ℤ)`. Simplify using the standard rewrite rules. Use `show (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) (Fin.last (N + 1)) (Fin.last (N + 1)) = ϖ ^ (-(0 : ℤ))`.

Simplify using the standard rewrite rules. Introduce `i j`. Conclude with `hone i j`. Conclude with `isLeviElt_unique h1 h2`. Establish `he'eq : e' = e⁻¹` using `eq_inv_of_mul_eq_one_right hee'`.

Establish `heK : e ∈ KU σ (N + 2)`. Use `mem_KU_of_mat_and_inv_mem_intL e (mat_apply_mem_intL_of_isLeviElt_of_mem_KU he k0.2) ?_` and prove the remaining obligations. Introduce `i j`. Establish `h` using `mat_apply_mem_intL_of_isLeviElt_of_mem_KU he' (Subgroup.inv_mem _ k0.2) i j`. Rewrite `h` using `[he'eq]`.

Conclude with `h`. Establish `heL'` using `he`. Take `⟨heL, -⟩` from `heL'`. Use `⟨e⁻¹ * (m0⁻¹ * p) * e, ?_, e⁻¹, Subgroup.inv_mem _ heK, ?_⟩` and prove the remaining obligations. Establish `h` using `(leviRad L σ (N + 2) (blk N) hσ e⁻¹ (Subgroup.inv_mem _ heL) (m0⁻¹ * p) hm0r).1`.

Rewrite `h` using `[inv_inv]`. Conclude with `h`. Rewrite using `[hmeq] group`.
-/
theorem levi_step (hLE : LeviExists) {ϖ : L} {q N : ℕ} (hU : IsUnramInv ϖ σ q) {s : ℤ} (p : GU σ (N + 2))
    (hp : ∀ i, mat p i 0 = ϖ ^ s * (Pi.single 0 1 : Fin (N + 2) → L) i) :
    ∃ y : GU σ N ⧸ KU σ N, ∀ m, IsLeviElt ϖ s y.out m →
      ∃ u ∈ radQ σ N, ∃ k ∈ KU σ (N + 2), p = m * u * k := by
  have hU' := hU
  obtain ⟨hσσ, hσ, hσϖ, hϖ, -⟩ := hU'
  have hϖ0 : ϖ ≠ 0 := by
    intro h
    rw [h, map_zero] at hϖ
    exact WithZero.zero_ne_coe hϖ
  have hcol0 : (fun k => mat p k 0) = ϖ ^ s • Pi.single 0 1 := by
    funext k
    rw [hp k]
    rfl
  have hσs : σ (ϖ ^ s) = ϖ ^ s := by rw [map_zpow₀, hσϖ]
  have hrow : ∀ b, ϖ ^ s * mat p (Fin.last (N + 1)) b = (Pi.single b (1 : L) : Fin (N + 2) → L) (Fin.last (N + 1)) := by
    intro b
    have h := hf_col p 0 b
    rw [hcol0, ← single_one_rev_eq_antiJ_apply, Fin.rev_zero] at h
    have h2 := hf_smul (σ := σ) (ϖ ^ s) 1 (Pi.single 0 1) (fun k => mat p k b)
    rw [one_smul, mul_one, hf_single_left, Fin.rev_zero, hσs] at h2
    rw [← h, h2]
  have hlast0 : ∀ b, b ≠ Fin.last (N + 1) → mat p (Fin.last (N + 1)) b = 0 := by
    intro b hb
    have h := hrow b
    rw [Pi.single_eq_of_ne (Ne.symm hb)] at h
    exact (mul_eq_zero.1 h).resolve_left (zpow_ne_zero _ hϖ0)
  have hlastlast : mat p (Fin.last (N + 1)) (Fin.last (N + 1)) = ϖ ^ (-s) := by
    have h := hrow (Fin.last (N + 1))
    rw [Pi.single_eq_same] at h
    rw [_root_.zpow_neg]
    exact eq_inv_of_mul_eq_one_right h
  have hp0 : ∀ i, i ≠ 0 → mat p i 0 = 0 := fun i hi => by rw [hp i, Pi.single_eq_of_ne hi, mul_zero]
  have htri : (mat p).BlockTriangular (blk N) := by
    intro i j hij
    rcases idx_cases i with rfl | ⟨i', rfl⟩ | rfl <;> rcases idx_cases j with rfl | ⟨j', rfl⟩ | rfl
    all_goals simp only [blk_zero, blk_mid, blk_last] at hij
    all_goals first
      | omega
      | exact hp0 _ (mid_ne_zero _)
      | exact hp0 _ last_ne_zero
      | exact hlast0 _ (mid_ne_last _)
  have hrevblk : ∀ a : Fin (N + 2), blk N a.rev = 2 - blk N a := by
    intro a
    rcases idx_cases a with rfl | ⟨i', rfl⟩ | rfl
    · rw [Fin.rev_zero, blk_last, blk_zero]
    · rw [← mid_rev, blk_mid, blk_mid]
    · rw [Fin.rev_last, blk_zero, blk_last]
  have hsym : ∀ a b : Fin (N + 2), blk N a = blk N b → blk N a.rev = blk N b.rev := by
    intro a b hab
    rw [hrevblk, hrevblk, hab]
  obtain ⟨m0, hm0L, hm0eq, hm0r⟩ := leviPart L σ (N + 2) (blk N) hsym p htri
  have hm0z : ∀ i j, blk N i ≠ blk N j → mat m0 i j = 0 := hm0L
  have hm0iL : m0⁻¹ ∈ leviU σ (blk N) := Subgroup.inv_mem _ hm0L
  have hm0iz : ∀ i j, blk N i ≠ blk N j → mat m0⁻¹ i j = 0 := hm0iL
  have hmidprod : ∀ (a b : GU σ (N + 2)), (∀ i j, blk N i ≠ blk N j → mat a i j = 0) → ∀ i j,
      mat (a * b) (mid i) (mid j) = ∑ k, mat a (mid i) (mid k) * mat b (mid k) (mid j) := by
    intro a b ha i j
    show (mat a * mat b) (mid i) (mid j) = _
    rw [Matrix.mul_apply, sum_idx, ha (mid i) 0 (by rw [blk_mid, blk_zero]; decide),
      ha (mid i) (Fin.last (N + 1)) (by rw [blk_mid, blk_last]; decide), zero_mul, zero_mul, zero_add, add_zero]
  have hone : ∀ i j : Fin N, (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) (mid i) (mid j) =
      (1 : Matrix (Fin N) (Fin N) L) i j := by
    intro i j
    by_cases h : i = j
    · subst h
      simp
    · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne (fun h' => h (mid_injective h'))]
  let G : Matrix (Fin N) (Fin N) L := fun i j => mat m0 (mid i) (mid j)
  let G' : Matrix (Fin N) (Fin N) L := fun i j => mat m0⁻¹ (mid i) (mid j)
  have hGG' : G * G' = 1 := by
    ext i j
    rw [Matrix.mul_apply]
    show ∑ k, mat m0 (mid i) (mid k) * mat m0⁻¹ (mid k) (mid j) = _
    rw [← hmidprod m0 m0⁻¹ hm0z, mul_inv_cancel]
    exact hone i j
  have hG'G : G' * G = 1 := by
    ext i j
    rw [Matrix.mul_apply]
    show ∑ k, mat m0⁻¹ (mid i) (mid k) * mat m0 (mid k) (mid j) = _
    rw [← hmidprod m0⁻¹ m0 hm0iz, inv_mul_cancel]
    exact hone i j
  have hGU : cT σ G * antiJ L N * G = antiJ L N := by
    ext i j
    rw [cT_mul_antiJ_mul_apply_eq_hf_col]
    have h := hf_col m0 (mid i) (mid j)
    have hJ : antiJ L (N + 2) (mid i) (mid j) = antiJ L N i j := by
      show (if ((mid i : Fin (N + 2)) : ℕ) + ((mid j : Fin (N + 2)) : ℕ) + 1 = N + 2 then (1 : L) else 0) =
        (if (i : ℕ) + (j : ℕ) + 1 = N then 1 else 0)
      rw [val_mid, val_mid]
      by_cases hc : (i : ℕ) + (j : ℕ) + 1 = N
      · rw [if_pos (by omega), if_pos hc]
      · rw [if_neg (by omega), if_neg hc]
    rw [hJ] at h
    rw [← h]
    show ∑ k, σ (G k.rev i) * G k j = ∑ l, σ (mat m0 l.rev (mid i)) * mat m0 l (mid j)
    rw [sum_idx, hm0z 0 (mid j) (by rw [blk_zero, blk_mid]; decide),
      hm0z (Fin.last (N + 1)) (mid j) (by rw [blk_last, blk_mid]; decide), mul_zero, mul_zero, zero_add, add_zero]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [← mid_rev]
  let g0 : GU σ N := ⟨⟨G, G', hGG', hG'G⟩, hGU⟩
  refine ⟨QuotientGroup.mk g0, fun m hm => ?_⟩
  obtain ⟨k0, hk0⟩ := QuotientGroup.mk_out_eq_mul (KU σ N) g0
  obtain ⟨e, he⟩ := hLE L ϖ σ q N hU 0 (k0 : GU σ N)
  obtain ⟨e', he'⟩ := hLE L ϖ σ q N hU 0 ((k0 : GU σ N)⁻¹)
  have hm0lev : IsLeviElt ϖ s g0 m0 := by
    refine ⟨hm0L, ?_, ?_, fun i j => rfl⟩
    · rw [hm0eq 0 0 rfl, hp 0, Pi.single_eq_same, mul_one]
    · rw [hm0eq _ _ rfl, hlastlast]
  have hprod := isLeviElt_mul hϖ0 hm0lev he
  rw [add_zero, ← hk0] at hprod
  have hmeq : m = m0 * e := isLeviElt_unique hm hprod
  have hee' : e * e' = 1 := by
    have h1 := isLeviElt_mul hϖ0 he he'
    rw [add_zero, mul_inv_cancel] at h1
    have h2 : IsLeviElt ϖ 0 (1 : GU σ N) (1 : GU σ (N + 2)) := by
      refine ⟨Subgroup.one_mem _, ?_, ?_, ?_⟩
      · show (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) 0 0 = ϖ ^ (0 : ℤ)
        simp
      · show (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) (Fin.last (N + 1)) (Fin.last (N + 1)) = ϖ ^ (-(0 : ℤ))
        simp
      · intro i j
        exact hone i j
    exact isLeviElt_unique h1 h2
  have he'eq : e' = e⁻¹ := eq_inv_of_mul_eq_one_right hee'
  have heK : e ∈ KU σ (N + 2) := by
    refine mem_KU_of_mat_and_inv_mem_intL e (mat_apply_mem_intL_of_isLeviElt_of_mem_KU he k0.2) ?_
    intro i j
    have h := mat_apply_mem_intL_of_isLeviElt_of_mem_KU he' (Subgroup.inv_mem _ k0.2) i j
    rw [he'eq] at h
    exact h
  have heL' := he
  obtain ⟨heL, -⟩ := heL'
  refine ⟨e⁻¹ * (m0⁻¹ * p) * e, ?_, e⁻¹, Subgroup.inv_mem _ heK, ?_⟩
  · have h := (leviRad L σ (N + 2) (blk N) hσ e⁻¹ (Subgroup.inv_mem _ heL) (m0⁻¹ * p) hm0r).1
    rw [inv_inv] at h
    exact h
  · rw [hmeq]
    group

/- English proof (translation)
Introduce `hLE L _ _ ϖ σ q N hU g`. Take `⟨s, k, hk, hcol⟩` from `exists_col hU g`. Take `⟨y, hy⟩` from `levi_step hLE hU (g * k) hcol`. Use `⟨s, y, fun m hm => ?_⟩` and prove the remaining obligations. Take `⟨u, hu, k', hk', he⟩` from `hy m hm`.

Use `⟨u, hu, k' * k⁻¹, Subgroup.mul_mem _ hk' (Subgroup.inv_mem _ hk), ?_⟩` and prove the remaining obligations. Rewrite using `[← mul_assoc, ← he, mul_inv_cancel_right]`.
-/
theorem cosetSurj : LeviExists → CosetSurj := by
  intro hLE L _ _ ϖ σ q N hU g
  obtain ⟨s, k, hk, hcol⟩ := exists_col hU g
  obtain ⟨y, hy⟩ := levi_step hLE hU (g * k) hcol
  refine ⟨s, y, fun m hm => ?_⟩
  obtain ⟨u, hu, k', hk', he⟩ := hy m hm
  refine ⟨u, hu, k' * k⁻¹, Subgroup.mul_mem _ hk' (Subgroup.inv_mem _ hk), ?_⟩
  rw [← mul_assoc, ← he, mul_inv_cancel_right]

end GlobalTheory.CompanionTheory.InertCoset

end
