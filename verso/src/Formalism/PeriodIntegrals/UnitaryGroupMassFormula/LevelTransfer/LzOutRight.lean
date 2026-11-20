import Mathlib
import Formalism.FormalDegreeBessel.StatementRP

open Matrix

noncomputable section

namespace PIQnLT

open Formalism.REAL Formalism.QuantumDeterminants

variable {k i r' : ℕ}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem lev_val (j : Fin (2 * r' + k + 1)) : (levPos k i r' j).val = j.val + i := rfl

/- English proof (translation)
Introduce `a b h`. Apply `Fin.ext` to reduce the goal to its premises. Establish `h'` using `congrArg Fin.val h`. Rewrite `h'` using `[lev_val, lev_val]`. Use linear arithmetic over natural numbers and integers.
-/
theorem lev_inj : Function.Injective (levPos k i r') := by
  intro a b h
  apply Fin.ext
  have h' := congrArg Fin.val h
  rw [lev_val, lev_val] at h'
  omega

/- English proof (translation)
Establish `hj` using `j.isLt`. Establish `h1 : i ≤ (levPos k i r' j).val ∧ (levPos k i r' j).val < 2 * r' + k + 1 + i` using `by rw [lev_val]; omega`. Simplify using `only [liftVec]`. Rewrite using `[dif_pos h1]`. Use `congr 1`.

Apply `Fin.ext` to reduce the goal to its premises. Use `show j.val + i - i = j.val`. Use linear arithmetic over natural numbers and integers.
-/
theorem liftVec_lev (v : Fin (2 * r' + k + 1) → ℂ) (j : Fin (2 * r' + k + 1)) :
    liftVec k i r' v (levPos k i r' j) = v j := by
  have hj := j.isLt
  have h1 : i ≤ (levPos k i r' j).val ∧ (levPos k i r' j).val < 2 * r' + k + 1 + i := by rw [lev_val]; omega
  simp only [liftVec]
  rw [dif_pos h1]
  congr 1
  apply Fin.ext
  show j.val + i - i = j.val
  omega

/- English proof (translation)
Simplify using `only [liftVec]`. Rewrite using `[dif_neg hp]`.
-/
theorem liftVec_out (v : Fin (2 * r' + k + 1) → ℂ) (p : Fin (2 * (i + r') + k + 1))
    (hp : ¬ (i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i)) : liftVec k i r' v p = 0 := by
  simp only [liftVec]
  rw [dif_neg hp]

/- English proof (translation)
Establish `hp` using `p.isLt`. Establish `hq` using `q.isLt`. Establish `h1 : i ≤ (levPos k i r' p).val ∧ (levPos k i r' p).val < 2 * r' + k + 1 + i` using `by rw [lev_val]; omega`. Establish `h2 : i ≤ (levPos k i r' q).val ∧ (levPos k i r' q).val < 2 * r' + k + 1 + i` using `by rw [lev_val]; omega`. Simplify using `only [ιLev]`.

Rewrite using `[dif_pos h1, dif_pos h2]`. Apply the tactic sequence `congr 1 <;> apply Fin.ext`. Use `show p.val + i - i = p.val`. Use linear arithmetic over natural numbers and integers. Use `show q.val + i - i = q.val`.

Use linear arithmetic over natural numbers and integers.
-/
theorem ιLev_lev (g : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) (p q : Fin (2 * r' + k + 1)) :
    ιLev k i r' g (levPos k i r' p) (levPos k i r' q) = g p q := by
  have hp := p.isLt
  have hq := q.isLt
  have h1 : i ≤ (levPos k i r' p).val ∧ (levPos k i r' p).val < 2 * r' + k + 1 + i := by rw [lev_val]; omega
  have h2 : i ≤ (levPos k i r' q).val ∧ (levPos k i r' q).val < 2 * r' + k + 1 + i := by rw [lev_val]; omega
  simp only [ιLev]
  rw [dif_pos h1, dif_pos h2]
  congr 1 <;> apply Fin.ext
  · show p.val + i - i = p.val
    omega
  · show q.val + i - i = q.val
    omega

/- English proof (translation)
Simplify using `only [ιLev]`. Rewrite using `[dif_neg hp]`.
-/
theorem ιLev_out (g : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) (p q : Fin (2 * (i + r') + k + 1))
    (hp : ¬ (i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i)) : ιLev k i r' g p q = if p = q then 1 else 0 := by
  simp only [ιLev]
  rw [dif_neg hp]

/- English proof (translation)
Simplify using `only [ιLev]`. Rewrite using `[dif_pos hp, dif_neg hq]`.
-/
theorem ιLev_in_out (g : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) (p q : Fin (2 * (i + r') + k + 1))
    (hp : i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i) (hq : ¬ (i ≤ q.val ∧ q.val < 2 * r' + k + 1 + i)) :
    ιLev k i r' g p q = 0 := by
  simp only [ιLev]
  rw [dif_pos hp, dif_neg hq]

/- English proof (translation)
Rewrite using `[← Finset.sum_image (s := Finset.univ) (g := levPos k i r') (fun x _ y _ e => lev_inj e)]`. Use `(Finset.sum_subset (Finset.subset_univ _) ?_).symm` and prove the remaining obligations. Introduce `p _ hp`. Apply `h` to reduce the goal to its premises. Introduce `hc`.

Apply `hp` to reduce the goal to its premises. Use `Finset.mem_image.2 ⟨⟨p.val - i, by omega⟩, Finset.mem_univ _, ?_⟩` and prove the remaining obligations. Apply `Fin.ext` to reduce the goal to its premises. Use `show p.val - i + i = p.val`. Use linear arithmetic over natural numbers and integers.
-/
theorem sum_lev {M : Type*} [AddCommMonoid M] (f : Fin (2 * (i + r') + k + 1) → M)
    (h : ∀ p : Fin (2 * (i + r') + k + 1), ¬ (i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i) → f p = 0) :
    ∑ p, f p = ∑ j : Fin (2 * r' + k + 1), f (levPos k i r' j) := by
  rw [← Finset.sum_image (s := Finset.univ) (g := levPos k i r') (fun x _ y _ e => lev_inj e)]
  refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
  intro p _ hp
  apply h
  intro hc
  apply hp
  refine Finset.mem_image.2 ⟨⟨p.val - i, by omega⟩, Finset.mem_univ _, ?_⟩
  apply Fin.ext
  show p.val - i + i = p.val
  omega

/- English proof (translation)
Establish `hp` using `p.isLt`. Establish `hq` using `q.isLt`. Simplify using `only [Hpk, Fin.ext_iff, lev_val]`. Establish `e1 : (↑p + i < i + r' ∧ ↑p + i + (↑q + i) = 2 * (i + r') + k) ↔ (↑p < r' ∧ ↑p + ↑q = 2 * r' + k)`. Apply the tactic sequence `constructor <;> intro h <;> omega`.

Establish `e2 : (↑q + i < i + r' ∧ ↑p + i + (↑q + i) = 2 * (i + r') + k) ↔ (↑q < r' ∧ ↑p + ↑q = 2 * r' + k)`. Apply the tactic sequence `constructor <;> intro h <;> omega`. Establish `e3 : (i + r' ≤ p.val + i ∧ p.val + i ≤ i + r' + k ∧ p.val + i = q.val + i) ↔ (r' ≤ p.val ∧ p.val ≤ r' + k ∧ p.val = q.val)`. Apply the tactic sequence `constructor <;> intro h <;> omega`. Establish `e4 : (↑p + i = i + r' + k) ↔ (↑p = r' + k)`.

Apply the tactic sequence `constructor <;> intro h <;> omega`. Simplify using `only [e1, e2, e3, e4]`.
-/
theorem hpk_lev (p q : Fin (2 * r' + k + 1)) :
    Hpk k (i + r') (levPos k i r' p) (levPos k i r' q) = Hpk k r' p q := by
  have hp := p.isLt
  have hq := q.isLt
  simp only [Hpk, Fin.ext_iff, lev_val]
  have e1 : (↑p + i < i + r' ∧ ↑p + i + (↑q + i) = 2 * (i + r') + k) ↔ (↑p < r' ∧ ↑p + ↑q = 2 * r' + k) := by
    constructor <;> intro h <;> omega
  have e2 : (↑q + i < i + r' ∧ ↑p + i + (↑q + i) = 2 * (i + r') + k) ↔ (↑q < r' ∧ ↑p + ↑q = 2 * r' + k) := by
    constructor <;> intro h <;> omega
  have e3 : (i + r' ≤ p.val + i ∧ p.val + i ≤ i + r' + k ∧ p.val + i = q.val + i) ↔
      (r' ≤ p.val ∧ p.val ≤ r' + k ∧ p.val = q.val) := by
    constructor <;> intro h <;> omega
  have e4 : (↑p + i = i + r' + k) ↔ (↑p = r' + k) := by
    constructor <;> intro h <;> omega
  simp only [e1, e2, e3, e4]

/- English proof (translation)
Simplify using `only [Hpk, Fin.ext_iff]`. Apply the tactic sequence `split_ifs <;> first | rfl | (exfalso; omega)`.
-/
theorem hpk_in_out (p q : Fin (2 * (i + r') + k + 1))
    (hp : i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i) (hq : ¬ (i ≤ q.val ∧ q.val < 2 * r' + k + 1 + i)) :
    Hpk k (i + r') p q = 0 := by
  simp only [Hpk, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

/- English proof (translation)
Simplify using `only [Hpk, Fin.ext_iff]`. Apply the tactic sequence `split_ifs <;> first | rfl | (exfalso; omega)`.
-/
theorem hpk_out_in (p q : Fin (2 * (i + r') + k + 1))
    (hp : ¬ (i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i)) (hq : i ≤ q.val ∧ q.val < 2 * r' + k + 1 + i) :
    Hpk k (i + r') p q = 0 := by
  simp only [Hpk, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

def Lz (k i r' : ℕ) (X : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) :
    Matrix (Fin (2 * (i + r') + k + 1)) (Fin (2 * (i + r') + k + 1)) ℂ := fun p q =>
  if hp : i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i then
    (if hq : i ≤ q.val ∧ q.val < 2 * r' + k + 1 + i then X ⟨p.val - i, by omega⟩ ⟨q.val - i, by omega⟩ else 0)
  else 0

/- English proof (translation)
Use extensionality with `p q`. Simplify using `only [ιLev, Lz, Matrix.add_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem ιLev_eq (X : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) :
    ιLev k i r' X = Lz k i r' X + ιLev k i r' 0 := by
  ext p q
  simp only [ιLev, Lz, Matrix.add_apply]
  split_ifs <;> simp

/- English proof (translation)
Establish `hp` using `p.isLt`. Establish `hq` using `q.isLt`. Establish `h1 : i ≤ (levPos k i r' p).val ∧ (levPos k i r' p).val < 2 * r' + k + 1 + i` using `by rw [lev_val]; omega`. Establish `h2 : i ≤ (levPos k i r' q).val ∧ (levPos k i r' q).val < 2 * r' + k + 1 + i` using `by rw [lev_val]; omega`. Simplify using `only [Lz]`.

Rewrite using `[dif_pos h1, dif_pos h2]`. Apply the tactic sequence `congr 1 <;> apply Fin.ext`. Use `show p.val + i - i = p.val`. Use linear arithmetic over natural numbers and integers. Use `show q.val + i - i = q.val`.

Use linear arithmetic over natural numbers and integers.
-/
theorem Lz_lev (X : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) (p q : Fin (2 * r' + k + 1)) :
    Lz k i r' X (levPos k i r' p) (levPos k i r' q) = X p q := by
  have hp := p.isLt
  have hq := q.isLt
  have h1 : i ≤ (levPos k i r' p).val ∧ (levPos k i r' p).val < 2 * r' + k + 1 + i := by rw [lev_val]; omega
  have h2 : i ≤ (levPos k i r' q).val ∧ (levPos k i r' q).val < 2 * r' + k + 1 + i := by rw [lev_val]; omega
  simp only [Lz]
  rw [dif_pos h1, dif_pos h2]
  congr 1 <;> apply Fin.ext
  · show p.val + i - i = p.val
    omega
  · show q.val + i - i = q.val
    omega

/- English proof (translation)
Simplify using `only [Lz]`. Rewrite using `[dif_neg hp]`.
-/
theorem Lz_out_left (X : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) (p q : Fin (2 * (i + r') + k + 1))
    (hp : ¬ (i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i)) : Lz k i r' X p q = 0 := by
  simp only [Lz]
  rw [dif_neg hp]

/- English proof (translation)
Simplify using `only [Lz]`. Apply the tactic sequence `split_ifs <;> first | rfl | (exfalso; apply hq; assumption)`.
-/
theorem Lz_out_right (X : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) (p q : Fin (2 * (i + r') + k + 1))
    (hq : ¬ (i ≤ q.val ∧ q.val < 2 * r' + k + 1 + i)) : Lz k i r' X p q = 0 := by
  simp only [Lz]
  split_ifs <;> first | rfl | (exfalso; apply hq; assumption)

def LzL (k i r' : ℕ) :
    Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ →ₗ[ℂ]
      Matrix (Fin (2 * (i + r') + k + 1)) (Fin (2 * (i + r') + k + 1)) ℂ where
  toFun := Lz k i r'
  map_add' X Y := by
    ext p q; simp only [Lz, Matrix.add_apply]; split_ifs <;> simp
  map_smul' c X := by
    ext p q; simp only [Lz, Matrix.smul_apply, RingHom.id_apply]; split_ifs <;> simp

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem LzL_apply (X : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) : LzL k i r' X = Lz k i r' X := rfl

section Hom

variable (hL : LevHom)
include hL

/- English proof (translation)
Use extensionality with `p q`. Distinguish the cases in `hp : i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i`. Distinguish the cases in `hq : i ≤ q.val ∧ q.val < 2 * r' + k + 1 + i`. Take `⟨a, rfl⟩ : ∃ a, levPos k i r' a = p` from `⟨⟨p.val - i, by omega⟩, Fin.ext (by show p.val - i + i = p.val; omega)⟩`. Take `⟨b, rfl⟩ : ∃ b, levPos k i r' b = q` from `⟨⟨q.val - i, by omega⟩, Fin.ext (by show q.val - i + i = q.val; omega)⟩`.

Rewrite using `[Lz_lev, Matrix.mul_apply, Matrix.mul_apply, sum_lev]`. Simplify using `only [Lz_lev]`. Introduce `m hm`. Rewrite using `[Lz_out_right _ _ _ hm, zero_mul]`. Rewrite using `[Lz_out_right _ _ _ hq, Matrix.mul_apply]`.

Conclude with `(Finset.sum_eq_zero fun m _ => by rw [Lz_out_right _ _ _ hq, mul_zero]).symm`. Rewrite using `[Lz_out_left _ _ _ hp, Matrix.mul_apply]`. Conclude with `(Finset.sum_eq_zero fun m _ => by rw [Lz_out_left _ _ _ hp, zero_mul]).symm`.
-/
theorem Lz_mul (X Y : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) :
    Lz k i r' (X * Y) = Lz k i r' X * Lz k i r' Y := by
  ext p q
  by_cases hp : i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i
  · by_cases hq : i ≤ q.val ∧ q.val < 2 * r' + k + 1 + i
    · obtain ⟨a, rfl⟩ : ∃ a, levPos k i r' a = p :=
        ⟨⟨p.val - i, by omega⟩, Fin.ext (by show p.val - i + i = p.val; omega)⟩
      obtain ⟨b, rfl⟩ : ∃ b, levPos k i r' b = q :=
        ⟨⟨q.val - i, by omega⟩, Fin.ext (by show q.val - i + i = q.val; omega)⟩
      rw [Lz_lev, Matrix.mul_apply, Matrix.mul_apply, sum_lev]
      · simp only [Lz_lev]
      · intro m hm
        rw [Lz_out_right _ _ _ hm, zero_mul]
    · rw [Lz_out_right _ _ _ hq, Matrix.mul_apply]
      exact (Finset.sum_eq_zero fun m _ => by rw [Lz_out_right _ _ _ hq, mul_zero]).symm
  · rw [Lz_out_left _ _ _ hp, Matrix.mul_apply]
    exact (Finset.sum_eq_zero fun m _ => by rw [Lz_out_left _ _ _ hp, zero_mul]).symm

/- English proof (translation)
Rewrite using `[← ιLev_eq]`. Conclude with `(hL k i r').1`.
-/
theorem Lz_one : Lz k i r' 1 + ιLev k i r' 0 = 1 := by
  rw [← ιLev_eq]
  exact (hL k i r').1

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => rw [zero_add, pow_one, pow_one]`. Consider the case `succ n ih => rw [pow_succ, Lz_mul hL, ih, ← pow_succ]`.
-/
theorem Lz_pow (X : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) (n : ℕ) :
    Lz k i r' (X ^ (n + 1)) = Lz k i r' X ^ (n + 1) := by
  induction n with
  | zero => rw [zero_add, pow_one, pow_one]
  | succ n ih => rw [pow_succ, Lz_mul hL, ih, ← pow_succ]

end Hom

end PIQnLT
