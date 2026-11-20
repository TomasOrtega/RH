import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFrameTranslatedPerpOfIsFrame

open Matrix GlobalTheory.RealBessel GlobalTheory.BesselMapOne Formalism.L2.Theta GlobalTheory.SmVec

noncomputable section

namespace UpperTheory.Lit.Bur.BesselFrame

def frameMat {m r : ℕ} (e f : Matrix (Fin (2 * r + m + 1)) (Fin r) ℂ)
    (Fa : Matrix (Fin (2 * r + m + 1)) (Fin m) ℂ) (y : Fin (2 * r + m + 1) → ℂ) :
    Matrix (Fin (2 * r + m + 1)) (Fin (2 * r + m + 1)) ℂ := fun i j =>
  if h : j.val < r then e i ⟨j.val, h⟩
  else if h2 : j.val < r + m then Fa i ⟨j.val - r, by omega⟩
  else if h3 : j.val = r + m then y i
  else f i ⟨2 * r + m - j.val, by have := j.isLt; omega⟩

section
variable {m r : ℕ} (e f : Matrix (Fin (2 * r + m + 1)) (Fin r) ℂ)
    (Fa : Matrix (Fin (2 * r + m + 1)) (Fin m) ℂ) (y : Fin (2 * r + m + 1) → ℂ)

/- English proof (translation)
Use `a.isLt` as an intermediate fact. Simplify using `[frameMat, Formalism.QuantumDeterminants.eI]`.
-/
theorem frameMat_eI (i) (a : Fin r) : frameMat e f Fa y i (Formalism.QuantumDeterminants.eI m r a) = e i a := by
  have := a.isLt
  simp [frameMat, Formalism.QuantumDeterminants.eI]

/- English proof (translation)
Use `a.isLt` as an intermediate fact. Simplify using `[frameMat, PI.HwUniqW.bl]`.
-/
theorem frameMat_bl (i) (a : Fin m) : frameMat e f Fa y i (PI.HwUniqW.bl m r a) = Fa i a := by
  have := a.isLt
  simp [frameMat, PI.HwUniqW.bl]

/- English proof (translation)
Simplify using `[frameMat, Formalism.QuantumDeterminants.wI]`.
-/
theorem frameMat_w (i) : frameMat e f Fa y i (Formalism.QuantumDeterminants.wI m r (Fin.last m)) = y i := by
  simp [frameMat, Formalism.QuantumDeterminants.wI]

/- English proof (translation)
Unfold `frameMat`. Rewrite using `[dif_neg (by omega), dif_neg (by omega), dif_neg (by omega)]`.
-/
theorem frameMat_of_gt (i j : Fin (2 * r + m + 1)) (h : r + m < j.val) :
    frameMat e f Fa y i j = f i ⟨2 * r + m - j.val, by have := j.isLt; omega⟩ := by
  unfold frameMat
  rw [dif_neg (by omega), dif_neg (by omega), dif_neg (by omega)]

/- English proof (translation)
Use `a.isLt` as an intermediate fact. Establish `hv : (Formalism.QuantumDeterminants.esI m r a).val = 2 * r + m - a.val` using `rfl`. Rewrite using `[frameMat_of_gt e f Fa y i _ (by omega)]`. Use `congrArg (f i) (Fin.ext ?_)` and prove the remaining obligations. Use `show 2 * r + m - (Formalism.QuantumDeterminants.esI m r a).val = a.val`.

Use linear arithmetic over natural numbers and integers.
-/
theorem frameMat_es (i) (a : Fin r) : frameMat e f Fa y i (Formalism.QuantumDeterminants.esI m r a) = f i a := by
  have := a.isLt
  have hv : (Formalism.QuantumDeterminants.esI m r a).val = 2 * r + m - a.val := rfl
  rw [frameMat_of_gt e f Fa y i _ (by omega)]
  refine congrArg (f i) (Fin.ext ?_)
  show 2 * r + m - (Formalism.QuantumDeterminants.esI m r a).val = a.val
  omega

end

/- English proof (translation)
Establish `hj` using `j.isLt`. Distinguish the cases in `h : j.val < r`. Conclude with `Or.inl ⟨⟨j.val, h⟩, Fin.ext rfl⟩`. Distinguish the cases in `h2 : j.val < r + m`. Conclude with `Or.inr (Or.inl ⟨⟨j.val - r, by omega⟩, Fin.ext (by simp only [PI.HwUniqW.bl]; omega)⟩)`.

Distinguish the cases in `h3 : j.val = r + m`. Conclude with `Or.inr (Or.inr (Or.inl (Fin.ext (by simpa [Formalism.QuantumDeterminants.wI] using h3))))`. Conclude with `Or.inr (Or.inr (Or.inr ⟨⟨2 * r + m - j.val, by omega⟩, Fin.ext (by simp only [Formalism.QuantumDeterminants.esI]; omega)⟩))`.
-/
theorem pos_cases {m r : ℕ} (j : Fin (2 * r + m + 1)) :
    (∃ a, j = Formalism.QuantumDeterminants.eI m r a) ∨ (∃ a, j = PI.HwUniqW.bl m r a) ∨
      j = Formalism.QuantumDeterminants.wI m r (Fin.last m) ∨ ∃ a, j = Formalism.QuantumDeterminants.esI m r a := by
  have hj := j.isLt
  by_cases h : j.val < r
  · exact Or.inl ⟨⟨j.val, h⟩, Fin.ext rfl⟩
  by_cases h2 : j.val < r + m
  · exact Or.inr (Or.inl ⟨⟨j.val - r, by omega⟩, Fin.ext (by simp only [PI.HwUniqW.bl]; omega)⟩)
  by_cases h3 : j.val = r + m
  · exact Or.inr (Or.inr (Or.inl (Fin.ext (by simpa [Formalism.QuantumDeterminants.wI] using h3))))
  · exact Or.inr (Or.inr (Or.inr ⟨⟨2 * r + m - j.val, by omega⟩,
      Fin.ext (by simp only [Formalism.QuantumDeterminants.esI]; omega)⟩))

section Hpk
variable {m r : ℕ}
open Formalism.QuantumDeterminants

/- English proof (translation)
Unfold `Hpk`. Rewrite using `[if_neg h1, if_neg h2, if_neg (fun h => h3 ⟨h.1, h.2.1, congrArg Fin.val h.2.2⟩)]`.
-/
theorem hpk_zero (i j : Fin (2 * r + m + 1)) (h1 : ¬ (i.val < r ∧ i.val + j.val = 2 * r + m))
    (h2 : ¬ (j.val < r ∧ i.val + j.val = 2 * r + m)) (h3 : ¬ (r ≤ i.val ∧ i.val ≤ r + m ∧ i.val = j.val)) :
    Hpk m r i j = 0 := by
  unfold Hpk
  rw [if_neg h1, if_neg h2, if_neg (fun h => h3 ⟨h.1, h.2.1, congrArg Fin.val h.2.2⟩)]

/- English proof (translation)
Unfold `Hpk`. Rewrite using `[if_pos h1]`.
-/
theorem hpk_one (i j : Fin (2 * r + m + 1)) (h1 : i.val < r ∧ i.val + j.val = 2 * r + m) :
    Hpk m r i j = 1 := by
  unfold Hpk
  rw [if_pos h1]

/- English proof (translation)
Unfold `Hpk`. Rewrite using `[if_neg (by omega), if_neg (by omega), if_pos ⟨h1, by omega, rfl⟩, if_neg (by omega)]`.
-/
theorem hpk_diag (i : Fin (2 * r + m + 1)) (h1 : r ≤ i.val) (h2 : i.val < r + m) : Hpk m r i i = 1 := by
  unfold Hpk
  rw [if_neg (by omega), if_neg (by omega), if_pos ⟨h1, by omega, rfl⟩, if_neg (by omega)]

/- English proof (translation)
Use `a.isLt` as an intermediate fact. Use `b.isLt` as an intermediate fact. Conclude with `hpk_zero _ _ (by simp only [eI]; omega) (by simp only [eI]; omega) (by simp only [eI]; omega)`.
-/
theorem hpk_ee (a b : Fin r) : Hpk m r (eI m r a) (eI m r b) = 0 := by
  have := a.isLt; have := b.isLt
  exact hpk_zero _ _ (by simp only [eI]; omega) (by simp only [eI]; omega) (by simp only [eI]; omega)
/- English proof (translation)
Use `a.isLt` as an intermediate fact. Use `b.isLt` as an intermediate fact. Conclude with `hpk_zero _ _ (by simp only [eI, PI.HwUniqW.bl]; omega) (by simp only [eI, PI.HwUniqW.bl]; omega) (by simp only [eI, PI.HwUniqW.bl]; omega)`.
-/
theorem hpk_eb (a : Fin r) (b : Fin m) : Hpk m r (eI m r a) (PI.HwUniqW.bl m r b) = 0 := by
  have := a.isLt; have := b.isLt
  exact hpk_zero _ _ (by simp only [eI, PI.HwUniqW.bl]; omega) (by simp only [eI, PI.HwUniqW.bl]; omega) (by simp only [eI, PI.HwUniqW.bl]; omega)
/- English proof (translation)
Use `a.isLt` as an intermediate fact. Conclude with `hpk_zero _ _ (by simp only [eI, wI, Fin.val_last]; omega) (by simp only [eI, wI, Fin.val_last]; omega) (by simp only [eI, wI, Fin.val_last]; omega)`.
-/
theorem hpk_ew (a : Fin r) : Hpk m r (eI m r a) (wI m r (Fin.last m)) = 0 := by
  have := a.isLt
  exact hpk_zero _ _ (by simp only [eI, wI, Fin.val_last]; omega) (by simp only [eI, wI, Fin.val_last]; omega) (by simp only [eI, wI, Fin.val_last]; omega)
/- English proof (translation)
Use `a.isLt` as an intermediate fact. Use `b.isLt` as an intermediate fact. Rewrite using `[Matrix.one_apply]`. Distinguish the cases in `h : a = b`. Substitute `h` using the available equality.

Rewrite using `[if_pos rfl]`. Conclude with `hpk_one _ _ (by simp only [eI, esI]; omega)`. Establish `h' : a.val ≠ b.val` using `fun q => h (Fin.ext q)`. Rewrite using `[if_neg h]`. Conclude with `hpk_zero _ _ (by simp only [eI, esI]; omega) (by simp only [eI, esI]; omega) (by simp only [eI, esI]; omega)`.
-/
theorem hpk_es (a b : Fin r) : Hpk m r (eI m r a) (esI m r b) = (1 : Matrix (Fin r) (Fin r) ℂ) a b := by
  have := a.isLt; have := b.isLt
  rw [Matrix.one_apply]
  by_cases h : a = b
  · subst h
    rw [if_pos rfl]
    exact hpk_one _ _ (by simp only [eI, esI]; omega)
  · have h' : a.val ≠ b.val := fun q => h (Fin.ext q)
    rw [if_neg h]
    exact hpk_zero _ _ (by simp only [eI, esI]; omega) (by simp only [eI, esI]; omega) (by simp only [eI, esI]; omega)
/- English proof (translation)
Use `a.isLt` as an intermediate fact. Use `b.isLt` as an intermediate fact. Rewrite using `[Matrix.one_apply]`. Distinguish the cases in `h : a = b`. Substitute `h` using the available equality.

Rewrite using `[if_pos rfl]`. Conclude with `hpk_diag _ (by simp only [PI.HwUniqW.bl]; omega) (by simp only [PI.HwUniqW.bl]; omega)`. Establish `h' : a.val ≠ b.val` using `fun q => h (Fin.ext q)`. Rewrite using `[if_neg h]`. Conclude with `hpk_zero _ _ (by simp only [PI.HwUniqW.bl]; omega) (by simp only [PI.HwUniqW.bl]; omega) (by simp only [PI.HwUniqW.bl]; omega)`.
-/
theorem hpk_bb (a b : Fin m) : Hpk m r (PI.HwUniqW.bl m r a) (PI.HwUniqW.bl m r b) =
    (1 : Matrix (Fin m) (Fin m) ℂ) a b := by
  have := a.isLt; have := b.isLt
  rw [Matrix.one_apply]
  by_cases h : a = b
  · subst h
    rw [if_pos rfl]
    exact hpk_diag _ (by simp only [PI.HwUniqW.bl]; omega) (by simp only [PI.HwUniqW.bl]; omega)
  · have h' : a.val ≠ b.val := fun q => h (Fin.ext q)
    rw [if_neg h]
    exact hpk_zero _ _ (by simp only [PI.HwUniqW.bl]; omega) (by simp only [PI.HwUniqW.bl]; omega) (by simp only [PI.HwUniqW.bl]; omega)
/- English proof (translation)
Use `a.isLt` as an intermediate fact. Conclude with `hpk_zero _ _ (by simp only [PI.HwUniqW.bl, wI, Fin.val_last]; omega) (by simp only [PI.HwUniqW.bl, wI, Fin.val_last]; omega) (by simp only [PI.HwUniqW.bl, wI, Fin.val_last]; omega)`.
-/
theorem hpk_bw (a : Fin m) : Hpk m r (PI.HwUniqW.bl m r a) (wI m r (Fin.last m)) = 0 := by
  have := a.isLt
  exact hpk_zero _ _ (by simp only [PI.HwUniqW.bl, wI, Fin.val_last]; omega) (by simp only [PI.HwUniqW.bl, wI, Fin.val_last]; omega) (by simp only [PI.HwUniqW.bl, wI, Fin.val_last]; omega)
/- English proof (translation)
Use `a.isLt` as an intermediate fact. Use `b.isLt` as an intermediate fact. Conclude with `hpk_zero _ _ (by simp only [PI.HwUniqW.bl, esI]; omega) (by simp only [PI.HwUniqW.bl, esI]; omega) (by simp only [PI.HwUniqW.bl, esI]; omega)`.
-/
theorem hpk_bs (a : Fin m) (b : Fin r) : Hpk m r (PI.HwUniqW.bl m r a) (esI m r b) = 0 := by
  have := a.isLt; have := b.isLt
  exact hpk_zero _ _ (by simp only [PI.HwUniqW.bl, esI]; omega) (by simp only [PI.HwUniqW.bl, esI]; omega) (by simp only [PI.HwUniqW.bl, esI]; omega)
/- English proof (translation)
Unfold `Hpk`. Establish `h : (wI m r (Fin.last m)).val = r + m` using `by simp [wI]`. Rewrite using `[if_neg (by omega), if_neg (by omega), if_pos ⟨by omega, by omega, rfl⟩, if_pos h]`.
-/
theorem hpk_ww : Hpk m r (wI m r (Fin.last m)) (wI m r (Fin.last m)) = -1 := by
  unfold Hpk
  have h : (wI m r (Fin.last m)).val = r + m := by simp [wI]
  rw [if_neg (by omega), if_neg (by omega), if_pos ⟨by omega, by omega, rfl⟩, if_pos h]

/- English proof (translation)
Use `b.isLt` as an intermediate fact. Conclude with `hpk_zero _ _ (by simp only [wI, esI, Fin.val_last]; omega) (by simp only [wI, esI, Fin.val_last]; omega) (by simp only [wI, esI, Fin.val_last]; omega)`.
-/
theorem hpk_ws (b : Fin r) : Hpk m r (wI m r (Fin.last m)) (esI m r b) = 0 := by
  have := b.isLt
  exact hpk_zero _ _ (by simp only [wI, esI, Fin.val_last]; omega) (by simp only [wI, esI, Fin.val_last]; omega) (by simp only [wI, esI, Fin.val_last]; omega)
/- English proof (translation)
Use `a.isLt` as an intermediate fact. Use `b.isLt` as an intermediate fact. Conclude with `hpk_zero _ _ (by simp only [esI]; omega) (by simp only [esI]; omega) (by simp only [esI]; omega)`.
-/
theorem hpk_ss (a b : Fin r) : Hpk m r (esI m r a) (esI m r b) = 0 := by
  have := a.isLt; have := b.isLt
  exact hpk_zero _ _ (by simp only [esI]; omega) (by simp only [esI]; omega) (by simp only [esI]; omega)

end Hpk

section Form
variable {n : Type} [Fintype n]

def bf (J : Matrix n n ℂ) (u v : n → ℂ) : ℂ := star u ⬝ᵥ (J *ᵥ v)

/- English proof (translation)
Establish `h : star v ᵥ* J = star (J *ᵥ v)` using `by rw [Matrix.star_mulVec, hH]`. Simplify using `only [bf]`. Rewrite using `[Matrix.dotProduct_mulVec, h, Matrix.star_dotProduct]`.
-/
theorem bf_symm {J : Matrix n n ℂ} (hH : Jᴴ = J) (u v : n → ℂ) : bf J v u = star (bf J u v) := by
  have h : star v ᵥ* J = star (J *ᵥ v) := by rw [Matrix.star_mulVec, hH]
  simp only [bf]
  rw [Matrix.dotProduct_mulVec, h, Matrix.star_dotProduct]

/- English proof (translation)
Simplify using `only [bf, Matrix.mul_apply, dotProduct, Matrix.mulVec, Matrix.conjTranspose_apply, Pi.star_apply, Finset.sum_mul, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Simplify using `only [mul_assoc]`.
-/
theorem entry_eq {p q : Type} [Fintype p] [Fintype q] (J : Matrix n n ℂ) (A : Matrix n p ℂ)
    (B : Matrix n q ℂ) (a : p) (b : q) :
    (Aᴴ * J * B) a b = bf J (fun i => A i a) (fun i => B i b) := by
  simp only [bf, Matrix.mul_apply, dotProduct, Matrix.mulVec, Matrix.conjTranspose_apply, Pi.star_apply,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [mul_assoc]

/- English proof (translation)
Simplify using `only [bf, Matrix.mul_apply, dotProduct, Matrix.mulVec, Matrix.conjTranspose_apply, Pi.star_apply, Finset.sum_mul, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Simplify using `only [mul_assoc]`.
-/
theorem vec_eq {p : Type} [Fintype p] (J : Matrix n n ℂ) (A : Matrix n p ℂ) (y : n → ℂ) (a : p) :
    ((Aᴴ * J) *ᵥ y) a = bf J (fun i => A i a) y := by
  simp only [bf, Matrix.mul_apply, dotProduct, Matrix.mulVec, Matrix.conjTranspose_apply, Pi.star_apply,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [mul_assoc]

end Form

/- English proof (translation)
Establish `h : (Formalism.QuantumDeterminants.Hpk m r)ᴴ = Formalism.QuantumDeterminants.Hpk m r` using `PI.HwUniqW.Hpk_conjTranspose`. Use `conv_lhs => rw [← h]`. Both sides reduce to the same expression.
-/
theorem hpk_symm {m r : ℕ} (i j : Fin (2 * r + m + 1)) :
    Formalism.QuantumDeterminants.Hpk m r j i = star (Formalism.QuantumDeterminants.Hpk m r i j) := by
  have h : (Formalism.QuantumDeterminants.Hpk m r)ᴴ = Formalism.QuantumDeterminants.Hpk m r := PI.HwUniqW.Hpk_conjTranspose
  conv_lhs => rw [← h]
  rfl

/- English proof (translation)
Use `set Q := frameMat e f Fa y with hQ`. Establish `ce : ∀ a, (fun k => Q k (Formalism.QuantumDeterminants.eI m r a)) = fun k => e k a` using `fun a => funext fun k => frameMat_eI e f Fa y k a`. Establish `cb : ∀ a, (fun k => Q k (PI.HwUniqW.bl m r a)) = fun k => Fa k a` using `fun a => funext fun k => frameMat_bl e f Fa y k a`. Establish `cw : (fun k => Q k (Formalism.QuantumDeterminants.wI m r (Fin.last m))) = y`. Use function extensionality and compare the values at `fun k => frameMat_w e f Fa y k`.

Establish `cs : ∀ a, (fun k => Q k (Formalism.QuantumDeterminants.esI m r a)) = fun k => f k a` using `fun a => funext fun k => frameMat_es e f Fa y k a`. Establish `sym : ∀ i j, bf J (fun k => Q k i) (fun k => Q k j) = Formalism.QuantumDeterminants.Hpk m r i j → bf J (fun k => Q k j) (fun k => Q k i) = Formalism.QuantumDeterminants.Hpk m r j i` using `fun i j h => by`. Rewrite using `[bf_symm hH, h, hpk_symm i j]`. Establish `pee : ∀ a b, bf J (fun k => Q k (Formalism.QuantumDeterminants.eI m r a)) (fun k => Q k (Formalism.QuantumDeterminants.eI m r b)) = Formalism.QuantumDeterminants.Hpk m r (Formalism.QuantumDeterminants.eI m r a) (Formalism.QuantumDeterminants.eI m r b)` using `fun a b => by`. Rewrite using `[ce, ce, ← entry_eq, h2, hpk_ee]`.

Both sides reduce to the same expression. Establish `peb : ∀ a b, bf J (fun k => Q k (PI.HwUniqW.bl m r b)) (fun k => Q k (Formalism.QuantumDeterminants.eI m r a)) = Formalism.QuantumDeterminants.Hpk m r (PI.HwUniqW.bl m r b) (Formalism.QuantumDeterminants.eI m r a)` using `fun a b => by`. Use `sym _ _ ?_` and prove the remaining obligations. Rewrite using `[ce, cb, bf_symm hH, ← entry_eq, h5, hpk_eb]`. Simplify using the standard rewrite rules.

Establish `pew : ∀ a, bf J (fun k => Q k (Formalism.QuantumDeterminants.eI m r a)) (fun k => Q k (Formalism.QuantumDeterminants.wI m r (Fin.last m))) = Formalism.QuantumDeterminants.Hpk m r (Formalism.QuantumDeterminants.eI m r a) (Formalism.QuantumDeterminants.wI m r (Fin.last m))` using `fun a => by`. Rewrite using `[ce, cw, ← vec_eq, h8, hpk_ew]`. Both sides reduce to the same expression. Establish `pes : ∀ a b, bf J (fun k => Q k (Formalism.QuantumDeterminants.eI m r a)) (fun k => Q k (Formalism.QuantumDeterminants.esI m r b)) = Formalism.QuantumDeterminants.Hpk m r (Formalism.QuantumDeterminants.eI m r a) (Formalism.QuantumDeterminants.esI m r b)` using `fun a b => by`. Rewrite using `[ce, cs, ← entry_eq, h4, hpk_es]`.

Establish `pbb : ∀ a b, bf J (fun k => Q k (PI.HwUniqW.bl m r a)) (fun k => Q k (PI.HwUniqW.bl m r b)) = Formalism.QuantumDeterminants.Hpk m r (PI.HwUniqW.bl m r a) (PI.HwUniqW.bl m r b)` using `fun a b => by`. Rewrite using `[cb, cb, ← entry_eq, h1, hpk_bb]`. Establish `pbw : ∀ a, bf J (fun k => Q k (PI.HwUniqW.bl m r a)) (fun k => Q k (Formalism.QuantumDeterminants.wI m r (Fin.last m))) = Formalism.QuantumDeterminants.Hpk m r (PI.HwUniqW.bl m r a) (Formalism.QuantumDeterminants.wI m r (Fin.last m))` using `fun a => by`. Rewrite using `[cb, cw, ← vec_eq, h7, hpk_bw]`. Both sides reduce to the same expression.

Establish `pbs : ∀ a b, bf J (fun k => Q k (PI.HwUniqW.bl m r a)) (fun k => Q k (Formalism.QuantumDeterminants.esI m r b)) = Formalism.QuantumDeterminants.Hpk m r (PI.HwUniqW.bl m r a) (Formalism.QuantumDeterminants.esI m r b)` using `fun a b => by`. Rewrite using `[cb, cs, ← entry_eq, h6, hpk_bs]`. Both sides reduce to the same expression. Establish `pww : bf J (fun k => Q k (Formalism.QuantumDeterminants.wI m r (Fin.last m))) (fun k => Q k (Formalism.QuantumDeterminants.wI m r (Fin.last m))) = Formalism.QuantumDeterminants.Hpk m r (Formalism.QuantumDeterminants.wI m r (Fin.last m)) (Formalism.QuantumDeterminants.wI m r (Fin. …`. Rewrite using `[cw, hpk_ww]`.

Conclude with `h10`. Establish `pws : ∀ b, bf J (fun k => Q k (Formalism.QuantumDeterminants.esI m r b)) (fun k => Q k (Formalism.QuantumDeterminants.wI m r (Fin.last m))) = Formalism.QuantumDeterminants.Hpk m r (Formalism.QuantumDeterminants.esI m r b) (Formalism.QuantumDeterminants.wI m r (Fin.last m))` using `fun b => by`. Use `sym _ _ ?_` and prove the remaining obligations. Rewrite using `[cs, cw, bf_symm hH, ← vec_eq, h9, hpk_ws]`. Simplify using the standard rewrite rules.

Establish `pss : ∀ a b, bf J (fun k => Q k (Formalism.QuantumDeterminants.esI m r a)) (fun k => Q k (Formalism.QuantumDeterminants.esI m r b)) = Formalism.QuantumDeterminants.Hpk m r (Formalism.QuantumDeterminants.esI m r a) (Formalism.QuantumDeterminants.esI m r b)` using `fun a b => by`. Rewrite using `[cs, cs, ← entry_eq, h3, hpk_ss]`. Both sides reduce to the same expression. Establish `key : Qᴴ * J * Q = Formalism.QuantumDeterminants.Hpk m r`. Use extensionality with `i j`.

Rewrite using `[entry_eq]`. Apply the tactic sequence `rcases pos_cases i with ⟨a, rfl⟩ | ⟨a, rfl⟩ | rfl | ⟨a, rfl⟩ <;>`. Break down `pos_cases j with ⟨b, rfl⟩ | ⟨b, rfl⟩ | rfl | ⟨b, rfl⟩` into its components or cases. Conclude with `pee a b`. Conclude with `sym _ _ (peb a b)`.

Conclude with `pew a`. Conclude with `pes a b`. Conclude with `peb b a`. Conclude with `pbb a b`. Conclude with `pbw a`.

Conclude with `pbs a b`. Conclude with `sym _ _ (pew b)`. Conclude with `sym _ _ (pbw b)`. Conclude with `pww`. Conclude with `sym _ _ (pws b)`.

Conclude with `sym _ _ (pes b a)`. Conclude with `sym _ _ (pbs b a)`. Conclude with `pws a`. Conclude with `pss a b`. Establish `hsq : Formalism.QuantumDeterminants.Hpk m r * Formalism.QuantumDeterminants.Hpk m r = 1` using `PI.HwUniqW.Hpk_mul_self`.

Establish `hinv : (Formalism.QuantumDeterminants.Hpk m r * Qᴴ * J) * Q = 1`. Rewrite using `[Matrix.mul_assoc (Formalism.QuantumDeterminants.Hpk m r), Matrix.mul_assoc (Formalism.QuantumDeterminants.Hpk m r), key, hsq]`. Use `⟨Q, Formalism.QuantumDeterminants.Hpk m r * Qᴴ * J, mul_eq_one_comm.1 hinv, hinv, key, ?_, ?_, ?_⟩` and prove the remaining obligations. Use extensionality with `i a`. Rewrite using `[Matrix.mul_apply]`.

Simplify using `only [colE, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Conclude with `frameMat_eI e f Fa y i a`. Use extensionality with `i a`. Rewrite using `[Matrix.mul_apply]`. Simplify using `only [colW, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]`.

Conclude with `frameMat_bl e f Fa y i a`. Use function extensionality and compare the values at `i`. Simplify using `only [Formalism.QuantumDeterminants.bvec, Matrix.mulVec_single_one]`. Conclude with `frameMat_w e f Fa y i`.
-/
theorem exists_frame_matrix {m r : ℕ} {J : Matrix (Fin (2 * r + m + 1)) (Fin (2 * r + m + 1)) ℂ} (hH : Jᴴ = J)
    {Fa : Matrix (Fin (2 * r + m + 1)) (Fin m) ℂ} {e f : Matrix (Fin (2 * r + m + 1)) (Fin r) ℂ}
    {y : Fin (2 * r + m + 1) → ℂ} (h1 : Faᴴ * J * Fa = 1) (h2 : eᴴ * J * e = 0) (h3 : fᴴ * J * f = 0)
    (h4 : eᴴ * J * f = 1) (h5 : Faᴴ * J * e = 0) (h6 : Faᴴ * J * f = 0) (h7 : (Faᴴ * J) *ᵥ y = 0)
    (h8 : (eᴴ * J) *ᵥ y = 0) (h9 : (fᴴ * J) *ᵥ y = 0) (h10 : Formalism.QuantumDeterminants.herm J y y = -1) :
    ∃ Q Qi : Matrix (Fin (2 * r + m + 1)) (Fin (2 * r + m + 1)) ℂ, Q * Qi = 1 ∧ Qi * Q = 1 ∧
      Qᴴ * J * Q = Formalism.QuantumDeterminants.Hpk m r ∧ Q * colE m r = e ∧ Q * colW m r = Fa ∧
      Q *ᵥ Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.wI m r (Fin.last m)) = y := by
  set Q := frameMat e f Fa y with hQ
  have ce : ∀ a, (fun k => Q k (Formalism.QuantumDeterminants.eI m r a)) = fun k => e k a :=
    fun a => funext fun k => frameMat_eI e f Fa y k a
  have cb : ∀ a, (fun k => Q k (PI.HwUniqW.bl m r a)) = fun k => Fa k a :=
    fun a => funext fun k => frameMat_bl e f Fa y k a
  have cw : (fun k => Q k (Formalism.QuantumDeterminants.wI m r (Fin.last m))) = y :=
    funext fun k => frameMat_w e f Fa y k
  have cs : ∀ a, (fun k => Q k (Formalism.QuantumDeterminants.esI m r a)) = fun k => f k a :=
    fun a => funext fun k => frameMat_es e f Fa y k a
  have sym : ∀ i j, bf J (fun k => Q k i) (fun k => Q k j) = Formalism.QuantumDeterminants.Hpk m r i j →
      bf J (fun k => Q k j) (fun k => Q k i) = Formalism.QuantumDeterminants.Hpk m r j i := fun i j h => by
    rw [bf_symm hH, h, hpk_symm i j]
  have pee : ∀ a b, bf J (fun k => Q k (Formalism.QuantumDeterminants.eI m r a)) (fun k => Q k (Formalism.QuantumDeterminants.eI m r b)) =
      Formalism.QuantumDeterminants.Hpk m r (Formalism.QuantumDeterminants.eI m r a) (Formalism.QuantumDeterminants.eI m r b) := fun a b => by
    rw [ce, ce, ← entry_eq, h2, hpk_ee]; rfl
  have peb : ∀ a b, bf J (fun k => Q k (PI.HwUniqW.bl m r b)) (fun k => Q k (Formalism.QuantumDeterminants.eI m r a)) =
      Formalism.QuantumDeterminants.Hpk m r (PI.HwUniqW.bl m r b) (Formalism.QuantumDeterminants.eI m r a) := fun a b => by
    refine sym _ _ ?_
    rw [ce, cb, bf_symm hH, ← entry_eq, h5, hpk_eb]; simp
  have pew : ∀ a, bf J (fun k => Q k (Formalism.QuantumDeterminants.eI m r a)) (fun k => Q k (Formalism.QuantumDeterminants.wI m r (Fin.last m))) =
      Formalism.QuantumDeterminants.Hpk m r (Formalism.QuantumDeterminants.eI m r a) (Formalism.QuantumDeterminants.wI m r (Fin.last m)) := fun a => by
    rw [ce, cw, ← vec_eq, h8, hpk_ew]; rfl
  have pes : ∀ a b, bf J (fun k => Q k (Formalism.QuantumDeterminants.eI m r a)) (fun k => Q k (Formalism.QuantumDeterminants.esI m r b)) =
      Formalism.QuantumDeterminants.Hpk m r (Formalism.QuantumDeterminants.eI m r a) (Formalism.QuantumDeterminants.esI m r b) := fun a b => by
    rw [ce, cs, ← entry_eq, h4, hpk_es]
  have pbb : ∀ a b, bf J (fun k => Q k (PI.HwUniqW.bl m r a)) (fun k => Q k (PI.HwUniqW.bl m r b)) =
      Formalism.QuantumDeterminants.Hpk m r (PI.HwUniqW.bl m r a) (PI.HwUniqW.bl m r b) := fun a b => by
    rw [cb, cb, ← entry_eq, h1, hpk_bb]
  have pbw : ∀ a, bf J (fun k => Q k (PI.HwUniqW.bl m r a)) (fun k => Q k (Formalism.QuantumDeterminants.wI m r (Fin.last m))) =
      Formalism.QuantumDeterminants.Hpk m r (PI.HwUniqW.bl m r a) (Formalism.QuantumDeterminants.wI m r (Fin.last m)) := fun a => by
    rw [cb, cw, ← vec_eq, h7, hpk_bw]; rfl
  have pbs : ∀ a b, bf J (fun k => Q k (PI.HwUniqW.bl m r a)) (fun k => Q k (Formalism.QuantumDeterminants.esI m r b)) =
      Formalism.QuantumDeterminants.Hpk m r (PI.HwUniqW.bl m r a) (Formalism.QuantumDeterminants.esI m r b) := fun a b => by
    rw [cb, cs, ← entry_eq, h6, hpk_bs]; rfl
  have pww : bf J (fun k => Q k (Formalism.QuantumDeterminants.wI m r (Fin.last m))) (fun k => Q k (Formalism.QuantumDeterminants.wI m r (Fin.last m))) =
      Formalism.QuantumDeterminants.Hpk m r (Formalism.QuantumDeterminants.wI m r (Fin.last m)) (Formalism.QuantumDeterminants.wI m r (Fin.last m)) := by
    rw [cw, hpk_ww]; exact h10
  have pws : ∀ b, bf J (fun k => Q k (Formalism.QuantumDeterminants.esI m r b)) (fun k => Q k (Formalism.QuantumDeterminants.wI m r (Fin.last m))) =
      Formalism.QuantumDeterminants.Hpk m r (Formalism.QuantumDeterminants.esI m r b) (Formalism.QuantumDeterminants.wI m r (Fin.last m)) := fun b => by
    refine sym _ _ ?_
    rw [cs, cw, bf_symm hH, ← vec_eq, h9, hpk_ws]; simp
  have pss : ∀ a b, bf J (fun k => Q k (Formalism.QuantumDeterminants.esI m r a)) (fun k => Q k (Formalism.QuantumDeterminants.esI m r b)) =
      Formalism.QuantumDeterminants.Hpk m r (Formalism.QuantumDeterminants.esI m r a) (Formalism.QuantumDeterminants.esI m r b) := fun a b => by
    rw [cs, cs, ← entry_eq, h3, hpk_ss]; rfl
  have key : Qᴴ * J * Q = Formalism.QuantumDeterminants.Hpk m r := by
    ext i j
    rw [entry_eq]
    rcases pos_cases i with ⟨a, rfl⟩ | ⟨a, rfl⟩ | rfl | ⟨a, rfl⟩ <;>
      rcases pos_cases j with ⟨b, rfl⟩ | ⟨b, rfl⟩ | rfl | ⟨b, rfl⟩
    · exact pee a b
    · exact sym _ _ (peb a b)
    · exact pew a
    · exact pes a b
    · exact peb b a
    · exact pbb a b
    · exact pbw a
    · exact pbs a b
    · exact sym _ _ (pew b)
    · exact sym _ _ (pbw b)
    · exact pww
    · exact sym _ _ (pws b)
    · exact sym _ _ (pes b a)
    · exact sym _ _ (pbs b a)
    · exact pws a
    · exact pss a b
  have hsq : Formalism.QuantumDeterminants.Hpk m r * Formalism.QuantumDeterminants.Hpk m r = 1 := PI.HwUniqW.Hpk_mul_self
  have hinv : (Formalism.QuantumDeterminants.Hpk m r * Qᴴ * J) * Q = 1 := by
    rw [Matrix.mul_assoc (Formalism.QuantumDeterminants.Hpk m r), Matrix.mul_assoc (Formalism.QuantumDeterminants.Hpk m r), key, hsq]
  refine ⟨Q, Formalism.QuantumDeterminants.Hpk m r * Qᴴ * J, mul_eq_one_comm.1 hinv, hinv, key, ?_, ?_, ?_⟩
  · ext i a
    rw [Matrix.mul_apply]
    simp only [colE, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    exact frameMat_eI e f Fa y i a
  · ext i a
    rw [Matrix.mul_apply]
    simp only [colW, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    exact frameMat_bl e f Fa y i a
  · funext i
    simp only [Formalism.QuantumDeterminants.bvec, Matrix.mulVec_single_one]
    exact frameMat_w e f Fa y i

end UpperTheory.Lit.Bur.BesselFrame

open Matrix GlobalTheory.RealBessel GlobalTheory.BesselMapOne Formalism.L2.Theta GlobalTheory.SmVec
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @UpperTheory.Lit.Bur.BesselFrame.exists_frame_matrix | exact UpperTheory.Lit.Bur.BesselFrame.exists_frame_matrix | (intros; apply UpperTheory.Lit.Bur.BesselFrame.exists_frame_matrix <;> assumption)`.
-/
theorem _root_.UpperTheory.Lit.Bur.hyperbolic_frame_congruent_splitHermGram : ∀ {m r : ℕ} {J : Matrix (Fin (2 * r + m + 1)) (Fin (2 * r + m + 1)) ℂ} (hH : Jᴴ = J) {Fa : Matrix (Fin (2 * r + m + 1)) (Fin m) ℂ} {e f : Matrix (Fin (2 * r + m + 1)) (Fin r) ℂ} {y : Fin (2 * r + m + 1) → ℂ} (h1 : Faᴴ * J * Fa = 1) (h2 : eᴴ * J * e = 0) (h3 : fᴴ * J * f = 0) (h4 : eᴴ * J * f = 1) (h5 : Faᴴ * J * e = 0) (h6 : Faᴴ * J * f = 0) (h7 : (Faᴴ * J) *ᵥ y = 0) (h8 : (eᴴ * J) *ᵥ y = 0) (h9 : (fᴴ * J) *ᵥ y = 0) (h10 : Formalism.QuantumDeterminants.herm J y y = -1), ∃ Q Qi : Matrix (Fin (2 * r + m + 1)) (Fin (2 * r + m + 1)) ℂ, Q * Qi = 1 ∧ Qi * Q = 1 ∧ Qᴴ * J * Q = Formalism.QuantumDeterminants.Hpk m r ∧ Q * colE m r = e ∧ Q * colW m r = Fa ∧ Q *ᵥ Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.wI m r (Fin.last m)) = y := by
  first | exact @UpperTheory.Lit.Bur.BesselFrame.exists_frame_matrix | exact UpperTheory.Lit.Bur.BesselFrame.exists_frame_matrix | (intros; apply UpperTheory.Lit.Bur.BesselFrame.exists_frame_matrix <;> assumption)
