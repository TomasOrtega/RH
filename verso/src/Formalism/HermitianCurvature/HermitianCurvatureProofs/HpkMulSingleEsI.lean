import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelZeroKernel

open Matrix
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.SingleEntryHermitianProducts

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

variable {k r : ℕ}

/- English proof (translation)
Use extensionality with `x y`. Simplify using `only [conjTranspose_apply, single_apply]`. Apply the tactic sequence `by_cases h1 : p = y <;> by_cases h2 : q = x <;> simp [h1, h2]`.
-/
theorem single_conjT {n : ℕ} (p q : Fin n) (c : ℂ) : (Matrix.single p q c)ᴴ = Matrix.single q p (star c) := by
  ext x y
  simp only [conjTranspose_apply, single_apply]
  by_cases h1 : p = y <;> by_cases h2 : q = x <;> simp [h1, h2]

/- English proof (translation)
Establish `hc` using `c.isLt`. Simplify using `only [Hpk, eI, esI, Fin.ext_iff]`. Apply the tactic sequence `split_ifs <;> first | rfl | (exfalso; omega)`.
-/
theorem hpk_col_eI (i : Fin (2 * r + k + 1)) (c : Fin r) :
    Hpk k r i (eI k r c) = if i = esI k r c then 1 else 0 := by
  have hc := c.isLt
  simp only [Hpk, eI, esI, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

/- English proof (translation)
Establish `hc` using `c.isLt`. Simplify using `only [Hpk, eI, esI, Fin.ext_iff]`. Apply the tactic sequence `split_ifs <;> first | rfl | (exfalso; omega)`.
-/
theorem hpk_col_esI (i : Fin (2 * r + k + 1)) (c : Fin r) :
    Hpk k r i (esI k r c) = if i = eI k r c then 1 else 0 := by
  have hc := c.isLt
  simp only [Hpk, eI, esI, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

/- English proof (translation)
Use extensionality with `i l`. Distinguish the cases in `hl : l = q`. Substitute `hl` using the available equality. Rewrite using `[mul_single_apply_same, hpk_col_eI, single_apply]`. Apply the tactic sequence `by_cases h : i = esI k r c <;> simp [h, eq_comm]`.

Rewrite using `[mul_single_apply_of_ne _ _ _ _ _ hl, single_apply_of_col_ne _ _ (Ne.symm hl)]`.
-/
theorem hpk_mul_single_eI (c : Fin r) (q : Fin (2 * r + k + 1)) (x : ℂ) :
    Hpk k r * Matrix.single (eI k r c) q x = Matrix.single (esI k r c) q x := by
  ext i l
  by_cases hl : l = q
  · subst hl
    rw [mul_single_apply_same, hpk_col_eI, single_apply]
    by_cases h : i = esI k r c <;> simp [h, eq_comm]
  · rw [mul_single_apply_of_ne _ _ _ _ _ hl, single_apply_of_col_ne _ _ (Ne.symm hl)]

/- English proof (translation)
Use extensionality with `i l`. Distinguish the cases in `hl : l = q`. Substitute `hl` using the available equality. Rewrite using `[mul_single_apply_same, hpk_col_esI, single_apply]`. Apply the tactic sequence `by_cases h : i = eI k r c <;> simp [h, eq_comm]`.

Rewrite using `[mul_single_apply_of_ne _ _ _ _ _ hl, single_apply_of_col_ne _ _ (Ne.symm hl)]`.
-/
theorem hpk_mul_single_esI (c : Fin r) (q : Fin (2 * r + k + 1)) (x : ℂ) :
    Hpk k r * Matrix.single (esI k r c) q x = Matrix.single (eI k r c) q x := by
  ext i l
  by_cases hl : l = q
  · subst hl
    rw [mul_single_apply_same, hpk_col_esI, single_apply]
    by_cases h : i = eI k r c <;> simp [h, eq_comm]
  · rw [mul_single_apply_of_ne _ _ _ _ _ hl, single_apply_of_col_ne _ _ (Ne.symm hl)]

/- English proof (translation)
Use `b.isLt` as an intermediate fact. Use `c.isLt` as an intermediate fact. Simplify using `only [eI, esI, ne_eq, Fin.ext_iff]`. Use linear arithmetic over natural numbers and integers.
-/
theorem eI_ne_esI (b c : Fin r) : eI k r b ≠ esI k r c := by
  have := b.isLt; have := c.isLt
  simp only [eI, esI, ne_eq, Fin.ext_iff]; omega

/- English proof (translation)
Simplify using `only [eI, Fin.ext_iff] at h`. Conclude with `Fin.ext h`.
-/
theorem eI_inj {b c : Fin r} (h : eI k r b = eI k r c) : b = c := by
  simp only [eI, Fin.ext_iff] at h; exact Fin.ext h

/- English proof (translation)
Use `b.isLt` as an intermediate fact. Use `c.isLt` as an intermediate fact. Simplify using `only [esI, Fin.ext_iff] at h; exact Fin.ext (by omega)`.
-/
theorem esI_inj {b c : Fin r} (h : esI k r b = esI k r c) : b = c := by
  have := b.isLt; have := c.isLt
  simp only [esI, Fin.ext_iff] at h; exact Fin.ext (by omega)

section nl

variable (j : ℕ) (hj : j + 1 ≤ r) (a : Fin j → ℂ)

def Xn : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ :=
  ∑ b : Fin j, (a b • Matrix.single (esI k r ⟨j, by omega⟩) (esI k r ⟨b, by omega⟩) (1 : ℂ) -
    conj (a b) • Matrix.single (eI k r ⟨b, by omega⟩) (eI k r ⟨j, by omega⟩) (1 : ℂ))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem nL_eq : LevelPointCoordinates.nL k r j hj a = 1 + Xn j hj a := rfl

/- English proof (translation)
Unfold `Xn`. Rewrite using `[Matrix.mul_sum]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul, hpk_mul_single_esI, hpk_mul_single_eI]`.
-/
theorem hX : Hpk k r * Xn j hj a = ∑ b : Fin j, (a b • Matrix.single (eI k r ⟨j, by omega⟩) (esI k r ⟨b, by omega⟩) (1 : ℂ) -
    conj (a b) • Matrix.single (esI k r ⟨b, by omega⟩) (eI k r ⟨j, by omega⟩) (1 : ℂ)) := by
  unfold Xn
  rw [Matrix.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul, hpk_mul_single_esI, hpk_mul_single_eI]

/- English proof (translation)
Unfold `Xn`. Rewrite using `[Matrix.conjTranspose_sum]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_smul, single_conjT, single_conjT]`. Simplify using the standard rewrite rules.
-/
theorem hXh : (Xn (k := k) j hj a)ᴴ = ∑ b : Fin j, (conj (a b) • Matrix.single (esI k r ⟨b, by omega⟩) (esI k r ⟨j, by omega⟩) (1 : ℂ) -
    a b • Matrix.single (eI k r ⟨j, by omega⟩) (eI k r ⟨b, by omega⟩) (1 : ℂ)) := by
  unfold Xn
  rw [Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_smul, single_conjT, single_conjT]
  simp

/- English proof (translation)
Establish `hH : (Hpk k r)ᴴ = Hpk k r` using `(hpkFacts k r).1`. Establish `e : (Xn (k` using `k) j hj a)ᴴ * Hpk k r = (Hpk k r * Xn j hj a)ᴴ := by`. Rewrite using `[Matrix.conjTranspose_mul, hH]`. Rewrite using `[e, hX, Matrix.conjTranspose_sum, ← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations.

Rewrite using `[Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_smul, single_conjT, single_conjT]`. Simplify using `only [star_one, RCLike.star_def, Complex.conj_conj]`. Normalize the expressions using the abelian group laws.
-/
theorem hXhH : (Xn (k := k) j hj a)ᴴ * Hpk k r = -(Hpk k r * Xn j hj a) := by
  have hH : (Hpk k r)ᴴ = Hpk k r := (hpkFacts k r).1
  have e : (Xn (k := k) j hj a)ᴴ * Hpk k r = (Hpk k r * Xn j hj a)ᴴ := by
    rw [Matrix.conjTranspose_mul, hH]
  rw [e, hX, Matrix.conjTranspose_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_smul, single_conjT, single_conjT]
  simp only [star_one, RCLike.star_def, Complex.conj_conj]
  abel

/- English proof (translation)
Rewrite using `[Matrix.mul_assoc, hX, hXh, Finset.sum_mul_sum]`. Use `Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun b' _ => ?_` and prove the remaining obligations. Establish `n1 : esI k r ⟨j, by omega⟩ ≠ eI k r ⟨j, by omega⟩` using `(eI_ne_esI _ _).symm`. Establish `n2 : esI k r ⟨j, by omega⟩ ≠ esI k r ⟨b', by omega⟩` using `fun h => by`. Use `congrArg Fin.val (esI_inj h)` as an intermediate fact.

Simplify using `at this`. Use linear arithmetic over natural numbers and integers. Establish `n3 : eI k r ⟨b, by omega⟩ ≠ eI k r ⟨j, by omega⟩` using `fun h => by`. Use `congrArg Fin.val (eI_inj h)` as an intermediate fact. Simplify using `at this`.

Use linear arithmetic over natural numbers and integers. Establish `n4 : eI k r ⟨b, by omega⟩ ≠ esI k r ⟨b', by omega⟩` using `eI_ne_esI _ _`. Simplify using `only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, single_mul_single_of_ne _ _ _ _ n1, single_mul_single_of_ne _ _ _ _ n2, single_mul_single_of_ne _ _ _ _ n3, single_mul_single_of_ne _ _ _ _ n4, smul_zero, sub_zero]`.
-/
theorem hXHX : (Xn (k := k) j hj a)ᴴ * Hpk k r * Xn j hj a = 0 := by
  rw [Matrix.mul_assoc, hX, hXh, Finset.sum_mul_sum]
  refine Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun b' _ => ?_
  have n1 : esI k r ⟨j, by omega⟩ ≠ eI k r ⟨j, by omega⟩ := (eI_ne_esI _ _).symm
  have n2 : esI k r ⟨j, by omega⟩ ≠ esI k r ⟨b', by omega⟩ := fun h => by
    have := congrArg Fin.val (esI_inj h); simp at this; omega
  have n3 : eI k r ⟨b, by omega⟩ ≠ eI k r ⟨j, by omega⟩ := fun h => by
    have := congrArg Fin.val (eI_inj h); simp at this; omega
  have n4 : eI k r ⟨b, by omega⟩ ≠ esI k r ⟨b', by omega⟩ := eI_ne_esI _ _
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
    single_mul_single_of_ne _ _ _ _ n1, single_mul_single_of_ne _ _ _ _ n2, single_mul_single_of_ne _ _ _ _ n3,
    single_mul_single_of_ne _ _ _ _ n4, smul_zero, sub_zero]

/- English proof (translation)
Use `show (LevelPointCoordinates.nL k r j hj a)ᴴ * Hpk k r * LevelPointCoordinates.nL k r j hj a = Hpk k r`. Rewrite using `[nL_eq, Matrix.conjTranspose_add, Matrix.conjTranspose_one]`. Establish `h1` using `hXhH (k := k) j hj a`. Establish `h2` using `hXHX (k := k) j hj a`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one]`. Normalize the expressions using the abelian group laws. Use `_ = Hpk k r := by rw [h2, h1]; abel`.
-/
theorem nL_uh : LevelPointCoordinates.nL k r j hj a ∈ UH (Hpk k r) := by
  show (LevelPointCoordinates.nL k r j hj a)ᴴ * Hpk k r * LevelPointCoordinates.nL k r j hj a = Hpk k r
  rw [nL_eq, Matrix.conjTranspose_add, Matrix.conjTranspose_one]
  have h1 := hXhH (k := k) j hj a
  have h2 := hXHX (k := k) j hj a
  calc (1 + (Xn j hj a)ᴴ) * Hpk k r * (1 + Xn j hj a)
      = Hpk k r + ((Xn (k := k) j hj a)ᴴ * Hpk k r + Hpk k r * Xn j hj a) +
          (Xn (k := k) j hj a)ᴴ * Hpk k r * Xn j hj a := by
        simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one]; abel
    _ = Hpk k r := by rw [h2, h1]; abel

/- English proof (translation)
Rewrite using `[nL_eq, Matrix.add_apply, Xn, Matrix.sum_apply]`. Simplify using `only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]`.
-/
theorem nL_apply (p q : Fin (2 * r + k + 1)) :
    LevelPointCoordinates.nL k r j hj a p q = (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) p q +
      ∑ b : Fin j, (a b * Matrix.single (esI k r ⟨j, by omega⟩) (esI k r ⟨b, by omega⟩) (1 : ℂ) p q -
        conj (a b) * Matrix.single (eI k r ⟨b, by omega⟩) (eI k r ⟨j, by omega⟩) (1 : ℂ) p q) := by
  rw [nL_eq, Matrix.add_apply, Xn, Matrix.sum_apply]
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]

/- English proof (translation)
Use `⟨nL_uh j hj a, ?_, ?_⟩` and prove the remaining obligations. Introduce `c i hci`. Rewrite using `[nL_apply, Finset.sum_eq_zero, add_zero]`. Apply the tactic sequence `by_cases h : i = eI k r c <;> simp [h, Matrix.one_apply]`. Introduce `b _`.

Establish `hc` using `c.isLt`. Rewrite using `[single_apply_of_col_ne _ _ (fun h => eI_ne_esI c ⟨b, by omega⟩ h.symm), mul_zero, zero_sub]`. Rewrite using `[single_apply, if_neg, mul_zero, neg_zero]`. Introduce and unpack `⟨h1, h2⟩`. Establish `e1` using `congrArg Fin.val h1`.

Establish `e2` using `congrArg Fin.val h2`. Simplify using `only [eI] at e1 e2`. Use `b.isLt` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Introduce `i q hq1 hq2 hi`.

Rewrite using `[nL_apply, Finset.sum_eq_zero, add_zero]`. Apply the tactic sequence `by_cases h : i = q <;> simp [h, Matrix.one_apply]`. Introduce `b _`. Establish `hb` using `b.isLt`. Rewrite using `[single_apply, if_neg, single_apply, if_neg, mul_zero, mul_zero, sub_zero]`.

Introduce and unpack `⟨_, h2⟩`. Establish `e2` using `congrArg Fin.val h2`. Simplify using `only [eI] at e2`. Use linear arithmetic over natural numbers and integers. Introduce and unpack `⟨_, h2⟩`.

Establish `e2` using `congrArg Fin.val h2`. Simplify using `only [esI] at e2`. Use linear arithmetic over natural numbers and integers.
-/
theorem nL_mem : LevelPointCoordinates.nL k r j hj a ∈ Nset k r := by
  refine ⟨nL_uh j hj a, ?_, ?_⟩
  · intro c i hci
    rw [nL_apply, Finset.sum_eq_zero, add_zero]
    · by_cases h : i = eI k r c <;> simp [h, Matrix.one_apply]
    · intro b _
      have hc := c.isLt
      rw [single_apply_of_col_ne _ _ (fun h => eI_ne_esI c ⟨b, by omega⟩ h.symm), mul_zero, zero_sub]
      rw [single_apply, if_neg, mul_zero, neg_zero]
      rintro ⟨h1, h2⟩
      have e1 := congrArg Fin.val h1; have e2 := congrArg Fin.val h2
      simp only [eI] at e1 e2
      have := b.isLt
      omega
  · intro i q hq1 hq2 hi
    rw [nL_apply, Finset.sum_eq_zero, add_zero]
    · by_cases h : i = q <;> simp [h, Matrix.one_apply]
    · intro b _
      have hb := b.isLt
      rw [single_apply, if_neg, single_apply, if_neg, mul_zero, mul_zero, sub_zero]
      · rintro ⟨_, h2⟩
        have e2 := congrArg Fin.val h2; simp only [eI] at e2; omega
      · rintro ⟨_, h2⟩
        have e2 := congrArg Fin.val h2; simp only [esI] at e2; omega

end nl

end Formalism.FourierDecayAlt.P.SingleEntryHermitianProducts
