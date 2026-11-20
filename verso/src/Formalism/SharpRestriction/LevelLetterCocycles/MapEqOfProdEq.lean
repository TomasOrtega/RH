import Formalism.WachLatticeTwists.RamifiedBlockRings.RamifiedBlockProofs.ChainWithExtensionOfSplit

noncomputable section

namespace Formalism.MainNotions.N.RepresentationBoundsCohomology

open Matrix Polynomial Formalism.RepresentationBoundsCohomology.ringDataObjects

section GlobalTheory

variable (r t : ℕ)

def blkG (a : Fin (r + t)) : Fin (t + 1) :=
  if _h : (a : ℕ) < r then 0 else ⟨(a : ℕ) - r + 1, by have := a.2; omega⟩

/- English proof (translation)
Rewrite using `[blkG, dif_pos (by simp)]`.
-/
theorem blkG_castAdd (a : Fin r) : blkG r t (Fin.castAdd t a) = 0 := by
  rw [blkG, dif_pos (by simp)]

/- English proof (translation)
Rewrite using `[blkG, dif_neg (by simp only [Fin.coe_natAdd]; omega)]`. Use `ext`. Simplify using the standard rewrite rules.
-/
theorem blkG_natAdd (c : Fin t) : blkG r t (Fin.natAdd r c) = c.succ := by
  rw [blkG, dif_neg (by simp only [Fin.coe_natAdd]; omega)]
  ext
  simp

variable (K : Type) [CommRing K]

def eG : (Fin (r + t) → K) ≃ₗ[K] ((Fin r → K) × (Fin t → K)) :=
  (LinearEquiv.funCongrLeft K K finSumFinEquiv).trans
    (LinearEquiv.sumArrowLequivProdArrow (Fin r) (Fin t) K K)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem eG_apply (u : Fin (r + t) → K) :
    eG r t K u = (fun a => u (Fin.castAdd t a), fun c => u (Fin.natAdd r c)) := rfl

variable {r t K}

/- English proof (translation)
Simplify using `only [eG_apply]`. Use extensionality with `a`. Simplify using `only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply]`. Rewrite using `[Fin.sum_univ_add]`. Establish `h0 : ∀ c : Fin t, M (Fin.castAdd t a) (Fin.natAdd r c) = 0` using `fun c => hM _ _ (by rw [blkG_castAdd, blkG_natAdd]; exact (Fin.succ_ne_zero c).symm)`.

Simplify using `[h0]`. Simplify using `only [Matrix.mulVec, dotProduct]`. Rewrite using `[Fin.sum_univ_add]`. Establish `h1 : ∀ b : Fin r, M (Fin.natAdd r a) (Fin.castAdd t b) = 0` using `fun b => hM _ _ (by rw [blkG_castAdd, blkG_natAdd]; exact Fin.succ_ne_zero a)`. Establish `h2 : ∀ c : Fin t, c ≠ a → M (Fin.natAdd r a) (Fin.natAdd r c) = 0` using `fun c hc => hM _ _ (by rw [blkG_natAdd, blkG_natAdd]; exact fun h => hc (Fin.succ_injective _ h).symm)`.

Simplify using `only [h1, zero_mul, Finset.sum_const_zero, zero_add]`. Rewrite using `[Finset.sum_eq_single a (fun c _ hc => by rw [h2 c hc, zero_mul]) (by simp)]`.
-/
theorem eG_mulVec (M : Matrix (Fin (r + t)) (Fin (r + t)) K)
    (hM : ∀ a b, blkG r t a ≠ blkG r t b → M a b = 0) (u : Fin (r + t) → K) :
    eG r t K (M *ᵥ u) = ((M.submatrix (Fin.castAdd t) (Fin.castAdd t)) *ᵥ (eG r t K u).1,
      fun c => M (Fin.natAdd r c) (Fin.natAdd r c) * (eG r t K u).2 c) := by
  simp only [eG_apply]
  ext a
  · simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply]
    rw [Fin.sum_univ_add]
    have h0 : ∀ c : Fin t, M (Fin.castAdd t a) (Fin.natAdd r c) = 0 := fun c =>
      hM _ _ (by rw [blkG_castAdd, blkG_natAdd]; exact (Fin.succ_ne_zero c).symm)
    simp [h0]
  · simp only [Matrix.mulVec, dotProduct]
    rw [Fin.sum_univ_add]
    have h1 : ∀ b : Fin r, M (Fin.natAdd r a) (Fin.castAdd t b) = 0 := fun b =>
      hM _ _ (by rw [blkG_castAdd, blkG_natAdd]; exact Fin.succ_ne_zero a)
    have h2 : ∀ c : Fin t, c ≠ a → M (Fin.natAdd r a) (Fin.natAdd r c) = 0 := fun c hc =>
      hM _ _ (by rw [blkG_natAdd, blkG_natAdd]; exact fun h => hc (Fin.succ_injective _ h).symm)
    simp only [h1, zero_mul, Finset.sum_const_zero, zero_add]
    rw [Finset.sum_eq_single a (fun c _ hc => by rw [h2 c hc, zero_mul]) (by simp)]

end GlobalTheory

section Pts

variable {O Y : Type} [CommRing O] [IsDomain O] (t : ℕ) (P : Y → O[X])

end Pts

section EE

variable {A : Type} [CommRing A] {d : Type} [Fintype d] [DecidableEq d]

end EE

section Gen2

variable {r t : ℕ} {A : Type} [CommRing A]

/- English proof (translation)
Unfold `blkG at h ha`. Distinguish the cases in `h1 : (a : ℕ) < r`. Rewrite `ha` using `[dif_pos h1]`. Conclude with `absurd rfl ha`. Distinguish the cases in `h2 : (b : ℕ) < r`.

Rewrite `h` using `[dif_pos h2, dif_neg h1]`. Conclude with `absurd (congrArg Fin.val h) (by simp)`. Rewrite `h` using `[dif_neg h1, dif_neg h2]`. Establish `h3 : (a : ℕ) - r + 1 = (b : ℕ) - r + 1` using `congrArg Fin.val h`. Conclude with `Fin.ext (by omega)`.
-/
theorem blkG_inj {a b : Fin (r + t)} (h : blkG r t a = blkG r t b) (ha : blkG r t a ≠ 0) : a = b := by
  unfold blkG at h ha
  by_cases h1 : (a : ℕ) < r
  · rw [dif_pos h1] at ha
    exact absurd rfl ha
  · by_cases h2 : (b : ℕ) < r
    · rw [dif_pos h2, dif_neg h1] at h
      exact absurd (congrArg Fin.val h) (by simp)
    · rw [dif_neg h1, dif_neg h2] at h
      have h3 : (a : ℕ) - r + 1 = (b : ℕ) - r + 1 := congrArg Fin.val h
      exact Fin.ext (by omega)

/- English proof (translation)
Use extensionality with `a b`. Rewrite using `[Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.diagonal_apply]`. Distinguish the cases in `hab : a = b`. Apply the tactic sequence `subst hab split_ifs <;> simp_all`. Rewrite using `[if_neg hab]`.

Distinguish the cases in `ha : blkG r t a = 0`. Simplify using `[ha]`. Distinguish the cases in `hb : blkG r t b = 0`. Simplify using `[hb]`. Establish `hne : blkG r t a ≠ blkG r t b` using `fun h => hab (blkG_inj h ha)`.

Simplify using `[hM a b hne]`.
-/
theorem diag_conj (M : Matrix (Fin (r + t)) (Fin (r + t)) A)
    (hM : ∀ a b, blkG r t a ≠ blkG r t b → M a b = 0) :
    (Matrix.diagonal fun a => if blkG r t a = 0 then (0 : A) else 1) * M *
        (Matrix.diagonal fun a => if blkG r t a = 0 then (0 : A) else 1) =
      Matrix.diagonal fun a => if blkG r t a = 0 then 0 else M a a := by
  ext a b
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.diagonal_apply]
  by_cases hab : a = b
  · subst hab
    split_ifs <;> simp_all
  · rw [if_neg hab]
    by_cases ha : blkG r t a = 0
    · simp [ha]
    · by_cases hb : blkG r t b = 0
      · simp [hb]
      · have hne : blkG r t a ≠ blkG r t b := fun h => hab (blkG_inj h ha)
        simp [hM a b hne]

end Gen2

end Formalism.MainNotions.N.RepresentationBoundsCohomology

end
