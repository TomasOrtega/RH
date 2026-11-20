import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PieceEqPieceT
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ZpowCongrOfModEq

open GlobalTheory.KummerEisensteinGalois

open Finset
open scoped Classical

namespace GlobalTheory.KummerEisensteinGalois

/- English proof (translation)
Establish `h : ∀ x : ℤ, (ζ ^ e) ^ x = ζ ^ ((e : ℤ) * x)`. Introduce `x`. Rewrite using `[← zpow_natCast, ← zpow_mul]`. Simplify using `only [eisF, const0, coefPos, h, mul_assoc, mul_neg]`.
-/
lemma eisF_pow_subst {K : Type} [Field K] [CharZero K] (j M : ℕ) (ζ : K) (e : ℕ) (a₁ a₂ : ℤ) (n : ℕ) :
    eisF j M (ζ ^ e) a₁ a₂ n = eisF j M ζ a₁ ((e : ℤ) * a₂) n := by
  have h : ∀ x : ℤ, (ζ ^ e) ^ x = ζ ^ ((e : ℤ) * x) := by
    intro x; rw [← zpow_natCast, ← zpow_mul]
  simp only [eisF, const0, coefPos, h, mul_assoc, mul_neg]

/- English proof (translation)
Simplify using `only [smF, eisF_pow_subst]`. Rewrite using `[mul_left_comm]`.
-/
lemma smF_pow_subst {K : Type} [Field K] [CharZero K] (c : ℤ) (j M : ℕ) (ζ : K) (e : ℕ) (a₁ a₂ : ℤ) (n : ℕ) :
    smF c j M (ζ ^ e) a₁ a₂ n = smF c j M ζ a₁ ((e : ℤ) * a₂) n := by
  simp only [smF, eisF_pow_subst]
  rw [mul_left_comm]

/- English proof (translation)
Establish `h1 : ζ ^ a₂ = ζ ^ a₂'` using `zpow_congr_of_modEq hζ hM h`. Simplify using `only [eisF, const0, coefPos, zpow_neg, zpow_mul, h1]`.
-/
lemma eisF_congr {K : Type} [Field K] [CharZero K] (j M : ℕ) (ζ : K) (hζ : IsPrimitiveRoot ζ M) (hM : 0 < M)
    (a₁ a₂ a₂' : ℤ) (h : a₂ ≡ a₂' [ZMOD M]) (n : ℕ) :
    eisF j M ζ a₁ a₂ n = eisF j M ζ a₁ a₂' n := by
  have h1 : ζ ^ a₂ = ζ ^ a₂' := zpow_congr_of_modEq hζ hM h
  simp only [eisF, const0, coefPos, zpow_neg, zpow_mul, h1]

/- English proof (translation)
Simplify using `only [smF, eisF_congr j M ζ hζ hM a₁ a₂ a₂' h, eisF_congr j M ζ hζ hM _ _ _ (h.mul_left c)]`.
-/
lemma smF_congr {K : Type} [Field K] [CharZero K] (c : ℤ) (j M : ℕ) (ζ : K) (hζ : IsPrimitiveRoot ζ M) (hM : 0 < M)
    (a₁ a₂ a₂' : ℤ) (h : a₂ ≡ a₂' [ZMOD M]) (n : ℕ) :
    smF c j M ζ a₁ a₂ n = smF c j M ζ a₁ a₂' n := by
  simp only [smF, eisF_congr j M ζ hζ hM a₁ a₂ a₂' h, eisF_congr j M ζ hζ hM _ _ _ (h.mul_left c)]

def diagOneUnit {R : Type} [CommRing R] (b : Rˣ) : GL (Fin 2) R :=
  ⟨Matrix.diagonal ![1, (b : R)], Matrix.diagonal ![1, ((b⁻¹ : Rˣ) : R)],
    by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; fin_cases i <;> simp,
    by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; fin_cases i <;> simp⟩

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [diagOneUnit, Matrix.GeneralLinearGroup.coe_mul, Units.val_mk, Matrix.diagonal_mul_diagonal]`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp`.
-/
lemma diagOneUnit_mul {R : Type} [CommRing R] (a b : Rˣ) : diagOneUnit a * diagOneUnit b = diagOneUnit (a * b) := by
  ext i j
  simp only [diagOneUnit, Matrix.GeneralLinearGroup.coe_mul, Units.val_mk, Matrix.diagonal_mul_diagonal]
  fin_cases i <;> fin_cases j <;> simp

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [diagOneUnit, Units.val_mk, Matrix.GeneralLinearGroup.coe_one]`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp`.
-/
lemma diagOneUnit_one {R : Type} [CommRing R] : diagOneUnit (1 : Rˣ) = 1 := by
  ext i j
  simp only [diagOneUnit, Units.val_mk, Matrix.GeneralLinearGroup.coe_one]
  fin_cases i <;> fin_cases j <;> simp

/- English proof (translation)
Simplify using `[diagOneUnit, Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_diagonal]`.
-/
lemma coe_mul_diagOneUnit {R : Type} [CommRing R] (γ : GL (Fin 2) R) (b : Rˣ) (i : Fin 2) :
    ((γ * diagOneUnit b : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) i 0 = (γ : Matrix (Fin 2) (Fin 2) R) i 0 ∧
    ((γ * diagOneUnit b : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) i 1 = (γ : Matrix (Fin 2) (Fin 2) R) i 1 * b := by
  simp [diagOneUnit, Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_diagonal]

/- English proof (translation)
Simplify using `[diagOneUnit, Matrix.GeneralLinearGroup.coe_mul, Matrix.det_mul, Matrix.det_diagonal, Fin.prod_univ_two]`.
-/
lemma det_mul_diagOneUnit {R : Type} [CommRing R] (γ : GL (Fin 2) R) (b : Rˣ) :
    ((γ * diagOneUnit b : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R).det = (γ : Matrix (Fin 2) (Fin 2) R).det * b := by
  simp [diagOneUnit, Matrix.GeneralLinearGroup.coe_mul, Matrix.det_mul, Matrix.det_diagonal, Fin.prod_univ_two]

/- English proof (translation)
Use function extensionality and compare the values at `n`. Rewrite using `[smF_pow_subst]`. Establish `h1 : (rowT N p m (γ * diagOneUnit b) i w).1 = (rowT N p m γ i w).1`. Simplify using `[rowT, (coe_mul_diagOneUnit γ b i).1]`. Rewrite using `[h1]`.

Establish `hp : 0 < p` using `Nat.pos_of_ne_zero (NeZero.ne p)`. Apply `smF_congr c j _ ζ hζ (by positivity)` to reduce the goal to its premises. Simplify using `only [rowT, (coe_mul_diagOneUnit γ b i).2]`. Rewrite using `[Int.modEq_iff_dvd]`. Establish `h2 : ((p ^ m : ℕ) : ℤ) ∣ (e : ℤ) * (((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ m))) i 1).val : ℤ) - ((((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ m))) i 1 * b).val : ℕ) : ℤ)`.

Rewrite using `[← ZMod.intCast_zmod_eq_zero_iff_dvd]`. Use `push_cast`. Simplify using `[he.1, mul_comm]`. Establish `h3 : (N : ℤ) ∣ (e : ℤ) - 1`. Rewrite using `[← ZMod.intCast_zmod_eq_zero_iff_dvd]`.

Use `push_cast`. Rewrite using `[he.2, sub_self]`. Take `⟨u, hu⟩` from `h2`. Take `⟨v, hv⟩` from `h3`. Use `⟨-(u + w.2 * v), ?_⟩` and prove the remaining obligations.

Move the coercions through the operations in `at hu ⊢`. Take the linear combination `(-(N : ℤ)) * hu - ((p : ℤ) ^ m * w.2) * hv`.
-/
lemma smF_rowT_subst {K : Type} [Field K] [CharZero K] (N p m : ℕ) [NeZero p] (c : ℤ) (j : ℕ) (ζ : K)
    (hζ : IsPrimitiveRoot ζ (N * p ^ m)) (hN : 0 < N) (γ : GL (Fin 2) (ZMod (p ^ m))) (b : (ZMod (p ^ m))ˣ) (e : ℕ)
    (he : ((e : ℕ) : ZMod (p ^ m)) = b ∧ ((e : ℕ) : ZMod N) = 1) (i : Fin 2) (w : ℤ × ℤ) :
    smF c j (N * p ^ m) (ζ ^ e) (rowT N p m γ i w).1 (rowT N p m γ i w).2 =
      smF c j (N * p ^ m) ζ (rowT N p m (γ * diagOneUnit b) i w).1 (rowT N p m (γ * diagOneUnit b) i w).2 := by
  funext n
  rw [smF_pow_subst]
  have h1 : (rowT N p m (γ * diagOneUnit b) i w).1 = (rowT N p m γ i w).1 := by
    simp [rowT, (coe_mul_diagOneUnit γ b i).1]
  rw [h1]
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  apply smF_congr c j _ ζ hζ (by positivity)
  simp only [rowT, (coe_mul_diagOneUnit γ b i).2]
  rw [Int.modEq_iff_dvd]
  have h2 : ((p ^ m : ℕ) : ℤ) ∣ (e : ℤ) * (((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ m))) i 1).val : ℤ) -
      ((((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ m))) i 1 * b).val : ℕ) : ℤ) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    simp [he.1, mul_comm]
  have h3 : (N : ℤ) ∣ (e : ℤ) - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [he.2, sub_self]
  obtain ⟨u, hu⟩ := h2
  obtain ⟨v, hv⟩ := h3
  refine ⟨-(u + w.2 * v), ?_⟩
  push_cast at hu ⊢
  linear_combination (-(N : ℤ)) * hu - ((p : ℤ) ^ m * w.2) * hv

/- English proof (translation)
Introduce `N p m k _ K _ _ ψ c d w w' ζ β _ hN _ _ hζ hβ r`. Unfold `pieceT`. Repeatedly rewrite using `[Finset.mul_sum]`. Rewrite using `[← Finset.sum_product']`. Apply `Finset.sum_nbij' (fun x => x.2 * diagOneUnit x.1) (fun γ => (Matrix.GeneralLinearGroup.det γ, γ * diagOneUnit (Matrix.GeneralLinearGroup.det γ)⁻¹))` to reduce the goal to its premises.

Introduce and unpack `⟨b, γ⟩ h`. Simplify using `only [Finset.mem_product, Finset.mem_filter, unitSet, Finset.mem_univ, true_and] at h ⊢`. Simplify using `only [(coe_mul_diagOneUnit γ b 0).1, (coe_mul_diagOneUnit γ b 1).1]`. Conclude with `h.1`. Introduce `γ h`.

Simplify using `only [Finset.mem_product, Finset.mem_filter, unitSet, Finset.mem_univ, true_and] at h ⊢`. Simplify using `only [(coe_mul_diagOneUnit γ _ 0).1, (coe_mul_diagOneUnit γ _ 1).1]`. Use `⟨h, ?_⟩` and prove the remaining obligations. Rewrite using `[det_mul_diagOneUnit, ← Matrix.GeneralLinearGroup.val_det_apply, Units.mul_inv]`. Introduce and unpack `⟨b, γ⟩ h`.

Simplify using `only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at h`. Establish `hd : Matrix.GeneralLinearGroup.det (γ * diagOneUnit b) = b`. Use `ext`. Rewrite using `[Matrix.GeneralLinearGroup.val_det_apply, det_mul_diagOneUnit, h.2, one_mul]`. Simplify using `only [hd, mul_assoc, diagOneUnit_mul, mul_inv_cancel, diagOneUnit_one, mul_one]`.

Introduce `γ _`. Simplify using `only [mul_assoc, diagOneUnit_mul, inv_mul_cancel, diagOneUnit_one, mul_one]`. Introduce and unpack `⟨b, γ⟩ h`. Simplify using `only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at h`. Simplify using `only`.

Rewrite using `[smF_rowT_subst N p m c (k - 1) ζ hζ hN γ b (β b) (hβ b) 0 w, smF_rowT_subst N p m d 1 ζ hζ hN γ b (β b) (hβ b) 1 w', det_mul_diagOneUnit, h.2, one_mul, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, map_one, one_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem psum_galois_unitPiece : ∀ (N p m k : ℕ) [NeZero p] (K : Type) [Field K] [CharZero K]
    (ψ : DirichletCharacter K (p ^ m)) (c d : ℤ) (w w' : ℤ × ℤ)
    (ζ : K) (β : (ZMod (p ^ m))ˣ → ℕ), p.Prime → 0 < N → Nat.Coprime p N → 1 ≤ m → IsPrimitiveRoot ζ (N * p ^ m) →
    (∀ b, ((β b : ℕ) : ZMod (p ^ m)) = b ∧ ((β b : ℕ) : ZMod N) = 1) →
    ∀ r : ℕ, ∑ b : (ZMod (p ^ m))ˣ, ψ b * pieceT N p m m k (1 : DirichletCharacter K (p ^ m)) c d w w' (ζ ^ β b)
        ((unitSet p m).filter (fun γ => (γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ m))).det = 1)) r =
      pieceT N p m m k ψ c d w w' ζ (unitSet p m) r := by
  intro N p m k _ K _ _ ψ c d w w' ζ β _ hN _ _ hζ hβ r
  unfold pieceT
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_product']
  apply Finset.sum_nbij' (fun x => x.2 * diagOneUnit x.1)
    (fun γ => (Matrix.GeneralLinearGroup.det γ, γ * diagOneUnit (Matrix.GeneralLinearGroup.det γ)⁻¹))
  · rintro ⟨b, γ⟩ h
    simp only [Finset.mem_product, Finset.mem_filter, unitSet, Finset.mem_univ, true_and] at h ⊢
    simp only [(coe_mul_diagOneUnit γ b 0).1, (coe_mul_diagOneUnit γ b 1).1]
    exact h.1
  · intro γ h
    simp only [Finset.mem_product, Finset.mem_filter, unitSet, Finset.mem_univ, true_and] at h ⊢
    simp only [(coe_mul_diagOneUnit γ _ 0).1, (coe_mul_diagOneUnit γ _ 1).1]
    refine ⟨h, ?_⟩
    rw [det_mul_diagOneUnit, ← Matrix.GeneralLinearGroup.val_det_apply, Units.mul_inv]
  · rintro ⟨b, γ⟩ h
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at h
    have hd : Matrix.GeneralLinearGroup.det (γ * diagOneUnit b) = b := by
      ext
      rw [Matrix.GeneralLinearGroup.val_det_apply, det_mul_diagOneUnit, h.2, one_mul]
    simp only [hd, mul_assoc, diagOneUnit_mul, mul_inv_cancel, diagOneUnit_one, mul_one]
  · intro γ _
    simp only [mul_assoc, diagOneUnit_mul, inv_mul_cancel, diagOneUnit_one, mul_one]
  · rintro ⟨b, γ⟩ h
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at h
    dsimp only
    rw [smF_rowT_subst N p m c (k - 1) ζ hζ hN γ b (β b) (hβ b) 0 w,
      smF_rowT_subst N p m d 1 ζ hζ hN γ b (β b) (hβ b) 1 w', det_mul_diagOneUnit, h.2, one_mul,
      ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, map_one, one_mul]
    ring

end GlobalTheory.KummerEisensteinGalois
