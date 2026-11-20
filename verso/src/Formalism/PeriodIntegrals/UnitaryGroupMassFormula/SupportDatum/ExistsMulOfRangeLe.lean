import Mathlib

namespace PI.SupportDatumW

open Matrix

def CokDet : Prop := ∀ (R : Type) [CommRing R] (n : ℕ) (Z Z' : Matrix (Fin n) (Fin n) R),
  Z.det ∈ nonZeroDivisors R → Z'.det ∈ nonZeroDivisors R →
  Nonempty (((Fin n → R) ⧸ LinearMap.range Z.mulVecLin) ≃ₗ[R]
    ((Fin n → R) ⧸ LinearMap.range Z'.mulVecLin)) →
  ∃ u : Rˣ, Z'.det = u * Z.det

section

variable {R : Type} [CommRing R]

/- English proof (translation)
Take `⟨h, hh⟩` from `Module.projective_lifting_property (LinearMap.range Z'.mulVecLin).mkQ (φ ∘ₗ (LinearMap.range Z.mulVecLin).mkQ) (Submodule.mkQ_surjective _)`. Use `⟨LinearMap.toMatrix' h, fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.toMatrix'_mulVec]`. Conclude with `LinearMap.congr_fun hh x`.
-/
theorem exists_lift {n : ℕ} (Z Z' : Matrix (Fin n) (Fin n) R)
    (φ : ((Fin n → R) ⧸ LinearMap.range Z.mulVecLin) →ₗ[R]
      ((Fin n → R) ⧸ LinearMap.range Z'.mulVecLin)) :
    ∃ A : Matrix (Fin n) (Fin n) R, ∀ x : Fin n → R,
      Submodule.Quotient.mk (p := LinearMap.range Z'.mulVecLin) (A *ᵥ x) =
        φ (Submodule.Quotient.mk x) := by
  obtain ⟨h, hh⟩ := Module.projective_lifting_property (LinearMap.range Z'.mulVecLin).mkQ
    (φ ∘ₗ (LinearMap.range Z.mulVecLin).mkQ) (Submodule.mkQ_surjective _)
  refine ⟨LinearMap.toMatrix' h, fun x => ?_⟩
  rw [LinearMap.toMatrix'_mulVec]
  exact LinearMap.congr_fun hh x

/- English proof (translation)
Establish `hcol : ∀ j, ∃ g : m → R, Q *ᵥ g = P.col j` using `fun j => by`. Take `⟨g, hg⟩` from `h (LinearMap.mem_range_self P.mulVecLin (Pi.single j 1))`. Conclude with `⟨g, by simpa [Matrix.mulVecLin_apply, Matrix.mulVec_single_one] using hg⟩`. Use `choose g hg using hcol`. Use `⟨Matrix.of fun k j => g j k, ?_⟩` and prove the remaining obligations.

Use extensionality with `i j`. Establish `hij` using `congr_fun (hg j) i`. Simplify using `only [Matrix.col_apply] at hij`. Rewrite using `[Matrix.mul_apply, ← hij]`. Simplify using `[Matrix.mulVec, dotProduct]`.
-/
theorem exists_mul_of_range_le {m : Type} [Fintype m] [DecidableEq m] (P Q : Matrix m m R)
    (h : LinearMap.range P.mulVecLin ≤ LinearMap.range Q.mulVecLin) :
    ∃ G : Matrix m m R, P = Q * G := by
  have hcol : ∀ j, ∃ g : m → R, Q *ᵥ g = P.col j := fun j => by
    obtain ⟨g, hg⟩ := h (LinearMap.mem_range_self P.mulVecLin (Pi.single j 1))
    exact ⟨g, by simpa [Matrix.mulVecLin_apply, Matrix.mulVec_single_one] using hg⟩
  choose g hg using hcol
  refine ⟨Matrix.of fun k j => g j k, ?_⟩
  ext i j
  have hij := congr_fun (hg j) i
  simp only [Matrix.col_apply] at hij
  rw [Matrix.mul_apply, ← hij]
  simp [Matrix.mulVec, dotProduct]

end

/- English proof (translation)
Introduce `R _ n Z Z' _ hZ' ⟨φ⟩`. Take `⟨A, hA⟩` from `exists_lift Z Z' φ.toLinearMap`. Take `⟨A', hA'⟩` from `exists_lift Z' Z φ.symm.toLinearMap`. Use `set M1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R := fromBlocks 1 0 A Z' with hM1`. Use `set M2 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R := fromBlocks Z A' 0 1 with hM2`.

Establish `h12 : LinearMap.range M1.mulVecLin ≤ LinearMap.range M2.mulVecLin`. Introduce and unpack `_ ⟨v, rfl⟩`. Use `set u := v ∘ Sum.inl with hu`. Use `set w := v ∘ Sum.inr with hw`. Use `set q := A *ᵥ u + Z' *ᵥ w with hq`.

Establish `h0 : Submodule.Quotient.mk (p` using `LinearMap.range Z'.mulVecLin) (Z' *ᵥ w) = 0 := (Submodule.Quotient.mk_eq_zero _).2 ⟨w, rfl⟩`. Establish `hmem : u - A' *ᵥ q ∈ LinearMap.range Z.mulVecLin`. Rewrite using `[← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, hA', hq, Submodule.Quotient.mk_add, h0, add_zero, hA]`. Simplify using the standard rewrite rules. Take `⟨p, hp⟩` from `hmem`.

Rewrite `hp` using `[Matrix.mulVecLin_apply]`. Use `⟨Sum.elim p q, ?_⟩` and prove the remaining obligations. Establish `e1 : Z *ᵥ p + A' *ᵥ q = 1 *ᵥ u + 0 *ᵥ w` using `by rw [hp]; simp`. Establish `e2 : 0 *ᵥ p + 1 *ᵥ q = A *ᵥ u + Z' *ᵥ w` using `by simp [hq]`. Rewrite using `[Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, hM1, hM2, fromBlocks_mulVec, fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr, e1, e2]`.

Establish `h21 : LinearMap.range M2.mulVecLin ≤ LinearMap.range M1.mulVecLin`. Introduce and unpack `_ ⟨v, rfl⟩`. Use `set p := v ∘ Sum.inl with hp`. Use `set q := v ∘ Sum.inr with hq`. Use `set u := Z *ᵥ p + A' *ᵥ q with hu`.

Establish `h0 : Submodule.Quotient.mk (p` using `LinearMap.range Z.mulVecLin) (Z *ᵥ p) = 0 := (Submodule.Quotient.mk_eq_zero _).2 ⟨p, rfl⟩`. Establish `hmem : q - A *ᵥ u ∈ LinearMap.range Z'.mulVecLin`. Rewrite using `[← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, hA, hu, Submodule.Quotient.mk_add, h0, zero_add, hA']`. Simplify using the standard rewrite rules. Take `⟨w, hw⟩` from `hmem`.

Rewrite `hw` using `[Matrix.mulVecLin_apply]`. Use `⟨Sum.elim u w, ?_⟩` and prove the remaining obligations. Establish `e1 : 1 *ᵥ u + 0 *ᵥ w = Z *ᵥ p + A' *ᵥ q` using `by simp [hu]`. Establish `e2 : A *ᵥ u + Z' *ᵥ w = 0 *ᵥ p + 1 *ᵥ q` using `by rw [hw]; simp`. Rewrite using `[Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, hM1, hM2, fromBlocks_mulVec, fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr, e1, e2]`.

Take `⟨G, hG⟩` from `exists_mul_of_range_le M1 M2 h12`. Take `⟨G', hG'⟩` from `exists_mul_of_range_le M2 M1 h21`. Establish `d1 : M1.det = Z'.det` using `by rw [hM1, det_fromBlocks_zero₁₂]; simp`. Establish `d2 : M2.det = Z.det` using `by rw [hM2, det_fromBlocks_zero₂₁]; simp`. Establish `e1 : Z'.det = Z.det * G.det` using `by rw [← d1, ← d2, ← det_mul, ← hG]`.

Establish `e2 : Z.det = Z'.det * G'.det` using `by rw [← d1, ← d2, ← det_mul, ← hG']`. Establish `hzero : (G.det * G'.det - 1) * Z'.det = 0`. Combine the equalities or inequalities in the displayed calculation. Establish `hGG : G.det * G'.det = 1` using `sub_eq_zero.mp (mem_nonZeroDivisors_iff_right.mp hZ' _ hzero)`. Use `⟨⟨G.det, G'.det, hGG, by rw [mul_comm, hGG]⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[Units.val_mk, e1, mul_comm]`.
-/
theorem cokernel_determinant : CokDet := by
  intro R _ n Z Z' _ hZ' ⟨φ⟩
  classical
  obtain ⟨A, hA⟩ := exists_lift Z Z' φ.toLinearMap
  obtain ⟨A', hA'⟩ := exists_lift Z' Z φ.symm.toLinearMap
  set M1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R := fromBlocks 1 0 A Z' with hM1
  set M2 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R := fromBlocks Z A' 0 1 with hM2
  have h12 : LinearMap.range M1.mulVecLin ≤ LinearMap.range M2.mulVecLin := by
    rintro _ ⟨v, rfl⟩
    set u := v ∘ Sum.inl with hu
    set w := v ∘ Sum.inr with hw
    set q := A *ᵥ u + Z' *ᵥ w with hq
    have h0 : Submodule.Quotient.mk (p := LinearMap.range Z'.mulVecLin) (Z' *ᵥ w) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).2 ⟨w, rfl⟩
    have hmem : u - A' *ᵥ q ∈ LinearMap.range Z.mulVecLin := by
      rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, hA', hq,
        Submodule.Quotient.mk_add, h0, add_zero, hA]
      simp
    obtain ⟨p, hp⟩ := hmem
    rw [Matrix.mulVecLin_apply] at hp
    refine ⟨Sum.elim p q, ?_⟩
    have e1 : Z *ᵥ p + A' *ᵥ q = 1 *ᵥ u + 0 *ᵥ w := by rw [hp]; simp
    have e2 : 0 *ᵥ p + 1 *ᵥ q = A *ᵥ u + Z' *ᵥ w := by simp [hq]
    rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, hM1, hM2, fromBlocks_mulVec,
      fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr, e1, e2]
  have h21 : LinearMap.range M2.mulVecLin ≤ LinearMap.range M1.mulVecLin := by
    rintro _ ⟨v, rfl⟩
    set p := v ∘ Sum.inl with hp
    set q := v ∘ Sum.inr with hq
    set u := Z *ᵥ p + A' *ᵥ q with hu
    have h0 : Submodule.Quotient.mk (p := LinearMap.range Z.mulVecLin) (Z *ᵥ p) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).2 ⟨p, rfl⟩
    have hmem : q - A *ᵥ u ∈ LinearMap.range Z'.mulVecLin := by
      rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, hA, hu,
        Submodule.Quotient.mk_add, h0, zero_add, hA']
      simp
    obtain ⟨w, hw⟩ := hmem
    rw [Matrix.mulVecLin_apply] at hw
    refine ⟨Sum.elim u w, ?_⟩
    have e1 : 1 *ᵥ u + 0 *ᵥ w = Z *ᵥ p + A' *ᵥ q := by simp [hu]
    have e2 : A *ᵥ u + Z' *ᵥ w = 0 *ᵥ p + 1 *ᵥ q := by rw [hw]; simp
    rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, hM1, hM2, fromBlocks_mulVec,
      fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr, e1, e2]
  obtain ⟨G, hG⟩ := exists_mul_of_range_le M1 M2 h12
  obtain ⟨G', hG'⟩ := exists_mul_of_range_le M2 M1 h21
  have d1 : M1.det = Z'.det := by rw [hM1, det_fromBlocks_zero₁₂]; simp
  have d2 : M2.det = Z.det := by rw [hM2, det_fromBlocks_zero₂₁]; simp
  have e1 : Z'.det = Z.det * G.det := by rw [← d1, ← d2, ← det_mul, ← hG]
  have e2 : Z.det = Z'.det * G'.det := by rw [← d1, ← d2, ← det_mul, ← hG']
  have hzero : (G.det * G'.det - 1) * Z'.det = 0 := by
    calc (G.det * G'.det - 1) * Z'.det = (Z'.det * G'.det) * G.det - Z'.det := by ring
      _ = 0 := by rw [← e2, ← e1, sub_self]
  have hGG : G.det * G'.det = 1 :=
    sub_eq_zero.mp (mem_nonZeroDivisors_iff_right.mp hZ' _ hzero)
  refine ⟨⟨G.det, G'.det, hGG, by rw [mul_comm, hGG]⟩, ?_⟩
  rw [Units.val_mk, e1, mul_comm]

end PI.SupportDatumW
