import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RCocompactPfMemSteps
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RCocompactPfConj

noncomputable section

open scoped Classical
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Pf.UnipB Formalism.L2.SG.Pf.Unip

namespace Formalism.L2.SG.TermOp.Vanish

section MemConj

variable {D : D7} (X : HidaSetting D)

/- English proof (translation)
Unfold `Gr`. Establish `h1` using `Bm_mul_Bm' X`. Establish `h2 : Bm' X * Bm X = 1` using `Bm'_mul_Bm X`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc (Bm X) (Bm' X), h1, Matrix.one_mul]`.

Establish `h3 : (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) * (((M⁻¹ : GL (Fin X.B.I.n) X.B.I.E) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) * Bm X) = Bm X`. Rewrite using `[← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]`. Rewrite using `[h3, h2]`.
-/
theorem mc_gr_mul_inv (M : GL (Fin X.B.I.n) X.B.I.E) :
    Gr X (M : Matrix _ _ _) * Gr X (↑M⁻¹ : Matrix _ _ _) = 1 := by
  unfold Gr
  have h1 := Bm_mul_Bm' X
  have h2 : Bm' X * Bm X = 1 := Bm'_mul_Bm X
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Bm X) (Bm' X), h1, Matrix.one_mul]
  have h3 : (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *
      (((M⁻¹ : GL (Fin X.B.I.n) X.B.I.E) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) * Bm X) = Bm X := by
    rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
  rw [h3, h2]

/- English proof (translation)
Establish `hc : Formalism.UG.cT (starRingEnd X.B.I.E) (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) = (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E)ᴴ`. Use extensionality with `i j`. Unfold `Formalism.UG.cT`. Simplify using `[Matrix.conjTranspose_apply, starRingEnd_apply]`. Establish `hMJ : (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E)ᴴ * X.B.I.J * (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) = X.B.I.J`.

Rewrite using `[← hc]`. Conclude with `hM`. Establish `hJB : JB X = (Bm X)ᴴ * X.B.I.J * Bm X`. Use extensionality with `k k'`. Unfold `JB hE Formalism.UG.hform Bm`.

Simplify using `only [Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul, starRingEnd_apply]`. Rewrite using `[Finset.sum_comm]`. Establish `h1` using `Bm_mul_Bm' X`. Establish `h5 : ∀ Z : Matrix (Fin X.B.I.n) (Kap X) X.B.I.E, (Bm' X)ᴴ * ((Bm X)ᴴ * Z) = Z` using `fun Z => by`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one, Matrix.one_mul]`.

Rewrite using `[hJB]`. Unfold `Gr`. Simplify using `only [Matrix.conjTranspose_mul, Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc (Bm X) (Bm' X), h1, Matrix.one_mul, h5]`. Establish `h4 : (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E)ᴴ * (X.B.I.J * ((M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) * Bm X)) = X.B.I.J * Bm X`.

Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, hMJ]`. Rewrite using `[h4]`.
-/
theorem mc_gr_unitary (M : GL (Fin X.B.I.n) X.B.I.E) (hM : M ∈ Formalism.UG.UJ (starRingEnd X.B.I.E) X.B.I.J) :
    (Gr X (M : Matrix _ _ _))ᴴ * JB X * Gr X (M : Matrix _ _ _) = JB X := by
  have hc : Formalism.UG.cT (starRingEnd X.B.I.E) (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) =
      (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E)ᴴ := by
    ext i j
    unfold Formalism.UG.cT
    simp [Matrix.conjTranspose_apply, starRingEnd_apply]
  have hMJ : (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E)ᴴ * X.B.I.J *
      (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) = X.B.I.J := by
    rw [← hc]
    exact hM
  have hJB : JB X = (Bm X)ᴴ * X.B.I.J * Bm X := by
    ext k k'
    unfold JB hE Formalism.UG.hform Bm
    simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul, starRingEnd_apply]
    rw [Finset.sum_comm]
  have h1 := Bm_mul_Bm' X
  have h5 : ∀ Z : Matrix (Fin X.B.I.n) (Kap X) X.B.I.E, (Bm' X)ᴴ * ((Bm X)ᴴ * Z) = Z := fun Z => by
    rw [← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one, Matrix.one_mul]
  rw [hJB]
  unfold Gr
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Bm X) (Bm' X), h1, Matrix.one_mul, h5]
  have h4 : (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E)ᴴ * (X.B.I.J *
      ((M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) * Bm X)) = X.B.I.J * Bm X := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hMJ]
  rw [h4]

/- English proof (translation)
Introduce `D X M hM`. Use `letI : Invertible (2 : X.B.I.E) := invertibleOfNonzero two_ne_zero`. Establish `h1 : Gr X (M : Matrix _ _ _) * Gr X (↑M⁻¹ : Matrix _ _ _) = 1` using `mc_gr_mul_inv X M`. Establish `h2 : Gr X (↑M⁻¹ : Matrix _ _ _) * Gr X (M : Matrix _ _ _) = 1`. Use `mc_gr_mul_inv X M⁻¹` as an intermediate fact.

Rewrite `this` using `[inv_inv]`. Then use the resulting hypothesis. Establish `hU` using `mc_gr_unitary X M hM`. Use `⟨fun Z => ?_, fun Z hZ => ?_, ?_⟩` and prove the remaining obligations. Establish `hBB : ∀ Y : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E, Bm X * (Bm' X * Y) = Y`. Introduce `Y`.

Rewrite using `[← Matrix.mul_assoc, Bm_mul_Bm', Matrix.one_mul]`. Unfold `Formalism.L2.SG.Pf.UnipB.gE`. Rewrite using `[← conj_cay h1]`. Unfold `Gr`. Simplify using `only [Matrix.mul_assoc, hBB, Bm_mul_Bm', Matrix.mul_one]`.

Use `set G := Gr X (M : Matrix _ _ _) with hG`. Use `set G' := Gr X (↑M⁻¹ : Matrix _ _ _) with hG'`. Establish `hA : Gᴴ * JB X = JB X * G'`. Combine the equalities or inequalities in the displayed calculation. Establish `hB : G'ᴴ * JB X = JB X * G`.

Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = Gᴴ * (Zᴴ * JB X) * G := by rw [hB]; simp only [Matrix.mul_assoc]`.

Use `_ = Gᴴ * (-(JB X * Z)) * G := by rw [hZ]`. Use `_ = -(Gᴴ * JB X * Z * G) := by simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]`. Use `_ = -(JB X * (G' * Z * G)) := by rw [hA]; simp only [Matrix.mul_assoc]`. Take `⟨y, hy0, hy⟩` from `exists_integral_multiples ℤ ℚ ((Finset.univ.image fun ij : Kap X × Kap X => Gr X (↑M⁻¹ : Matrix _ _ _) ij.1 ij.2) ∪ (Finset.univ.image fun ij : Kap X × Kap X => Gr X (M : Matrix _ _ _) ij.1 ij.2))`. Establish `hint : ∀ z ∈ ((Finset.univ.image fun ij : Kap X × Kap X => Gr X (↑M⁻¹ : Matrix _ _ _) ij.1 ij.2) ∪ (Finset.univ.image fun ij : Kap X × Kap X => Gr X (M : Matrix _ _ _) ij.1 ij.2)), (y.natAbs : X.B.I.E) * z ∈ integralClosure ℤ X.B.I.E`.

Introduce `z hz`. Rewrite using `[mem_integralClosure_iff]`. Establish `h` using `hy z hz`. Rewrite `h` using `[zsmul_eq_mul]`. Break down `Int.natAbs_eq y with e | e` into its components or cases.

Rewrite `h` using `[e]`. Simplify using `using h`. Rewrite `h` using `[e]`. Establish `h'` using `h.neg`. Simplify `h'` using `[neg_mul]`.

Establish `hP : ∀ i j, (y.natAbs : X.B.I.E) * Gr X (↑M⁻¹ : Matrix _ _ _) i j ∈ integralClosure ℤ X.B.I.E` using `fun i j => hint _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩))`. Establish `hQ : ∀ i j, (y.natAbs : X.B.I.E) * Gr X (M : Matrix _ _ _) i j ∈ integralClosure ℤ X.B.I.E` using `fun i j => hint _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩))`. Set `P1 : Matrix (Kap X) (Kap X) (𝓞 X.B.I.E)` to `Matrix.of fun i j => ⟨_, hP i j⟩`. Set `Q1 : Matrix (Kap X) (Kap X) (𝓞 X.B.I.E)` to `Matrix.of fun i j => ⟨_, hQ i j⟩`. Establish `hP1 : P1.map (fun a => (a : X.B.I.E)) = (y.natAbs : X.B.I.E) • Gr X (↑M⁻¹ : Matrix _ _ _)`.

Use extensionality with `i j`. Both sides reduce to the same expression. Establish `hQ1 : Q1.map (fun a => (a : X.B.I.E)) = (y.natAbs : X.B.I.E) • Gr X (M : Matrix _ _ _)`. Use extensionality with `i j`. Both sides reduce to the same expression.

Establish `hmap : ∀ U V : Matrix (Kap X) (Kap X) (𝓞 X.B.I.E), (U * V).map (fun a => (a : X.B.I.E)) = U.map (fun a => (a : X.B.I.E)) * V.map (fun a => (a : X.B.I.E))` using `fun U V => Matrix.map_mul (f := algebraMap (𝓞 X.B.I.E) X.B.I.E)`. Use `⟨y.natAbs * y.natAbs, Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (Int.natAbs_ne_zero.mpr hy0) (Int.natAbs_ne_zero.mpr hy0)), fun d A => ⟨P1 * A * Q1, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[hmap, hmap, hP1, hQ1]`. Simplify using `only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Nat.cast_mul]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem memConjOf_holds : MemConjOf := by
  intro D X M hM
  letI : Invertible (2 : X.B.I.E) := invertibleOfNonzero two_ne_zero
  have h1 : Gr X (M : Matrix _ _ _) * Gr X (↑M⁻¹ : Matrix _ _ _) = 1 := mc_gr_mul_inv X M
  have h2 : Gr X (↑M⁻¹ : Matrix _ _ _) * Gr X (M : Matrix _ _ _) = 1 := by
    have := mc_gr_mul_inv X M⁻¹
    rwa [inv_inv] at this
  have hU := mc_gr_unitary X M hM
  refine ⟨fun Z => ?_, fun Z hZ => ?_, ?_⟩
  ·
    have hBB : ∀ Y : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E, Bm X * (Bm' X * Y) = Y := by
      intro Y
      rw [← Matrix.mul_assoc, Bm_mul_Bm', Matrix.one_mul]
    unfold Formalism.L2.SG.Pf.UnipB.gE
    rw [← conj_cay h1]
    unfold Gr
    simp only [Matrix.mul_assoc, hBB, Bm_mul_Bm', Matrix.mul_one]
  ·
    set G := Gr X (M : Matrix _ _ _) with hG
    set G' := Gr X (↑M⁻¹ : Matrix _ _ _) with hG'
    have hA : Gᴴ * JB X = JB X * G' := by
      calc Gᴴ * JB X = Gᴴ * JB X * (G * G') := by rw [h1, Matrix.mul_one]
        _ = Gᴴ * JB X * G * G' := by simp only [Matrix.mul_assoc]
        _ = JB X * G' := by rw [hU]
    have hB : G'ᴴ * JB X = JB X * G := by
      calc G'ᴴ * JB X = G'ᴴ * (Gᴴ * JB X * G) := by rw [hU]
        _ = (G * G')ᴴ * JB X * G := by rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
        _ = JB X * G := by rw [h1, Matrix.conjTranspose_one, Matrix.one_mul]
    calc (G' * Z * G)ᴴ * JB X = Gᴴ * Zᴴ * (G'ᴴ * JB X) := by
          rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
          simp only [Matrix.mul_assoc]
      _ = Gᴴ * (Zᴴ * JB X) * G := by rw [hB]; simp only [Matrix.mul_assoc]
      _ = Gᴴ * (-(JB X * Z)) * G := by rw [hZ]
      _ = -(Gᴴ * JB X * Z * G) := by simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
      _ = -(JB X * (G' * Z * G)) := by rw [hA]; simp only [Matrix.mul_assoc]
  ·
    obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ
      ((Finset.univ.image fun ij : Kap X × Kap X => Gr X (↑M⁻¹ : Matrix _ _ _) ij.1 ij.2) ∪
        (Finset.univ.image fun ij : Kap X × Kap X => Gr X (M : Matrix _ _ _) ij.1 ij.2))
    have hint : ∀ z ∈ ((Finset.univ.image fun ij : Kap X × Kap X => Gr X (↑M⁻¹ : Matrix _ _ _) ij.1 ij.2) ∪
        (Finset.univ.image fun ij : Kap X × Kap X => Gr X (M : Matrix _ _ _) ij.1 ij.2)),
        (y.natAbs : X.B.I.E) * z ∈ integralClosure ℤ X.B.I.E := by
      intro z hz
      rw [mem_integralClosure_iff]
      have h := hy z hz
      rw [zsmul_eq_mul] at h
      rcases Int.natAbs_eq y with e | e
      · rw [e] at h
        simpa using h
      · rw [e] at h
        have h' := h.neg
        simpa [neg_mul] using h'
    have hP : ∀ i j, (y.natAbs : X.B.I.E) * Gr X (↑M⁻¹ : Matrix _ _ _) i j ∈ integralClosure ℤ X.B.I.E :=
      fun i j => hint _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩))
    have hQ : ∀ i j, (y.natAbs : X.B.I.E) * Gr X (M : Matrix _ _ _) i j ∈ integralClosure ℤ X.B.I.E :=
      fun i j => hint _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩))
    let P1 : Matrix (Kap X) (Kap X) (𝓞 X.B.I.E) := Matrix.of fun i j => ⟨_, hP i j⟩
    let Q1 : Matrix (Kap X) (Kap X) (𝓞 X.B.I.E) := Matrix.of fun i j => ⟨_, hQ i j⟩
    have hP1 : P1.map (fun a => (a : X.B.I.E)) = (y.natAbs : X.B.I.E) • Gr X (↑M⁻¹ : Matrix _ _ _) := by
      ext i j
      rfl
    have hQ1 : Q1.map (fun a => (a : X.B.I.E)) = (y.natAbs : X.B.I.E) • Gr X (M : Matrix _ _ _) := by
      ext i j
      rfl
    have hmap : ∀ U V : Matrix (Kap X) (Kap X) (𝓞 X.B.I.E),
        (U * V).map (fun a => (a : X.B.I.E)) =
          U.map (fun a => (a : X.B.I.E)) * V.map (fun a => (a : X.B.I.E)) :=
      fun U V => Matrix.map_mul (f := algebraMap (𝓞 X.B.I.E) X.B.I.E)
    refine ⟨y.natAbs * y.natAbs, Nat.one_le_iff_ne_zero.mpr
      (mul_ne_zero (Int.natAbs_ne_zero.mpr hy0) (Int.natAbs_ne_zero.mpr hy0)), fun d A => ⟨P1 * A * Q1, ?_⟩⟩
    rw [hmap, hmap, hP1, hQ1]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Nat.cast_mul]
    congr 1
    ring

end MemConj

end Formalism.L2.SG.TermOp.Vanish
