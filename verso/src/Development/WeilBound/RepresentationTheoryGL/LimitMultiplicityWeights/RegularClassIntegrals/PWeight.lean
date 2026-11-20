import Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.ClosedGraph
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EqOfNearOfCharpolyEq

open MeasureTheory Set GlobalTheory.AutomorphicL2Unitary GlobalTheory.Orb Matrix
open scoped ContDiff ComplexConjugate

noncomputable section

namespace MainStatements.WeightKernel.PWeight

variable {n : ℕ}

/- English proof (translation)
Rewrite using `[← Matrix.mul_assoc, h, Matrix.one_mul]`.
-/
theorem cancel_l {A B : Matrix (Fin n) (Fin n) ℂ} (h : A * B = 1) (X : Matrix (Fin n) (Fin n) ℂ) :
    A * (B * X) = X := by
  rw [← Matrix.mul_assoc, h, Matrix.one_mul]

def conjHom {H : Type} [Group H] (ι : H →* Matrix (Fin n) (Fin n) ℂ) (Q P : Matrix (Fin n) (Fin n) ℂ)
    (hPQ : P * Q = 1) (hQP : Q * P = 1) : H →* Matrix (Fin n) (Fin n) ℂ where
  toFun h := Q * ι h * P
  map_one' := by simp [hQP]
  map_mul' a b := by simp only [map_mul, Matrix.mul_assoc, cancel_l hPQ]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem conjHom_apply {H : Type} [Group H] (ι : H →* Matrix (Fin n) (Fin n) ℂ) (Q P : Matrix (Fin n) (Fin n) ℂ)
    (hPQ : P * Q = 1) (hQP : Q * P = 1) (g : H) : conjHom ι Q P hPQ hQP g = Q * ι g * P := rfl

def conjHomeo (Q P : Matrix (Fin n) (Fin n) ℂ) (hPQ : P * Q = 1) (hQP : Q * P = 1) :
    Matrix (Fin n) (Fin n) ℂ ≃ₜ Matrix (Fin n) (Fin n) ℂ where
  toFun Y := Q * Y * P
  invFun Y := P * Y * Q
  left_inv Y := by simp only [Matrix.mul_assoc, cancel_l hPQ, hPQ, Matrix.mul_one]
  right_inv Y := by simp only [Matrix.mul_assoc, cancel_l hQP, hQP, Matrix.mul_one]
  continuous_toFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  continuous_invFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

/- English proof (translation)
Establish `hPQh : Qᴴ * Pᴴ = 1` using `by rw [← conjTranspose_mul, hPQ, conjTranspose_one]`. Establish `hQPh : Pᴴ * Qᴴ = 1` using `by rw [← conjTranspose_mul, hQP, conjTranspose_one]`. Establish `hP : IsUnit P.det` using `isUnit_iff_exists_inv.2 ⟨Q.det, by rw [← det_mul, hPQ, det_one]⟩`. Establish `hPh : IsUnit Pᴴ.det` using `isUnit_iff_exists_inv.2 ⟨Qᴴ.det, by rw [← det_mul, hQPh, det_one]⟩`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[det_mul, det_mul]`. Conclude with `(hPh.mul hU.1).mul hP`. Conclude with `(conjHomeo Q P hPQ hQP).isClosedEmbedding.comp hU.2.1`. Establish `key1 : ∀ X : Matrix (Fin n) (Fin n) ℂ, (Q * X * P)ᴴ * (Pᴴ * J * P) * (Q * X * P) = Pᴴ * (Xᴴ * J * X) * P`. Introduce `X`.

Simplify using `only [conjTranspose_mul, Matrix.mul_assoc, cancel_l hPQh, cancel_l hPQ]`. Establish `key2 : ∀ X : Matrix (Fin n) (Fin n) ℂ, (P * X * Q)ᴴ * J * (P * X * Q) = Qᴴ * (Xᴴ * (Pᴴ * J * P) * X) * Q`. Introduce `X`. Simplify using `only [conjTranspose_mul, Matrix.mul_assoc]`. Establish `key3 : Qᴴ * (Pᴴ * J * P) * Q = J`.

Simplify using `only [Matrix.mul_assoc, cancel_l hPQh, hPQ, Matrix.mul_one]`. Introduce `M`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h, rfl⟩`. Establish `hA` using `(hU.2.2 (ι h)).1 ⟨h, rfl⟩`.

Rewrite using `[conjHom_apply, key1, hA]`. Introduce `hM`. Establish `hN : (P * M * Q)ᴴ * J * (P * M * Q) = J` using `by rw [key2, hM, key3]`. Take `⟨h, hh⟩` from `(hU.2.2 _).2 hN`. Use `⟨h, ?_⟩` and prove the remaining obligations.

Rewrite using `[conjHom_apply, hh]`. Simplify using `only [Matrix.mul_assoc, cancel_l hQP, hQP, Matrix.mul_one]`.
-/
theorem isUGroup_conj {H : Type} [Group H] [TopologicalSpace H] (ι : H →* Matrix (Fin n) (Fin n) ℂ)
    (J Q P : Matrix (Fin n) (Fin n) ℂ) (hPQ : P * Q = 1) (hQP : Q * P = 1) (hU : IsUGroup ι J) :
    IsUGroup (conjHom ι Q P hPQ hQP) (Pᴴ * J * P) := by
  have hPQh : Qᴴ * Pᴴ = 1 := by rw [← conjTranspose_mul, hPQ, conjTranspose_one]
  have hQPh : Pᴴ * Qᴴ = 1 := by rw [← conjTranspose_mul, hQP, conjTranspose_one]
  have hP : IsUnit P.det := isUnit_iff_exists_inv.2 ⟨Q.det, by rw [← det_mul, hPQ, det_one]⟩
  have hPh : IsUnit Pᴴ.det := isUnit_iff_exists_inv.2 ⟨Qᴴ.det, by rw [← det_mul, hQPh, det_one]⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [det_mul, det_mul]
    exact (hPh.mul hU.1).mul hP
  · exact (conjHomeo Q P hPQ hQP).isClosedEmbedding.comp hU.2.1
  · have key1 : ∀ X : Matrix (Fin n) (Fin n) ℂ,
        (Q * X * P)ᴴ * (Pᴴ * J * P) * (Q * X * P) = Pᴴ * (Xᴴ * J * X) * P := by
      intro X
      simp only [conjTranspose_mul, Matrix.mul_assoc, cancel_l hPQh, cancel_l hPQ]
    have key2 : ∀ X : Matrix (Fin n) (Fin n) ℂ,
        (P * X * Q)ᴴ * J * (P * X * Q) = Qᴴ * (Xᴴ * (Pᴴ * J * P) * X) * Q := by
      intro X
      simp only [conjTranspose_mul, Matrix.mul_assoc]
    have key3 : Qᴴ * (Pᴴ * J * P) * Q = J := by
      simp only [Matrix.mul_assoc, cancel_l hPQh, hPQ, Matrix.mul_one]
    intro M
    constructor
    · rintro ⟨h, rfl⟩
      have hA := (hU.2.2 (ι h)).1 ⟨h, rfl⟩
      rw [conjHom_apply, key1, hA]
    · intro hM
      have hN : (P * M * Q)ᴴ * J * (P * M * Q) = J := by rw [key2, hM, key3]
      obtain ⟨h, hh⟩ := (hU.2.2 _).2 hN
      refine ⟨h, ?_⟩
      rw [conjHom_apply, hh]
      simp only [Matrix.mul_assoc, cancel_l hQP, hQP, Matrix.mul_one]

def conjMx (Q P : Matrix (Fin n) (Fin n) ℂ) (Y : MainStatements.WeightKernel.Mx n) : MainStatements.WeightKernel.Mx n :=
  fun i j => (Q * Matrix.of Y * P) i j

/- English proof (translation)
Use `contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_` and prove the remaining obligations. Simplify using `only [conjMx, Matrix.mul_apply, Matrix.of_apply]`. Conclude with `ContDiff.sum fun x _ => ContDiff.mul (ContDiff.sum fun y _ => contDiff_const.mul ((contDiff_apply ℝ ℂ x).comp (contDiff_apply ℝ (Fin n → ℂ) y))) contDiff_const`.
-/
theorem contDiff_conjMx (Q P : Matrix (Fin n) (Fin n) ℂ) : ContDiff ℝ ∞ (conjMx Q P) := by
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
  simp only [conjMx, Matrix.mul_apply, Matrix.of_apply]
  exact ContDiff.sum fun x _ => ContDiff.mul (ContDiff.sum fun y _ =>
    contDiff_const.mul ((contDiff_apply ℝ ℂ x).comp (contDiff_apply ℝ (Fin n → ℂ) y))) contDiff_const

end MainStatements.WeightKernel.PWeight

namespace MainStatements.WeightKernel

open PWeight in
/- English proof (translation)
Introduce `hWD H _ _ _ _ _ _ _ _ n ι J hU s hreg hprop`. Take `⟨P, Q, l, hl, hPQ, hQP, hd⟩` from `GlobalTheory.CompanionTheory.WeylNear.exists_diag n (ι s) hreg`. Take `⟨B', hB'⟩` from `hWD H n (conjHom ι Q P hPQ hQP) (Pᴴ * J * P) (isUGroup_conj ι J Q P hPQ hQP hU) s l hl hd hprop`. Use `⟨fun z => B' (conjMx Q P z.1, conjMx Q P z.2), ?_, fun z => hB'.nonneg _, hB'.pos, hB'.shift, hB'.proper⟩` and prove the remaining obligations. Conclude with `hB'.smooth.comp (((contDiff_conjMx Q P).comp contDiff_fst).prodMk ((contDiff_conjMx Q P).comp contDiff_snd))`.
-/
theorem weight : WeightDiag → Weight := by
  intro hWD H _ _ _ _ _ _ _ _ n ι J hU s hreg hprop
  obtain ⟨P, Q, l, hl, hPQ, hQP, hd⟩ := GlobalTheory.CompanionTheory.WeylNear.exists_diag n (ι s) hreg
  obtain ⟨B', hB'⟩ := hWD H n (conjHom ι Q P hPQ hQP) (Pᴴ * J * P) (isUGroup_conj ι J Q P hPQ hQP hU) s l hl
    hd hprop
  refine ⟨fun z => B' (conjMx Q P z.1, conjMx Q P z.2), ?_, fun z => hB'.nonneg _, hB'.pos, hB'.shift, hB'.proper⟩
  exact hB'.smooth.comp (((contDiff_conjMx Q P).comp contDiff_fst).prodMk ((contDiff_conjMx Q P).comp contDiff_snd))

end MainStatements.WeightKernel

end
