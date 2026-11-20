import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Matrix

noncomputable section

namespace GlobalTheory.RealPar.DerivedAdjoint

variable {p q : ℕ}

/- English proof (translation)
Unfold `Jm Formalism.UG.Jpq`. Use extensionality with `i j`. Apply the tactic sequence `rcases i with i | i <;> rcases j with j | j <;> simp [Matrix.one_apply, Matrix.diagonal_apply, eq_comm] <;> split_ifs <;> simp`.
-/
theorem Jm_diag (p q : ℕ) :
    Jm p q = Matrix.diagonal (Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1)) := by
  unfold Jm Formalism.UG.Jpq
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp [Matrix.one_apply, Matrix.diagonal_apply, eq_comm] <;> split_ifs <;> simp

/- English proof (translation)
Rewrite using `[Jm_diag, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Use `congr 1`. Use extensionality with `i`. Apply the tactic sequence `rcases i with i | i <;> simp`.
-/
theorem Jm_mul_Jm (p q : ℕ) : Jm p q * Jm p q = 1 := by
  rw [Jm_diag, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  ext i
  rcases i with i | i <;> simp

/- English proof (translation)
Rewrite using `[Jm_diag, Matrix.diagonal_conjTranspose]`. Use `congr 1`. Use extensionality with `i`. Apply the tactic sequence `rcases i with i | i <;> simp`.
-/
theorem Jm_conjTranspose (p q : ℕ) : (Jm p q)ᴴ = Jm p q := by
  rw [Jm_diag, Matrix.diagonal_conjTranspose]
  congr 1
  ext i
  rcases i with i | i <;> simp

/- English proof (translation)
Unfold `adjZ`. Simplify using `only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Jm_conjTranspose, ← Matrix.mul_assoc, Jm_mul_Jm, Matrix.one_mul]`. Simplify using `only [Matrix.mul_assoc, Jm_mul_Jm, Matrix.mul_one]`.
-/
theorem adjZ_adjZ (Z : Mat p q) : adjZ (adjZ Z) = Z := by
  unfold adjZ
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Jm_conjTranspose, ← Matrix.mul_assoc, Jm_mul_Jm, Matrix.one_mul]
  simp only [Matrix.mul_assoc, Jm_mul_Jm, Matrix.mul_one]

/- English proof (translation)
Unfold `adjZ`. Rewrite using `[Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul]`.
-/
theorem adjZ_add (X Y : Mat p q) : adjZ (X + Y) = adjZ X + adjZ Y := by
  unfold adjZ
  rw [Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul]

/- English proof (translation)
Unfold `adjZ`. Rewrite using `[Matrix.conjTranspose_sub, Matrix.mul_sub, Matrix.sub_mul]`.
-/
theorem adjZ_sub (X Y : Mat p q) : adjZ (X - Y) = adjZ X - adjZ Y := by
  unfold adjZ
  rw [Matrix.conjTranspose_sub, Matrix.mul_sub, Matrix.sub_mul]

/- English proof (translation)
Unfold `adjZ`. Rewrite using `[Matrix.conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul]`.
-/
theorem adjZ_smul (c : ℂ) (X : Mat p q) : adjZ (c • X) = star c • adjZ X := by
  unfold adjZ
  rw [Matrix.conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul]

/- English proof (translation)
Unfold `upq`. Use `show Xᴴ * Jm p q + Jm p q * X = 0`. Establish `key : Jm p q * adjZ X = Xᴴ * Jm p q`. Unfold `adjZ`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, Jm_mul_Jm, Matrix.one_mul]`.

Rewrite using `[← key, h, Matrix.mul_neg, neg_add_cancel]`.
-/
theorem mem_upq_of_adjZ {X : Mat p q} (h : adjZ X = -X) : X ∈ upq p q := by
  unfold upq
  show Xᴴ * Jm p q + Jm p q * X = 0
  have key : Jm p q * adjZ X = Xᴴ * Jm p q := by
    unfold adjZ
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Jm_mul_Jm, Matrix.one_mul]
  rw [← key, h, Matrix.mul_neg, neg_add_cancel]

/- English proof (translation)
Conclude with `(LinearIsometry.mk (πU.π g).toLinearMap (πU.isom g)).inner_map_map x y`.
-/
theorem inner_map (T : GrpData p q) (πU : URep T) (g : T.G) (x y : πU.H) :
    inner ℂ (πU.π g x) (πU.π g y) = inner ℂ x y := by
  exact (LinearIsometry.mk (πU.π g).toLinearMap (πU.isom g)).inner_map_map x y

/- English proof (translation)
Introduce `p q T πU M j hd`. Establish `skew : ∀ Y ∈ upq p q, ∀ x y, inner ℂ (j (M.act Y x)) (j y) = - inner ℂ (j x) (j (M.act Y y))`. Introduce `Y hY x y`. Establish `h1` using `(hd Y hY x).inner ℂ (hd Y hY y)`. Establish `hconst : (fun t : ℝ => inner ℂ (πU.π (T.expt (t • Y)) (j x)) (πU.π (T.expt (t • Y)) (j y))) = fun _ => inner ℂ (j x) (j y)`.

Use function extensionality and compare the values at `t`. Conclude with `inner_map T πU _ (j x) (j y)`. Rewrite `h1` using `[hconst]`. Establish `h0` using `h1.unique (hasDerivAt_const (0 : ℝ) (inner ℂ (j x) (j y)))`. Simplify using `only [zero_smul, T.expt_zero, map_one, ContinuousLinearMap.one_apply] at h0`.

Take the linear combination `h0`. Establish `adj_of_mem : ∀ Y ∈ upq p q, adjZ Y = -Y`. Introduce `Y hY`. Establish `hY' : Yᴴ * Jm p q + Jm p q * Y = 0` using `hY`. Establish `e : Yᴴ * Jm p q = -(Jm p q * Y)` using `eq_neg_of_add_eq_zero_left hY'`.

Unfold `adjZ`. Rewrite using `[Matrix.mul_assoc, e, Matrix.mul_neg, ← Matrix.mul_assoc, Jm_mul_Jm, Matrix.one_mul]`. Establish `base : ∀ Y ∈ upq p q, ∀ x y, inner ℂ (j (M.act Y x)) (j y) = inner ℂ (j x) (j (M.act (adjZ Y) y))`. Introduce `Y hY x y`. Rewrite using `[adj_of_mem Y hY, map_neg, LinearMap.neg_apply, map_neg, inner_neg_right]`.

Conclude with `skew Y hY x y`. Introduce `Z x y`. Take `⟨A, hA⟩ : ∃ A : Mat p q, A = (1 / 2 : ℂ) • (Z - adjZ Z)` from `⟨_, rfl⟩`. Take `⟨B, hB⟩ : ∃ B : Mat p q, B = (-Complex.I / 2) • (Z + adjZ Z)` from `⟨_, rfl⟩`. Establish `hc : Complex.I * (-Complex.I / 2) = 1 / 2`.

Take the linear combination `(-1 / 2 : ℂ) * Complex.I_sq`. Establish `hs1 : star (1 / 2 : ℂ) = 1 / 2` using `by simp`. Establish `hs2 : star (-Complex.I / 2) = Complex.I / 2`. Apply the tactic sequence `apply Complex.ext <;> simp`. Establish `hZ : Z = A + Complex.I • B`.

Rewrite using `[hA, hB, smul_smul, hc]`. Use `module`. Establish `hAm : A ∈ upq p q`. Apply `mem_upq_of_adjZ` to reduce the goal to its premises. Rewrite using `[hA, adjZ_smul, adjZ_sub, adjZ_adjZ, hs1]`.

Use `module`. Establish `hBm : B ∈ upq p q`. Apply `mem_upq_of_adjZ` to reduce the goal to its premises. Rewrite using `[hB, adjZ_smul, adjZ_add, adjZ_adjZ, hs2]`. Use `module`.

Rewrite using `[hZ]`. Simplify using `only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, adjZ_add, adjZ_smul, base A hAm, base B hBm, starRingEnd_apply]`.
-/
theorem derived_adjoint : ∀ (p q : ℕ) (T : GrpData p q) (πU : URep T) (M : GKMod p q) (j : M.V →ₗ[ℂ] πU.H), (∀ Y ∈ upq p q, ∀ x, HasDerivAt (fun t : ℝ => πU.π (T.expt (t • Y)) (j x)) (j (M.act Y x)) 0) → (∀ Z x y, inner ℂ (j (M.act Z x)) (j y) = inner ℂ (j x) (j (M.act (adjZ Z) y))) := by
  intro p q T πU M j hd

  have skew : ∀ Y ∈ upq p q, ∀ x y,
      inner ℂ (j (M.act Y x)) (j y) = - inner ℂ (j x) (j (M.act Y y)) := by
    intro Y hY x y
    have h1 := (hd Y hY x).inner ℂ (hd Y hY y)
    have hconst : (fun t : ℝ => inner ℂ (πU.π (T.expt (t • Y)) (j x)) (πU.π (T.expt (t • Y)) (j y)))
        = fun _ => inner ℂ (j x) (j y) := by
      funext t
      exact inner_map T πU _ (j x) (j y)
    rw [hconst] at h1
    have h0 := h1.unique (hasDerivAt_const (0 : ℝ) (inner ℂ (j x) (j y)))
    simp only [zero_smul, T.expt_zero, map_one, ContinuousLinearMap.one_apply] at h0
    linear_combination h0

  have adj_of_mem : ∀ Y ∈ upq p q, adjZ Y = -Y := by
    intro Y hY
    have hY' : Yᴴ * Jm p q + Jm p q * Y = 0 := hY
    have e : Yᴴ * Jm p q = -(Jm p q * Y) := eq_neg_of_add_eq_zero_left hY'
    unfold adjZ
    rw [Matrix.mul_assoc, e, Matrix.mul_neg, ← Matrix.mul_assoc, Jm_mul_Jm, Matrix.one_mul]
  have base : ∀ Y ∈ upq p q, ∀ x y,
      inner ℂ (j (M.act Y x)) (j y) = inner ℂ (j x) (j (M.act (adjZ Y) y)) := by
    intro Y hY x y
    rw [adj_of_mem Y hY, map_neg, LinearMap.neg_apply, map_neg, inner_neg_right]
    exact skew Y hY x y

  intro Z x y
  obtain ⟨A, hA⟩ : ∃ A : Mat p q, A = (1 / 2 : ℂ) • (Z - adjZ Z) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : Mat p q, B = (-Complex.I / 2) • (Z + adjZ Z) := ⟨_, rfl⟩
  have hc : Complex.I * (-Complex.I / 2) = 1 / 2 := by
    linear_combination (-1 / 2 : ℂ) * Complex.I_sq
  have hs1 : star (1 / 2 : ℂ) = 1 / 2 := by simp
  have hs2 : star (-Complex.I / 2) = Complex.I / 2 := by
    apply Complex.ext <;> simp
  have hZ : Z = A + Complex.I • B := by
    rw [hA, hB, smul_smul, hc]
    module
  have hAm : A ∈ upq p q := by
    apply mem_upq_of_adjZ
    rw [hA, adjZ_smul, adjZ_sub, adjZ_adjZ, hs1]
    module
  have hBm : B ∈ upq p q := by
    apply mem_upq_of_adjZ
    rw [hB, adjZ_smul, adjZ_add, adjZ_adjZ, hs2]
    module
  rw [hZ]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, inner_add_left,
    inner_add_right, inner_smul_left, inner_smul_right, adjZ_add, adjZ_smul, base A hAm,
    base B hBm, starRingEnd_apply]

end GlobalTheory.RealPar.DerivedAdjoint

end
