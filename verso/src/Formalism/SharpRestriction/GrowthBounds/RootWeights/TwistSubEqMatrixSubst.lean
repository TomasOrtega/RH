import Formalism.SharpRestriction.GrowthBounds.ObjPol

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G

open Classical in

def matrixSubst {R B : Type*} [CommRing R] [CommRing B] {ι : Type*} {n : ℕ} (LL : Letters ι) (S : Set ι)
    (φ : R →+* B) (m m' : Matrix (Fin n) (Fin n) B) :
    MvPolynomial (ι × Fin n) R →+* MvPolynomial (ι × Fin n) B :=
  MvPolynomial.eval₂Hom (MvPolynomial.C.comp φ) fun v =>
    if v.1 ∈ S then
      (if LL.vec v.1 then ∑ b : Fin n, MvPolynomial.C (m b v.2) * X (v.1, b)
       else ∑ b : Fin n, MvPolynomial.C (m' v.2 b) * X (v.1, b))
    else X v

section basic

variable {R B B' : Type*} [CommRing R] [CommRing B] [CommRing B'] {ι : Type*} {n : ℕ} (LL : Letters ι) (S : Set ι)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem twistSub_eq_matrixSubst (j : Fin n) :
    twistSub (R := R) LL S j = matrixSubst LL S (coefL R n) (twistMat R n j 1) (twistMat R n j (-1)) := rfl

/- English proof (translation)
Simplify using `[matrixSubst]`.
-/
theorem matrixSubst_C (φ : R →+* B) (m m' : Matrix (Fin n) (Fin n) B) (c : R) :
    matrixSubst LL S φ m m' (C c) = C (φ c) := by
  simp [matrixSubst]

open Classical in
/- English proof (translation)
Simplify using `[matrixSubst]`.
-/
theorem matrixSubst_X (φ : R →+* B) (m m' : Matrix (Fin n) (Fin n) B) (v : ι × Fin n) :
    matrixSubst LL S φ m m' (X v) = if v.1 ∈ S then
      (if LL.vec v.1 then ∑ b : Fin n, MvPolynomial.C (m b v.2) * X (v.1, b)
       else ∑ b : Fin n, MvPolynomial.C (m' v.2 b) * X (v.1, b))
    else X v := by
  simp [matrixSubst]

/- English proof (translation)
Establish `: (matrixSubst LL S (RingHom.id B) m1 m1').comp (matrixSubst LL S φ m2 m2') = matrixSubst LL S φ (m1 * m2) (m2' * m1')`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `c`. Simplify using `[matrixSubst_C]`. Introduce `v`.

Rewrite using `[RingHom.comp_apply, matrixSubst_X, matrixSubst_X]`. Distinguish the cases in `hS : v.1 ∈ S`. Distinguish the cases in `hv : LL.vec v.1 = true`. Rewrite using `[if_pos hS, if_pos hv, if_pos hS, if_pos hv, map_sum]`. Establish `h1 : ∀ b : Fin n, matrixSubst LL S (RingHom.id B) m1 m1' (C (m2 b v.2) * X (v.1, b)) = ∑ a : Fin n, C (m1 a b * m2 b v.2) * X (v.1, a)`.

Introduce `b`. Rewrite using `[map_mul, matrixSubst_C, matrixSubst_X, if_pos hS, if_pos hv, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[RingHom.id_apply, map_mul]`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `only [h1]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.mul_apply, map_sum, Finset.sum_mul]`. Rewrite using `[if_pos hS, if_neg hv, if_pos hS, if_neg hv, map_sum]`.

Establish `h1 : ∀ b : Fin n, matrixSubst LL S (RingHom.id B) m1 m1' (C (m2' v.2 b) * X (v.1, b)) = ∑ a : Fin n, C (m2' v.2 b * m1' b a) * X (v.1, a)`. Introduce `b`. Rewrite using `[map_mul, matrixSubst_C, matrixSubst_X, if_pos hS, if_neg hv, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[RingHom.id_apply, map_mul]`.

Expand and normalize the polynomial expressions, which then agree. Simplify using `only [h1]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.mul_apply, map_sum, Finset.sum_mul]`.

Rewrite using `[if_neg hS, if_neg hS, matrixSubst_X, if_neg hS]`. Conclude with `congrArg (fun f => f F) this`.
-/
theorem matrixSubst_comp (φ : R →+* B) (m1 m1' m2 m2' : Matrix (Fin n) (Fin n) B) (F : MvPolynomial (ι × Fin n) R) :
    matrixSubst LL S (RingHom.id B) m1 m1' (matrixSubst LL S φ m2 m2' F) = matrixSubst LL S φ (m1 * m2) (m2' * m1') F := by
  classical
  have : (matrixSubst LL S (RingHom.id B) m1 m1').comp (matrixSubst LL S φ m2 m2') =
      matrixSubst LL S φ (m1 * m2) (m2' * m1') := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [matrixSubst_C]
    · intro v
      rw [RingHom.comp_apply, matrixSubst_X, matrixSubst_X]
      by_cases hS : v.1 ∈ S
      · by_cases hv : LL.vec v.1 = true
        · rw [if_pos hS, if_pos hv, if_pos hS, if_pos hv, map_sum]
          have h1 : ∀ b : Fin n, matrixSubst LL S (RingHom.id B) m1 m1' (C (m2 b v.2) * X (v.1, b)) =
              ∑ a : Fin n, C (m1 a b * m2 b v.2) * X (v.1, a) := by
            intro b
            rw [map_mul, matrixSubst_C, matrixSubst_X, if_pos hS, if_pos hv, Finset.mul_sum]
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [RingHom.id_apply, map_mul]; ring
          simp only [h1]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Matrix.mul_apply, map_sum, Finset.sum_mul]
        · rw [if_pos hS, if_neg hv, if_pos hS, if_neg hv, map_sum]
          have h1 : ∀ b : Fin n, matrixSubst LL S (RingHom.id B) m1 m1' (C (m2' v.2 b) * X (v.1, b)) =
              ∑ a : Fin n, C (m2' v.2 b * m1' b a) * X (v.1, a) := by
            intro b
            rw [map_mul, matrixSubst_C, matrixSubst_X, if_pos hS, if_neg hv, Finset.mul_sum]
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [RingHom.id_apply, map_mul]; ring
          simp only [h1]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Matrix.mul_apply, map_sum, Finset.sum_mul]
      · rw [if_neg hS, if_neg hS, matrixSubst_X, if_neg hS]
  exact congrArg (fun f => f F) this

/- English proof (translation)
Establish `: (MvPolynomial.map ψ).comp (matrixSubst LL S φ m m') = matrixSubst LL S (ψ.comp φ) (m.map ψ) (m'.map ψ)`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `c`. Simplify using `[matrixSubst_C]`. Introduce `v`.

Simplify using `only [RingHom.comp_apply, matrixSubst_X]`. Apply the tactic sequence `split_ifs <;> simp`. Conclude with `congrArg (fun f => f F) this`.
-/
theorem map_matrixSubst (φ : R →+* B) (ψ : B →+* B') (m m' : Matrix (Fin n) (Fin n) B)
    (F : MvPolynomial (ι × Fin n) R) :
    MvPolynomial.map ψ (matrixSubst LL S φ m m' F) = matrixSubst LL S (ψ.comp φ) (m.map ψ) (m'.map ψ) F := by
  classical
  have : (MvPolynomial.map ψ).comp (matrixSubst LL S φ m m') = matrixSubst LL S (ψ.comp φ) (m.map ψ) (m'.map ψ) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [matrixSubst_C]
    · intro v
      simp only [RingHom.comp_apply, matrixSubst_X]
      split_ifs <;> simp
  exact congrArg (fun f => f F) this

/- English proof (translation)
Establish `: matrixSubst LL S φ (1 : Matrix (Fin n) (Fin n) B) 1 = MvPolynomial.map φ`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `c`. Simplify using `[matrixSubst_C]`. Introduce `v`.

Simplify using `only [matrixSubst_X, map_X]`. Apply the tactic sequence `split_ifs <;> simp [Matrix.one_apply]`. Conclude with `congrArg (fun f => f F) this`.
-/
theorem matrixSubst_one (φ : R →+* B) (F : MvPolynomial (ι × Fin n) R) :
    matrixSubst LL S φ 1 1 F = MvPolynomial.map φ F := by
  classical
  have : matrixSubst LL S φ (1 : Matrix (Fin n) (Fin n) B) 1 = MvPolynomial.map φ := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [matrixSubst_C]
    · intro v
      simp only [matrixSubst_X, map_X]
      split_ifs <;> simp [Matrix.one_apply]
  exact congrArg (fun f => f F) this

/- English proof (translation)
Rewrite using `[← matrixSubst_one LL S, matrixSubst_comp, mul_one, one_mul]`.
-/
theorem matrixSubst_map (φ : R →+* B) (m m' : Matrix (Fin n) (Fin n) B) (F : MvPolynomial (ι × Fin n) R) :
    matrixSubst LL S (RingHom.id B) m m' (MvPolynomial.map φ F) = matrixSubst LL S φ m m' F := by
  rw [← matrixSubst_one LL S, matrixSubst_comp, mul_one, one_mul]

end basic

def TransvectionExpansion : Prop :=
  ∀ (R B : Type) [CommRing R] [CommRing B] (ι : Type) [Fintype ι] (LL : Letters ι) (n : ℕ) (S : Set ι)
    (φ : R →+* B) (a b : Fin n), a ≠ b → ∀ (t : B) (F : MvPolynomial (ι × Fin n) R) (N : ℕ), F.totalDegree < N →
      matrixSubst LL S φ (Matrix.transvection a b t) (Matrix.transvection a b (-t)) F =
        ∑ k ∈ Finset.range N, C (t ^ k) * MvPolynomial.map φ (divPow R LL S a b k F)

end Formalism.MainNotions.G.GLWeightTheory
