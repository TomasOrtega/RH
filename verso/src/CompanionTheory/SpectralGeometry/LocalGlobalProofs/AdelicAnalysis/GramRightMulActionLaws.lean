import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.RMulGram

/- English proof (translation)
Simplify using `only [Matrix.mul_assoc]`.
-/
theorem mul_regroup {A : Type} [CommRing A] {m n : Type} [Fintype m] [Fintype n]
    (P : Matrix n n A) (B : Matrix n m A) (J : Matrix m m A) (C : Matrix m n A)
    (g : Matrix n n A) :
    (P * B) * J * (C * g) = P * ((B * J : Matrix n m A) * C) * g := by
  simp only [Matrix.mul_assoc]

section
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

def colsM {M n : ℕ} (X : Fin n → Fin M → R ⊗[F] E) : Matrix (Fin M) (Fin n) (R ⊗[F] E) :=
  fun i a => X a i

/- English proof (translation)
Use function extensionality and compare the values at `a i`. Conclude with `congrFun (congrFun h i) a`.
-/
theorem colsM_injective {M n : ℕ} {X Y : Fin n → Fin M → R ⊗[F] E}
    (h : colsM R X = colsM R Y) : X = Y := by
  funext a i
  exact congrFun (congrFun h i) a

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [gramR, hR, hform, Matrix.mul_apply, cT, Matrix.transpose_apply, Matrix.map_apply, colsM, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_mul]`.

Use `congr 1`.
-/
theorem gramR_eq_mul (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (X : Fin n → Fin M → R ⊗[F] E) :
    gramR R σ J X =
      (cT (sigR R σ) (colsM R X) * JR R J : Matrix (Fin n) (Fin M) (R ⊗[F] E)) * colsM R X := by
  ext a b
  simp only [gramR, hR, hform, Matrix.mul_apply, cT, Matrix.transpose_apply, Matrix.map_apply,
    colsM, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_mul]
  congr 1

/- English proof (translation)
Use extensionality with `i a`. Simplify using `only [rmul, colsM, Matrix.mul_apply]`.
-/
theorem colsM_rmul {M n : ℕ} (X : Fin n → Fin M → R ⊗[F] E)
    (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    colsM R (rmul R X g) = colsM R X * g := by
  ext i a
  simp only [rmul, colsM, Matrix.mul_apply]

/- English proof (translation)
Rewrite using `[gramR_eq_mul, gramR_eq_mul, colsM_rmul, cT_mul]`. Conclude with `mul_regroup _ _ _ _ _`.
-/
theorem gramR_rmul (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (X : Fin n → Fin M → R ⊗[F] E) (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    gramR R σ J (rmul R X g) = cT (sigR R σ) g * gramR R σ J X * g := by
  rw [gramR_eq_mul, gramR_eq_mul, colsM_rmul, cT_mul]
  exact mul_regroup _ _ _ _ _

/- English proof (translation)
Apply `colsM_injective` to reduce the goal to its premises. Rewrite using `[colsM_rmul, colsM_rmul, colsM_rmul, Matrix.mul_assoc]`.
-/
theorem rmul_rmul {M n : ℕ} (X : Fin n → Fin M → R ⊗[F] E)
    (g g' : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    rmul R (rmul R X g) g' = rmul R X (g * g') := by
  apply colsM_injective
  rw [colsM_rmul, colsM_rmul, colsM_rmul, Matrix.mul_assoc]

/- English proof (translation)
Apply `colsM_injective` to reduce the goal to its premises. Rewrite using `[colsM_rmul, Matrix.mul_one]`.
-/
theorem rmul_one {M n : ℕ} (X : Fin n → Fin M → R ⊗[F] E) : rmul R X 1 = X := by
  apply colsM_injective
  rw [colsM_rmul, Matrix.mul_one]

/- English proof (translation)
Use function extensionality and compare the values at `a i`. Simplify using `only [actTup, rmul, Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun j _ => (mul_assoc _ _ _).symm`.
-/
theorem actTup_rmul {M n : ℕ} (k : GL (Fin M) (R ⊗[F] E)) (X : Fin n → Fin M → R ⊗[F] E)
    (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    actTup R k (rmul R X g) = rmul R (actTup R k X) g := by
  funext a i
  simp only [actTup, rmul, Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun j _ => (mul_assoc _ _ _).symm

end

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ _ R _ _ M n J X g g'`. Conclude with `⟨gramR_rmul R σ J X g, rmul_rmul R X g g', rmul_one R X, fun k => actTup_rmul R k X g⟩`.
-/
theorem rmul_gram_facts : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] (M n : ℕ) (J : Matrix (Fin M) (Fin M) E) (X : Fin n → Fin M → R ⊗[F] E) (g g' : Matrix (Fin n) (Fin n) (R ⊗[F] E)), gramR R σ J (rmul R X g) = cT (sigR R σ) g * gramR R σ J X * g ∧ rmul R (rmul R X g) g' = rmul R X (g * g') ∧ rmul R X 1 = X ∧ ∀ k : GL (Fin M) (R ⊗[F] E), actTup R k (rmul R X g) = rmul R (actTup R k X) g := by
  intro F E _ _ _ _ _ σ _ R _ _ M n J X g g'
  exact ⟨gramR_rmul R σ J X g, rmul_rmul R X g g', rmul_one R X, fun k => actTup_rmul R k X g⟩

end GlobalTheory.CompanionTheory.SW.RMulGram
