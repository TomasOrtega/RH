import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.GramAlg

section Gen

variable {A : Type} [CommRing A] {M n : ℕ}

def colM (X : Fin n → Fin M → A) : Matrix (Fin M) (Fin n) A := fun i a => X a i

/- English proof (translation)
Introduce `X Y h`. Use function extensionality and compare the values at `a i`. Conclude with `congrFun (congrFun h i) a`.
-/
theorem colM_injective : Function.Injective (colM : (Fin n → Fin M → A) → _) := by
  intro X Y h
  funext a i
  exact congrFun (congrFun h i) a

/- English proof (translation)
Simplify using `only [hform, Matrix.mul_apply, cT, colM, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]`. Conclude with `Finset.sum_comm`.
-/
theorem hform_eq_entry (s : A →+* A) (J : Matrix (Fin M) (Fin M) A) (X : Fin n → Fin M → A)
    (a b : Fin n) :
    hform s J (X a) (X b) = (cT s (colM X) * J * colM X) a b := by
  simp only [hform, Matrix.mul_apply, cT, colM, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul]
  exact Finset.sum_comm

/- English proof (translation)
Simplify using `only [Matrix.mul_assoc]`.
-/
theorem mul_shape {p q r s t u : Type} [Fintype q] [Fintype r] [Fintype s] [Fintype t]
    (a : Matrix p q A) (b : Matrix q r A) (c : Matrix r s A) (d : Matrix s t A) (e : Matrix t u A) :
    (((a * b : Matrix p r A) * c : Matrix p s A) * (d * e : Matrix s u A) : Matrix p u A) =
      ((a * ((b * c : Matrix q s A) * d : Matrix q t A) : Matrix p t A) * e : Matrix p u A) := by
  simp only [Matrix.mul_assoc]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[cT, hs]`.
-/
theorem cT_cT (s : A →+* A) (hs : ∀ x, s (s x) = x) {m p : Type} (B : Matrix m p A) :
    cT s (cT s B) = B := by
  ext i j
  simp [cT, hs]

end Gen

section Conj

variable {F E : Type} [Field F] [Field E] [Algebra F E]

/- English proof (translation)
Set `τ : E →+* ℂ` to `(IsAlgClosed.lift : E →ₐ[ℚ] ℂ).toRingHom`. Apply `τ.injective` to reduce the goal to its premises. Rewrite using `[hσ.2.2.2 τ, hσ.2.2.2 τ, star_star]`.
-/
theorem sigma_invol [NumberField F] [NumberField E] {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) (x : E) :
    σ (σ x) = x := by
  let τ : E →+* ℂ := (IsAlgClosed.lift : E →ₐ[ℚ] ℂ).toRingHom
  apply τ.injective
  rw [hσ.2.2.2 τ, hσ.2.2.2 τ, star_star]

variable (R : Type) [CommRing R] [Algebra F R]

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul r e => simp [sigR, h]`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`.
-/
theorem sigR_invol {σ : E →ₐ[F] E} (h : ∀ x, σ (σ x) = x) (x : R ⊗[F] E) :
    sigR R σ (sigR R σ x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [sigR, h]
  | add a b ha hb => simp only [map_add, ha, hb]

variable {M n : ℕ}

/- English proof (translation)
Use extensionality with `a b`. Apply the tactic sequence `exact hform_eq_entry _ _ X a b`.
-/
theorem gramR_eq (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) (X : Fin n → Fin M → R ⊗[F] E) :
    gramR R σ J X =
      (cT (sigR R σ) (colM X) * JR R J : Matrix (Fin n) (Fin M) (R ⊗[F] E)) * colM X := by
  ext a b
  exact hform_eq_entry _ _ X a b

/- English proof (translation)
Use extensionality with `i a`. Simplify using `[colM, rmul, Matrix.mul_apply]`.
-/
theorem colM_rmul (X : Fin n → Fin M → R ⊗[F] E) (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    colM (rmul R X g) = colM X * g := by
  ext i a
  simp [colM, rmul, Matrix.mul_apply]

/- English proof (translation)
Use extensionality with `i a`. Simplify using `[colM, actTup, Matrix.mulVec, dotProduct, Matrix.mul_apply]`.
-/
theorem colM_actTup (g : GL (Fin M) (R ⊗[F] E)) (X : Fin n → Fin M → R ⊗[F] E) :
    colM (actTup R g X) = (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) * colM X := by
  ext i a
  simp [colM, actTup, Matrix.mulVec, dotProduct, Matrix.mul_apply]

end Conj

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hσ M J _ R _ _ n`. Establish `hs : ∀ x : R ⊗[F] E, sigR R σ (sigR R σ x) = x` using `sigR_invol R (sigma_invol hσ)`. Use `⟨?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `X g`. Rewrite using `[gramR_eq, gramR_eq, colM_rmul, cT_mul]`.

Conclude with `mul_shape _ _ _ _ _`. Introduce `X g g'`. Apply `colM_injective` to reduce the goal to its premises. Rewrite using `[colM_rmul, colM_rmul, colM_rmul, Matrix.mul_assoc]`. Introduce `X`.

Apply `colM_injective` to reduce the goal to its premises. Rewrite using `[colM_rmul, Matrix.mul_one]`. Introduce `S g`. Establish `hS : cT (sigR R σ) (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = S`. Use extensionality with `a b`.

Conclude with `S.2 a b`. Establish `key : cT (sigR R σ) (cT (sigR R σ) g * (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * g) = cT (sigR R σ) g * (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * g`. Rewrite using `[cT_mul, cT_mul, cT_cT _ hs, hS, Matrix.mul_assoc]`. Introduce `a b`. Conclude with `congrFun (congrFun key a) b`.

Introduce `J' g hJ X`. Rewrite using `[gramR_eq, gramR_eq, colM_actTup, cT_mul, hJ]`. Conclude with `mul_shape _ _ _ _ _`.
-/
theorem gram_algebra : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] (n : ℕ), (∀ (X : Fin n → Fin M → R ⊗[F] E) (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)), gramR R σ J (rmul R X g) = cT (sigR R σ) g * gramR R σ J X * g) ∧ (∀ (X : Fin n → Fin M → R ⊗[F] E) (g g' : Matrix (Fin n) (Fin n) (R ⊗[F] E)), rmul R (rmul R X g) g' = rmul R X (g * g')) ∧ (∀ X : Fin n → Fin M → R ⊗[F] E, rmul R X 1 = X) ∧ (∀ (S : HermR R σ n) (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)), cT (sigR R σ) g * (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * g ∈ HermR R σ n) ∧ ∀ (J' : Matrix (Fin M) (Fin M) E) (g : GL (Fin M) (R ⊗[F] E)), JR R J' = cT (sigR R σ) (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) * JR R J * (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) → ∀ X : Fin n → Fin M → R ⊗[F] E, gramR R σ J (actTup R g X) = gramR R σ J' X := by
  intro F E _ _ _ _ _ σ hσ M J _ R _ _ n
  have hs : ∀ x : R ⊗[F] E, sigR R σ (sigR R σ x) = x := sigR_invol R (sigma_invol hσ)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro X g
    rw [gramR_eq, gramR_eq, colM_rmul, cT_mul]
    exact mul_shape _ _ _ _ _
  · intro X g g'
    apply colM_injective
    rw [colM_rmul, colM_rmul, colM_rmul, Matrix.mul_assoc]
  · intro X
    apply colM_injective
    rw [colM_rmul, Matrix.mul_one]
  · intro S g
    have hS : cT (sigR R σ) (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = S := by
      ext a b
      exact S.2 a b
    have key : cT (sigR R σ) (cT (sigR R σ) g * (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * g)
        = cT (sigR R σ) g * (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * g := by
      rw [cT_mul, cT_mul, cT_cT _ hs, hS, Matrix.mul_assoc]
    intro a b
    exact congrFun (congrFun key a) b
  · intro J' g hJ X
    rw [gramR_eq, gramR_eq, colM_actTup, cT_mul, hJ]
    exact mul_shape _ _ _ _ _

end GlobalTheory.CompanionTheory.SW.GramAlg
