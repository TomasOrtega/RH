import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.GSteps

noncomputable section

open Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

section LiftAlg

variable {R : Type} [CommRing R] {r : ℕ}

def liftE (r : ℕ) : Matrix (Fin (r + 1)) (Fin (r + 1)) R :=
  Matrix.of fun a b => if a = Fin.last r ∧ b = Fin.last r then 1 else 0

def lstar (σ : R →+* R) (X : Matrix (Fin (r + 1)) (Fin (r + 1)) R) : Matrix (Fin (r + 1)) (Fin (r + 1)) R :=
  (X.map σ).transpose

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem lstar_apply (σ : R →+* R) (X : Matrix (Fin (r + 1)) (Fin (r + 1)) R) (i j : Fin (r + 1)) :
    lstar σ X i j = σ (X j i) := rfl

/- English proof (translation)
Unfold `lstar`. Rewrite using `[Matrix.map_mul, Matrix.transpose_mul]`.
-/
theorem lstar_mul (σ : R →+* R) (X Y : Matrix (Fin (r + 1)) (Fin (r + 1)) R) :
    lstar σ (X * Y) = lstar σ Y * lstar σ X := by
  unfold lstar; rw [Matrix.map_mul, Matrix.transpose_mul]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[lstar_apply]`.
-/
theorem lstar_add (σ : R →+* R) (X Y : Matrix (Fin (r + 1)) (Fin (r + 1)) R) :
    lstar σ (X + Y) = lstar σ X + lstar σ Y := by
  ext i j; simp [lstar_apply]

/- English proof (translation)
Apply the tactic sequence `ext i j; rw [lstar_apply, Matrix.one_apply, Matrix.one_apply]; split_ifs with h1 h2 h2 <;> simp_all`.
-/
theorem lstar_one (σ : R →+* R) : lstar σ (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) R) = 1 := by
  ext i j; rw [lstar_apply, Matrix.one_apply, Matrix.one_apply]; split_ifs with h1 h2 h2 <;> simp_all

/- English proof (translation)
Establish `: Z.mulVec v = ∑ b : Fin r, v b.castSucc • fun i => Z i b.castSucc`. Use function extensionality and compare the values at `i`. Simplify using `only [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, hv, mul_zero, add_zero, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]`. Conclude with `Finset.sum_congr rfl fun b _ => mul_comm _ _`. Rewrite using `[this]`.

Conclude with `Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)`.
-/
theorem lift_mem_head (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) R) (v : Fin (r + 1) → R)
    (hv : v (Fin.last r) = 0) : Z.mulVec v ∈ headCols Z := by
  have : Z.mulVec v = ∑ b : Fin r, v b.castSucc • fun i => Z i b.castSucc := by
    funext i
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, hv, mul_zero, add_zero, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun b _ => mul_comm _ _
  rw [this]
  exact Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `only [Matrix.mul_apply, Matrix.mulVec, dotProduct]`.
-/
theorem lift_col_mul (A X : Matrix (Fin (r + 1)) (Fin (r + 1)) R) (a : Fin (r + 1)) :
    (fun i => (A * X) i a) = A.mulVec fun i => X i a := by
  funext i; simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct]

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single (Fin.last r)]`. Simplify using `only [lstar_apply, liftE, Matrix.of_apply, hQ]`. Apply the tactic sequence `by_cases hi : i = Fin.last r <;> by_cases hj : j = Fin.last r <;> simp [hi, hj]`. Introduce `k _ hk`.

Simplify using `[liftE, hk]`. Simplify using the standard rewrite rules.
-/
theorem lift_QE (σ : R →+* R) (Q : Matrix (Fin (r + 1)) (Fin (r + 1)) R)
    (hQ : ∀ j, Q (Fin.last r) j = if j = Fin.last r then 1 else 0) : lstar σ Q * liftE r = liftE r := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.last r)]
  · simp only [lstar_apply, liftE, Matrix.of_apply, hQ]
    by_cases hi : i = Fin.last r <;> by_cases hj : j = Fin.last r <;> simp [hi, hj]
  · intro k _ hk; simp [liftE, hk]
  · simp

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single (Fin.last r)]`. Simplify using `only [lstar_apply, liftE, Matrix.of_apply, hP]`. Apply the tactic sequence `by_cases hi : i = Fin.last r <;> by_cases hj : j = Fin.last r <;> simp [hi, hj]`. Introduce `k _ hk`.

Simplify using `[liftE, hk]`. Simplify using the standard rewrite rules.
-/
theorem lift_EP (σ : R →+* R) (P : Matrix (Fin (r + 1)) (Fin (r + 1)) R)
    (hP : ∀ i, P i (Fin.last r) = if i = Fin.last r then 1 else 0) : liftE r * lstar σ P = liftE r := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.last r)]
  · simp only [lstar_apply, liftE, Matrix.of_apply, hP]
    by_cases hi : i = Fin.last r <;> by_cases hj : j = Fin.last r <;> simp [hi, hj]
  · intro k _ hk; simp [liftE, hk]
  · simp

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single (Fin.last r)]`. Simplify using `[lstar_apply, liftE, hK]`. Introduce `k _ hk`. Simplify using `[liftE, hk]`.

Simplify using the standard rewrite rules.
-/
theorem lift_EK (σ : R →+* R) (K : Matrix (Fin (r + 1)) (Fin (r + 1)) R)
    (hK : ∀ i, K i (Fin.last r) = 0) : liftE r * lstar σ K = 0 := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.last r)]
  · simp [lstar_apply, liftE, hK]
  · intro k _ hk; simp [liftE, hk]
  · simp

def liftMapQ (Z Z' A : Matrix (Fin (r + 1)) (Fin (r + 1)) R)
    (h : ∀ a : Fin r, A.mulVec (fun i => Z i a.castSucc) ∈ headCols Z') : MbMod Z →ₗ[R] MbMod Z' :=
  (headCols Z).mapQ (headCols Z') A.mulVecLin (Submodule.span_le.2 (by rintro _ ⟨a, rfl⟩; exact h a))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem liftMapQ_mk (Z Z' A : Matrix (Fin (r + 1)) (Fin (r + 1)) R)
    (h : ∀ a : Fin r, A.mulVec (fun i => Z i a.castSucc) ∈ headCols Z') (v : Fin (r + 1) → R) :
    liftMapQ Z Z' A h (Submodule.Quotient.mk v) = Submodule.Quotient.mk (A.mulVec v) := rfl

def liftEquiv (Z Z' A B : Matrix (Fin (r + 1)) (Fin (r + 1)) R)
    (hA : ∀ a : Fin r, A.mulVec (fun i => Z i a.castSucc) ∈ headCols Z')
    (hB : ∀ a : Fin r, B.mulVec (fun i => Z' i a.castSucc) ∈ headCols Z)
    (hBA : ∀ w, B.mulVec (A.mulVec w) - w ∈ headCols Z) (hAB : ∀ w, A.mulVec (B.mulVec w) - w ∈ headCols Z') :
    MbMod Z ≃ₗ[R] MbMod Z' :=
  LinearEquiv.ofLinear (liftMapQ Z Z' A hA) (liftMapQ Z' Z B hB)
    (Submodule.linearMap_qext _ (LinearMap.ext fun w => by
      simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, liftMapQ_mk, LinearMap.id_comp]
      exact (Submodule.Quotient.eq _).2 (hAB w)))
    (Submodule.linearMap_qext _ (LinearMap.ext fun w => by
      simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, liftMapQ_mk, LinearMap.id_comp]
      exact (Submodule.Quotient.eq _).2 (hBA w)))

/- English proof (translation)
Establish `hQQ : Q₂ * Q = 1 + K * Z₁`. Apply `hc₁` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation. Establish `hQQ' : Q * Q₂ = 1 + K' * Z₂`. Apply `hc₂` to reduce the goal to its premises.

Combine the equalities or inequalities in the displayed calculation. Establish `hst₁ : lstar σ Z₁ = ε • liftE r - Zσ₁` using `by rw [hs₁]; abel`. Establish `hst₂ : lstar σ Z₂ = ε • liftE r - Zσ₂` using `by rw [hs₂]; abel`. Establish `hA : lstar σ Q₂ * Zσ₁ = Zσ₂ * lstar σ P₂`. Establish `e1 : lstar σ Q₂ * lstar σ Z₁ = lstar σ Z₂ * lstar σ P₂` using `by rw [← lstar_mul, ← lstar_mul, h2]`.

Rewrite using `[hs₁, hs₂, Matrix.mul_add, Matrix.add_mul, Matrix.mul_neg, Matrix.neg_mul, e1, Matrix.mul_smul, Matrix.smul_mul, lift_QE σ Q₂ hQ₂l, lift_EP σ P₂ hP₂l]`. Establish `hB : lstar σ Q * Zσ₂ = Zσ₁ * lstar σ P`. Establish `e1 : lstar σ Q * lstar σ Z₂ = lstar σ Z₁ * lstar σ P` using `by rw [← lstar_mul, ← lstar_mul, h1]`. Rewrite using `[hs₁, hs₂, Matrix.mul_add, Matrix.add_mul, Matrix.mul_neg, Matrix.neg_mul, e1, Matrix.mul_smul, Matrix.smul_mul, lift_QE σ Q hQl, lift_EP σ P hPl]`. Establish `hBA : lstar σ Q * lstar σ Q₂ = 1 - Zσ₁ * lstar σ K`.

Rewrite using `[← lstar_mul, hQQ, lstar_add, lstar_one, lstar_mul, hst₁, Matrix.sub_mul, Matrix.smul_mul, lift_EK σ K hKc, smul_zero, zero_sub, sub_eq_add_neg]`. Establish `hAB : lstar σ Q₂ * lstar σ Q = 1 - Zσ₂ * lstar σ K'`. Rewrite using `[← lstar_mul, hQQ', lstar_add, lstar_one, lstar_mul, hst₂, Matrix.sub_mul, Matrix.smul_mul, lift_EK σ K' hK'c, smul_zero, zero_sub, sub_eq_add_neg]`. Establish `hlastK : ∀ (K₀ : Matrix (Fin (r + 1)) (Fin (r + 1)) R), (∀ i, K₀ i (Fin.last r) = 0) → ∀ w, ((lstar σ K₀).mulVec w) (Fin.last r) = 0`. Introduce `K₀ h w`.

Simplify using `[Matrix.mulVec, dotProduct, lstar_apply, h]`. Establish `hmapA : ∀ a : Fin r, (lstar σ Q₂).mulVec (fun i => Zσ₁ i a.castSucc) ∈ headCols Zσ₂`. Introduce `a`. Rewrite using `[← lift_col_mul, hA, lift_col_mul]`. Apply `lift_mem_head` to reduce the goal to its premises.

Rewrite using `[lstar_apply, hP₂l]`. Simplify using `[Fin.castSucc_ne_last]`. Establish `hmapB : ∀ a : Fin r, (lstar σ Q).mulVec (fun i => Zσ₂ i a.castSucc) ∈ headCols Zσ₁`. Introduce `a`. Rewrite using `[← lift_col_mul, hB, lift_col_mul]`.

Apply `lift_mem_head` to reduce the goal to its premises. Rewrite using `[lstar_apply, hPl]`. Simplify using `[Fin.castSucc_ne_last]`. Establish `hcompBA : ∀ w, (lstar σ Q).mulVec ((lstar σ Q₂).mulVec w) - w ∈ headCols Zσ₁`. Introduce `w`.

Rewrite using `[Matrix.mulVec_mulVec, hBA, Matrix.sub_mulVec, Matrix.one_mulVec, sub_sub_cancel_left, ← Matrix.mulVec_mulVec]`. Conclude with `Submodule.neg_mem _ (lift_mem_head _ _ (hlastK K hKc w))`. Establish `hcompAB : ∀ w, (lstar σ Q₂).mulVec ((lstar σ Q).mulVec w) - w ∈ headCols Zσ₂`. Introduce `w`. Rewrite using `[Matrix.mulVec_mulVec, hAB, Matrix.sub_mulVec, Matrix.one_mulVec, sub_sub_cancel_left, ← Matrix.mulVec_mulVec]`.

Conclude with `Submodule.neg_mem _ (lift_mem_head _ _ (hlastK K' hK'c w))`. Set `φ` to `liftEquiv Zσ₁ Zσ₂ (lstar σ Q₂) (lstar σ Q) hmapA hmapB hcompBA hcompAB`. Establish `hb : φ (bCls Zσ₁) = bCls Zσ₂` using `by show Submodule.Quotient.mk ((lstar σ Q₂).mulVec fun i => Zσ₁ i (Fin.last r)) = Submodule.Quotient.mk _`. Rewrite using `[Submodule.Quotient.eq, ← lift_col_mul, hA, lift_col_mul]`. Establish `: (fun i => Zσ₂ i (Fin.last r)) = Zσ₂.mulVec (Pi.single (Fin.last r) 1)`.

Use function extensionality and compare the values at `i`. Simplify using `[Matrix.mulVec, dotProduct, Pi.single_apply]`. Rewrite using `[this, ← Matrix.mulVec_sub]`. Apply `lift_mem_head` to reduce the goal to its premises. Simplify using `[lstar_apply, hP₂l]`.

Establish `he : φ (eCl Zσ₁) = eCl Zσ₂` using `by show Submodule.Quotient.mk ((lstar σ Q₂).mulVec (Pi.single (Fin.last r) 1)) = Submodule.Quotient.mk _`. Use `congr 1`. Use function extensionality and compare the values at `i`. Simplify using `[Matrix.mulVec, dotProduct, Pi.single_apply, lstar_apply, hQ₂l]`. Use `⟨⟨φ, hb, he⟩, fun w => rfl, fun w => ⟨-(lstar σ K).mulVec w, by simp [hlastK K hKc w], ?_⟩⟩` and prove the remaining obligations.

Rewrite using `[Matrix.mulVec_mulVec, hBA, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_neg, ← Matrix.mulVec_mulVec, sub_eq_add_neg]`.
-/
theorem lift_partner (σ : R →+* R) (Z₁ Z₂ Zσ₁ Zσ₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) R)
    (ε : R) (hs₁ : Zσ₁ = -lstar σ Z₁ + ε • liftE r) (hs₂ : Zσ₂ = -lstar σ Z₂ + ε • liftE r)
    (hc₁ : ∀ A B : Matrix (Fin (r + 1)) (Fin (r + 1)) R, Z₁ * A = Z₁ * B → A = B)
    (hc₂ : ∀ A B : Matrix (Fin (r + 1)) (Fin (r + 1)) R, Z₂ * A = Z₂ * B → A = B)
    (P Q P₂ Q₂ K K' : Matrix (Fin (r + 1)) (Fin (r + 1)) R)
    (h1 : P * Z₁ = Z₂ * Q) (h2 : P₂ * Z₂ = Z₁ * Q₂) (hK : P₂ * P = 1 + Z₁ * K) (hK' : P * P₂ = 1 + Z₂ * K')
    (hPl : ∀ i, P i (Fin.last r) = if i = Fin.last r then 1 else 0)
    (hP₂l : ∀ i, P₂ i (Fin.last r) = if i = Fin.last r then 1 else 0)
    (hQl : ∀ j, Q (Fin.last r) j = if j = Fin.last r then 1 else 0)
    (hQ₂l : ∀ j, Q₂ (Fin.last r) j = if j = Fin.last r then 1 else 0)
    (hKc : ∀ i, K i (Fin.last r) = 0) (hK'c : ∀ i, K' i (Fin.last r) = 0) :
    ∃ γ' : IsoMbe Zσ₁ Zσ₂,
      (∀ w, γ'.1 (Submodule.Quotient.mk w) = Submodule.Quotient.mk ((lstar σ Q₂).mulVec w)) ∧
      ∀ w : Fin (r + 1) → R, ∃ m : Fin (r + 1) → R, m (Fin.last r) = 0 ∧
        (lstar σ Q).mulVec ((lstar σ Q₂).mulVec w) = w + Zσ₁.mulVec m := by

  have hQQ : Q₂ * Q = 1 + K * Z₁ := by
    apply hc₁
    calc Z₁ * (Q₂ * Q) = P₂ * (P * Z₁) := by rw [h1, ← Matrix.mul_assoc, ← h2, Matrix.mul_assoc]
      _ = (P₂ * P) * Z₁ := by rw [Matrix.mul_assoc]
      _ = Z₁ * (1 + K * Z₁) := by rw [hK, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
            Matrix.mul_assoc]
  have hQQ' : Q * Q₂ = 1 + K' * Z₂ := by
    apply hc₂
    calc Z₂ * (Q * Q₂) = P * (P₂ * Z₂) := by rw [h2, ← Matrix.mul_assoc, ← h1, Matrix.mul_assoc]
      _ = (P * P₂) * Z₂ := by rw [Matrix.mul_assoc]
      _ = Z₂ * (1 + K' * Z₂) := by rw [hK', Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
            Matrix.mul_assoc]
  have hst₁ : lstar σ Z₁ = ε • liftE r - Zσ₁ := by rw [hs₁]; abel
  have hst₂ : lstar σ Z₂ = ε • liftE r - Zσ₂ := by rw [hs₂]; abel

  have hA : lstar σ Q₂ * Zσ₁ = Zσ₂ * lstar σ P₂ := by
    have e1 : lstar σ Q₂ * lstar σ Z₁ = lstar σ Z₂ * lstar σ P₂ := by rw [← lstar_mul, ← lstar_mul, h2]
    rw [hs₁, hs₂, Matrix.mul_add, Matrix.add_mul, Matrix.mul_neg, Matrix.neg_mul, e1, Matrix.mul_smul,
      Matrix.smul_mul, lift_QE σ Q₂ hQ₂l, lift_EP σ P₂ hP₂l]
  have hB : lstar σ Q * Zσ₂ = Zσ₁ * lstar σ P := by
    have e1 : lstar σ Q * lstar σ Z₂ = lstar σ Z₁ * lstar σ P := by rw [← lstar_mul, ← lstar_mul, h1]
    rw [hs₁, hs₂, Matrix.mul_add, Matrix.add_mul, Matrix.mul_neg, Matrix.neg_mul, e1, Matrix.mul_smul,
      Matrix.smul_mul, lift_QE σ Q hQl, lift_EP σ P hPl]

  have hBA : lstar σ Q * lstar σ Q₂ = 1 - Zσ₁ * lstar σ K := by
    rw [← lstar_mul, hQQ, lstar_add, lstar_one, lstar_mul, hst₁, Matrix.sub_mul, Matrix.smul_mul,
      lift_EK σ K hKc, smul_zero, zero_sub, sub_eq_add_neg]
  have hAB : lstar σ Q₂ * lstar σ Q = 1 - Zσ₂ * lstar σ K' := by
    rw [← lstar_mul, hQQ', lstar_add, lstar_one, lstar_mul, hst₂, Matrix.sub_mul, Matrix.smul_mul,
      lift_EK σ K' hK'c, smul_zero, zero_sub, sub_eq_add_neg]
  have hlastK : ∀ (K₀ : Matrix (Fin (r + 1)) (Fin (r + 1)) R), (∀ i, K₀ i (Fin.last r) = 0) →
      ∀ w, ((lstar σ K₀).mulVec w) (Fin.last r) = 0 := by
    intro K₀ h w
    simp [Matrix.mulVec, dotProduct, lstar_apply, h]
  have hmapA : ∀ a : Fin r, (lstar σ Q₂).mulVec (fun i => Zσ₁ i a.castSucc) ∈ headCols Zσ₂ := by
    intro a
    rw [← lift_col_mul, hA, lift_col_mul]
    apply lift_mem_head
    rw [lstar_apply, hP₂l]; simp [Fin.castSucc_ne_last]
  have hmapB : ∀ a : Fin r, (lstar σ Q).mulVec (fun i => Zσ₂ i a.castSucc) ∈ headCols Zσ₁ := by
    intro a
    rw [← lift_col_mul, hB, lift_col_mul]
    apply lift_mem_head
    rw [lstar_apply, hPl]; simp [Fin.castSucc_ne_last]
  have hcompBA : ∀ w, (lstar σ Q).mulVec ((lstar σ Q₂).mulVec w) - w ∈ headCols Zσ₁ := by
    intro w
    rw [Matrix.mulVec_mulVec, hBA, Matrix.sub_mulVec, Matrix.one_mulVec, sub_sub_cancel_left, ← Matrix.mulVec_mulVec]
    exact Submodule.neg_mem _ (lift_mem_head _ _ (hlastK K hKc w))
  have hcompAB : ∀ w, (lstar σ Q₂).mulVec ((lstar σ Q).mulVec w) - w ∈ headCols Zσ₂ := by
    intro w
    rw [Matrix.mulVec_mulVec, hAB, Matrix.sub_mulVec, Matrix.one_mulVec, sub_sub_cancel_left, ← Matrix.mulVec_mulVec]
    exact Submodule.neg_mem _ (lift_mem_head _ _ (hlastK K' hK'c w))
  let φ := liftEquiv Zσ₁ Zσ₂ (lstar σ Q₂) (lstar σ Q) hmapA hmapB hcompBA hcompAB
  have hb : φ (bCls Zσ₁) = bCls Zσ₂ := by
    show Submodule.Quotient.mk ((lstar σ Q₂).mulVec fun i => Zσ₁ i (Fin.last r)) = Submodule.Quotient.mk _
    rw [Submodule.Quotient.eq, ← lift_col_mul, hA, lift_col_mul]
    have : (fun i => Zσ₂ i (Fin.last r)) = Zσ₂.mulVec (Pi.single (Fin.last r) 1) := by
      funext i; simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [this, ← Matrix.mulVec_sub]
    apply lift_mem_head
    simp [lstar_apply, hP₂l]
  have he : φ (eCl Zσ₁) = eCl Zσ₂ := by
    show Submodule.Quotient.mk ((lstar σ Q₂).mulVec (Pi.single (Fin.last r) 1)) = Submodule.Quotient.mk _
    congr 1
    funext i
    simp [Matrix.mulVec, dotProduct, Pi.single_apply, lstar_apply, hQ₂l]
  refine ⟨⟨φ, hb, he⟩, fun w => rfl, fun w => ⟨-(lstar σ K).mulVec w, by simp [hlastK K hKc w], ?_⟩⟩
  rw [Matrix.mulVec_mulVec, hBA, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_neg, ← Matrix.mulVec_mulVec,
    sub_eq_add_neg]

end LiftAlg

end Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork
