import Mathlib

namespace GlobalTheory.TwistDual

open Matrix

variable {E : Type} [Field E] [StarRing E] [CharZero E]

/- English proof (translation)
Establish `hBC : Bᴴ * G * C = 0`. Use `congrArg conjTranspose hCB` as an intermediate fact. Simplify `this` using `[conjTranspose_mul, hG, Matrix.mul_assoc]`. Establish `hsplit : C *ᵥ (u ∘ Sum.inl) + B *ᵥ (u ∘ Sum.inr) = 0`. Rewrite using `[← hu]`.

Use function extensionality and compare the values at `i`. Simplify using `[mulVec, dotProduct, Fintype.sum_sum_type]`. Establish `hb : u ∘ Sum.inr = 0`. Establish `h2` using `congrArg (fun w => (Bᴴ * G) *ᵥ w) hsplit`. Simplify using `only [mulVec_add, mulVec_mulVec, hBC, zero_mulVec, zero_add, mulVec_zero] at h2`.

Conclude with `Matrix.eq_zero_of_mulVec_eq_zero hBB h2`. Establish `ha : u ∘ Sum.inl = 0`. Rewrite `hsplit` using `[hb, mulVec_zero, add_zero]`. Establish `hC'` using `Fintype.linearIndependent_iff.1 hC`. Use function extensionality and compare the values at `k`.

Use `hC' _ ?_ k` and prove the remaining obligations. Rewrite using `[← hsplit]`. Use function extensionality and compare the values at `i`. Simplify using `[mulVec, dotProduct, Finset.sum_apply, mul_comm]`. Use function extensionality and compare the values at `x`.

Break down `x with k | k` into its components or cases. Conclude with `congrFun ha k`. Conclude with `congrFun hb k`.
-/
theorem fromCols_mulVec_eq_zero {n r m : ℕ} {G : Matrix (Fin n) (Fin n) E} (hG : Gᴴ = G)
    {C : Matrix (Fin n) (Fin r) E} {B : Matrix (Fin n) (Fin m) E} (hC : LinearIndependent E Cᵀ)
    (hBB : (Bᴴ * G * B).det ≠ 0) (hCB : Cᴴ * G * B = 0)
    (u : Fin r ⊕ Fin m → E) (hu : Matrix.fromCols C B *ᵥ u = 0) : u = 0 := by
  have hBC : Bᴴ * G * C = 0 := by
    have := congrArg conjTranspose hCB
    simpa [conjTranspose_mul, hG, Matrix.mul_assoc] using this
  have hsplit : C *ᵥ (u ∘ Sum.inl) + B *ᵥ (u ∘ Sum.inr) = 0 := by
    rw [← hu]; funext i
    simp [mulVec, dotProduct, Fintype.sum_sum_type]
  have hb : u ∘ Sum.inr = 0 := by
    have h2 := congrArg (fun w => (Bᴴ * G) *ᵥ w) hsplit
    simp only [mulVec_add, mulVec_mulVec, hBC, zero_mulVec, zero_add, mulVec_zero] at h2
    exact Matrix.eq_zero_of_mulVec_eq_zero hBB h2
  have ha : u ∘ Sum.inl = 0 := by
    rw [hb, mulVec_zero, add_zero] at hsplit
    have hC' := Fintype.linearIndependent_iff.1 hC
    funext k
    refine hC' _ ?_ k
    rw [← hsplit]; funext i
    simp [mulVec, dotProduct, Finset.sum_apply, mul_comm]
  funext x
  rcases x with k | k
  · exact congrFun ha k
  · exact congrFun hb k

/- English proof (translation)
Use `set M := (Matrix.fromCols C B)ᴴ * G`. Establish `hinj : Function.Injective Mᵀ.mulVecLin`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `w hw`. Rewrite `hw` using `[Matrix.mulVecLin_apply, mulVec_transpose]`.

Establish `h1` using `congrArg star hw`. Rewrite `h1` using `[star_vecMul, star_zero, conjTranspose_mul, hG, conjTranspose_conjTranspose, ← mulVec_mulVec]`. Establish `h2` using `Matrix.eq_zero_of_mulVec_eq_zero hGd h1`. Establish `h3` using `fromCols_mulVec_eq_zero hG hC hBB hCB _ h2`. Simplify using `using congrArg star h3`.

Establish `hr : Mᵀ.rank = Fintype.card (Fin r ⊕ Fin m)`. Rewrite using `[Matrix.rank, LinearMap.finrank_range_of_inj hinj, Module.finrank_fintype_fun_eq_card]`. Rewrite `hr` using `[Matrix.rank_transpose]`. Rewrite using `[← LinearMap.range_eq_top]`. Apply `Submodule.eq_top_of_finrank_eq` to reduce the goal to its premises.

Rewrite using `[Module.finrank_fintype_fun_eq_card, ← hr]`. Both sides reduce to the same expression.
-/
theorem mulVec_surjective {n r m : ℕ} {G : Matrix (Fin n) (Fin n) E} (hG : Gᴴ = G) (hGd : G.det ≠ 0)
    {C : Matrix (Fin n) (Fin r) E} {B : Matrix (Fin n) (Fin m) E} (hC : LinearIndependent E Cᵀ)
    (hBB : (Bᴴ * G * B).det ≠ 0) (hCB : Cᴴ * G * B = 0) :
    Function.Surjective ((Matrix.fromCols C B)ᴴ * G).mulVecLin := by
  set M := (Matrix.fromCols C B)ᴴ * G
  have hinj : Function.Injective Mᵀ.mulVecLin := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    rw [Matrix.mulVecLin_apply, mulVec_transpose] at hw
    have h1 := congrArg star hw
    rw [star_vecMul, star_zero, conjTranspose_mul, hG, conjTranspose_conjTranspose, ← mulVec_mulVec] at h1
    have h2 := Matrix.eq_zero_of_mulVec_eq_zero hGd h1
    have h3 := fromCols_mulVec_eq_zero hG hC hBB hCB _ h2
    simpa using congrArg star h3
  have hr : Mᵀ.rank = Fintype.card (Fin r ⊕ Fin m) := by
    rw [Matrix.rank, LinearMap.finrank_range_of_inj hinj, Module.finrank_fintype_fun_eq_card]
  rw [Matrix.rank_transpose] at hr
  rw [← LinearMap.range_eq_top]
  apply Submodule.eq_top_of_finrank_eq
  rw [Module.finrank_fintype_fun_eq_card, ← hr]
  rfl

/- English proof (translation)
Establish `hs` using `mulVec_surjective hG hGd hC hBB hCB`. Use `choose v hv using fun k : Fin r => hs (Pi.single (Sum.inl k) (1 : E))`. Use `set C₁ : Matrix (Fin n) (Fin r) E := Matrix.of fun i k => v k i`. Establish `key : ∀ a k, ∑ i, ((Matrix.fromCols C B)ᴴ * G) a i * C₁ i k = (Pi.single (Sum.inl k) (1 : E) : Fin r ⊕ Fin m → E) a`. Introduce `a k`.

Rewrite using `[← hv k]`. Simplify using `only [C₁, Matrix.mulVecLin_apply, mulVec, dotProduct, Matrix.of_apply]`. Establish `hC1 : Cᴴ * (G * C₁) = 1`. Use extensionality with `j k`. Use `key (Sum.inl j) k` as an intermediate fact.

Rewrite using `[← Matrix.mul_assoc]`. Simplify using `only [Matrix.mul_apply, conjTranspose_apply, fromCols_apply_inl] at this ⊢`. Rewrite using `[this, Pi.single_apply, Matrix.one_apply]`. Simplify using `[eq_comm]`. Establish `hB1 : Bᴴ * (G * C₁) = 0`.

Use extensionality with `j k`. Use `key (Sum.inr j) k` as an intermediate fact. Rewrite using `[← Matrix.mul_assoc]`. Simplify using `only [Matrix.mul_apply, conjTranspose_apply, fromCols_apply_inr] at this ⊢`. Rewrite using `[this]`.

Simplify using the standard rewrite rules. Establish `hGc : ∀ (p q : ℕ) (X : Matrix (Fin n) (Fin p) E) (Y : Matrix (Fin n) (Fin q) E), Yᴴ * (G * X) = (Xᴴ * (G * Y))ᴴ`. Introduce `p q X Y`. Simplify using `[conjTranspose_mul, hG, Matrix.mul_assoc]`. Establish `hCC' : Cᴴ * (G * C) = 0` using `by rw [← Matrix.mul_assoc]; exact hCC`.

Establish `hCB' : Cᴴ * (G * B) = 0` using `by rw [← Matrix.mul_assoc]; exact hCB`. Establish `h1C : C₁ᴴ * (G * C) = 1` using `by rw [hGc, hC1, conjTranspose_one]`. Establish `h1B : C₁ᴴ * (G * B) = 0`. Use `congrArg conjTranspose hB1` as an intermediate fact. Rewrite `this` using `[conjTranspose_zero, ← hGc]`.

Conclude with `this`. Use `set S := C₁ᴴ * (G * C₁) with hSdef`. Establish `hS : Sᴴ = S` using `by rw [hSdef, ← hGc]`. Use `set X : Matrix (Fin r) (Fin r) E := (2 : E)⁻¹ • S with hXdef`. Establish `hX : Xᴴ = X`.

Rewrite using `[hXdef, conjTranspose_smul, hS, star_inv₀, star_ofNat]`. Establish `hXX : X + X = S`. Rewrite using `[hXdef, ← add_smul, ← two_mul, mul_inv_cancel₀ (two_ne_zero), one_smul]`. Establish `a1 : ∀ Y : Matrix (Fin r) (Fin r) E, Cᴴ * (G * (C * Y)) = 0` using `fun Y => by`. Rewrite using `[← Matrix.mul_assoc G, ← Matrix.mul_assoc, hCC', Matrix.zero_mul]`.

Establish `a2 : ∀ Y : Matrix (Fin r) (Fin r) E, C₁ᴴ * (G * (C * Y)) = Y` using `fun Y => by`. Rewrite using `[← Matrix.mul_assoc G, ← Matrix.mul_assoc, h1C, Matrix.one_mul]`. Use `⟨C₁ - C * X, ?_, ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, hC1, a1, sub_zero]`. Simplify using `only [conjTranspose_sub, conjTranspose_mul, hX, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, hC1, a1, a2, Matrix.mul_one, Matrix.mul_zero, sub_zero]`.

Rewrite using `[← hSdef, ← hXX]`. Normalize the expressions using the abelian group laws. Simplify using `only [conjTranspose_sub, conjTranspose_mul, hX, Matrix.sub_mul, Matrix.mul_assoc, h1B, hCB', Matrix.mul_zero, sub_zero]`.
-/
theorem exists_dual {n r m : ℕ} {G : Matrix (Fin n) (Fin n) E} (hG : Gᴴ = G) (hGd : G.det ≠ 0)
    {C : Matrix (Fin n) (Fin r) E} {B : Matrix (Fin n) (Fin m) E} (hC : LinearIndependent E Cᵀ)
    (hCC : Cᴴ * G * C = 0) (hBB : (Bᴴ * G * B).det ≠ 0) (hCB : Cᴴ * G * B = 0) :
    ∃ C' : Matrix (Fin n) (Fin r) E, Cᴴ * G * C' = 1 ∧ C'ᴴ * G * C' = 0 ∧ C'ᴴ * G * B = 0 := by
  have hs := mulVec_surjective hG hGd hC hBB hCB
  choose v hv using fun k : Fin r => hs (Pi.single (Sum.inl k) (1 : E))
  set C₁ : Matrix (Fin n) (Fin r) E := Matrix.of fun i k => v k i
  have key : ∀ a k, ∑ i, ((Matrix.fromCols C B)ᴴ * G) a i * C₁ i k = (Pi.single (Sum.inl k) (1 : E) : Fin r ⊕ Fin m → E) a := by
    intro a k
    rw [← hv k]
    simp only [C₁, Matrix.mulVecLin_apply, mulVec, dotProduct, Matrix.of_apply]
  have hC1 : Cᴴ * (G * C₁) = 1 := by
    ext j k
    have := key (Sum.inl j) k
    rw [← Matrix.mul_assoc]
    simp only [Matrix.mul_apply, conjTranspose_apply, fromCols_apply_inl] at this ⊢
    rw [this, Pi.single_apply, Matrix.one_apply]
    simp [eq_comm]
  have hB1 : Bᴴ * (G * C₁) = 0 := by
    ext j k
    have := key (Sum.inr j) k
    rw [← Matrix.mul_assoc]
    simp only [Matrix.mul_apply, conjTranspose_apply, fromCols_apply_inr] at this ⊢
    rw [this]
    simp
  have hGc : ∀ (p q : ℕ) (X : Matrix (Fin n) (Fin p) E) (Y : Matrix (Fin n) (Fin q) E),
      Yᴴ * (G * X) = (Xᴴ * (G * Y))ᴴ := by
    intro p q X Y
    simp [conjTranspose_mul, hG, Matrix.mul_assoc]
  have hCC' : Cᴴ * (G * C) = 0 := by rw [← Matrix.mul_assoc]; exact hCC
  have hCB' : Cᴴ * (G * B) = 0 := by rw [← Matrix.mul_assoc]; exact hCB
  have h1C : C₁ᴴ * (G * C) = 1 := by rw [hGc, hC1, conjTranspose_one]
  have h1B : C₁ᴴ * (G * B) = 0 := by
    have := congrArg conjTranspose hB1
    rw [conjTranspose_zero, ← hGc] at this
    exact this
  set S := C₁ᴴ * (G * C₁) with hSdef
  have hS : Sᴴ = S := by rw [hSdef, ← hGc]
  set X : Matrix (Fin r) (Fin r) E := (2 : E)⁻¹ • S with hXdef
  have hX : Xᴴ = X := by
    rw [hXdef, conjTranspose_smul, hS, star_inv₀, star_ofNat]
  have hXX : X + X = S := by
    rw [hXdef, ← add_smul, ← two_mul, mul_inv_cancel₀ (two_ne_zero), one_smul]
  have a1 : ∀ Y : Matrix (Fin r) (Fin r) E, Cᴴ * (G * (C * Y)) = 0 := fun Y => by
    rw [← Matrix.mul_assoc G, ← Matrix.mul_assoc, hCC', Matrix.zero_mul]
  have a2 : ∀ Y : Matrix (Fin r) (Fin r) E, C₁ᴴ * (G * (C * Y)) = Y := fun Y => by
    rw [← Matrix.mul_assoc G, ← Matrix.mul_assoc, h1C, Matrix.one_mul]
  refine ⟨C₁ - C * X, ?_, ?_, ?_⟩
  · simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, hC1, a1, sub_zero]
  · simp only [conjTranspose_sub, conjTranspose_mul, hX, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc,
      hC1, a1, a2, Matrix.mul_one, Matrix.mul_zero, sub_zero]
    rw [← hSdef, ← hXX]; abel
  · simp only [conjTranspose_sub, conjTranspose_mul, hX, Matrix.sub_mul, Matrix.mul_assoc, h1B, hCB',
      Matrix.mul_zero, sub_zero]

end GlobalTheory.TwistDual
