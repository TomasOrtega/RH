import Mathlib

open Matrix

/- English proof (translation)
Take `⟨V, U, s, hV, hU, heq⟩` from `exists_rank_normal_form A`. Take `⟨W, hVW, hWV⟩ : ∃ W, V * W = 1 ∧ W * V = 1` from `isUnit_iff_exists.1 hV`. Take `⟨T, hUT⟩ : ∃ T, U * T = 1` from `hU.exists_right_inv`. Establish `hPP : (V * A * U) * (V * A * U) = V * A * U`. Rewrite using `[heq, submatrix_mul_equiv]`.

Simplify using `[fromBlocks_multiply]`. Establish `hPt : (V * A * U)ᵀ = V * A * U`. Rewrite using `[heq, transpose_submatrix]`. Simplify using `[fromBlocks_transpose]`. Use `set P := V * A * U with hP`.

Establish `h1 : V * A = P * T` using `by rw [hP, Matrix.mul_assoc (V * A), hUT, Matrix.mul_one]`. Establish `h2 : P * Wᵀ = Uᵀ * Aᵀ`. Rewrite using `[← hPt, ← transpose_mul, ← transpose_mul, hP, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hWV, Matrix.one_mul]`. Use `⟨W * (1 - P) * Wᵀ, ?_, ?_⟩` and prove the remaining obligations. Simplify using `[Matrix.IsSymm, transpose_mul, transpose_sub, hPt, Matrix.mul_assoc]`.

Use `mulVec_injective_iff_isUnit.1 ?_` and prove the remaining obligations. Rewrite using `[← coe_mulVecLin, ← LinearMap.ker_eq_bot]`. Use `ker_mulVecLin_eq_bot_iff.2 fun y hy => ?_` and prove the remaining obligations. Use `set M := A + W * (1 - P) * Wᵀ * C with hM`. Establish `e1 : V * M = P * T + (1 - P) * (Wᵀ * C)`.

Rewrite using `[hM, Matrix.mul_add, h1]`. Simplify using `only [← Matrix.mul_assoc, hVW, Matrix.one_mul]`. Establish `e2 : W * P * V * M = A`. Rewrite using `[Matrix.mul_assoc _ V, e1, Matrix.mul_assoc W, Matrix.mul_add, ← Matrix.mul_assoc P P, ← Matrix.mul_assoc P (1 - P), Matrix.mul_sub, hPP, Matrix.mul_one, sub_self, Matrix.zero_mul, add_zero, ← h1, ← Matrix.mul_assoc, hWV, Matrix.one_mul]`. Establish `hA : A *ᵥ y = 0` using `by rw [← e2, ← mulVec_mulVec, hy, mulVec_zero]`.

Establish `e3 : C = Vᵀ * V * M - Vᵀ * V * A + Vᵀ * (Uᵀ * Cᵀ) * A`. Establish `: Vᵀ * Wᵀ = 1` using `by rw [← transpose_mul, hWV, transpose_one]`. Rewrite using `[Matrix.mul_assoc _ V, Matrix.mul_assoc _ V, e1, h1, Matrix.mul_assoc _ (Uᵀ * Cᵀ), Matrix.mul_assoc Uᵀ, ← hs, ← Matrix.mul_assoc Uᵀ, ← h2, ← Matrix.mul_sub, ← Matrix.mul_add, add_sub_cancel_left, Matrix.mul_assoc P, ← Matrix.add_mul, sub_add_cancel, Matrix.one_mul, ← Matrix.mul_a …`. Use `hker y hA ?_` and prove the remaining obligations. Rewrite using `[e3, add_mulVec, sub_mulVec, ← mulVec_mulVec _ _ M, ← mulVec_mulVec _ _ A, ← mulVec_mulVec _ _ A, hy, hA]`.

Simplify using the standard rewrite rules.
-/
private lemma UpperTheory.symmetric_shift_isUnit {K : Type} [Field K] {κ : Type} [Fintype κ] [DecidableEq κ]
    (A C : Matrix κ κ K) (hker : ∀ x : κ → K, A *ᵥ x = 0 → C *ᵥ x = 0 → x = 0)
    (hs : Aᵀ * C = Cᵀ * A) : ∃ X : Matrix κ κ K, X.IsSymm ∧ IsUnit (A + X * C) := by
  obtain ⟨V, U, s, hV, hU, heq⟩ := exists_rank_normal_form A
  obtain ⟨W, hVW, hWV⟩ : ∃ W, V * W = 1 ∧ W * V = 1 := isUnit_iff_exists.1 hV
  obtain ⟨T, hUT⟩ : ∃ T, U * T = 1 := hU.exists_right_inv
  have hPP : (V * A * U) * (V * A * U) = V * A * U := by
    rw [heq, submatrix_mul_equiv]; simp [fromBlocks_multiply]
  have hPt : (V * A * U)ᵀ = V * A * U := by
    rw [heq, transpose_submatrix]; simp [fromBlocks_transpose]
  set P := V * A * U with hP
  have h1 : V * A = P * T := by rw [hP, Matrix.mul_assoc (V * A), hUT, Matrix.mul_one]
  have h2 : P * Wᵀ = Uᵀ * Aᵀ := by
    rw [← hPt, ← transpose_mul, ← transpose_mul, hP, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hWV,
      Matrix.one_mul]
  refine ⟨W * (1 - P) * Wᵀ, ?_, ?_⟩
  · simp [Matrix.IsSymm, transpose_mul, transpose_sub, hPt, Matrix.mul_assoc]
  · refine mulVec_injective_iff_isUnit.1 ?_
    rw [← coe_mulVecLin, ← LinearMap.ker_eq_bot]
    refine ker_mulVecLin_eq_bot_iff.2 fun y hy => ?_
    set M := A + W * (1 - P) * Wᵀ * C with hM
    have e1 : V * M = P * T + (1 - P) * (Wᵀ * C) := by
      rw [hM, Matrix.mul_add, h1]
      simp only [← Matrix.mul_assoc, hVW, Matrix.one_mul]
    have e2 : W * P * V * M = A := by
      rw [Matrix.mul_assoc _ V, e1, Matrix.mul_assoc W, Matrix.mul_add, ← Matrix.mul_assoc P P,
        ← Matrix.mul_assoc P (1 - P), Matrix.mul_sub, hPP, Matrix.mul_one, sub_self,
        Matrix.zero_mul, add_zero, ← h1, ← Matrix.mul_assoc, hWV, Matrix.one_mul]
    have hA : A *ᵥ y = 0 := by rw [← e2, ← mulVec_mulVec, hy, mulVec_zero]
    have e3 : C = Vᵀ * V * M - Vᵀ * V * A + Vᵀ * (Uᵀ * Cᵀ) * A := by
      have : Vᵀ * Wᵀ = 1 := by rw [← transpose_mul, hWV, transpose_one]
      rw [Matrix.mul_assoc _ V, Matrix.mul_assoc _ V, e1, h1, Matrix.mul_assoc _ (Uᵀ * Cᵀ),
        Matrix.mul_assoc Uᵀ, ← hs, ← Matrix.mul_assoc Uᵀ, ← h2, ← Matrix.mul_sub,
        ← Matrix.mul_add, add_sub_cancel_left, Matrix.mul_assoc P, ← Matrix.add_mul,
        sub_add_cancel, Matrix.one_mul, ← Matrix.mul_assoc, this, Matrix.one_mul]
    refine hker y hA ?_
    rw [e3, add_mulVec, sub_mulVec, ← mulVec_mulVec _ _ M, ← mulVec_mulVec _ _ A,
      ← mulVec_mulVec _ _ A, hy, hA]
    simp

/- English proof (translation)
Use extensionality with `i j`. Simplify using `using h (Pi.single i 1) (Pi.single j 1)`.
-/
private lemma UpperTheory.matrix_ext_bilinear {K : Type} [Field K] {κ : Type} [Fintype κ] [DecidableEq κ]
    {M N : Matrix κ κ K} (h : ∀ x y : κ → K, x ⬝ᵥ M *ᵥ y = x ⬝ᵥ N *ᵥ y) : M = N := by
  ext i j
  simpa using h (Pi.single i 1) (Pi.single j 1)

/- English proof (translation)
Rewrite using `[← mulVec_mulVec, dotProduct_mulVec x, vecMul_transpose]`.
-/
private lemma UpperTheory.dot_mulVec_eq {K : Type} [Field K] {κ : Type} [Fintype κ]
    (M N : Matrix κ κ K) (x y : κ → K) : (M *ᵥ x) ⬝ᵥ (N *ᵥ y) = x ⬝ᵥ (Mᵀ * N) *ᵥ y := by
  rw [← mulVec_mulVec, dotProduct_mulVec x, vecMul_transpose]

/- English proof (translation)
Introduce `K _ κ _ _ P hcomp hJ hL hD g hg`. Establish `hU : ∀ S : Matrix κ κ K, S.IsSymm → P (fun w => (w.1 + S *ᵥ w.2, w.2))`. Introduce `S hS`. Use `hcomp _ _ hJ (hcomp _ _ (hL _ hS.neg) (hcomp _ _ hJ (hcomp _ _ hJ hJ))) using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `w`.

Simplify using `[neg_mulVec, mulVec_neg]`. Establish `hinv : ∀ A B C D : Matrix κ κ K, IsUnit A → Aᵀ * C = Cᵀ * A → Bᵀ * D = Dᵀ * B → Aᵀ * D - Cᵀ * B = 1 → P (fun w => (A *ᵥ w.1 + B *ᵥ w.2, C *ᵥ w.1 + D *ᵥ w.2))`. Introduce `A B C D hA h1 h2 h3`. Take `⟨E, hAE, hEA⟩ : ∃ E, A * E = 1 ∧ E * A = 1` from `isUnit_iff_exists.1 hA`. Establish `hT : Eᵀ * Aᵀ = 1` using `by rw [← transpose_mul, hAE, transpose_one]`.

Establish `s1 : Eᵀ * Cᵀ = C * E`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.mul_assoc, Matrix.mul_assoc, hAE, Matrix.mul_one]`. Use `_ = C * E := by rw [← h1, ← Matrix.mul_assoc, hT, Matrix.one_mul]`. Establish `hDe : Eᵀ = D - C * E * B`.

Rewrite using `[← Matrix.mul_one Eᵀ, ← h3, Matrix.mul_sub, ← Matrix.mul_assoc, hT, Matrix.one_mul, ← Matrix.mul_assoc, s1]`. Establish `hEe : E = Dᵀ - Bᵀ * (C * E)`. Rewrite using `[← s1]`. Simplify `congrArg transpose hDe` using `[transpose_sub, transpose_mul]`. Establish `s2 : (E * B).IsSymm`.

Rewrite using `[Matrix.IsSymm, transpose_mul, hDe]`. Use `conv_rhs => rw [hEe]`. Rewrite using `[Matrix.mul_sub, Matrix.sub_mul, h2]`. Simplify using `only [Matrix.mul_assoc]`. Establish `s3 : (C * E).IsSymm` using `by rw [Matrix.IsSymm, transpose_mul, s1]`.

Use `hcomp _ _ (hL _ s3) (hcomp _ _ (hD A E hEA) (hU _ s2)) using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `w`. Establish `a1 : A * (E * B) = B` using `by rw [← Matrix.mul_assoc, hAE, Matrix.one_mul]`. Establish `a2 : C * E * A = C` using `by rw [Matrix.mul_assoc, hEA, Matrix.mul_one]`. Simplify using `only [Function.comp, mulVec_add, mulVec_mulVec, a1, a2, hDe, sub_mulVec, Prod.mk.injEq, true_and]`.

Normalize the expressions using the abelian group laws. Choose the witnesses or unpack the hypotheses as in `⟨A, B, C, D, hw⟩ : ∃ A B C D : Matrix κ κ K, ∀ w, g w = (A *ᵥ w.1 + B *ᵥ w.2, C *ᵥ w.1 + D *ᵥ w.2) := by`. Use `⟨LinearMap.toMatrix' (LinearMap.fst K _ _ ∘ₗ g ∘ₗ LinearMap.inl K _ _), LinearMap.toMatrix' (LinearMap.fst K _ _ ∘ₗ g ∘ₗ LinearMap.inr K _ _), LinearMap.toMatrix' (LinearMap.snd K _ _ ∘ₗ g ∘ₗ LinearMap.inl K _ _), LinearMap.toMatrix' (LinearMap.snd K _ _ ∘ₗ g ∘ₗ LinearMap.inr K _ …` and prove the remaining obligations. Simplify using `only [LinearMap.toMatrix'_mulVec]`. Establish `: g w = g (w.1, 0) + g (0, w.2)` using `by rw [← map_add]; simp`.

Rewrite using `[this]`. Both sides reduce to the same expression. Simplify using `only [hw] at hg`. Establish `h1 : Aᵀ * C = Cᵀ * A` using `UpperTheory.matrix_ext_bilinear fun x y => by`. Use `hg (x, 0) (y, 0)` as an intermediate fact.

Simplify using `only [mulVec_zero, add_zero, dotProduct_zero, sub_self] at this`. Rewrite using `[← UpperTheory.dot_mulVec_eq, ← UpperTheory.dot_mulVec_eq, dotProduct_comm (C *ᵥ x)]`. Conclude with `sub_eq_zero.1 this`. Establish `h2 : Bᵀ * D = Dᵀ * B` using `UpperTheory.matrix_ext_bilinear fun x y => by`. Use `hg (0, x) (0, y)` as an intermediate fact.

Simplify using `only [mulVec_zero, zero_add, zero_dotProduct, sub_self] at this`. Rewrite using `[← UpperTheory.dot_mulVec_eq, ← UpperTheory.dot_mulVec_eq, dotProduct_comm (D *ᵥ x)]`. Conclude with `sub_eq_zero.1 this`. Establish `h3 : Aᵀ * D - Cᵀ * B = 1` using `UpperTheory.matrix_ext_bilinear fun x y => by`. Use `hg (x, 0) (0, y)` as an intermediate fact.

Simplify using `only [mulVec_zero, zero_add, add_zero, zero_dotProduct, sub_zero] at this`. Rewrite using `[sub_mulVec, dotProduct_sub, ← UpperTheory.dot_mulVec_eq, ← UpperTheory.dot_mulVec_eq, dotProduct_comm (C *ᵥ x), one_mulVec]`. Conclude with `this`. Establish `h4 : Dᵀ * A - Bᵀ * C = 1`. Simplify `congrArg transpose h3` using `[transpose_sub, transpose_mul]`.

Take `⟨X, hX, hu⟩` from `UpperTheory.symmetric_shift_isUnit A C (fun x hA hC => by`. Rewrite using `[← one_mulVec x, ← h4, sub_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, hA, hC]`. Use the proof step `simp) h1`. Establish `key` using `hinv (A + X * C) (B + X * D) C D hu (by simp only [transpose_add, transpose_mul, hX.eq, Matrix.add_mul, Matrix.mul_add, h1, Matrix.mul_assoc]) (by simp only [transpose_add, transpose_mul, hX.eq, Matrix.add_mul, Matrix.mul_add, h2, Matrix.mul_assoc]) (by`. Simplify using `only [transpose_add, transpose_mul, hX.eq, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, ← h3]`.

Use the proof step `abel)`. Use `hcomp _ _ (hU _ hX.neg) key using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `w`. Simplify using `only [hw, Function.comp, add_mulVec, neg_mulVec, mulVec_add, mulVec_mulVec, Matrix.neg_mul, Prod.mk.injEq, and_true]`. Normalize the expressions using the abelian group laws.
-/
theorem UpperTheory.symplectic_generation :
    ∀ (K : Type) [Field K] (κ : Type) [Fintype κ] [DecidableEq κ]
        (P : ((κ → K) × (κ → K) → (κ → K) × (κ → K)) → Prop),
        (∀ f g, P f → P g → P (f ∘ g)) →
        P (fun w => (w.2, -w.1)) →
        (∀ S : Matrix κ κ K, S.IsSymm → P (fun w => (w.1, w.2 + S.mulVec w.1))) →
        (∀ A A' : Matrix κ κ K, A' * A = 1 → P (fun w => (A.mulVec w.1, A'.transpose.mulVec w.2))) →
        ∀ g : (κ → K) × (κ → K) →ₗ[K] (κ → K) × (κ → K),
          (∀ w w', dotProduct (g w).1 (g w').2 - dotProduct (g w').1 (g w).2 = dotProduct w.1 w'.2 - dotProduct w'.1 w.2) →
          P g := by
  intro K _ κ _ _ P hcomp hJ hL hD g hg
  have hU : ∀ S : Matrix κ κ K, S.IsSymm → P (fun w => (w.1 + S *ᵥ w.2, w.2)) := by
    intro S hS
    convert hcomp _ _ hJ (hcomp _ _ (hL _ hS.neg) (hcomp _ _ hJ (hcomp _ _ hJ hJ))) using 1
    funext w
    simp [neg_mulVec, mulVec_neg]
  have hinv : ∀ A B C D : Matrix κ κ K, IsUnit A → Aᵀ * C = Cᵀ * A → Bᵀ * D = Dᵀ * B →
      Aᵀ * D - Cᵀ * B = 1 →
      P (fun w => (A *ᵥ w.1 + B *ᵥ w.2, C *ᵥ w.1 + D *ᵥ w.2)) := by
    intro A B C D hA h1 h2 h3
    obtain ⟨E, hAE, hEA⟩ : ∃ E, A * E = 1 ∧ E * A = 1 := isUnit_iff_exists.1 hA
    have hT : Eᵀ * Aᵀ = 1 := by rw [← transpose_mul, hAE, transpose_one]
    have s1 : Eᵀ * Cᵀ = C * E := by
      calc Eᵀ * Cᵀ = Eᵀ * (Cᵀ * A) * E := by
            rw [Matrix.mul_assoc, Matrix.mul_assoc, hAE, Matrix.mul_one]
        _ = C * E := by rw [← h1, ← Matrix.mul_assoc, hT, Matrix.one_mul]
    have hDe : Eᵀ = D - C * E * B := by
      rw [← Matrix.mul_one Eᵀ, ← h3, Matrix.mul_sub, ← Matrix.mul_assoc, hT, Matrix.one_mul,
        ← Matrix.mul_assoc, s1]
    have hEe : E = Dᵀ - Bᵀ * (C * E) := by
      rw [← s1]
      simpa [transpose_sub, transpose_mul] using congrArg transpose hDe
    have s2 : (E * B).IsSymm := by
      rw [Matrix.IsSymm, transpose_mul, hDe]
      conv_rhs => rw [hEe]
      rw [Matrix.mul_sub, Matrix.sub_mul, h2]
      simp only [Matrix.mul_assoc]
    have s3 : (C * E).IsSymm := by rw [Matrix.IsSymm, transpose_mul, s1]
    convert hcomp _ _ (hL _ s3) (hcomp _ _ (hD A E hEA) (hU _ s2)) using 1
    funext w
    have a1 : A * (E * B) = B := by rw [← Matrix.mul_assoc, hAE, Matrix.one_mul]
    have a2 : C * E * A = C := by rw [Matrix.mul_assoc, hEA, Matrix.mul_one]
    simp only [Function.comp, mulVec_add, mulVec_mulVec, a1, a2, hDe, sub_mulVec, Prod.mk.injEq,
      true_and]
    abel
  obtain ⟨A, B, C, D, hw⟩ : ∃ A B C D : Matrix κ κ K,
      ∀ w, g w = (A *ᵥ w.1 + B *ᵥ w.2, C *ᵥ w.1 + D *ᵥ w.2) := by
    refine ⟨LinearMap.toMatrix' (LinearMap.fst K _ _ ∘ₗ g ∘ₗ LinearMap.inl K _ _),
      LinearMap.toMatrix' (LinearMap.fst K _ _ ∘ₗ g ∘ₗ LinearMap.inr K _ _),
      LinearMap.toMatrix' (LinearMap.snd K _ _ ∘ₗ g ∘ₗ LinearMap.inl K _ _),
      LinearMap.toMatrix' (LinearMap.snd K _ _ ∘ₗ g ∘ₗ LinearMap.inr K _ _), fun w => ?_⟩
    simp only [LinearMap.toMatrix'_mulVec]
    have : g w = g (w.1, 0) + g (0, w.2) := by rw [← map_add]; simp
    rw [this]
    rfl
  simp only [hw] at hg
  have h1 : Aᵀ * C = Cᵀ * A := UpperTheory.matrix_ext_bilinear fun x y => by
    have := hg (x, 0) (y, 0)
    simp only [mulVec_zero, add_zero, dotProduct_zero, sub_self] at this
    rw [← UpperTheory.dot_mulVec_eq, ← UpperTheory.dot_mulVec_eq, dotProduct_comm (C *ᵥ x)]
    exact sub_eq_zero.1 this
  have h2 : Bᵀ * D = Dᵀ * B := UpperTheory.matrix_ext_bilinear fun x y => by
    have := hg (0, x) (0, y)
    simp only [mulVec_zero, zero_add, zero_dotProduct, sub_self] at this
    rw [← UpperTheory.dot_mulVec_eq, ← UpperTheory.dot_mulVec_eq, dotProduct_comm (D *ᵥ x)]
    exact sub_eq_zero.1 this
  have h3 : Aᵀ * D - Cᵀ * B = 1 := UpperTheory.matrix_ext_bilinear fun x y => by
    have := hg (x, 0) (0, y)
    simp only [mulVec_zero, zero_add, add_zero, zero_dotProduct, sub_zero] at this
    rw [sub_mulVec, dotProduct_sub, ← UpperTheory.dot_mulVec_eq, ← UpperTheory.dot_mulVec_eq,
      dotProduct_comm (C *ᵥ x), one_mulVec]
    exact this
  have h4 : Dᵀ * A - Bᵀ * C = 1 := by
    simpa [transpose_sub, transpose_mul] using congrArg transpose h3
  obtain ⟨X, hX, hu⟩ := UpperTheory.symmetric_shift_isUnit A C (fun x hA hC => by
    rw [← one_mulVec x, ← h4, sub_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, hA, hC]
    simp) h1
  have key := hinv (A + X * C) (B + X * D) C D hu
    (by simp only [transpose_add, transpose_mul, hX.eq, Matrix.add_mul, Matrix.mul_add, h1,
          Matrix.mul_assoc])
    (by simp only [transpose_add, transpose_mul, hX.eq, Matrix.add_mul, Matrix.mul_add, h2,
          Matrix.mul_assoc])
    (by
      simp only [transpose_add, transpose_mul, hX.eq, Matrix.add_mul, Matrix.mul_add,
        Matrix.mul_assoc, ← h3]
      abel)
  convert hcomp _ _ (hU _ hX.neg) key using 1
  funext w
  simp only [hw, Function.comp, add_mulVec, neg_mulVec, mulVec_add, mulVec_mulVec, Matrix.neg_mul,
    Prod.mk.injEq, and_true]
  abel
