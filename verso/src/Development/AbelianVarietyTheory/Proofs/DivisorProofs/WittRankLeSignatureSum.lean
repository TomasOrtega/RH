import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat

open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability

noncomputable section

namespace GlobalTheory.WittBoundSkew

open Matrix
open scoped ComplexOrder

/- English proof (translation)
Establish `hs : star (Q *ᵥ x) = Q.map star *ᵥ star x`. Use extensionality with `i`. Simplify using `[mulVec, dotProduct, star_sum]`. Rewrite using `[hs, ← vecMul_transpose, mulVec_mulVec, dotProduct_mulVec, vecMul_vecMul, dotProduct_mulVec, Matrix.mul_assoc]`.
-/
theorem form_mulVec {n k : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (Q : Matrix (Fin n) (Fin k) ℂ) (x : Fin k → ℂ) :
    (Q *ᵥ x) ⬝ᵥ (M *ᵥ star (Q *ᵥ x)) = x ⬝ᵥ ((Qᵀ * M * Q.map star) *ᵥ star x) := by
  have hs : star (Q *ᵥ x) = Q.map star *ᵥ star x := by
    ext i; simp [mulVec, dotProduct, star_sum]
  rw [hs, ← vecMul_transpose, mulVec_mulVec, dotProduct_mulVec, vecMul_vecMul, dotProduct_mulVec, Matrix.mul_assoc]

/- English proof (translation)
Take `⟨hn, A, hA⟩` from `hS`. Use `set A₁ : Matrix (Fin n) (Fin m) ℂ := A.submatrix id Sum.inl with hA₁`. Establish `hA₁M : A₁ᵀ * M * A₁.map star = 1`. Use extensionality with `i j`. Establish `h` using `congrFun (congrFun hA (Sum.inl i)) (Sum.inl j)`.

Simplify `h` using `[A₁, Matrix.mul_apply, transpose_apply, Matrix.one_apply]`. Establish `hpos : ∀ x : Fin m → ℂ, (A₁ *ᵥ x) ⬝ᵥ (M *ᵥ star (A₁ *ᵥ x)) = 0 → x = 0`. Introduce `x hx`. Rewrite `hx` using `[form_mulVec, hA₁M, one_mulVec, dotProduct_comm]`. Conclude with `dotProduct_star_self_eq_zero.mp hx`.

Establish `hiso : ∀ y : Fin r → ℂ, (Z *ᵥ y) ⬝ᵥ (M *ᵥ star (Z *ᵥ y)) = 0`. Introduce `y`. Rewrite using `[form_mulVec, hZ, zero_mulVec, dotProduct_zero]`. Establish `hinj : Function.Injective (fromCols Z A₁).mulVecLin`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`.

Introduce `w hw`. Establish `hw' : Z *ᵥ (fun i => w (Sum.inl i)) + A₁ *ᵥ (fun i => w (Sum.inr i)) = 0`. Rewrite using `[← hw]`. Use extensionality with `i`. Simplify using `[mulVec, dotProduct, Fintype.sum_sum_type, fromCols]`.

Establish `hZA : Z *ᵥ (fun i => w (Sum.inl i)) = A₁ *ᵥ (-(fun i => w (Sum.inr i)))`. Rewrite using `[mulVec_neg]`. Conclude with `eq_neg_of_add_eq_zero_left hw'`. Establish `hx : -(fun i => w (Sum.inr i)) = 0` using `hpos _ (by rw [← hZA]; exact hiso _)`. Establish `hx' : (fun i => w (Sum.inr i)) = 0` using `neg_eq_zero.mp hx`.

Establish `hy0 : Z *ᵥ (fun i => w (Sum.inl i)) = 0` using `by rw [hZA, hx, mulVec_zero]`. Establish `hy : (fun i => w (Sum.inl i)) = 0`. Combine the equalities or inequalities in the displayed calculation. Use function extensionality and compare the values at `i`. Break down `i with i | i` into its components or cases.

Conclude with `congrFun hy i`. Conclude with `congrFun hx' i`. Establish `h` using `LinearMap.finrank_le_finrank_of_injective hinj`. Simplify using `only [Module.finrank_fin_fun, Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin] at h`. Use linear arithmetic over natural numbers and integers.
-/
theorem le_of_isotropic_sig {n m s r : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (hS : HasSig M m s)
    (Z : Matrix (Fin n) (Fin r) ℂ) (L : Matrix (Fin r) (Fin n) ℂ) (hL : L * Z = 1)
    (hZ : Zᵀ * M * Z.map star = 0) : r ≤ s := by
  obtain ⟨hn, A, hA⟩ := hS
  set A₁ : Matrix (Fin n) (Fin m) ℂ := A.submatrix id Sum.inl with hA₁
  have hA₁M : A₁ᵀ * M * A₁.map star = 1 := by
    ext i j
    have h := congrFun (congrFun hA (Sum.inl i)) (Sum.inl j)
    simpa [A₁, Matrix.mul_apply, transpose_apply, Matrix.one_apply] using h
  have hpos : ∀ x : Fin m → ℂ, (A₁ *ᵥ x) ⬝ᵥ (M *ᵥ star (A₁ *ᵥ x)) = 0 → x = 0 := by
    intro x hx
    rw [form_mulVec, hA₁M, one_mulVec, dotProduct_comm] at hx
    exact dotProduct_star_self_eq_zero.mp hx
  have hiso : ∀ y : Fin r → ℂ, (Z *ᵥ y) ⬝ᵥ (M *ᵥ star (Z *ᵥ y)) = 0 := by
    intro y
    rw [form_mulVec, hZ, zero_mulVec, dotProduct_zero]
  have hinj : Function.Injective (fromCols Z A₁).mulVecLin := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    have hw' : Z *ᵥ (fun i => w (Sum.inl i)) + A₁ *ᵥ (fun i => w (Sum.inr i)) = 0 := by
      rw [← hw]
      ext i
      simp [mulVec, dotProduct, Fintype.sum_sum_type, fromCols]
    have hZA : Z *ᵥ (fun i => w (Sum.inl i)) = A₁ *ᵥ (-(fun i => w (Sum.inr i))) := by
      rw [mulVec_neg]; exact eq_neg_of_add_eq_zero_left hw'
    have hx : -(fun i => w (Sum.inr i)) = 0 := hpos _ (by rw [← hZA]; exact hiso _)
    have hx' : (fun i => w (Sum.inr i)) = 0 := neg_eq_zero.mp hx
    have hy0 : Z *ᵥ (fun i => w (Sum.inl i)) = 0 := by rw [hZA, hx, mulVec_zero]
    have hy : (fun i => w (Sum.inl i)) = 0 := by
      calc (fun i => w (Sum.inl i)) = (L * Z) *ᵥ (fun i => w (Sum.inl i)) := by rw [hL, one_mulVec]
        _ = 0 := by rw [← mulVec_mulVec, hy0, mulVec_zero]
    funext i
    rcases i with i | i
    · exact congrFun hy i
    · exact congrFun hx' i
  have h := LinearMap.finrank_le_finrank_of_injective hinj
  simp only [Module.finrank_fin_fun, Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin] at h
  omega

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B a a' G X om om' hT c hc _ r Xf Yf hW`. Take `⟨w⟩ : Nonempty (InfinitePlace F)` from `inferInstance`. Use `set τ : E →+* ℂ := (B.emb w).1 with hτ`. Establish `hconj : ∀ x, τ (σ x) = star (τ x)` using `fun x => hT.base.cm.2.2.2 τ x`. Use `set ρ : E →+* ℂ := (starRingEnd ℂ).comp τ with hρ`.

Establish `hρσ : ∀ x, ρ (σ x) = τ x` using `fun x => by simp [ρ, hconj]`. Use `set Z : Matrix (Fin (a + a')) (Fin r) ℂ := Xf.map τ with hZ`. Establish `hXρ : Xf.map ρ = Z.map star` using `by ext i j; simp [ρ, Z]`. Establish `key : ∀ {k : ℕ} (Y : Matrix (Fin (a + a')) (Fin k) E), (Formalism.UG.cT (σ : E →+* E) Xf * (c • G.W.J.map σ) * Y).map ρ = Zᵀ * (ρ c • G.W.J.map τ) * Y.map ρ`. Introduce `k Y`.

Rewrite using `[Matrix.map_mul, Matrix.map_mul]`. Use `congr 2`. Use extensionality with `i j`. Simplify using `[Formalism.UG.cT, Z, hρσ]`. Use extensionality with `i j`.

Simplify using `[hρσ]`. Establish `hρc : ρ c ≠ 0` using `(map_ne_zero ρ).mpr hc`. Establish `hxx : Zᵀ * (Complex.I • G.W.J.map τ) * Z.map star = 0`. Establish `h` using `key Xf`. Rewrite `h` using `[hW.xx, Matrix.map_zero _ (map_zero _), hXρ]`.

Establish `h2 : ρ c • (Zᵀ * G.W.J.map τ * Z.map star) = 0`. Rewrite using `[h]`. Simplify using `[Matrix.mul_smul, Matrix.smul_mul]`. Establish `h3 : Zᵀ * G.W.J.map τ * Z.map star = 0` using `(smul_eq_zero.mp h2).resolve_left hρc`. Rewrite using `[Matrix.mul_smul, Matrix.smul_mul, h3, smul_zero]`.

Establish `hxy : Zᵀ * ((ρ c • G.W.J.map τ) * Yf.map ρ) = 1`. Establish `h` using `key Yf`. Rewrite `h` using `[hW.xy, Matrix.map_one _ (map_zero _) (map_one _)]`. Rewrite using `[← Matrix.mul_assoc, ← h]`. Establish `hL : ((ρ c • G.W.J.map τ) * Yf.map ρ)ᵀ * Z = 1`.

Establish `h` using `congrArg Matrix.transpose hxy`. Rewrite `h` using `[Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one]`. Then use the resulting hypothesis. Conclude with `le_of_isotropic_sig _ (hT.geo.hW.sig w) Z _ hL hxx`.
-/
theorem wittIndex_le : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' → ∀ c : E, c ≠ 0 → σ c = -c →
      ∀ (r : ℕ) (Xf Yf : Matrix (Fin (a + a')) (Fin r) E), IsWittFrame σ (c • G.W.J.map σ) Xf Yf → r ≤ G.p + G.q := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT c hc _ r Xf Yf hW
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  set τ : E →+* ℂ := (B.emb w).1 with hτ
  have hconj : ∀ x, τ (σ x) = star (τ x) := fun x => hT.base.cm.2.2.2 τ x
  set ρ : E →+* ℂ := (starRingEnd ℂ).comp τ with hρ
  have hρσ : ∀ x, ρ (σ x) = τ x := fun x => by simp [ρ, hconj]
  set Z : Matrix (Fin (a + a')) (Fin r) ℂ := Xf.map τ with hZ
  have hXρ : Xf.map ρ = Z.map star := by ext i j; simp [ρ, Z]
  have key : ∀ {k : ℕ} (Y : Matrix (Fin (a + a')) (Fin k) E),
      (Formalism.UG.cT (σ : E →+* E) Xf * (c • G.W.J.map σ) * Y).map ρ = Zᵀ * (ρ c • G.W.J.map τ) * Y.map ρ := by
    intro k Y
    rw [Matrix.map_mul, Matrix.map_mul]
    congr 2
    · ext i j; simp [Formalism.UG.cT, Z, hρσ]
    · ext i j; simp [hρσ]
  have hρc : ρ c ≠ 0 := (map_ne_zero ρ).mpr hc
  have hxx : Zᵀ * (Complex.I • G.W.J.map τ) * Z.map star = 0 := by
    have h := key Xf
    rw [hW.xx, Matrix.map_zero _ (map_zero _), hXρ] at h
    have h2 : ρ c • (Zᵀ * G.W.J.map τ * Z.map star) = 0 := by
      rw [h]; simp [Matrix.mul_smul, Matrix.smul_mul]
    have h3 : Zᵀ * G.W.J.map τ * Z.map star = 0 := (smul_eq_zero.mp h2).resolve_left hρc
    rw [Matrix.mul_smul, Matrix.smul_mul, h3, smul_zero]
  have hxy : Zᵀ * ((ρ c • G.W.J.map τ) * Yf.map ρ) = 1 := by
    have h := key Yf
    rw [hW.xy, Matrix.map_one _ (map_zero _) (map_one _)] at h
    rw [← Matrix.mul_assoc, ← h]
  have hL : ((ρ c • G.W.J.map τ) * Yf.map ρ)ᵀ * Z = 1 := by
    have h := congrArg Matrix.transpose hxy
    rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at h
  exact le_of_isotropic_sig _ (hT.geo.hW.sig w) Z _ hL hxx

end GlobalTheory.WittBoundSkew
