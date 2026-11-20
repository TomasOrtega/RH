import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviEmbeddingExistsDoublingConfiguration
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.LeviSupp

open Matrix GlobalTheory.LeviElem

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Establish `h0 : u • (M - 1) * fromCols ι (cols2 x y) = 0`. Use extensionality with `i (j | j)`. Use `congrFun (congrFun hι i) j` as an intermediate fact. Simplify using `only [Matrix.smul_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_apply, Matrix.sub_apply, Matrix.mul_fromCols, fromCols_apply_inl, this, sub_self, smul_zero, Matrix.zero_apply]`. Establish `hx'` using `congrFun hx i`.

Establish `hy'` using `congrFun hy i`. Simplify using `only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at hx' hy'`. Use `fin_cases j`. Simplify using `only [Matrix.smul_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_apply, Matrix.sub_apply, Matrix.mul_fromCols, fromCols_apply_inr, Matrix.zero_apply]`. Establish `: (M * cols2 x y) i 0 = t * x i` using `by simp [Matrix.mul_apply, cols2, hx']`.

Simplify using `only [Fin.zero_eta] at this ⊢`. Rewrite using `[this, show cols2 x y i 0 = x i by simp [cols2], ← sub_one_mul, ← smul_mul_assoc, ht, zero_mul]`. Simplify using `only [Matrix.smul_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_apply, Matrix.sub_apply, Matrix.mul_fromCols, fromCols_apply_inr, Matrix.zero_apply]`. Establish `: (M * cols2 x y) i 1 = s * y i` using `by simp [Matrix.mul_apply, cols2, hy']`. Simplify using `only [Fin.mk_one] at this ⊢`.

Rewrite using `[this, show cols2 x y i 1 = y i by simp [cols2], ← sub_one_mul, ← smul_mul_assoc, hs, zero_mul]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem smul_sub_one_eq_zero {n b : ℕ} {R : Type} [CommRing R] [Algebra (AF F) R] (M : Matrix (Fin n) (Fin n) R)
    (ι : Matrix (Fin n) (Fin b) R) (x y : Fin n → R) (Q : Matrix (Fin b ⊕ Fin 2) (Fin n) R)
    (hPQ : fromCols ι (cols2 x y) * Q = 1) (t s : R) (hx : M *ᵥ x = t • x) (hy : M *ᵥ y = s • y) (hι : M * ι = ι)
    (u : AF F) (ht : u • (t - 1) = 0) (hs : u • (s - 1) = 0) : u • (M - 1) = 0 := by
  have h0 : u • (M - 1) * fromCols ι (cols2 x y) = 0 := by
    ext i (j | j)
    · have := congrFun (congrFun hι i) j
      simp only [Matrix.smul_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_apply, Matrix.sub_apply,
        Matrix.mul_fromCols, fromCols_apply_inl, this, sub_self, smul_zero, Matrix.zero_apply]
    · have hx' := congrFun hx i
      have hy' := congrFun hy i
      simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at hx' hy'
      fin_cases j
      · simp only [Matrix.smul_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_apply, Matrix.sub_apply,
          Matrix.mul_fromCols, fromCols_apply_inr, Matrix.zero_apply]
        have : (M * cols2 x y) i 0 = t * x i := by simp [Matrix.mul_apply, cols2, hx']
        simp only [Fin.zero_eta] at this ⊢
        rw [this, show cols2 x y i 0 = x i by simp [cols2], ← sub_one_mul, ← smul_mul_assoc, ht, zero_mul]
      · simp only [Matrix.smul_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_apply, Matrix.sub_apply,
          Matrix.mul_fromCols, fromCols_apply_inr, Matrix.zero_apply]
        have : (M * cols2 x y) i 1 = s * y i := by simp [Matrix.mul_apply, cols2, hy']
        simp only [Fin.mk_one] at this ⊢
        rw [this, show cols2 x y i 1 = y i by simp [cols2], ← sub_one_mul, ← smul_mul_assoc, hs, zero_mul]
  calc u • (M - 1) = u • (M - 1) * (fromCols ι (cols2 x y) * Q) := by rw [hPQ, Matrix.mul_one]
    _ = 0 := by rw [← Matrix.mul_assoc, h0, Matrix.zero_mul]

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B b a' G G₁ H H' hC hB hG hG₁`. Take `⟨m₀, hm₀⟩` from `levi_exists F E σ B b a' G G₁ H H' hC hB hG hG₁`. Use `⟨fun l => m₀ l 1, fun l hl => ⟨hm₀ l 1, ?_⟩⟩` and prove the remaining obligations. Take `⟨w⟩ : Nonempty (InfinitePlace F)` from `inferInstance`. Establish `hσ : ∀ z, σ (σ z) = z` using `fun z => (B.emb w).1.injective (by rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star])`.

Establish `hdet : G₁.V.J.det ≠ 0`. Establish `h` using `det_ne_of_sig _ (hG₁.hV.sig w)`. Introduce `h0`. Apply `h` to reduce the goal to its premises. Establish `: (G₁.V.J.map (B.emb w).1).det = (B.emb w).1 G₁.V.J.det` using `(RingHom.map_det (B.emb w).1 _).symm`.

Rewrite using `[this, h0, map_zero]`. Use `set P := fromCols H.ι (cols2 H.x H.y) with hP`. Establish `hK : Pᵀ * G.V.J * P.map σ = fromBlocks G₁.V.J 0 0 swap2` using `gram_block σ hσ B hG.hV.herm hC.hH`. Use `set K : Matrix (Fin b ⊕ Fin 2) (Fin b ⊕ Fin 2) E := fromBlocks G₁.V.J 0 0 swap2 with hKdef`. Establish `hKdet : IsUnit Kᵀ.det`.

Rewrite using `[det_transpose, hKdef, det_fromBlocks_zero₂₁]`. Simplify using `[swap2, det_fin_two, hdet]`. Use `set Q := (Kᵀ)⁻¹ * ((P.map σ)ᵀ * G.V.Jᵀ) with hQ`. Establish `hQP : Q * P = 1`. Establish `: (P.map σ)ᵀ * G.V.Jᵀ * P = Kᵀ`.

Rewrite using `[← hK]`. Simplify using `only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]`. Rewrite using `[hQ, Matrix.mul_assoc, this, nonsing_inv_mul _ hKdet]`. Establish `hPQ : P * Q = 1` using `(Matrix.mul_eq_one_comm_of_equiv finSumFinEquiv).1 hQP`. Use `set f : E →+* AE F E := inclR (F := F) (E := E) (AF F) with hf`.

Establish `hPf : P.map f = fromCols (incM F H.ι) (cols2 (incV F H.x) (incV F H.y))`. Use extensionality with `i (j | j)`. Both sides reduce to the same expression. Apply the tactic sequence `fin_cases j <;> rfl`. Establish `hPQ' : fromCols (incM F H.ι) (cols2 (incV F H.x) (incV F H.y)) * Q.map f = 1`.

Rewrite using `[← hPf, ← Matrix.map_mul, hPQ, Matrix.map_one _ (map_zero f) (map_one f)]`. Take `⟨hx, hy, hι⟩` from `hm₀ l 1`. Establish `hone : mat (1 : UA σ G₁.V.J) = 1` using `rfl`. Rewrite `hι` using `[hone, Matrix.mul_one]`. Establish `hl'` using `mem_idelesAt.1 hl`.

Introduce `u hu`. Use `smul_sub_one_eq_zero (mat (m₀ l 1)) _ _ _ _ hPQ' _ _ hx hy hι u (hl' u hu) ?_` and prove the remaining obligations. Establish `e1 : cA σ (l⁻¹ : (AE F E)ˣ).1 - 1 = cA σ (-((l⁻¹ : (AE F E)ˣ).1 * ((l : AE F E) - 1)))`. Rewrite using `[mul_sub, Units.inv_mul, mul_one, neg_sub, map_sub, map_one]`. Rewrite using `[e1, ← map_smul, smul_neg, ← mul_smul_comm, hl' u hu, mul_zero, neg_zero, map_zero]`.
-/
theorem levi_section : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ)
    (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    B.IsGood σ → G.IsGood B → G₁.IsGood B →
    ∃ m : (AE F E)ˣ → UA σ G.V.J, ∀ l ∈ idelesAt E (evI F), IsLevi (W₁ := G₁.V) H l 1 (m l) ∧ m l ∈ UAt σ G.V (evI F) := by
  intro F E _ _ _ _ _ σ B b a' G G₁ H H' hC hB hG hG₁
  obtain ⟨m₀, hm₀⟩ := levi_exists F E σ B b a' G G₁ H H' hC hB hG hG₁
  refine ⟨fun l => m₀ l 1, fun l hl => ⟨hm₀ l 1, ?_⟩⟩
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hσ : ∀ z, σ (σ z) = z := fun z => (B.emb w).1.injective (by rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star])
  have hdet : G₁.V.J.det ≠ 0 := by
    have h := det_ne_of_sig _ (hG₁.hV.sig w)
    intro h0
    apply h
    have : (G₁.V.J.map (B.emb w).1).det = (B.emb w).1 G₁.V.J.det := (RingHom.map_det (B.emb w).1 _).symm
    rw [this, h0, map_zero]
  set P := fromCols H.ι (cols2 H.x H.y) with hP
  have hK : Pᵀ * G.V.J * P.map σ = fromBlocks G₁.V.J 0 0 swap2 := gram_block σ hσ B hG.hV.herm hC.hH
  set K : Matrix (Fin b ⊕ Fin 2) (Fin b ⊕ Fin 2) E := fromBlocks G₁.V.J 0 0 swap2 with hKdef
  have hKdet : IsUnit Kᵀ.det := by
    rw [det_transpose, hKdef, det_fromBlocks_zero₂₁]
    simp [swap2, det_fin_two, hdet]
  set Q := (Kᵀ)⁻¹ * ((P.map σ)ᵀ * G.V.Jᵀ) with hQ
  have hQP : Q * P = 1 := by
    have : (P.map σ)ᵀ * G.V.Jᵀ * P = Kᵀ := by
      rw [← hK]; simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    rw [hQ, Matrix.mul_assoc, this, nonsing_inv_mul _ hKdet]
  have hPQ : P * Q = 1 := (Matrix.mul_eq_one_comm_of_equiv finSumFinEquiv).1 hQP
  set f : E →+* AE F E := inclR (F := F) (E := E) (AF F) with hf
  have hPf : P.map f = fromCols (incM F H.ι) (cols2 (incV F H.x) (incV F H.y)) := by
    ext i (j | j)
    · rfl
    · fin_cases j <;> rfl
  have hPQ' : fromCols (incM F H.ι) (cols2 (incV F H.x) (incV F H.y)) * Q.map f = 1 := by
    rw [← hPf, ← Matrix.map_mul, hPQ, Matrix.map_one _ (map_zero f) (map_one f)]
  obtain ⟨hx, hy, hι⟩ := hm₀ l 1
  have hone : mat (1 : UA σ G₁.V.J) = 1 := rfl
  rw [hone, Matrix.mul_one] at hι
  have hl' := mem_idelesAt.1 hl
  intro u hu
  refine smul_sub_one_eq_zero (mat (m₀ l 1)) _ _ _ _ hPQ' _ _ hx hy hι u (hl' u hu) ?_
  have e1 : cA σ (l⁻¹ : (AE F E)ˣ).1 - 1 = cA σ (-((l⁻¹ : (AE F E)ˣ).1 * ((l : AE F E) - 1))) := by
    rw [mul_sub, Units.inv_mul, mul_one, neg_sub, map_sub, map_one]
  rw [e1, ← map_smul, smul_neg, ← mul_smul_comm, hl' u hu, mul_zero, neg_zero, map_zero]

end GlobalTheory.LeviSupp
