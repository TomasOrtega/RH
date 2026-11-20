import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeEvFun
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviEmbeddingExistsDoublingConfiguration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLocalTorusFactorization
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.PlaneLeviHermAt

open GlobalTheory.LeviElem

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Establish `h : M * P = P * blk (1 : Matrix (Fin b) (Fin b) R) t u`. Substitute `hP` using the available equality. Rewrite using `[Matrix.mul_fromCols, blk, Matrix.fromCols_mul_fromBlocks]`. Simplify using `only [Matrix.mul_one, Matrix.mul_zero, add_zero, zero_add, hι]`. Use `congr 1`.

Use extensionality with `i k`. Use `fin_cases k`. Use `congrFun hx i` as an intermediate fact. Simplify `this` using `[cols2, Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.diagonal, mul_comm]`. Use `congrFun hy i` as an intermediate fact.

Simplify `this` using `[cols2, Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.diagonal, mul_comm]`. Rewrite using `[← h, Matrix.mul_assoc, hPQ, Matrix.mul_one]`.
-/
lemma eq_conj {R : Type} [CommRing R] {b : ℕ} (ι : Matrix (Fin (b + 2)) (Fin b) R) (x y : Fin (b + 2) → R)
    (P : Matrix (Fin (b + 2)) (Fin b ⊕ Fin 2) R) (hP : P = Matrix.fromCols ι (cols2 x y))
    (Q : Matrix (Fin b ⊕ Fin 2) (Fin (b + 2)) R) (hPQ : P * Q = 1)
    (M : Matrix (Fin (b + 2)) (Fin (b + 2)) R) (t u : R) (hx : M *ᵥ x = t • x) (hy : M *ᵥ y = u • y) (hι : M * ι = ι) :
    M = P * blk (1 : Matrix (Fin b) (Fin b) R) t u * Q := by
  have h : M * P = P * blk (1 : Matrix (Fin b) (Fin b) R) t u := by
    subst hP
    rw [Matrix.mul_fromCols, blk, Matrix.fromCols_mul_fromBlocks]
    simp only [Matrix.mul_one, Matrix.mul_zero, add_zero, zero_add, hι]
    congr 1
    ext i k
    fin_cases k
    · have := congrFun hx i
      simpa [cols2, Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.diagonal, mul_comm] using this
    · have := congrFun hy i
      simpa [cols2, Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.diagonal, mul_comm] using this
  rw [← h, Matrix.mul_assoc, hPQ, Matrix.mul_one]

/- English proof (translation)
Take `⟨w⟩ : Nonempty (InfinitePlace F)` from `inferInstance`. Establish `hσ : ∀ z, σ (σ z) = z` using `fun z => (B.emb w).1.injective (by rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star])`. Establish `hdet : G₁.V.J.det ≠ 0`. Establish `h` using `det_ne_of_sig _ (hG₁.hV.sig w)`. Introduce `h0`.

Apply `h` to reduce the goal to its premises. Establish `: (G₁.V.J.map (B.emb w).1).det = (B.emb w).1 G₁.V.J.det` using `(RingHom.map_det (B.emb w).1 _).symm`. Rewrite using `[this, h0, map_zero]`. Use `set P : Matrix (Fin (b + 2)) (Fin b ⊕ Fin 2) E := Matrix.fromCols H.ι (cols2 H.x H.y) with hP`. Establish `hK : Pᵀ * G.V.J * P.map σ = Matrix.fromBlocks G₁.V.J 0 0 swap2` using `gram_block σ hσ B hG.hV.herm hH`.

Use `set K : Matrix (Fin b ⊕ Fin 2) (Fin b ⊕ Fin 2) E := Matrix.fromBlocks G₁.V.J 0 0 swap2 with hKdef`. Establish `hKdet : IsUnit Kᵀ.det`. Rewrite using `[Matrix.det_transpose, hKdef, Matrix.det_fromBlocks_zero₂₁]`. Simplify using `[swap2, Matrix.det_fin_two, hdet]`. Use `set Q : Matrix (Fin b ⊕ Fin 2) (Fin (b + 2)) E := (Kᵀ)⁻¹ * ((P.map σ)ᵀ * G.V.Jᵀ) with hQ`.

Establish `hQP : Q * P = 1`. Establish `: (P.map σ)ᵀ * G.V.Jᵀ * P = Kᵀ`. Rewrite using `[← hK]`. Simplify using `only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]`. Rewrite using `[hQ, Matrix.mul_assoc, this, Matrix.nonsing_inv_mul _ hKdet]`.

Establish `hPQ : P * Q = 1` using `(Matrix.mul_eq_one_comm_of_equiv finSumFinEquiv).1 hQP`. Use `set f : E →+* AE F E := inclR (F := F) (E := E) (AF F) with hf`. Establish `hPf : P.map f = Matrix.fromCols (incM F H.ι) (cols2 (incV F H.x) (incV F H.y))`. Use extensionality with `i (j | j)`. Both sides reduce to the same expression.

Apply the tactic sequence `fin_cases j <;> rfl`. Use `⟨Q.map f, ?_⟩` and prove the remaining obligations. Rewrite using `[← hPf, ← Matrix.map_mul, hPQ, Matrix.map_one _ (map_zero f) (map_one f)]`.
-/
lemma frame_inv (σ : E →ₐ[F] E) (B : Base F E) {b a' : ℕ} (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (hB : B.IsGood σ) (hG : G.IsGood B) (hG₁ : G₁.IsGood B)
    (hH : H.IsAdapted σ B G.V G₁.V 0 (b + 1)) :
    ∃ Q : Matrix (Fin b ⊕ Fin 2) (Fin (b + 2)) (AE F E),
      (Matrix.fromCols (incM F H.ι) (cols2 (incV F H.x) (incV F H.y)) : Matrix (Fin (b + 2)) (Fin b ⊕ Fin 2) (AE F E)) * Q = 1 := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hσ : ∀ z, σ (σ z) = z := fun z => (B.emb w).1.injective (by rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star])
  have hdet : G₁.V.J.det ≠ 0 := by
    have h := det_ne_of_sig _ (hG₁.hV.sig w)
    intro h0
    apply h
    have : (G₁.V.J.map (B.emb w).1).det = (B.emb w).1 G₁.V.J.det := (RingHom.map_det (B.emb w).1 _).symm
    rw [this, h0, map_zero]
  set P : Matrix (Fin (b + 2)) (Fin b ⊕ Fin 2) E := Matrix.fromCols H.ι (cols2 H.x H.y) with hP
  have hK : Pᵀ * G.V.J * P.map σ = Matrix.fromBlocks G₁.V.J 0 0 swap2 := gram_block σ hσ B hG.hV.herm hH
  set K : Matrix (Fin b ⊕ Fin 2) (Fin b ⊕ Fin 2) E := Matrix.fromBlocks G₁.V.J 0 0 swap2 with hKdef
  have hKdet : IsUnit Kᵀ.det := by
    rw [Matrix.det_transpose, hKdef, Matrix.det_fromBlocks_zero₂₁]
    simp [swap2, Matrix.det_fin_two, hdet]
  set Q : Matrix (Fin b ⊕ Fin 2) (Fin (b + 2)) E := (Kᵀ)⁻¹ * ((P.map σ)ᵀ * G.V.Jᵀ) with hQ
  have hQP : Q * P = 1 := by
    have : (P.map σ)ᵀ * G.V.Jᵀ * P = Kᵀ := by
      rw [← hK]; simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    rw [hQ, Matrix.mul_assoc, this, Matrix.nonsing_inv_mul _ hKdet]
  have hPQ : P * Q = 1 := (Matrix.mul_eq_one_comm_of_equiv finSumFinEquiv).1 hQP
  set f : E →+* AE F E := inclR (F := F) (E := E) (AF F) with hf
  have hPf : P.map f = Matrix.fromCols (incM F H.ι) (cols2 (incV F H.x) (incV F H.y)) := by
    ext i (j | j)
    · rfl
    · fin_cases j <;> rfl
  refine ⟨Q.map f, ?_⟩
  rw [← hPf, ← Matrix.map_mul, hPQ, Matrix.map_one _ (map_zero f) (map_one f)]

end GlobalTheory.PlaneLeviHermAt

namespace GlobalTheory.PlaneLeviHermAt

open GlobalTheory.LeviElem

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B b a' G G₁ H H' hC X om om' om₁ om₁' hT hT₁ v`. Take `⟨m0, hm0⟩` from `levi_exists F E σ B b a' G G₁ H H' hC hT.base hT.geo hT₁.geo`. Take `⟨Q, hPQ⟩` from `frame_inv σ B G G₁ H hT.base hT.geo hT₁.geo hC.hH`. Use `⟨fun t => m0 t 1, fun t ht => ⟨hm0 t 1, ?_⟩⟩` and prove the remaining obligations. Take `⟨h1, h2, h3⟩` from `hm0 t 1`.

Establish `h3' : mat (m0 t 1) * incM F H.ι = incM F H.ι`. Rewrite using `[h3, GlobalTheory.StabHaar.mat_one, Matrix.mul_one]`. Establish `e` using `eq_conj (incM F H.ι) (incV F H.x) (incV F H.y) _ rfl Q hPQ (mat (m0 t 1)) t.1 (cA σ (t⁻¹).1) h1 h2 h3'`. Use `show At (evFin F v) (mat (m0 t 1) - 1)`. Establish `e' : mat (m0 t 1) - 1 = (Matrix.fromCols (incM F H.ι) (cols2 (incV F H.x) (incV F H.y)) : Matrix (Fin (b + 2)) (Fin b ⊕ Fin 2) (AE F E)) * (GlobalTheory.PlaneLeviAt.blkT σ t (1 : Matrix (Fin b) (Fin b) (AE F E)) - 1) * Q`.

Rewrite using `[e, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hPQ]`. Both sides reduce to the same expression. Rewrite using `[e']`. Use `GlobalTheory.PlaneLeviAt.at_mul _ _ _ _ (GlobalTheory.PlaneLeviAt.at_blkT _ σ t _ ht ?_)` and prove the remaining obligations. Introduce `u _`.

Rewrite using `[sub_self, smul_zero]`.
-/
theorem exists_isLevi_herm_at : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ)
    (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' → ∀ v : Pl F,
    ∃ m : (AE F E)ˣ → UA σ G.V.J, ∀ t ∈ idelesAt E (evFin F v),
      IsLevi H t (1 : UA σ G₁.V.J) (m t) ∧ m t ∈ UAt σ G.V (evFin F v) := by
  intro F E _ _ _ _ _ σ B b a' G G₁ H H' hC X om om' om₁ om₁' hT hT₁ v
  obtain ⟨m0, hm0⟩ := levi_exists F E σ B b a' G G₁ H H' hC hT.base hT.geo hT₁.geo
  obtain ⟨Q, hPQ⟩ := frame_inv σ B G G₁ H hT.base hT.geo hT₁.geo hC.hH
  refine ⟨fun t => m0 t 1, fun t ht => ⟨hm0 t 1, ?_⟩⟩
  obtain ⟨h1, h2, h3⟩ := hm0 t 1
  have h3' : mat (m0 t 1) * incM F H.ι = incM F H.ι := by
    rw [h3, GlobalTheory.StabHaar.mat_one, Matrix.mul_one]
  have e := eq_conj (incM F H.ι) (incV F H.x) (incV F H.y) _ rfl Q hPQ (mat (m0 t 1)) t.1 (cA σ (t⁻¹).1) h1 h2 h3'
  show At (evFin F v) (mat (m0 t 1) - 1)
  have e' : mat (m0 t 1) - 1 = (Matrix.fromCols (incM F H.ι) (cols2 (incV F H.x) (incV F H.y)) :
      Matrix (Fin (b + 2)) (Fin b ⊕ Fin 2) (AE F E)) *
      (GlobalTheory.PlaneLeviAt.blkT σ t (1 : Matrix (Fin b) (Fin b) (AE F E)) - 1) * Q := by
    rw [e, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hPQ]; rfl
  rw [e']
  refine GlobalTheory.PlaneLeviAt.at_mul _ _ _ _ (GlobalTheory.PlaneLeviAt.at_blkT _ σ t _ ht ?_)
  intro u _
  rw [sub_self, smul_zero]

end GlobalTheory.PlaneLeviHermAt
