import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.OrientEv
import Development.AutomorphicArithmetic.CMTraceEmbeddings.CmFieldRealTensorMatrixBijectiveCmType
import Development.AutomorphicArithmetic.CMTraceEmbeddings.CmTypeTraceEmbeddingInjectiveOfLinearEquiv
import Development.AutomorphicArithmetic.CMTraceEmbeddings.CmFieldHermitianFormBaseChangeRealEqSum

noncomputable section

open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

namespace UpperTheory.Gal.W2.Seed.Ori

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

private def dv (A : Arith E) (n : ℕ) (σ : E →+* ℂ) (i : Fin n) : ℂ :=
  if 0 < (σ (A.hd n i : E)).re then Complex.I else -Complex.I

/- English proof (translation)
Take `⟨-, -, h1, h2⟩` from `hS E A n σ i`. Distinguish the cases in `h : InfinitePlace.mk σ = InfinitePlace.mk A.τ₀ ∧ (i : ℕ) = 0`. Conclude with `(h1 h).ne'`. Conclude with `(h2 h).ne`.
-/
private theorem hd_ne (hS : HdSign) (A : Arith E) (n : ℕ) (σ : E →+* ℂ) (i : Fin n) : (σ (A.hd n i : E)).re ≠ 0 := by
  obtain ⟨-, -, h1, h2⟩ := hS E A n σ i
  by_cases h : InfinitePlace.mk σ = InfinitePlace.mk A.τ₀ ∧ (i : ℕ) = 0
  · exact (h1 h).ne'
  · exact (h2 h).ne

/- English proof (translation)
Apply the tactic sequence `unfold dv; split_ifs <;> simp`.
-/
private theorem dv_sq (A : Arith E) (n : ℕ) (σ : E →+* ℂ) (i : Fin n) : dv A n σ i * dv A n σ i = -1 := by
  unfold dv; split_ifs <;> simp

/- English proof (translation)
Apply the tactic sequence `unfold dv; split_ifs <;> simp`.
-/
private theorem dv_conj (A : Arith E) (n : ℕ) (σ : E →+* ℂ) (i : Fin n) :
    (starRingEnd ℂ) (dv A n σ i) = -dv A n σ i := by
  unfold dv; split_ifs <;> simp

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [gramAt, Arith.H, Matrix.transpose_apply, Matrix.map_apply, Matrix.diagonal_apply]`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[h, Ne.symm h]`.
-/
private theorem gram_diag (A : Arith E) (n : ℕ) (σ : E →+* ℂ) :
    gramAt (A.H n) σ = Matrix.diagonal fun i => σ (A.hd n i : E) := by
  ext i j
  simp only [gramAt, Arith.H, Matrix.transpose_apply, Matrix.map_apply, Matrix.diagonal_apply]
  by_cases h : i = j
  · subst h
    simp
  · simp [h, Ne.symm h]

/- English proof (translation)
Establish `hh : h = ((h.re : ℝ) : ℂ)` using `Complex.ext (by simp) (by simp [hi])`. Use `split_ifs with hp`. Rewrite using `[abs_of_pos hp]`. Prove the components needed by the constructor for the conclusion. Rewrite using `[hh]`.

Put the polynomial expressions in normal form. Simplify using the standard rewrite rules. Rewrite using `[hh]`. Simplify using the standard rewrite rules. Put the polynomial expressions in normal form.

Simplify using the standard rewrite rules. Rewrite using `[abs_of_neg (lt_of_le_of_ne (not_lt.mp hp) hr)]`. Prove the components needed by the constructor for the conclusion. Rewrite using `[hh]`. Put the polynomial expressions in normal form.

Simplify using the standard rewrite rules. Rewrite using `[hh]`. Simplify using the standard rewrite rules. Put the polynomial expressions in normal form. Simplify using the standard rewrite rules.
-/
private theorem real_abs (h : ℂ) (hi : h.im = 0) (hr : h.re ≠ 0) :
    -Complex.I * (h * (if 0 < h.re then Complex.I else -Complex.I)) = ((|h.re| : ℝ) : ℂ) ∧
    Complex.I * (h * (starRingEnd ℂ) (if 0 < h.re then Complex.I else -Complex.I)) = ((|h.re| : ℝ) : ℂ) := by
  have hh : h = ((h.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hi])
  split_ifs with hp
  · rw [abs_of_pos hp]
    constructor
    · rw [hh]
      ring_nf
      simp
    · rw [hh]
      simp
      ring_nf
      simp
  · rw [abs_of_neg (lt_of_le_of_ne (not_lt.mp hp) hr)]
    constructor
    · rw [hh]
      ring_nf
      simp
    · rw [hh]
      simp
      ring_nf
      simp

open scoped ComplexOrder in
/- English proof (translation)
Rewrite using `[Matrix.posDef_diagonal_iff]`. Introduce `i`. Conclude with `Complex.zero_lt_real.mpr (ha i)`.
-/
private theorem posDiag {n : ℕ} (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) :
    (Matrix.diagonal fun i => ((a i : ℝ) : ℂ)).PosDef := by
  rw [Matrix.posDef_diagonal_iff]
  intro i
  exact Complex.zero_lt_real.mpr (ha i)

open scoped Classical ComplexOrder in
/- English proof (translation)
Take `⟨J, hJ⟩` from `(cmField_real_tensor_matrix_bijective_cmType hT A n).2 (fun τ : Phi A => Matrix.diagonal (dv A n τ.1))`. Establish `hJτ : ∀ τ : Phi A, evM τ.1 J = Matrix.diagonal (dv A n τ.1)` using `fun τ => congrFun hJ τ`. Establish `hne : ∀ (σ : E →+* ℂ) (i : Fin n), σ (A.hd n i : E) ≠ 0` using `fun σ i h0 => hd_ne hS A n σ i (by rw [h0]; simp)`. Take `⟨β, hβ1, hβ2⟩` from `hrep`. Use `⟨J, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Use `(cmField_real_tensor_matrix_bijective_cmType hT A n).1 (funext fun τ => ?_) dsimp only` and prove the remaining obligations. Rewrite using `[map_mul, map_neg, map_one, hJτ, Matrix.diagonal_mul_diagonal]`. Use extensionality with `i j`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality.

Simplify using `[dv_sq]`. Simplify using `[Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]`. Use `(cmField_real_tensor_matrix_bijective_cmType hT A n).1 (funext fun τ => ?_) dsimp only` and prove the remaining obligations. Establish `key` using `evM_star (A.H n) (A.herm n) (A.det_ne n) τ.1 J`. Rewrite `key` using `[gram_diag, hJτ, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]`.

Rewrite using `[map_neg, hJτ]`. Use extensionality with `i j`. Establish `hk` using `congrFun (congrFun key i) j`. Rewrite `hk` using `[Matrix.diagonal_mul]`. Distinguish the cases in `hij : i = j`.

Substitute `hij` using the available equality. Simplify using `only [Matrix.diagonal_apply_eq, Pi.star_apply, Matrix.neg_apply] at hk ⊢`. Apply `mul_left_cancel₀ (hne τ.1 i)` to reduce the goal to its premises. Rewrite using `[hk, Complex.star_def, dv_conj]`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `only [Matrix.diagonal_apply_ne _ hij, Matrix.neg_apply, neg_zero] at hk ⊢`. Conclude with `(mul_eq_zero.mp hk).resolve_left (hne τ.1 i)`. Introduce `x hx`. Rewrite using `[cmField_hermitianForm_baseChange_real_eq_sum hT A n (β : ℚ ⊗[ℤ] (Fin n → 𝓞 E) →ₗ[ℚ] Fin n → E) hβ1]`. Establish `hterm : ∀ k : Phi A × Fin n, Th (fun τ : Phi A => (τ : E →+* ℂ)) (β : ℚ ⊗[ℤ] (Fin n → 𝓞 E) →ₗ[ℚ] Fin n → E) (actOn rep ℝ J x) k = dv A n k.1.1 k.2 * Th (fun τ : Phi A => (τ : E →+* ℂ)) (β : ℚ ⊗[ℤ] (Fin n → 𝓞 E) →ₗ[ℚ] Fin n → E) x k`.

Introduce and unpack `⟨τ, i⟩`. Rewrite using `[Th_act (fun τ : Phi A => (τ : E →+* ℂ)) (β : ℚ ⊗[ℤ] (Fin n → 𝓞 E) →ₗ[ℚ] Fin n → E) rep hβ2 J x τ i, hJτ, Matrix.mulVec_diagonal]`. Establish `hz : ∃ k, Th (fun τ : Phi A => (τ : E →+* ℂ)) (β : ℚ ⊗[ℤ] (Fin n → 𝓞 E) →ₗ[ℚ] Fin n → E) x k ≠ 0`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`.

Apply `hx` to reduce the goal to its premises. Apply `cmType_trace_embedding_injective_of_linearEquiv hT A n β` to reduce the goal to its premises. Rewrite using `[map_zero]`. Use function extensionality and compare the values at `k`. Conclude with `hc k`.

Take `⟨k₀, hk₀⟩` from `hz`. Establish `tp` using `fun (τ : Phi A) (i : Fin n) (z : ℂ) => term_pos (τ.1 A.δ) (τ.1 (A.hd n i : E)) z (hS E A n τ.1 i).2.1 (A.δ_sign τ.1 τ.2) (hS E A n τ.1 i).1 (hd_ne hS A n τ.1 i)`. Apply `Finset.sum_pos'` to reduce the goal to its premises. Introduce and unpack `⟨τ, i⟩ -`. Rewrite using `[hterm]`.

Unfold `dv`. Conclude with `mul_nonneg two_pos.le (tp τ i _).1`. Use `⟨k₀, Finset.mem_univ _, ?_⟩` and prove the remaining obligations. Take `⟨τ, i⟩` from `k₀`. Rewrite using `[hterm]`.

Unfold `dv`. Conclude with `mul_pos two_pos ((tp τ i _).2 hk₀)`. Introduce `v`. Take `⟨τ, hτv, -⟩` from `(hT E A).2.2.1 v`. Substitute `hτv` using the available equality.

Establish `hω` using `(hT E A).2.2.2`. Break down `InfinitePlace.embedding_mk_eq (τ : E →+* ℂ) with he | he` into its components or cases. Rewrite using `[he, if_pos τ.2, gram_diag, hJτ, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_smul]`. Establish `hf : (-Complex.I • fun i => τ.1 (A.hd n i : E) * dv A n τ.1 i) = fun i => (((|(τ.1 (A.hd n i : E)).re| : ℝ)) : ℂ)`. Use function extensionality and compare the values at `i`.

Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Conclude with `(real_abs _ (hS E A n τ.1 i).1 (hd_ne hS A n τ.1 i)).1`. Rewrite using `[hf]`. Conclude with `posDiag _ fun i => abs_pos.mpr (hd_ne hS A n τ.1 i)`. Establish `hc : ¬ (ComplexEmbedding.conjugate (τ : E →+* ℂ)) (A.ω : E) = A.τ₀ (A.ω : E)`.

Introduce `h`. Rewrite `h` using `[ComplexEmbedding.conjugate_coe_eq, τ.2]`. Conclude with `hω (Complex.conj_eq_iff_im.mp h)`. Rewrite using `[he, if_neg hc, gram_diag, evM_conj, hJτ, Matrix.diagonal_map (map_zero _), Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_smul]`. Establish `hf : (Complex.I • fun i => (ComplexEmbedding.conjugate (τ : E →+* ℂ)) (A.hd n i : E) * (starRingEnd ℂ) (dv A n τ.1 i)) = fun i => (((|(τ.1 (A.hd n i : E)).re| : ℝ)) : ℂ)`.

Use function extensionality and compare the values at `i`. Simplify using `only [Pi.smul_apply, smul_eq_mul, ComplexEmbedding.conjugate_coe_eq]`. Rewrite using `[Complex.conj_eq_iff_im.mpr (hS E A n τ.1 i).1]`. Conclude with `(real_abs _ (hS E A n τ.1 i).1 (hd_ne hS A n τ.1 i)).2`. Rewrite using `[hf]`.

Conclude with `posDiag _ fun i => abs_pos.mpr (hd_ne hS A n τ.1 i)`.
-/
private theorem orient_core (hT : TraceType) (hS : HdSign) (A : Arith E) (n : ℕ)
    (rep : Matrix (Fin n) (Fin n) E →ₐ[ℚ] Module.End ℚ (ℚ ⊗[ℤ] (Fin n → 𝓞 E))) (hrep : RepOK A n rep) :
    ∃ J : ℝ ⊗[ℚ] Matrix (Fin n) (Fin n) E, J * J = -1 ∧
      (starT (hermStar (A.H n) (A.det_ne n)) ℝ J).unop = -J ∧
      (∀ x, x ≠ 0 → 0 < ((A.EF n).baseChange ℚ).baseChange ℝ (actOn rep ℝ J x) x) ∧
      ∀ v : InfinitePlace E, ((if v.embedding (A.ω : E) = A.τ₀ (A.ω : E) then -Complex.I else Complex.I) •
        (gramAt (A.H n) v.embedding * evM v.embedding J)).PosDef := by
  obtain ⟨J, hJ⟩ := (cmField_real_tensor_matrix_bijective_cmType hT A n).2 (fun τ : Phi A => Matrix.diagonal (dv A n τ.1))
  have hJτ : ∀ τ : Phi A, evM τ.1 J = Matrix.diagonal (dv A n τ.1) := fun τ => congrFun hJ τ
  have hne : ∀ (σ : E →+* ℂ) (i : Fin n), σ (A.hd n i : E) ≠ 0 := fun σ i h0 =>
    hd_ne hS A n σ i (by rw [h0]; simp)
  obtain ⟨β, hβ1, hβ2⟩ := hrep
  refine ⟨J, ?_, ?_, ?_, ?_⟩
  · refine (cmField_real_tensor_matrix_bijective_cmType hT A n).1 (funext fun τ => ?_)
    dsimp only
    rw [map_mul, map_neg, map_one, hJτ, Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [dv_sq]
    · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
  · refine (cmField_real_tensor_matrix_bijective_cmType hT A n).1 (funext fun τ => ?_)
    dsimp only
    have key := evM_star (A.H n) (A.herm n) (A.det_ne n) τ.1 J
    rw [gram_diag, hJτ, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal] at key
    rw [map_neg, hJτ]
    ext i j
    have hk := congrFun (congrFun key i) j
    rw [Matrix.diagonal_mul] at hk
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.diagonal_apply_eq, Pi.star_apply, Matrix.neg_apply] at hk ⊢
      apply mul_left_cancel₀ (hne τ.1 i)
      rw [hk, Complex.star_def, dv_conj]
      ring
    · simp only [Matrix.diagonal_apply_ne _ hij, Matrix.neg_apply, neg_zero] at hk ⊢
      exact (mul_eq_zero.mp hk).resolve_left (hne τ.1 i)
  · intro x hx
    rw [cmField_hermitianForm_baseChange_real_eq_sum hT A n (β : ℚ ⊗[ℤ] (Fin n → 𝓞 E) →ₗ[ℚ] Fin n → E) hβ1]
    have hterm : ∀ k : Phi A × Fin n,
        Th (fun τ : Phi A => (τ : E →+* ℂ)) (β : ℚ ⊗[ℤ] (Fin n → 𝓞 E) →ₗ[ℚ] Fin n → E) (actOn rep ℝ J x) k =
          dv A n k.1.1 k.2 * Th (fun τ : Phi A => (τ : E →+* ℂ)) (β : ℚ ⊗[ℤ] (Fin n → 𝓞 E) →ₗ[ℚ] Fin n → E) x k := by
      rintro ⟨τ, i⟩
      rw [Th_act (fun τ : Phi A => (τ : E →+* ℂ)) (β : ℚ ⊗[ℤ] (Fin n → 𝓞 E) →ₗ[ℚ] Fin n → E) rep hβ2 J x τ i,
        hJτ, Matrix.mulVec_diagonal]
    have hz : ∃ k, Th (fun τ : Phi A => (τ : E →+* ℂ)) (β : ℚ ⊗[ℤ] (Fin n → 𝓞 E) →ₗ[ℚ] Fin n → E) x k ≠ 0 := by
      by_contra hc
      push_neg at hc
      apply hx
      apply cmType_trace_embedding_injective_of_linearEquiv hT A n β
      rw [map_zero]
      funext k
      exact hc k
    obtain ⟨k₀, hk₀⟩ := hz
    have tp := fun (τ : Phi A) (i : Fin n) (z : ℂ) => term_pos (τ.1 A.δ) (τ.1 (A.hd n i : E)) z
      (hS E A n τ.1 i).2.1 (A.δ_sign τ.1 τ.2) (hS E A n τ.1 i).1 (hd_ne hS A n τ.1 i)
    apply Finset.sum_pos'
    · rintro ⟨τ, i⟩ -
      rw [hterm]
      unfold dv
      exact mul_nonneg two_pos.le (tp τ i _).1
    · refine ⟨k₀, Finset.mem_univ _, ?_⟩
      obtain ⟨τ, i⟩ := k₀
      rw [hterm]
      unfold dv
      exact mul_pos two_pos ((tp τ i _).2 hk₀)
  · intro v
    obtain ⟨τ, hτv, -⟩ := (hT E A).2.2.1 v
    subst hτv
    have hω := (hT E A).2.2.2
    rcases InfinitePlace.embedding_mk_eq (τ : E →+* ℂ) with he | he
    · rw [he, if_pos τ.2, gram_diag, hJτ, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_smul]
      have hf : (-Complex.I • fun i => τ.1 (A.hd n i : E) * dv A n τ.1 i) =
          fun i => (((|(τ.1 (A.hd n i : E)).re| : ℝ)) : ℂ) := by
        funext i
        simp only [Pi.smul_apply, smul_eq_mul]
        exact (real_abs _ (hS E A n τ.1 i).1 (hd_ne hS A n τ.1 i)).1
      rw [hf]
      exact posDiag _ fun i => abs_pos.mpr (hd_ne hS A n τ.1 i)
    · have hc : ¬ (ComplexEmbedding.conjugate (τ : E →+* ℂ)) (A.ω : E) = A.τ₀ (A.ω : E) := by
        intro h
        rw [ComplexEmbedding.conjugate_coe_eq, τ.2] at h
        exact hω (Complex.conj_eq_iff_im.mp h)
      rw [he, if_neg hc, gram_diag, evM_conj, hJτ, Matrix.diagonal_map (map_zero _),
        Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_smul]
      have hf : (Complex.I • fun i => (ComplexEmbedding.conjugate (τ : E →+* ℂ)) (A.hd n i : E) *
          (starRingEnd ℂ) (dv A n τ.1 i)) = fun i => (((|(τ.1 (A.hd n i : E)).re| : ℝ)) : ℂ) := by
        funext i
        simp only [Pi.smul_apply, smul_eq_mul, ComplexEmbedding.conjugate_coe_eq]
        rw [Complex.conj_eq_iff_im.mpr (hS E A n τ.1 i).1]
        exact (real_abs _ (hS E A n τ.1 i).1 (hd_ne hS A n τ.1 i)).2
      rw [hf]
      exact posDiag _ fun i => abs_pos.mpr (hd_ne hS A n τ.1 i)

end UpperTheory.Gal.W2.Seed.Ori

/- English proof (translation)
Introduce `hT hS E _ _ _ A n hn hs p _ P rep hrep`. Conclude with `UpperTheory.Gal.W2.Seed.Ori.orient_core hT hS A n rep hrep`.
-/
theorem UpperTheory.Gal.W2.Seed.pOrient :
    TraceType → HdSign → Orient := by
  intro hT hS E _ _ _ A n hn hs p _ P rep hrep
  exact UpperTheory.Gal.W2.Seed.Ori.orient_core hT hS A n rep hrep
