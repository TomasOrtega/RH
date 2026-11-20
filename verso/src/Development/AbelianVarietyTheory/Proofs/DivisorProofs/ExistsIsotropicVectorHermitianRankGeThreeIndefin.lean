import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.HermitianHassePrincipleHolds

open scoped TensorProduct Matrix ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

namespace GlobalTheory.HermIso

/- English proof (translation)
Take `⟨hrs, A, hA⟩` from `h`. Set `e : Fin r ⊕ Fin s ≃ Fin n` to `finSumFinEquiv.trans (finCongr hrs)`. Set `D : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ` to `Matrix.diagonal (Sum.elim (fun _ => 1) (fun _ => -1))`. Establish `hD : Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1) = D`. Use extensionality with `i j`.

Apply the tactic sequence `rcases i with i | i <;> rcases j with j | j <;> simp [D, Matrix.one_apply, Matrix.diagonal_apply] <;> split_ifs <;> simp`. Set `A' : Matrix (Fin n) (Fin n) ℂ` to `A.submatrix id e.symm`. Establish `hA' : A'ᵀ * M * A'.map (starRingEnd ℂ) = D.submatrix e.symm e.symm`. Rewrite using `[← hD, ← hA]`. Use extensionality with `i j`.

Simplify using `[A', Matrix.mul_apply, Matrix.transpose_apply]`. Establish `hdet : A'.det ≠ 0`. Introduce `h0`. Establish `h1` using `congrArg Matrix.det hA'`. Rewrite `h1` using `[Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h0, Matrix.det_submatrix_equiv_self, Matrix.det_diagonal]`.

Simplify using `[Fintype.prod_sum_type] at h1`. Conclude with `pow_ne_zero s (by norm_num) h1.symm`. Rewrite using `[← GlobalTheory.Inertia.posIndex_congr M hdet, hA', GlobalTheory.Inertia.posIndex_submatrix_equiv, GlobalTheory.Inertia.posIndex_diagonal]`. Rewrite using `[Finset.card_filter, Fintype.sum_sum_type]`. Simplify using the standard rewrite rules.
-/
theorem posIndex_of_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) :
    GlobalTheory.Inertia.posIndex M = r := by
  obtain ⟨hrs, A, hA⟩ := h
  let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hrs)
  let D : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ :=
    Matrix.diagonal (Sum.elim (fun _ => 1) (fun _ => -1))
  have hD : Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1) = D := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> simp [D, Matrix.one_apply, Matrix.diagonal_apply] <;> split_ifs <;> simp
  let A' : Matrix (Fin n) (Fin n) ℂ := A.submatrix id e.symm
  have hA' : A'ᵀ * M * A'.map (starRingEnd ℂ) = D.submatrix e.symm e.symm := by
    rw [← hD, ← hA]
    ext i j
    simp [A', Matrix.mul_apply, Matrix.transpose_apply]
  have hdet : A'.det ≠ 0 := by
    intro h0
    have h1 := congrArg Matrix.det hA'
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h0, Matrix.det_submatrix_equiv_self,
      Matrix.det_diagonal] at h1
    simp [Fintype.prod_sum_type] at h1
    exact pow_ne_zero s (by norm_num) h1.symm
  rw [← GlobalTheory.Inertia.posIndex_congr M hdet, hA', GlobalTheory.Inertia.posIndex_submatrix_equiv,
    GlobalTheory.Inertia.posIndex_diagonal]
  rw [Finset.card_filter, Fintype.sum_sum_type]
  simp

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B hB n Y r s hn hr hs hY`. Take `⟨-, hEC, h2, hconj⟩` from `hB.cm`. Take `⟨w0⟩ : Nonempty (InfinitePlace E)` from `inferInstance`. Establish `invol : ∀ x, σ (σ x) = x` using `fun x => w0.embedding.injective (by rw [hconj, hconj, star_star])`. Set `σe : E ≃ₐ[F] E` to `AlgEquiv.ofAlgHom σ σ (AlgHom.ext invol) (AlgHom.ext invol)`.

Establish `hne : σe ≠ 1`. Introduce `h`. Establish `hid : ∀ x, σ x = x` using `fun x => by simpa [σe] using DFunLike.congr_fun h x`. Establish `hre : ComplexEmbedding.IsReal w0.embedding` using `ComplexEmbedding.isReal_iff.2 (RingHom.ext fun x => by`. Rewrite using `[ComplexEmbedding.conjugate_coe_eq]`.

Use `hconj w0.embedding x` as an intermediate fact. Rewrite `this` using `[hid]`. Conclude with `this.symm)`. Conclude with `InfinitePlace.not_isReal_iff_isComplex.2 (hEC.isComplex w0) (InfinitePlace.isReal_iff.2 hre)`. Use `haveI : Algebra.IsQuadraticExtension F E := { finrank_eq_two' := h2 }`.

Take `⟨hc, hF, θ, hθ0, hθ⟩` from `GlobalTheory.HermGlobal.involutive_and_fixed hne`. Take `⟨P, g, hP, hPg, hgf, hg0⟩` from `GlobalTheory.HermDiag.exists_congr_diagonal (c := (σ : E →+* E)) two_ne_zero (fun t => invol t) (G := Y.J) (fun a b => hY.herm b a)`. Establish `hgf' : ∀ i, σ (g i) = g i` using `fun i => hgf i`. Establish `key : ∀ y : Fin n → E, form σ Y.J (P *ᵥ y) (P *ᵥ y) = y ⬝ᵥ Matrix.diagonal g *ᵥ (fun i => σ (y i))`. Introduce `y`.

Establish `h1 : (fun i => σ ((P *ᵥ y) i)) = (P.map (σ : E →+* E)) *ᵥ (fun i => σ (y i))`. Use function extensionality and compare the values at `i`. Simplify using `[Matrix.mulVec, dotProduct, map_sum, map_mul]`. Rewrite using `[form, h1, ← hPg]`. Simplify using `only [Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.mulVec_mulVec]`.

Rewrite using `[← Matrix.vecMul_transpose, Matrix.vecMul_vecMul, Matrix.mul_assoc]`. Distinguish the cases in `hz : ∃ i, g i = 0`. Take `⟨i, hi⟩` from `hz`. Use `⟨P *ᵥ Pi.single i 1, fun h => ?_, ?_⟩` and prove the remaining obligations. Use `congrFun (Matrix.eq_zero_of_mulVec_eq_zero hP h) i` as an intermediate fact.

Simplify using `at this`. Rewrite using `[key]`. Simplify using `[Matrix.mulVec_diagonal, dotProduct, Pi.single_apply, hi]`. Use `push_neg at hz`. Take `⟨m, rfl⟩ : ∃ m, n = m + 1` from `⟨n - 1, by omega⟩`.

Establish `hsg : ∀ τ : E →+* ℂ, (∀ x, τ (σe x) = conj (τ x)) → ∃ i : Fin m, (0 < (τ (g i.succ)).re ↔ 0 < (τ (-g 0)).re)`. Introduce `τ _`. Establish `hre : ComplexEmbedding.IsReal (τ.comp (algebraMap F E))` using `ComplexEmbedding.isReal_iff.2 (RingHom.ext fun c => by`. Rewrite using `[ComplexEmbedding.conjugate_coe_eq]`. Use `hconj τ (algebraMap F E c)` as an intermediate fact.

Rewrite `this` using `[AlgHom.commutes]`. Conclude with `this.symm)`. Establish `hw : (InfinitePlace.mk (τ.comp (algebraMap F E))).embedding = τ.comp (algebraMap F E)` using `InfinitePlace.embedding_mk_eq_of_isReal hre`. Use `set w := InfinitePlace.mk (τ.comp (algebraMap F E))`. Use `set τ' := (B.emb w).1`.

Establish `hτ' : ∀ c : F, τ' (algebraMap F E c) = τ (algebraMap F E c)` using `fun c => by`. Use `congrArg (fun f => f c) ((B.emb w).2.trans hw)` as an intermediate fact. Simplify using `using this`. Establish `hgτ : ∀ k, τ' (g k) = τ (g k)` using `fun k => by`. Take `⟨c, hc'⟩` from `(hF (g k)).1 (hgf' k)`.

Rewrite using `[← hc', hτ']`. Establish `hcong : (Matrix.diagonal g).map τ' = (P.map τ')ᵀ * Y.J.map τ' * (P.map τ').map (starRingEnd ℂ)`. Rewrite using `[← hPg, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]`. Use `congr 1`. Use extensionality with `a b`.

Simplify using `[hconj]`. Establish `hPd : (P.map τ').det ≠ 0`. Rewrite using `[show (P.map τ').det = τ' P.det from (RingHom.map_det τ' P).symm]`. Conclude with `(map_ne_zero τ').2 hP`. Establish `hcount : (Finset.univ.filter fun k => 0 < (τ (g k)).re).card = r`.

Use `GlobalTheory.Inertia.posIndex_congr (Y.J.map τ') hPd` as an intermediate fact. Rewrite `this` using `[← hcong, posIndex_of_hasSig (hY.sig w), Matrix.diagonal_map (map_zero _), GlobalTheory.Inertia.posIndex_diagonal]`. Simplify `this` using `[hgτ]`. Establish `hrn : r < m + 1` using `by have := (hY.sig w).1; omega`. Establish `him : (τ (g 0)).im = 0`.

Establish `h` using `hconj τ (g 0)`. Rewrite `h` using `[hgf' 0]`. Conclude with `Complex.conj_eq_iff_im.1 h.symm`. Establish `hne0 : τ (g 0) ≠ 0` using `(map_ne_zero τ).2 (hz 0)`. Distinguish the cases in `hp : 0 < (τ (g 0)).re`.

Choose the witnesses or unpack the hypotheses as in `⟨k, hk⟩ : ∃ k, ¬ 0 < (τ (g k)).re := by`. Assume the negation of the conclusion as `hall`. Use `push_neg at hall`. Establish `h' : (Finset.univ.filter fun k => 0 < (τ (g k)).re) = Finset.univ` using `Finset.filter_true_of_mem fun k _ => hall k`. Rewrite `hcount` using `[h', Finset.card_univ, Fintype.card_fin]`.

Use linear arithmetic over natural numbers and integers. Take `⟨i, rfl⟩` from `Fin.exists_succ_eq.2 (show k ≠ 0 by rintro rfl; exact hk hp)`. Use `⟨i, iff_of_false hk ?_⟩` and prove the remaining obligations. Simplify using `only [map_neg, Complex.neg_re]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hneg : (τ (g 0)).re < 0`. Break down `lt_or_eq_of_le (not_lt.1 hp) with h | h` into its components or cases. Conclude with `h`. Conclude with `absurd (Complex.ext (by simpa using h) (by simpa using him)) hne0`. Choose the witnesses or unpack the hypotheses as in `⟨k, hk⟩ : ∃ k, 0 < (τ (g k)).re := by`.

Assume the negation of the conclusion as `hall`. Use `push_neg at hall`. Establish `h' : (Finset.univ.filter fun k => 0 < (τ (g k)).re) = ∅` using `Finset.filter_false_of_mem fun k _ => not_lt.2 (hall k)`. Rewrite `hcount` using `[h', Finset.card_empty]`. Use linear arithmetic over natural numbers and integers.

Take `⟨i, rfl⟩` from `Fin.exists_succ_eq.2 (show k ≠ 0 by rintro rfl; exact hp hk)`. Use `⟨i, iff_of_true hk ?_⟩` and prove the remaining obligations. Simplify using `only [map_neg, Complex.neg_re]`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨z, hz'⟩` from `GlobalTheory.HermGlobal.exists_represent hc hF hθ0 hθ (r := m) (by omega) (g := fun i => g i.succ) (fun i => hgf' _) (fun i => hz _) (b := -g 0) (by simp [σe, hgf']) (neg_ne_zero.2 (hz 0)) hsg`.

Use `⟨P *ᵥ Fin.cons 1 z, fun h => ?_, ?_⟩` and prove the remaining obligations. Use `congrFun (Matrix.eq_zero_of_mulVec_eq_zero hP h) 0` as an intermediate fact. Simplify using `at this`. Rewrite using `[key]`. Simplify using `only [Matrix.mulVec_diagonal, dotProduct, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, map_one, one_mul, mul_one] at hz' ⊢`.

Simplify using `only [σe, Function.comp_apply, RingHom.coe_coe, AlgEquiv.ofAlgHom_apply] at hz'`. Take the linear combination `hz'`.
-/
theorem exists_isotropic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E), B.IsGood σ → ∀ (n : ℕ) (Y : Spc F E n) (r s : ℕ), 3 ≤ n → 1 ≤ r → 1 ≤ s →
    Y.IsHerm σ B r s → ∃ x : Fin n → E, x ≠ 0 ∧ form σ Y.J x x = 0 := by
  intro F E _ _ _ _ _ σ B hB n Y r s hn hr hs hY
  obtain ⟨-, hEC, h2, hconj⟩ := hB.cm
  obtain ⟨w0⟩ : Nonempty (InfinitePlace E) := inferInstance
  have invol : ∀ x, σ (σ x) = x := fun x =>
    w0.embedding.injective (by rw [hconj, hconj, star_star])
  let σe : E ≃ₐ[F] E := AlgEquiv.ofAlgHom σ σ (AlgHom.ext invol) (AlgHom.ext invol)
  have hne : σe ≠ 1 := by
    intro h
    have hid : ∀ x, σ x = x := fun x => by simpa [σe] using DFunLike.congr_fun h x
    have hre : ComplexEmbedding.IsReal w0.embedding :=
      ComplexEmbedding.isReal_iff.2 (RingHom.ext fun x => by
        rw [ComplexEmbedding.conjugate_coe_eq]
        have := hconj w0.embedding x
        rw [hid] at this
        exact this.symm)
    exact InfinitePlace.not_isReal_iff_isComplex.2 (hEC.isComplex w0) (InfinitePlace.isReal_iff.2 hre)
  haveI : Algebra.IsQuadraticExtension F E := { finrank_eq_two' := h2 }
  obtain ⟨hc, hF, θ, hθ0, hθ⟩ := GlobalTheory.HermGlobal.involutive_and_fixed hne
  obtain ⟨P, g, hP, hPg, hgf, hg0⟩ := GlobalTheory.HermDiag.exists_congr_diagonal (c := (σ : E →+* E))
    two_ne_zero (fun t => invol t) (G := Y.J) (fun a b => hY.herm b a)
  have hgf' : ∀ i, σ (g i) = g i := fun i => hgf i
  have key : ∀ y : Fin n → E,
      form σ Y.J (P *ᵥ y) (P *ᵥ y) = y ⬝ᵥ Matrix.diagonal g *ᵥ (fun i => σ (y i)) := by
    intro y
    have h1 : (fun i => σ ((P *ᵥ y) i)) = (P.map (σ : E →+* E)) *ᵥ (fun i => σ (y i)) := by
      funext i
      simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
    rw [form, h1, ← hPg]
    simp only [Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.mulVec_mulVec]
    rw [← Matrix.vecMul_transpose, Matrix.vecMul_vecMul, Matrix.mul_assoc]
  by_cases hz : ∃ i, g i = 0
  · obtain ⟨i, hi⟩ := hz
    refine ⟨P *ᵥ Pi.single i 1, fun h => ?_, ?_⟩
    · have := congrFun (Matrix.eq_zero_of_mulVec_eq_zero hP h) i
      simp at this
    · rw [key]
      simp [Matrix.mulVec_diagonal, dotProduct, Pi.single_apply, hi]
  push_neg at hz
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hsg : ∀ τ : E →+* ℂ, (∀ x, τ (σe x) = conj (τ x)) →
      ∃ i : Fin m, (0 < (τ (g i.succ)).re ↔ 0 < (τ (-g 0)).re) := by
    intro τ _
    have hre : ComplexEmbedding.IsReal (τ.comp (algebraMap F E)) :=
      ComplexEmbedding.isReal_iff.2 (RingHom.ext fun c => by
        rw [ComplexEmbedding.conjugate_coe_eq]
        have := hconj τ (algebraMap F E c)
        rw [AlgHom.commutes] at this
        exact this.symm)
    have hw : (InfinitePlace.mk (τ.comp (algebraMap F E))).embedding = τ.comp (algebraMap F E) :=
      InfinitePlace.embedding_mk_eq_of_isReal hre
    set w := InfinitePlace.mk (τ.comp (algebraMap F E))
    set τ' := (B.emb w).1
    have hτ' : ∀ c : F, τ' (algebraMap F E c) = τ (algebraMap F E c) := fun c => by
      have := congrArg (fun f => f c) ((B.emb w).2.trans hw)
      simpa using this
    have hgτ : ∀ k, τ' (g k) = τ (g k) := fun k => by
      obtain ⟨c, hc'⟩ := (hF (g k)).1 (hgf' k)
      rw [← hc', hτ']
    have hcong : (Matrix.diagonal g).map τ' =
        (P.map τ')ᵀ * Y.J.map τ' * (P.map τ').map (starRingEnd ℂ) := by
      rw [← hPg, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
      congr 1
      ext a b
      simp [hconj]
    have hPd : (P.map τ').det ≠ 0 := by
      rw [show (P.map τ').det = τ' P.det from (RingHom.map_det τ' P).symm]
      exact (map_ne_zero τ').2 hP
    have hcount : (Finset.univ.filter fun k => 0 < (τ (g k)).re).card = r := by
      have := GlobalTheory.Inertia.posIndex_congr (Y.J.map τ') hPd
      rw [← hcong, posIndex_of_hasSig (hY.sig w), Matrix.diagonal_map (map_zero _),
        GlobalTheory.Inertia.posIndex_diagonal] at this
      simpa [hgτ] using this
    have hrn : r < m + 1 := by have := (hY.sig w).1; omega
    have him : (τ (g 0)).im = 0 := by
      have h := hconj τ (g 0)
      rw [hgf' 0] at h
      exact Complex.conj_eq_iff_im.1 h.symm
    have hne0 : τ (g 0) ≠ 0 := (map_ne_zero τ).2 (hz 0)
    by_cases hp : 0 < (τ (g 0)).re
    · obtain ⟨k, hk⟩ : ∃ k, ¬ 0 < (τ (g k)).re := by
        by_contra hall
        push_neg at hall
        have h' : (Finset.univ.filter fun k => 0 < (τ (g k)).re) = Finset.univ :=
          Finset.filter_true_of_mem fun k _ => hall k
        rw [h', Finset.card_univ, Fintype.card_fin] at hcount
        omega
      obtain ⟨i, rfl⟩ := Fin.exists_succ_eq.2 (show k ≠ 0 by rintro rfl; exact hk hp)
      refine ⟨i, iff_of_false hk ?_⟩
      simp only [map_neg, Complex.neg_re]
      linarith
    · have hneg : (τ (g 0)).re < 0 := by
        rcases lt_or_eq_of_le (not_lt.1 hp) with h | h
        · exact h
        · exact absurd (Complex.ext (by simpa using h) (by simpa using him)) hne0
      obtain ⟨k, hk⟩ : ∃ k, 0 < (τ (g k)).re := by
        by_contra hall
        push_neg at hall
        have h' : (Finset.univ.filter fun k => 0 < (τ (g k)).re) = ∅ :=
          Finset.filter_false_of_mem fun k _ => not_lt.2 (hall k)
        rw [h', Finset.card_empty] at hcount
        omega
      obtain ⟨i, rfl⟩ := Fin.exists_succ_eq.2 (show k ≠ 0 by rintro rfl; exact hp hk)
      refine ⟨i, iff_of_true hk ?_⟩
      simp only [map_neg, Complex.neg_re]
      linarith
  obtain ⟨z, hz'⟩ := GlobalTheory.HermGlobal.exists_represent hc hF hθ0 hθ (r := m) (by omega)
    (g := fun i => g i.succ) (fun i => hgf' _) (fun i => hz _) (b := -g 0)
    (by simp [σe, hgf']) (neg_ne_zero.2 (hz 0)) hsg
  refine ⟨P *ᵥ Fin.cons 1 z, fun h => ?_, ?_⟩
  · have := congrFun (Matrix.eq_zero_of_mulVec_eq_zero hP h) 0
    simp at this
  · rw [key]
    simp only [Matrix.mulVec_diagonal, dotProduct, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
      map_one, one_mul, mul_one] at hz' ⊢
    simp only [σe, Function.comp_apply, RingHom.coe_coe, AlgEquiv.ofAlgHom_apply] at hz'
    linear_combination hz'

end GlobalTheory.HermIso
