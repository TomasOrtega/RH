import Mathlib
import ReciprocityTheory.SemistableReduction.SemiAll
import ReciprocityTheory.SemistableReduction.SemiDegZ
import ReciprocityTheory.SemistableReduction.LatTest
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmApproximationTransference
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsThickPointHyperbolic
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFinsetTypesOfBoundedBases

open NumberField Matrix Module Submodule ReciprocityTheory.MultiplicativeHeights ComplexConjugate
open ReciprocityTheory.ChartRestriction.G.FD (herm cc fdeg dE)
open scoped ComplexOrder MatrixOrder

namespace GlobalTheory

namespace ClassCount

section Semistable

variable {K : Type} [Field K] [NumberField K] {r : ℕ}

/- English proof (translation)
Establish `h0 : embVec σ v ≠ 0` using `fun h => hv (funext fun a => σ.injective (by`. Simplify `congrFun h a))` using `[embVec]`. Conclude with `(Complex.pos_iff.1 (hH.dotProduct_mulVec_pos h0)).1`.
-/
theorem hq_embVec_pos {H : Matrix (Fin r) (Fin r) ℂ} (hH : H.PosDef) (σ : K →+* ℂ)
    {v : Fin r → K} (hv : v ≠ 0) : 0 < hq H (embVec σ v) := by
  have h0 : embVec σ v ≠ 0 := fun h => hv (funext fun a => σ.injective (by
    simpa [embVec] using congrFun h a))
  exact (Complex.pos_iff.1 (hH.dotProduct_mulVec_pos h0)).1

/- English proof (translation)
Establish `h` using `hss.2 (span (𝓞 K) (Set.range fun _ : Fin 1 => v)) (span_le.2 (by rintro _ ⟨_, rfl⟩; exact hv)) 1 (fun _ => v) ⟨fun i => subset_span ⟨i, rfl⟩, linearIndependent_unique_iff.2 hv0, fun x hx => span_le_restrictScalars (𝓞 K) K _ hx⟩`. Simplify using `only [latDeg, AddSubgroup.relIndex_self, Nat.cast_one, Real.log_one, det_unique, gramC, of_apply] at h`. Unfold `hq`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem sum_log_hq_nonneg {H : (K →+* ℂ) → Matrix (Fin r) (Fin r) ℂ}
    {L : Submodule (𝓞 K) (Fin r → K)} (hss : IsSemistableZero H L) {v : Fin r → K} (hv : v ∈ L)
    (hv0 : v ≠ 0) : 0 ≤ ∑ σ : K →+* ℂ, Real.log (hq (H σ) (embVec σ v)) := by
  have h := hss.2 (span (𝓞 K) (Set.range fun _ : Fin 1 => v))
    (span_le.2 (by rintro _ ⟨_, rfl⟩; exact hv)) 1 (fun _ => v)
    ⟨fun i => subset_span ⟨i, rfl⟩, linearIndependent_unique_iff.2 hv0,
      fun x hx => span_le_restrictScalars (𝓞 K) K _ hx⟩
  simp only [latDeg, AddSubgroup.relIndex_self, Nat.cast_one, Real.log_one, det_unique, gramC,
    of_apply] at h
  unfold hq
  linarith

/- English proof (translation)
Establish `h1` using `sum_log_hq_nonneg hss hv hv0`. Establish `h2 : ∑ σ : K →+* ℂ, Real.log (hq (H σ) (embVec σ v)) ≤ ∑ σ : K →+* ℂ, (hq (H σ) (embVec σ v) - 1)` using `Finset.sum_le_sum fun σ _ => Real.log_le_sub_one_of_pos (hq_embVec_pos (hH σ) σ hv0)`. Rewrite `h2` using `[Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Embeddings.card K ℂ, nsmul_eq_mul]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem finrank_le_sum_hq {H : (K →+* ℂ) → Matrix (Fin r) (Fin r) ℂ} (hH : ∀ σ, (H σ).PosDef)
    {L : Submodule (𝓞 K) (Fin r → K)} (hss : IsSemistableZero H L) {v : Fin r → K} (hv : v ∈ L)
    (hv0 : v ≠ 0) : (finrank ℚ K : ℝ) ≤ ∑ σ : K →+* ℂ, hq (H σ) (embVec σ v) := by
  have h1 := sum_log_hq_nonneg hss hv hv0
  have h2 : ∑ σ : K →+* ℂ, Real.log (hq (H σ) (embVec σ v)) ≤
      ∑ σ : K →+* ℂ, (hq (H σ) (embVec σ v) - 1) :=
    Finset.sum_le_sum fun σ _ => Real.log_le_sub_one_of_pos (hq_embVec_pos (hH σ) σ hv0)
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Embeddings.card K ℂ,
    nsmul_eq_mul] at h2
  linarith

/- English proof (translation)
Rewrite using `[hq, ← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec, normSq, dotProduct, Complex.re_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Pi.star_apply, Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]`.
-/
theorem normSq_mulVec (C : Matrix (Fin r) (Fin r) ℂ) (u : Fin r → ℂ) :
    normSq (C *ᵥ u) = hq (Cᴴ * C) u := by
  rw [hq, ← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec, normSq, dotProduct, Complex.re_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Pi.star_apply, Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]

/- English proof (translation)
Take `⟨C, hC⟩` from `CStarAlgebra.nonneg_iff_eq_star_mul_self.1 hH.posSemidef.nonneg`. Rewrite `hC` using `[star_eq_conjTranspose]`. Establish `h1 : Cᴴ * (C * (G⁻¹ * H)) = G`. Rewrite using `[← Matrix.mul_assoc, ← hC, ← Matrix.mul_assoc, hmaj]`. Use `⟨C, C * (G⁻¹ * H), fun u => by rw [normSq_mulVec, ← hC], fun u => ?_, fun u w => ?_⟩` and prove the remaining obligations.

Rewrite using `[normSq_mulVec, conjTranspose_mul, Matrix.mul_assoc, h1, conjTranspose_mul, hG.inv.eq, hH.isHermitian.eq, Matrix.mul_assoc, nonsing_inv_mul _ hdet.isUnit, Matrix.mul_one]`. Rewrite using `[star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, h1]`.
-/
theorem exists_coord {H G : Matrix (Fin r) (Fin r) ℂ} (hH : H.PosDef) (hG : G.IsHermitian)
    (hdet : G.det ≠ 0) (hmaj : H * G⁻¹ * H = G) :
    ∃ C D : Matrix (Fin r) (Fin r) ℂ, (∀ u, normSq (C *ᵥ u) = hq H u) ∧
      (∀ u, normSq (D *ᵥ u) = hq H u) ∧
      ∀ u w, star (C *ᵥ u) ⬝ᵥ (D *ᵥ w) = star u ⬝ᵥ (G *ᵥ w) := by
  obtain ⟨C, hC⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.1 hH.posSemidef.nonneg
  rw [star_eq_conjTranspose] at hC
  have h1 : Cᴴ * (C * (G⁻¹ * H)) = G := by
    rw [← Matrix.mul_assoc, ← hC, ← Matrix.mul_assoc, hmaj]
  refine ⟨C, C * (G⁻¹ * H), fun u => by rw [normSq_mulVec, ← hC], fun u => ?_, fun u w => ?_⟩
  · rw [normSq_mulVec, conjTranspose_mul, Matrix.mul_assoc, h1, conjTranspose_mul, hG.inv.eq,
      hH.isHermitian.eq, Matrix.mul_assoc, nonsing_inv_mul _ hdet.isUnit, Matrix.mul_one]
  · rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, h1]

/- English proof (translation)
Simplify using `[HermForm.h, dotProduct, mulVec, embVec, S.c_emb, Finset.mul_sum, mul_assoc]`.
-/
theorem emb_h (S : HermForm K r) (σ : K →+* ℂ) (x y : Fin r → K) :
    σ (S.h x y) = star (embVec σ x) ⬝ᵥ (S.G.map σ *ᵥ embVec σ y) := by
  simp [HermForm.h, dotProduct, mulVec, embVec, S.c_emb, Finset.mul_sum, mul_assoc]

/- English proof (translation)
Use extensionality with `a b`. Simplify using `[conjTranspose_apply, ← S.c_emb, S.G_herm]`.
-/
theorem isHermitian_map (S : HermForm K r) (σ : K →+* ℂ) : (S.G.map σ).IsHermitian := by
  ext a b
  simp [conjTranspose_apply, ← S.c_emb, S.G_herm]

/- English proof (translation)
Rewrite using `[dotProduct, normSq, normSq, ← Finset.sum_add_distrib, Finset.sum_div]`. Use `(norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)` and prove the remaining obligations. Rewrite using `[norm_mul, Pi.star_apply, norm_star]`. Use polynomial arithmetic with `[sq_nonneg (‖u k‖ - ‖w k‖)]`.
-/
theorem norm_dotProduct_le (u w : Fin r → ℂ) : ‖star u ⬝ᵥ w‖ ≤ (normSq u + normSq w) / 2 := by
  rw [dotProduct, normSq, normSq, ← Finset.sum_add_distrib, Finset.sum_div]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [norm_mul, Pi.star_apply, norm_star]
  nlinarith [sq_nonneg (‖u k‖ - ‖w k‖)]

/- English proof (translation)
Take `⟨C, D, hC, hD, hCD⟩` from `exists_coord (M.posDef σ) (isHermitian_map S σ) (by rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact (map_ne_zero σ).2 hdet) (M.major σ)`. Rewrite using `[emb_h, ← hCD, ← hC, ← hD]`. Conclude with `norm_dotProduct_le _ _`.
-/
theorem norm_h_le {S : HermForm K r} (hdet : S.G.det ≠ 0) (M : Majorant S) (σ : K →+* ℂ)
    (x y : Fin r → K) :
    ‖σ (S.h x y)‖ ≤ (hq (M.H σ) (embVec σ x) + hq (M.H σ) (embVec σ y)) / 2 := by
  obtain ⟨C, D, hC, hD, hCD⟩ := exists_coord (M.posDef σ) (isHermitian_map S σ)
    (by rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact (map_ne_zero σ).2 hdet)
    (M.major σ)
  rw [emb_h, ← hCD, ← hC, ← hD]
  exact norm_dotProduct_le _ _

/- English proof (translation)
Establish `h : M.H (ComplexEmbedding.conjugate σ) = _` using `M.conj_compat σ`. Rewrite using `[h, hq, hq, ← Complex.conj_re]`. Use `congr 1`. Simplify using `[dotProduct, mulVec, embVec]`.
-/
theorem hq_conjugate {S : HermForm K r} (M : Majorant S) (σ : K →+* ℂ) (x : Fin r → K) :
    hq (M.H (ComplexEmbedding.conjugate σ)) (embVec (ComplexEmbedding.conjugate σ) x) =
      hq (M.H σ) (embVec σ x) := by
  have h : M.H (ComplexEmbedding.conjugate σ) = _ := M.conj_compat σ
  rw [h, hq, hq, ← Complex.conj_re]
  congr 1
  simp [dotProduct, mulVec, embVec]

end Semistable

section Short

variable {K : Type} [Field K] [NumberField K] [IsCMField K] {r : ℕ}

omit [NumberField K] [IsCMField K] in
/- English proof (translation)
Introduce `w w' h` and use `by rw [← w.mk_embedding, ← w'.mk_embedding] exact congrArg _ h`.
-/
theorem embedding_injective :
    Function.Injective (fun w : InfinitePlace K => w.embedding) := fun w w' h => by
  rw [← w.mk_embedding, ← w'.mk_embedding]
  exact congrArg _ h

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨w, rfl⟩ ⟨w', hw'⟩`. Establish `h1 : w' = w`. Rewrite using `[← w'.mk_embedding, hw', InfinitePlace.mk_conjugate_eq, w.mk_embedding]`. Substitute `h1` using the available equality.

Conclude with `IsTotallyComplex.complexEmbedding_not_isReal w'.embedding (ComplexEmbedding.isReal_iff.2 hw'.symm)`. Introduce `h`. Break down `InfinitePlace.embedding_mk_eq τ with h1 | h1` into its components or cases. Conclude with `⟨_, h1⟩`. Conclude with `absurd ⟨_, h1⟩ h`.
-/
theorem embedding_cmType (τ : K →+* ℂ) : (∃ w : InfinitePlace K, w.embedding = τ) ↔
    ¬ ∃ w : InfinitePlace K, w.embedding = ComplexEmbedding.conjugate τ := by
  constructor
  · rintro ⟨w, rfl⟩ ⟨w', hw'⟩
    have h1 : w' = w := by
      rw [← w'.mk_embedding, hw', InfinitePlace.mk_conjugate_eq, w.mk_embedding]
    subst h1
    exact IsTotallyComplex.complexEmbedding_not_isReal w'.embedding
      (ComplexEmbedding.isReal_iff.2 hw'.symm)
  · intro h
    rcases InfinitePlace.embedding_mk_eq τ with h1 | h1
    · exact ⟨_, h1⟩
    · exact absurd ⟨_, h1⟩ h

/- English proof (translation)
Establish `h1` using `CMTransference.finrank_eq_two_mul (K := K) embedding_injective embedding_cmType`. Establish `h2` using `BoundedBasis.finrank_eq_two_mul_fdeg (E := K)`. Use linear arithmetic over natural numbers and integers.
-/
theorem card_infinitePlace : Fintype.card (InfinitePlace K) = fdeg K := by
  have h1 := CMTransference.finrank_eq_two_mul (K := K) embedding_injective embedding_cmType
  have h2 := BoundedBasis.finrank_eq_two_mul_fdeg (E := K)
  omega

/- English proof (translation)
Rewrite using `[← (CMTransference.sumElim_bijective (K := K) embedding_injective embedding_cmType).sum_comp (fun σ => hq (M.H σ) (embVec σ x)), Fintype.sum_sum_type, two_mul]`. Simplify using `only [Sum.elim_inl, Sum.elim_inr, hq_conjugate]`.
-/
theorem sum_hq_eq {S : HermForm K r} (M : Majorant S) (x : Fin r → K) :
    ∑ σ : K →+* ℂ, hq (M.H σ) (embVec σ x) =
      2 * ∑ w : InfinitePlace K, hq (M.H w.embedding) (embVec w.embedding x) := by
  rw [← (CMTransference.sumElim_bijective (K := K) embedding_injective embedding_cmType).sum_comp
    (fun σ => hq (M.H σ) (embVec σ x)), Fintype.sum_sum_type, two_mul]
  simp only [Sum.elim_inl, Sum.elim_inr, hq_conjugate]

/- English proof (translation)
Rewrite using `[sum_hq_eq]`. Establish `h : hq (M.H σ) (embVec σ x) = hq (M.H (InfinitePlace.mk σ).embedding) (embVec (InfinitePlace.mk σ).embedding x)`. Break down `InfinitePlace.embedding_mk_eq σ with h1 | h1` into its components or cases. Rewrite using `[h1]`. Rewrite using `[h1, hq_conjugate]`.

Rewrite using `[h]`. Use `mul_le_mul_of_nonneg_left (Finset.single_le_sum (f := fun w : InfinitePlace K => hq (M.H w.embedding) (embVec w.embedding x)) (fun w _ => ?_) (Finset.mem_univ _)) zero_le_two` and prove the remaining obligations. Conclude with `(Complex.nonneg_iff.1 ((M.posDef _).posSemidef.dotProduct_mulVec_nonneg _)).1`.
-/
theorem two_mul_hq_le {S : HermForm K r} (M : Majorant S) (σ : K →+* ℂ) (x : Fin r → K) :
    2 * hq (M.H σ) (embVec σ x) ≤ ∑ τ : K →+* ℂ, hq (M.H τ) (embVec τ x) := by
  rw [sum_hq_eq]
  have h : hq (M.H σ) (embVec σ x) = hq (M.H (InfinitePlace.mk σ).embedding)
      (embVec (InfinitePlace.mk σ).embedding x) := by
    rcases InfinitePlace.embedding_mk_eq σ with h1 | h1
    · rw [h1]
    · rw [h1, hq_conjugate]
  rw [h]
  refine mul_le_mul_of_nonneg_left (Finset.single_le_sum
    (f := fun w : InfinitePlace K => hq (M.H w.embedding) (embVec w.embedding x))
    (fun w _ => ?_) (Finset.mem_univ _)) zero_le_two
  exact (Complex.nonneg_iff.1 ((M.posDef _).posSemidef.dotProduct_mulVec_nonneg _)).1

open CMTransference in

/- English proof (translation)
Establish `hdet` using `SemiPt.detG_ne_zero S L hL hsd`. Set `σ : InfinitePlace K → K →+* ℂ` to `fun w => w.embedding`. Use `choose C D hC hD hCD using fun w => exists_coord (M.posDef (σ w)) (isHermitian_map S (σ w)) (by rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact (map_ne_zero _).2 hdet) (M.major (σ w))`. Establish `hQC : ∀ x, majSq σ C x = (∑ τ : K →+* ℂ, hq (M.H τ) (embVec τ x)) / 2` using `fun x => by`. Rewrite using `[sum_hq_eq, majSq]`.

Simplify using `only [hC, σ]`. Expand and normalize the polynomial expressions, which then agree. Establish `hQD : ∀ x, majSq σ D x = (∑ τ : K →+* ℂ, hq (M.H τ) (embVec τ x)) / 2` using `fun x => by`. Rewrite using `[sum_hq_eq, majSq]`. Simplify using `only [hD, σ]`.

Expand and normalize the polynomial expressions, which then agree. Take `⟨b, hb⟩` from `ShortVectors.exists_basis L hL.1 hL.2`. Establish `hV : finrank ℝ (EuclideanSpace ℂ (InfinitePlace K × Fin r)) = 2 * fdeg K * r`. Rewrite using `[← Module.finrank_mul_finrank ℝ ℂ, Complex.finrank_real_complex, finrank_euclideanSpace, Fintype.card_prod, Fintype.card_fin, card_infinitePlace, mul_assoc]`. Set `θ` to `((stdOrthonormalBasis ℝ (EuclideanSpace ℂ (InfinitePlace K × Fin r))).reindex (finCongr hV)).repr`.

Establish `hsymm : (traceForm S).IsSymm` using `⟨fun x y => by`. Establish `h : ∀ x y, (traceForm S x y : ℝ) = 2 * ∑ w, (σ w (S.h x y)).re` using `fun x y => trace_eq_two_mul_sum_re embedding_injective embedding_cmType _`. Establish `: (traceForm S x y : ℝ) = traceForm S y x`. Rewrite using `[h, h, wa_symm S x y]`. Simplify using `only [S.c_emb, Complex.conj_re]`.

Conclude with `this⟩` after adjusting the coercions. Establish `hn : (traceForm S).Nondegenerate`. Use `LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft fun z hz => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hz0`. Use `SemiPt.no_line L hL.1 ((discr K : K) • z) (smul_ne_zero (by exact_mod_cast discr_ne_zero K) hz0) fun t => ?_` and prove the remaining obligations.

Rewrite using `[smul_comm]`. Use `discr_smul_mem hsd fun y _ => ⟨0, ?_⟩` and prove the remaining obligations. Rewrite using `[traceForm_apply, h_smul_left, ← h_smul_right, ← traceForm_apply, hz, Int.cast_zero]`. Establish `hd0 : (discr K : ℝ) ≠ 0` using `by exact_mod_cast discr_ne_zero K`. Establish `hd : 0 < dE K` using `abs_pos.mpr hd0`.

Establish `hd2 : dE K ^ 2 = (discr K : ℝ) ^ 2` using `sq_abs _`. Establish `hs` using `Real.sqrt_pos.mpr hε`. Set `φ` to `θ.toLinearEquiv.toLinearMap.toAddMonoidHom.comp (emb σ C)`. Set `ψ` to `θ.toLinearEquiv.toLinearMap.toAddMonoidHom.comp ((2 : ℕ) • emb σ D)`. Establish `hφ : ∀ x, φ x = θ (emb σ C x)` using `fun _ => rfl`.

Establish `hψ : ∀ x, ψ x = θ ((2 : ℝ) • emb σ D x)` using `fun x => by`. Rewrite using `[two_smul, ← two_nsmul]`. Both sides reduce to the same expression. Take `⟨v, hv, hli, hle⟩` from `ThickPoint.transference_pair b (traceForm S) hsymm hn φ ψ (fun x y => by`. Rewrite using `[hφ, hψ, θ.inner_map_map, real_inner_smul_right, traceForm_apply, trace_eq_two_mul_sum_re embedding_injective embedding_cmType, PiLp.inner_apply, Fintype.sum_prod_type]`.

Use `congr 1`. Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations. Rewrite using `[emb_h, ← hCD w, dotProduct, Complex.re_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Complex.inner, mul_comm]`.

Use the proof step `rfl)`. Use the proof step `(2 * √ε / dE K) (by positivity) (by`. Introduce `u hu hk`. Establish `hmem : ((discr K : ℤ) : K) • u ∈ L`. Use `discr_smul_mem hsd fun y hy => ?_` and prove the remaining obligations.

Take `⟨c, rfl⟩` from `(mem_span_range_iff_exists_fun ℤ).1 ((hb y).2 hy)`. Use `choose k hk using hk`. Use `⟨∑ j, c j * k j, ?_⟩` and prove the remaining obligations. Rewrite using `[map_sum]`. Simplify using `only [map_zsmul, hk]`.

Simplify using the standard rewrite rules. Establish `h` using `hmin _ hmem (smul_ne_zero (by exact_mod_cast discr_ne_zero K) hu)`. Rewrite `h` using `[← hQD, majSq_intCast_smul]`. Rewrite using `[hψ, θ.norm_map, norm_smul, mul_pow, norm_emb_sq, div_pow, mul_pow, Real.sq_sqrt hε.le, hd2, div_le_iff₀ (by positivity), Real.norm_ofNat]`. Use the proof step `linarith)`.

Take `⟨s, hs1, hs2, -⟩` from `euclidean_basis_exists K (Fin r → K) _ v hli (by`. Simplify using `[ShortVectors.finrank_eq])`. Establish `hsr : s.card = r` using `by simpa using hs1`. Set `e : Fin r ≃ s` to `(s.equivFinOfCardEq hsr).symm`. Use `⟨fun i => v (e i), fun i => (hb _).1 (hv _), hs2.comp e e.injective, fun i => ?_⟩` and prove the remaining obligations.

Establish `h` using `hle (e i)`. Rewrite `h` using `[hφ, θ.norm_map, norm_emb_sq, hQC]`. Use `h.trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[div_pow, div_pow, mul_pow 2 (√ε), Real.sq_sqrt hε.le]`. Use `push_cast`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_short_basis {S : HermForm K r} {L : Submodule (𝓞 K) (Fin r → K)}
    (hL : IsLattice L) (hsd : IsSelfDual S L) (M : Majorant S) {ε : ℝ} (hε : 0 < ε)
    (hmin : ∀ v ∈ L, v ≠ 0 → ε ≤ (∑ σ : K →+* ℂ, hq (M.H σ) (embVec σ v)) / 2) :
    ∃ v : Fin r → Fin r → K, (∀ i, v i ∈ L) ∧ LinearIndependent K v ∧
      ∀ i, (∑ σ : K →+* ℂ, hq (M.H σ) (embVec σ (v i))) / 2 ≤
        (2 * fdeg K * r : ℝ) ^ 4 * dE K ^ 2 / (4 * ε) := by
  have hdet := SemiPt.detG_ne_zero S L hL hsd
  let σ : InfinitePlace K → K →+* ℂ := fun w => w.embedding
  choose C D hC hD hCD using fun w => exists_coord (M.posDef (σ w)) (isHermitian_map S (σ w))
    (by rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact (map_ne_zero _).2 hdet)
    (M.major (σ w))
  have hQC : ∀ x, majSq σ C x = (∑ τ : K →+* ℂ, hq (M.H τ) (embVec τ x)) / 2 := fun x => by
    rw [sum_hq_eq, majSq]; simp only [hC, σ]; ring
  have hQD : ∀ x, majSq σ D x = (∑ τ : K →+* ℂ, hq (M.H τ) (embVec τ x)) / 2 := fun x => by
    rw [sum_hq_eq, majSq]; simp only [hD, σ]; ring
  obtain ⟨b, hb⟩ := ShortVectors.exists_basis L hL.1 hL.2
  have hV : finrank ℝ (EuclideanSpace ℂ (InfinitePlace K × Fin r)) = 2 * fdeg K * r := by
    rw [← Module.finrank_mul_finrank ℝ ℂ, Complex.finrank_real_complex, finrank_euclideanSpace,
      Fintype.card_prod, Fintype.card_fin, card_infinitePlace, mul_assoc]
  let θ := ((stdOrthonormalBasis ℝ (EuclideanSpace ℂ (InfinitePlace K × Fin r))).reindex
    (finCongr hV)).repr
  have hsymm : (traceForm S).IsSymm := ⟨fun x y => by
    have h : ∀ x y, (traceForm S x y : ℝ) = 2 * ∑ w, (σ w (S.h x y)).re := fun x y =>
      trace_eq_two_mul_sum_re embedding_injective embedding_cmType _
    have : (traceForm S x y : ℝ) = traceForm S y x := by
      rw [h, h, wa_symm S x y]
      simp only [S.c_emb, Complex.conj_re]
    exact_mod_cast this⟩
  have hn : (traceForm S).Nondegenerate := by
    refine LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft fun z hz => ?_
    by_contra hz0
    refine SemiPt.no_line L hL.1 ((discr K : K) • z)
      (smul_ne_zero (by exact_mod_cast discr_ne_zero K) hz0) fun t => ?_
    rw [smul_comm]
    refine discr_smul_mem hsd fun y _ => ⟨0, ?_⟩
    rw [traceForm_apply, h_smul_left, ← h_smul_right, ← traceForm_apply, hz, Int.cast_zero]
  have hd0 : (discr K : ℝ) ≠ 0 := by exact_mod_cast discr_ne_zero K
  have hd : 0 < dE K := abs_pos.mpr hd0
  have hd2 : dE K ^ 2 = (discr K : ℝ) ^ 2 := sq_abs _
  have hs := Real.sqrt_pos.mpr hε
  let φ := θ.toLinearEquiv.toLinearMap.toAddMonoidHom.comp (emb σ C)
  let ψ := θ.toLinearEquiv.toLinearMap.toAddMonoidHom.comp ((2 : ℕ) • emb σ D)
  have hφ : ∀ x, φ x = θ (emb σ C x) := fun _ => rfl
  have hψ : ∀ x, ψ x = θ ((2 : ℝ) • emb σ D x) := fun x => by
    rw [two_smul, ← two_nsmul]; rfl
  obtain ⟨v, hv, hli, hle⟩ := ThickPoint.transference_pair b (traceForm S) hsymm hn φ ψ
    (fun x y => by
      rw [hφ, hψ, θ.inner_map_map, real_inner_smul_right, traceForm_apply,
        trace_eq_two_mul_sum_re embedding_injective embedding_cmType, PiLp.inner_apply,
        Fintype.sum_prod_type]
      congr 1
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [emb_h, ← hCD w, dotProduct, Complex.re_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Complex.inner, mul_comm]
      rfl)
    (2 * √ε / dE K) (by positivity) (by
      intro u hu hk
      have hmem : ((discr K : ℤ) : K) • u ∈ L := by
        refine discr_smul_mem hsd fun y hy => ?_
        obtain ⟨c, rfl⟩ := (mem_span_range_iff_exists_fun ℤ).1 ((hb y).2 hy)
        choose k hk using hk
        refine ⟨∑ j, c j * k j, ?_⟩
        rw [map_sum]
        simp only [map_zsmul, hk]
        simp
      have h := hmin _ hmem (smul_ne_zero (by exact_mod_cast discr_ne_zero K) hu)
      rw [← hQD, majSq_intCast_smul] at h
      rw [hψ, θ.norm_map, norm_smul, mul_pow, norm_emb_sq, div_pow, mul_pow, Real.sq_sqrt hε.le,
        hd2, div_le_iff₀ (by positivity), Real.norm_ofNat]
      linarith)
  obtain ⟨s, hs1, hs2, -⟩ := euclidean_basis_exists K (Fin r → K) _ v hli (by
    simp [ShortVectors.finrank_eq])
  have hsr : s.card = r := by simpa using hs1
  let e : Fin r ≃ s := (s.equivFinOfCardEq hsr).symm
  refine ⟨fun i => v (e i), fun i => (hb _).1 (hv _), hs2.comp e e.injective, fun i => ?_⟩
  have h := hle (e i)
  rw [hφ, θ.norm_map, norm_emb_sq, hQC] at h
  refine h.trans (le_of_eq ?_)
  rw [div_pow, div_pow, mul_pow 2 (√ε), Real.sq_sqrt hε.le]
  push_cast
  field_simp
  ring

/- English proof (translation)
Establish `h1` using `BoundedBasis.finrank_eq_two_mul_fdeg (E := K)`. Establish `h2` using `finrank_pos (R := ℚ) (M := K)`. Use linear arithmetic over natural numbers and integers.
-/
theorem fdeg_pos : 0 < fdeg K := by
  have h1 := BoundedBasis.finrank_eq_two_mul_fdeg (E := K)
  have h2 := finrank_pos (R := ℚ) (M := K)
  omega

/- English proof (translation)
Take `⟨M, hM⟩` from `Closed.semiPoint K r S L hL hsd`. Take `⟨v, hv, hli, hle⟩` from `exists_short_basis hL hsd M (ε := fdeg K) (by exact_mod_cast fdeg_pos) fun v hv hv0 => by`. Establish `h` using `finrank_le_sum_hq M.posDef hM hv hv0`. Rewrite `h` using `[BoundedBasis.finrank_eq_two_mul_fdeg]`. Move the coercions through the operations in `at h`.

Combine the linear equalities and inequalities to obtain the conclusion. Use `⟨v, hv, hli, fun σ i k => ?_⟩` and prove the remaining obligations. Establish `h1` using `norm_h_le (SemiPt.detG_ne_zero S L hL hsd) M σ (v i) (v k)`. Combine the linear relations using `[two_mul_hq_le M σ (v i), two_mul_hq_le M σ (v k), hle i, hle k]`.
-/
theorem exists_bounded_basis {S : HermForm K r} {L : Submodule (𝓞 K) (Fin r → K)}
    (hL : IsLattice L) (hsd : IsSelfDual S L) :
    ∃ v : Fin r → Fin r → K, (∀ i, v i ∈ L) ∧ LinearIndependent K v ∧
      ∀ (σ : K →+* ℂ) (i k : Fin r), ‖σ (S.h (v i) (v k))‖ ≤
        (2 * fdeg K * r : ℝ) ^ 4 * dE K ^ 2 / (4 * fdeg K) := by
  obtain ⟨M, hM⟩ := Closed.semiPoint K r S L hL hsd
  obtain ⟨v, hv, hli, hle⟩ := exists_short_basis hL hsd M (ε := fdeg K)
    (by exact_mod_cast fdeg_pos) fun v hv hv0 => by
      have h := finrank_le_sum_hq M.posDef hM hv hv0
      rw [BoundedBasis.finrank_eq_two_mul_fdeg] at h
      push_cast at h
      linarith
  refine ⟨v, hv, hli, fun σ i k => ?_⟩
  have h1 := norm_h_le (SemiPt.detG_ne_zero S L hL hsd) M σ (v i) (v k)
  linarith [two_mul_hq_le M σ (v i), two_mul_hq_le M σ (v k), hle i, hle k]

end Short

section Count

/- English proof (translation)
Use `Fintype.ofFinite ((Fin r → R) ⧸ LinearMap.range N.vecMulLinear)` as an intermediate fact. Use `⟨Finset.univ.image fun y : Fin r → (Fin r → R) ⧸ LinearMap.range N.vecMulLinear => (span R (Set.range y)).comap (LinearMap.range N.vecMulLinear).mkQ, ?_, fun P hP => ?_⟩` and prove the remaining obligations. Use `Finset.card_image_le.trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Nat.card_eq_fintype_card]`. Take `⟨x, hx⟩` from `BoundedBasis.exists_generators_mod_smul hN r P P.subtype P.injective_subtype`.

Use `Finset.mem_image.2 ⟨fun j => (LinearMap.range N.vecMulLinear).mkQ (x j), Finset.mem_univ _, le_antisymm ?_ fun m hm => ?_⟩` and prove the remaining obligations. Use `(comap_mono (q' := P.map (LinearMap.range N.vecMulLinear).mkQ) ?_).trans ?_` and prove the remaining obligations. Rewrite using `[span_le]`. Introduce and unpack `_ ⟨j, rfl⟩`. Conclude with `mem_map_of_mem (x j).2`.

Rewrite using `[comap_map_mkQ]`. Conclude with `sup_le hP le_rfl`. Take `⟨c, m', h⟩` from `hx ⟨m, hm⟩`. Establish `h'` using `congrArg Subtype.val h`. Simplify using `only [Submodule.coe_add, Submodule.coe_sum, Submodule.coe_smul] at h'`.

Establish `h0 : (LinearMap.range N.vecMulLinear).mkQ (N.det • (m' : Fin r → R)) = 0`. Rewrite using `[mkQ_apply, Quotient.mk_eq_zero]`. Conclude with `⟨m' ᵥ* N.adjugate, by`. Rewrite using `[vecMulLinear_apply, vecMul_vecMul, adjugate_mul, vecMul_smul, vecMul_one]⟩`. Rewrite using `[mem_comap, h', map_add, h0, add_zero, map_sum]`.

Use `sum_mem fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul]`. Conclude with `smul_mem _ _ (subset_span ⟨j, rfl⟩)`.
-/
theorem exists_finset_submodule {R : Type} [CommRing R] [IsDedekindDomain R] {r : ℕ}
    (N : Matrix (Fin r) (Fin r) R) (hN : N.det ≠ 0)
    [Finite ((Fin r → R) ⧸ LinearMap.range N.vecMulLinear)] :
    ∃ T : Finset (Submodule R (Fin r → R)),
      T.card ≤ Nat.card ((Fin r → R) ⧸ LinearMap.range N.vecMulLinear) ^ r ∧
      ∀ P, LinearMap.range N.vecMulLinear ≤ P → P ∈ T := by
  classical
  have := Fintype.ofFinite ((Fin r → R) ⧸ LinearMap.range N.vecMulLinear)
  refine ⟨Finset.univ.image fun y : Fin r → (Fin r → R) ⧸ LinearMap.range N.vecMulLinear =>
    (span R (Set.range y)).comap (LinearMap.range N.vecMulLinear).mkQ, ?_, fun P hP => ?_⟩
  · refine Finset.card_image_le.trans (le_of_eq ?_)
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Nat.card_eq_fintype_card]
  · obtain ⟨x, hx⟩ := BoundedBasis.exists_generators_mod_smul hN r P P.subtype
      P.injective_subtype
    refine Finset.mem_image.2 ⟨fun j => (LinearMap.range N.vecMulLinear).mkQ (x j),
      Finset.mem_univ _, le_antisymm ?_ fun m hm => ?_⟩
    · refine (comap_mono (q' := P.map (LinearMap.range N.vecMulLinear).mkQ) ?_).trans ?_
      · rw [span_le]
        rintro _ ⟨j, rfl⟩
        exact mem_map_of_mem (x j).2
      · rw [comap_map_mkQ]
        exact sup_le hP le_rfl
    · obtain ⟨c, m', h⟩ := hx ⟨m, hm⟩
      have h' := congrArg Subtype.val h
      simp only [Submodule.coe_add, Submodule.coe_sum, Submodule.coe_smul] at h'
      have h0 : (LinearMap.range N.vecMulLinear).mkQ (N.det • (m' : Fin r → R)) = 0 := by
        rw [mkQ_apply, Quotient.mk_eq_zero]
        exact ⟨m' ᵥ* N.adjugate, by
          rw [vecMulLinear_apply, vecMul_vecMul, adjugate_mul, vecMul_smul, vecMul_one]⟩
      rw [mem_comap, h', map_add, h0, add_zero, map_sum]
      refine sum_mem fun j _ => ?_
      rw [map_smul]
      exact smul_mem _ _ (subset_span ⟨j, rfl⟩)

variable {K : Type} [Field K] [NumberField K] [IsCMField K] {r : ℕ}

open BoundedBasis

noncomputable def pairings (G : Matrix (Fin r) (Fin r) K) (L : Submodule (𝓞 K) (Fin r → K))
    (v : Fin r → Fin r → K) : Submodule (𝓞 K) (Fin r → 𝓞 K) where
  carrier := {z | ∃ x ∈ L, ∀ k, (z k : K) = herm G x (v k)}
  add_mem' := by
    rintro a b ⟨x, hx, ha⟩ ⟨y, hy, hb⟩
    exact ⟨x + y, add_mem hx hy, fun k => by rw [herm_add_left, ← ha, ← hb]; simp⟩
  zero_mem' := ⟨0, zero_mem _, fun k => by simp [herm]⟩
  smul_mem' := by
    rintro c a ⟨x, hx, ha⟩
    refine ⟨c • x, smul_mem _ _ hx, fun k => ?_⟩
    change _ = herm G ((c : K) • x) (v k)
    rw [herm_smul_left, ← ha]
    simp

/- English proof (translation)
Introduce and unpack `_ ⟨o, rfl⟩`. Use `⟨(fun i => (o i : K)) ᵥ* Matrix.of v, ?_, fun k => ?_⟩` and prove the remaining obligations. Rewrite using `[vecMul_of]`. Conclude with `sum_mem fun i _ => L.smul_mem (o i) (hv i)`. Rewrite using `[herm_vecMul_left, hA]`.

Simplify using `[vecMul, dotProduct]`.
-/
theorem range_le_pairings {G : Matrix (Fin r) (Fin r) K} {L : Submodule (𝓞 K) (Fin r → K)}
    {v : Fin r → Fin r → K} (hv : ∀ i, v i ∈ L) {A : Matrix (Fin r) (Fin r) (𝓞 K)}
    (hA : gramOf G v = A.map (algebraMap (𝓞 K) K)) :
    LinearMap.range A.vecMulLinear ≤ pairings G L v := by
  rintro _ ⟨o, rfl⟩
  refine ⟨(fun i => (o i : K)) ᵥ* Matrix.of v, ?_, fun k => ?_⟩
  · rw [vecMul_of]
    exact sum_mem fun i _ => L.smul_mem (o i) (hv i)
  · rw [herm_vecMul_left, hA]
    simp [vecMul, dotProduct]

/- English proof (translation)
Take `⟨x, hx, hx'⟩` from `h (x := fun k => ⟨_, hint _ hc k⟩) ⟨_, hc, fun _ => rfl⟩`. Take `⟨d, rfl⟩` from `exists_vecMul_eq hw x`. Establish `h1 : (c - d) ᵥ* gramOf G w = 0`. Use function extensionality and compare the values at `k`. Rewrite using `[sub_vecMul, Pi.sub_apply, ← herm_vecMul_left G w d, ← hx' k, ← hgram, ← herm_vecMul_left]`.

Conclude with `sub_self _`. Rewrite using `[sub_eq_zero.1 (Matrix.eq_zero_of_vecMul_eq_zero (det_gramOf_ne_zero hG hw) h1)]` and apply the resulting hypothesis.
-/
theorem vecMul_mem_of_pairings_le {G : Matrix (Fin r) (Fin r) K} (hG : G.det ≠ 0)
    {L L' : Submodule (𝓞 K) (Fin r → K)} {v w : Fin r → Fin r → K}
    (hint : ∀ x ∈ L, ∀ k, IsIntegral ℤ (herm G x (v k))) (hw : LinearIndependent K w)
    (hgram : gramOf G v = gramOf G w) (h : pairings G L v ≤ pairings G L' w) (c : Fin r → K)
    (hc : c ᵥ* Matrix.of v ∈ L) : c ᵥ* Matrix.of w ∈ L' := by
  obtain ⟨x, hx, hx'⟩ := h (x := fun k => ⟨_, hint _ hc k⟩) ⟨_, hc, fun _ => rfl⟩
  obtain ⟨d, rfl⟩ := exists_vecMul_eq hw x
  have h1 : (c - d) ᵥ* gramOf G w = 0 := by
    funext k
    rw [sub_vecMul, Pi.sub_apply, ← herm_vecMul_left G w d, ← hx' k, ← hgram, ← herm_vecMul_left]
    exact sub_self _
  rwa [sub_eq_zero.1 (Matrix.eq_zero_of_vecMul_eq_zero (det_gramOf_ne_zero hG hw) h1)]

/- English proof (translation)
Establish `key : ∀ A : Matrix (Fin r) (Fin r) (𝓞 K), ∃ V : Finset (Submodule (𝓞 K) (Fin r → 𝓞 K)), (V.card : ℝ) ≤ (r * B) ^ (2 * fdeg K * r ^ 2) ∧ ∀ P, A.det ≠ 0 → (∀ (σ : K →+* ℂ) i k, ‖σ (A i k : K)‖ ≤ B) → LinearMap.range A.vecMulLinear ≤ P → P ∈ V`. Introduce `A`. Distinguish the cases in `h : A.det ≠ 0 ∧ ∀ (σ : K →+* ℂ) i k, ‖σ (A i k : K)‖ ≤ B`. Use `swap`. Conclude with `⟨∅, by simp only [Finset.card_empty, Nat.cast_zero]; positivity, fun P h1 h2 => absurd ⟨h1, h2⟩ h⟩`.

Establish `hcard` using `card_quotient_range_vecMulLinear A h.1`. Establish `hbound : ((Algebra.norm ℤ A.det).natAbs : ℝ) ≤ ((r * B) ^ r) ^ finrank ℚ K`. Use `natAbs_norm_le_pow fun σ => ?_` and prove the remaining obligations. Establish `h1 : σ ((A.det : 𝓞 K) : K) = (A.map (σ.comp (algebraMap (𝓞 K) K))).det` using `RingHom.map_det (σ.comp (algebraMap (𝓞 K) K)) A`. Rewrite using `[h1]`.

Conclude with `norm_det_le_pow _ hB fun i k => h.2 σ i k`. Establish `: Finite ((Fin r → 𝓞 K) ⧸ LinearMap.range A.vecMulLinear)`. Use `Nat.finite_of_card_ne_zero ?_` and prove the remaining obligations. Rewrite using `[hcard, Int.natAbs_ne_zero, Algebra.norm_ne_zero_iff]`. Conclude with `h.1`.

Take `⟨V, hV, hV'⟩` from `exists_finset_submodule A h.1`. Use `⟨V, ?_, fun P _ _ => hV' P⟩` and prove the remaining obligations. Rewrite `hV` using `[hcard]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← pow_mul, ← pow_mul, finrank_eq_two_mul_fdeg]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Use `choose V hV hV' using key`. Take `⟨hfin, hc⟩` from `ReciprocityTheory.ChartRestriction.G.FD.PackingSeparation.count (E := K) B hB`. Rewrite `hc` using `[Set.ncard_eq_toFinset_card _ hfin]`.

Set `T : Finset (Fin r → Fin r → 𝓞 K)` to `Fintype.piFinset fun _ => Fintype.piFinset fun _ => hfin.toFinset`. Establish `hT : (T.card : ℝ) ≤ (1 + 2 * B) ^ (2 * fdeg K * r ^ 2)`. Rewrite using `[Fintype.card_piFinset_const, Fintype.card_piFinset_const]`. Use `push_cast`. Combine the equalities or inequalities in the displayed calculation.

Use `⟨T.biUnion fun A => (V (Matrix.of A)).image fun P => (Matrix.of A, P), ?_, fun A P h1 h2 h3 => ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Conclude with `Finset.card_biUnion_le` after adjusting the coercions. Use `_ ≤ ∑ _A ∈ T, (r * B) ^ (2 * fdeg K * r ^ 2) := Finset.sum_le_sum fun A _ => le_trans (by exact_mod_cast Finset.card_image_le) (hV _)`. Use `_ = T.card * (r * B) ^ (2 * fdeg K * r ^ 2) := by rw [Finset.sum_const, nsmul_eq_mul]`.

Use `_ ≤ _ := by gcongr`. Use `Finset.mem_biUnion.2 ⟨A, ?_, Finset.mem_image.2 ⟨P, hV' A P h1 h2 h3, rfl⟩⟩` and prove the remaining obligations. Conclude with `Fintype.mem_piFinset.2 fun i => Fintype.mem_piFinset.2 fun k => hfin.mem_toFinset.2 fun σ => h2 σ i k`.
-/
theorem exists_finset_types {B : ℝ} (hB : 0 ≤ B) :
    ∃ T : Finset (Matrix (Fin r) (Fin r) (𝓞 K) × Submodule (𝓞 K) (Fin r → 𝓞 K)),
      (T.card : ℝ) ≤ (1 + 2 * B) ^ (2 * fdeg K * r ^ 2) * (r * B) ^ (2 * fdeg K * r ^ 2) ∧
      ∀ (A : Matrix (Fin r) (Fin r) (𝓞 K)) P, A.det ≠ 0 →
        (∀ (σ : K →+* ℂ) i k, ‖σ (A i k : K)‖ ≤ B) → LinearMap.range A.vecMulLinear ≤ P →
        (A, P) ∈ T := by
  classical
  have key : ∀ A : Matrix (Fin r) (Fin r) (𝓞 K), ∃ V : Finset (Submodule (𝓞 K) (Fin r → 𝓞 K)),
      (V.card : ℝ) ≤ (r * B) ^ (2 * fdeg K * r ^ 2) ∧ ∀ P, A.det ≠ 0 →
        (∀ (σ : K →+* ℂ) i k, ‖σ (A i k : K)‖ ≤ B) → LinearMap.range A.vecMulLinear ≤ P →
        P ∈ V := by
    intro A
    by_cases h : A.det ≠ 0 ∧ ∀ (σ : K →+* ℂ) i k, ‖σ (A i k : K)‖ ≤ B
    swap
    · exact ⟨∅, by simp only [Finset.card_empty, Nat.cast_zero]; positivity,
        fun P h1 h2 => absurd ⟨h1, h2⟩ h⟩
    have hcard := card_quotient_range_vecMulLinear A h.1
    have hbound : ((Algebra.norm ℤ A.det).natAbs : ℝ) ≤ ((r * B) ^ r) ^ finrank ℚ K := by
      refine natAbs_norm_le_pow fun σ => ?_
      have h1 : σ ((A.det : 𝓞 K) : K) = (A.map (σ.comp (algebraMap (𝓞 K) K))).det :=
        RingHom.map_det (σ.comp (algebraMap (𝓞 K) K)) A
      rw [h1]
      exact norm_det_le_pow _ hB fun i k => h.2 σ i k
    have : Finite ((Fin r → 𝓞 K) ⧸ LinearMap.range A.vecMulLinear) := by
      refine Nat.finite_of_card_ne_zero ?_
      rw [hcard, Int.natAbs_ne_zero, Algebra.norm_ne_zero_iff]
      exact h.1
    obtain ⟨V, hV, hV'⟩ := exists_finset_submodule A h.1
    refine ⟨V, ?_, fun P _ _ => hV' P⟩
    rw [hcard] at hV
    calc (V.card : ℝ) ≤ ((Algebra.norm ℤ A.det).natAbs : ℝ) ^ r := by exact_mod_cast hV
      _ ≤ (((r * B) ^ r) ^ finrank ℚ K) ^ r := by gcongr
      _ = _ := by
          rw [← pow_mul, ← pow_mul, finrank_eq_two_mul_fdeg]
          congr 1
          ring
  choose V hV hV' using key
  obtain ⟨hfin, hc⟩ := ReciprocityTheory.ChartRestriction.G.FD.PackingSeparation.count (E := K) B hB
  rw [Set.ncard_eq_toFinset_card _ hfin] at hc
  let T : Finset (Fin r → Fin r → 𝓞 K) :=
    Fintype.piFinset fun _ => Fintype.piFinset fun _ => hfin.toFinset
  have hT : (T.card : ℝ) ≤ (1 + 2 * B) ^ (2 * fdeg K * r ^ 2) := by
    rw [Fintype.card_piFinset_const, Fintype.card_piFinset_const]
    push_cast
    calc ((hfin.toFinset.card : ℝ) ^ r) ^ r ≤ (((1 + 2 * B) ^ (2 * fdeg K)) ^ r) ^ r := by gcongr
      _ = _ := by rw [← pow_mul, ← pow_mul, sq]
  refine ⟨T.biUnion fun A => (V (Matrix.of A)).image fun P => (Matrix.of A, P), ?_,
    fun A P h1 h2 h3 => ?_⟩
  · calc ((T.biUnion fun A => (V (Matrix.of A)).image fun P => (Matrix.of A, P)).card : ℝ)
        ≤ ∑ A ∈ T, (((V (Matrix.of A)).image fun P => (Matrix.of A, P)).card : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ _A ∈ T, (r * B) ^ (2 * fdeg K * r ^ 2) :=
          Finset.sum_le_sum fun A _ => le_trans (by exact_mod_cast Finset.card_image_le) (hV _)
      _ = T.card * (r * B) ^ (2 * fdeg K * r ^ 2) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := by gcongr
  · refine Finset.mem_biUnion.2 ⟨A, ?_, Finset.mem_image.2 ⟨P, hV' A P h1 h2 h3, rfl⟩⟩
    exact Fintype.mem_piFinset.2 fun i => Fintype.mem_piFinset.2 fun k =>
      hfin.mem_toFinset.2 fun σ => h2 σ i k

/- English proof (translation)
Take `⟨T, hT, hT'⟩` from `exists_finset_types (K := K) (r := r) hB`. Use `choose hG hint v hv hli hle using h𝓛`. Set `A : 𝓛 → Matrix (Fin r) (Fin r) (𝓞 K)` to `fun L => Matrix.of fun i k => ⟨_, hint L.1 L.2 _ (hv L.1 L.2 i) _ (hv L.1 L.2 k)⟩`. Establish `hA : ∀ L : 𝓛, gramOf G (v L.1 L.2) = (A L).map (algebraMap (𝓞 K) K)` using `fun _ => rfl`. Establish `hmem : ∀ L : 𝓛, (A L, pairings G L.1 (v L.1 L.2)) ∈ T` using `fun L => by`.

Use `hT' _ _ (fun h0 => ?_) (hle L.1 L.2) (range_le_pairings (hv L.1 L.2) (hA L))` and prove the remaining obligations. Apply `det_gramOf_ne_zero (hG L.1 L.2) (hli L.1 L.2)` to reduce the goal to its premises. Rewrite using `[hA, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]`. Take `⟨V, hV, hV'⟩` from `exists_finset_representatives (β := T) 𝓛 fun L => ⟨_, hmem L⟩`. Use `⟨V.image Subtype.val, fun L hL => ?_, fun L hL => ?_, le_trans ?_ hT⟩` and prove the remaining obligations.

Take `⟨L', -, rfl⟩` from `Finset.mem_image.1 hL`. Conclude with `L'.2`. Take `⟨L₀, hL₀, h⟩` from `hV' ⟨L, hL⟩`. Take `⟨h1, h2⟩` from `Prod.ext_iff.1 (congrArg Subtype.val h)`. Establish `hgram : gramOf G (v L₀.1 L₀.2) = gramOf G (v L hL)`.

Rewrite using `[hA L₀, hA ⟨L, hL⟩]`. Conclude with `congrArg (fun M => M.map (algebraMap (𝓞 K) K)) h1`. Take `⟨γ, hγ⟩` from `exists_gl_mulVec (hli L hL) (hli L₀.1 L₀.2)`. Use `⟨L₀.1, Finset.mem_image_of_mem _ hL₀, γ, fun x y => ?_, fun x => ?_⟩` and prove the remaining obligations. Take `⟨c, rfl⟩` from `exists_vecMul_eq (hli L₀.1 L₀.2) x`.

Take `⟨d, rfl⟩` from `exists_vecMul_eq (hli L₀.1 L₀.2) y`. Rewrite using `[hγ, hγ, herm_vecMul, herm_vecMul, hgram]`. Take `⟨c, rfl⟩` from `exists_vecMul_eq (hli L₀.1 L₀.2) x`. Rewrite using `[hγ]`. Conclude with `⟨vecMul_mem_of_pairings_le (hG L hL) (fun x hx k => hint _ L₀.2 x hx _ (hv _ L₀.2 k)) (hli L hL) hgram h2.le c, vecMul_mem_of_pairings_le (hG L hL) (fun x hx k => hint _ hL x hx _ (hv _ hL k)) (hli _ L₀.2) hgram.symm h2.ge c⟩`.

Rewrite `hV` using `[Nat.card_eq_fintype_card, Fintype.card_coe]`. Conclude with `Finset.card_image_le.trans hV` after adjusting the coercions.
-/
theorem exists_finset_classes {G : Matrix (Fin r) (Fin r) K} (𝓛 : Set (Submodule (𝓞 K) (Fin r → K)))
    {B : ℝ} (hB : 0 ≤ B)
    (h𝓛 : ∀ L ∈ 𝓛, G.det ≠ 0 ∧ (∀ x ∈ L, ∀ y ∈ L, IsIntegral ℤ (herm G x y)) ∧
      ∃ v : Fin r → Fin r → K, (∀ i, v i ∈ L) ∧ LinearIndependent K v ∧
        ∀ (σ : K →+* ℂ) (i k : Fin r), ‖σ (herm G (v i) (v k))‖ ≤ B) :
    ∃ 𝒮 : Finset (Submodule (𝓞 K) (Fin r → K)), (∀ L ∈ 𝒮, L ∈ 𝓛) ∧
      (∀ L ∈ 𝓛, ∃ L₀ ∈ 𝒮, ∃ γ : GL (Fin r) K,
        (∀ x y, herm G ((γ : Matrix (Fin r) (Fin r) K) *ᵥ x)
          ((γ : Matrix (Fin r) (Fin r) K) *ᵥ y) = herm G x y) ∧
        ∀ x, x ∈ L₀ ↔ (γ : Matrix (Fin r) (Fin r) K) *ᵥ x ∈ L) ∧
      (𝒮.card : ℝ) ≤ (1 + 2 * B) ^ (2 * fdeg K * r ^ 2) * (r * B) ^ (2 * fdeg K * r ^ 2) := by
  classical
  obtain ⟨T, hT, hT'⟩ := exists_finset_types (K := K) (r := r) hB
  choose hG hint v hv hli hle using h𝓛
  let A : 𝓛 → Matrix (Fin r) (Fin r) (𝓞 K) := fun L =>
    Matrix.of fun i k => ⟨_, hint L.1 L.2 _ (hv L.1 L.2 i) _ (hv L.1 L.2 k)⟩
  have hA : ∀ L : 𝓛, gramOf G (v L.1 L.2) = (A L).map (algebraMap (𝓞 K) K) := fun _ => rfl
  have hmem : ∀ L : 𝓛, (A L, pairings G L.1 (v L.1 L.2)) ∈ T := fun L => by
    refine hT' _ _ (fun h0 => ?_) (hle L.1 L.2) (range_le_pairings (hv L.1 L.2) (hA L))
    apply det_gramOf_ne_zero (hG L.1 L.2) (hli L.1 L.2)
    rw [hA, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]
  obtain ⟨V, hV, hV'⟩ := exists_finset_representatives (β := T) 𝓛 fun L => ⟨_, hmem L⟩
  refine ⟨V.image Subtype.val, fun L hL => ?_, fun L hL => ?_, le_trans ?_ hT⟩
  · obtain ⟨L', -, rfl⟩ := Finset.mem_image.1 hL
    exact L'.2
  · obtain ⟨L₀, hL₀, h⟩ := hV' ⟨L, hL⟩
    obtain ⟨h1, h2⟩ := Prod.ext_iff.1 (congrArg Subtype.val h)
    have hgram : gramOf G (v L₀.1 L₀.2) = gramOf G (v L hL) := by
      rw [hA L₀, hA ⟨L, hL⟩]
      exact congrArg (fun M => M.map (algebraMap (𝓞 K) K)) h1
    obtain ⟨γ, hγ⟩ := exists_gl_mulVec (hli L hL) (hli L₀.1 L₀.2)
    refine ⟨L₀.1, Finset.mem_image_of_mem _ hL₀, γ, fun x y => ?_, fun x => ?_⟩
    · obtain ⟨c, rfl⟩ := exists_vecMul_eq (hli L₀.1 L₀.2) x
      obtain ⟨d, rfl⟩ := exists_vecMul_eq (hli L₀.1 L₀.2) y
      rw [hγ, hγ, herm_vecMul, herm_vecMul, hgram]
    · obtain ⟨c, rfl⟩ := exists_vecMul_eq (hli L₀.1 L₀.2) x
      rw [hγ]
      exact ⟨vecMul_mem_of_pairings_le (hG L hL)
          (fun x hx k => hint _ L₀.2 x hx _ (hv _ L₀.2 k)) (hli L hL) hgram h2.le c,
        vecMul_mem_of_pairings_le (hG L hL)
          (fun x hx k => hint _ hL x hx _ (hv _ hL k)) (hli _ L₀.2) hgram.symm h2.ge c⟩
  · rw [Nat.card_eq_fintype_card, Fintype.card_coe] at hV
    exact_mod_cast Finset.card_image_le.trans hV

end Count

section Numbers

/- English proof (translation)
Use `set B : ℝ := max 1 ((2 * f * r : ℝ) ^ 4 * d ^ 2 / (4 * f)) with hB`. Establish `hf' : (16 : ℝ) ≤ f` using `by exact_mod_cast hf`. Establish `e : ∀ {x y : ℝ}, Real.log x ≤ y → x ≤ Real.exp y` using `fun h => (Real.le_exp_log _).trans (Real.exp_le_exp.2 h)`. Establish `hB1 : 1 ≤ B` using `le_max_left _ _`. Establish `hBe : B ≤ Real.exp (12 * ℓ + 8 * f * ℓ)`.

Use `max_le (Real.one_le_exp (by positivity)) ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ f * ((f : ℝ) ^ 3 * r ^ 4 * d ^ 2) := by gcongr; linarith`.

Use `_ = (f : ℝ) ^ 4 * r ^ 4 * d ^ 2 := by ring`. Use `_ ≤ Real.exp (2 * ℓ) ^ 4 * Real.exp ℓ ^ 4 * Real.exp (4 * f * ℓ) ^ 2 := by gcongr exacts [e hfℓ, e hr, e hd]`. Use `_ = _ := by`. Simplify using `only [← Real.exp_nat_mul, ← Real.exp_add]`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `h3 : 1 + 2 * B ≤ Real.exp ℓ * B`. Use polynomial arithmetic with `[Real.add_one_le_exp ℓ]`. Rewrite using `[← mul_pow, ← mul_pow]`.

Combine the equalities or inequalities in the displayed calculation. Conclude with `e hM`. Conclude with `h3.trans (by gcongr)`. Conclude with `e hr`. Use `_ = Real.exp ((2 * f * r ^ 2 * ℓ) * (56 + 16 * f)) := by`.

Simplify using `only [← Real.exp_nat_mul, ← Real.exp_add]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ Real.exp ((2 * f * r ^ 2 * ℓ) * (10 * f * ℓ)) := by gcongr`.

Use the polynomial consequences of the given equalities and inequalities. Use `_ = _ := by congr 1; ring`.
-/
theorem pow_mul_bound_le_exp (f r : ℕ) {d ℓ M : ℝ} (hf : 16 ≤ f) (hℓ : 2 ≤ ℓ) (hd0 : 0 ≤ d)
    (hd : Real.log d ≤ 4 * f * ℓ) (hr : Real.log r ≤ ℓ) (hfℓ : Real.log f ≤ 2 * ℓ) (hM0 : 0 ≤ M)
    (hM : Real.log M ≤ 30 * ℓ) :
    M ^ (2 * f * r ^ 2) *
      ((1 + 2 * max 1 ((2 * f * r : ℝ) ^ 4 * d ^ 2 / (4 * f))) ^ (2 * f * r ^ 2) *
        (r * max 1 ((2 * f * r : ℝ) ^ 4 * d ^ 2 / (4 * f))) ^ (2 * f * r ^ 2)) ≤
      Real.exp (20 * (f * r * ℓ) ^ 2) := by
  set B : ℝ := max 1 ((2 * f * r : ℝ) ^ 4 * d ^ 2 / (4 * f)) with hB
  have hf' : (16 : ℝ) ≤ f := by exact_mod_cast hf
  have e : ∀ {x y : ℝ}, Real.log x ≤ y → x ≤ Real.exp y := fun h =>
    (Real.le_exp_log _).trans (Real.exp_le_exp.2 h)
  have hB1 : 1 ≤ B := le_max_left _ _
  have hBe : B ≤ Real.exp (12 * ℓ + 8 * f * ℓ) := by
    refine max_le (Real.one_le_exp (by positivity)) ?_
    calc (2 * f * r : ℝ) ^ 4 * d ^ 2 / (4 * f) = 4 * ((f : ℝ) ^ 3 * r ^ 4 * d ^ 2) := by
          field_simp
          ring
      _ ≤ f * ((f : ℝ) ^ 3 * r ^ 4 * d ^ 2) := by gcongr; linarith
      _ = (f : ℝ) ^ 4 * r ^ 4 * d ^ 2 := by ring
      _ ≤ Real.exp (2 * ℓ) ^ 4 * Real.exp ℓ ^ 4 * Real.exp (4 * f * ℓ) ^ 2 := by
          gcongr
          exacts [e hfℓ, e hr, e hd]
      _ = _ := by
          simp only [← Real.exp_nat_mul, ← Real.exp_add]
          congr 1
          push_cast
          ring
  have h3 : 1 + 2 * B ≤ Real.exp ℓ * B := by
    nlinarith [Real.add_one_le_exp ℓ]
  rw [← mul_pow, ← mul_pow]
  calc (M * ((1 + 2 * B) * (r * B))) ^ (2 * f * r ^ 2)
      ≤ (Real.exp (30 * ℓ) * ((Real.exp ℓ * Real.exp (12 * ℓ + 8 * f * ℓ)) *
          (Real.exp ℓ * Real.exp (12 * ℓ + 8 * f * ℓ)))) ^ (2 * f * r ^ 2) := by
        gcongr
        · exact e hM
        · exact h3.trans (by gcongr)
        · exact e hr
    _ = Real.exp ((2 * f * r ^ 2 * ℓ) * (56 + 16 * f)) := by
        simp only [← Real.exp_nat_mul, ← Real.exp_add]
        congr 1
        push_cast
        ring
    _ ≤ Real.exp ((2 * f * r ^ 2 * ℓ) * (10 * f * ℓ)) := by
        gcongr
        nlinarith
    _ = _ := by congr 1; ring

end Numbers

variable {K : Type} [Field K] [NumberField K] [IsCMField K] {r : ℕ}

/- English proof (translation)
Take `⟨σ⟩ : Nonempty (K →+* ℂ)` from `inferInstance`. Conclude with `σ.injective (by rw [S.c_emb, cc, IsCMField.complexEmbedding_complexConj])`.
-/
theorem c_eq_cc (S : HermForm K r) (x : K) : S.c x = cc x := by
  obtain ⟨σ⟩ : Nonempty (K →+* ℂ) := inferInstance
  exact σ.injective (by rw [S.c_emb, cc, IsCMField.complexEmbedding_complexConj])

/- English proof (translation)
Simplify using `only [herm, HermForm.h, c_eq_cc, transpose_apply]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring`.
-/
theorem herm_transpose (S : HermForm K r) (x y : Fin r → K) : herm S.Gᵀ x y = S.h y x := by
  simp only [herm, HermForm.h, c_eq_cc, transpose_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

omit [IsCMField K] in
/- English proof (translation)
Assemble the required witnesses or components as `⟨fun ⟨z, hz⟩ => hz ▸ z.isIntegral_coe, fun h => ⟨⟨x, h⟩, rfl⟩⟩`.
-/
theorem isIntegralElt_iff {x : K} : IsIntegralElt x ↔ IsIntegral ℤ x :=
  ⟨fun ⟨z, hz⟩ => hz ▸ z.isIntegral_coe, fun h => ⟨⟨x, h⟩, rfl⟩⟩

noncomputable def hermFormOf (G : Matrix (Fin r) (Fin r) K) (hG : ∀ a b, cc (G a b) = G b a) :
    HermForm K r where
  c := (IsCMField.complexConj K : K →+* K)
  c_invol := fun x => IsCMField.complexConj_apply_apply K x
  c_emb := fun σ x => IsCMField.complexEmbedding_complexConj K σ x
  G := Gᵀ
  G_herm := fun a b => hG b a

/- English proof (translation)
The claim follows from `(herm_transpose (hermFormOf G hG) y x).symm`.
-/
theorem hermFormOf_h (G : Matrix (Fin r) (Fin r) K) (hG : ∀ a b, cc (G a b) = G b a)
    (x y : Fin r → K) : (hermFormOf G hG).h x y = herm G y x :=
  (herm_transpose (hermFormOf G hG) y x).symm

end ClassCount

open ClassCount

variable {K : Type} [Field K] [NumberField K] [IsCMField K] {r : ℕ}

/- English proof (translation)
Take `⟨𝒮, h1, h2, h3⟩` from `exists_finset_classes (G := S.Gᵀ) {L | IsLattice L ∧ IsSelfDual S L} (B := max 1 ((2 * fdeg K * r : ℝ) ^ 4 * dE K ^ 2 / (4 * fdeg K))) (by positivity) fun L hL => by`. Take `⟨v, hv, hli, hle⟩` from `exists_bounded_basis hL.1 hL.2`. Use `⟨by rw [det_transpose]; exact SemiPt.detG_ne_zero S L hL.1 hL.2, fun x hx y hy => ?_, v, hv, hli, fun σ i k => ?_⟩` and prove the remaining obligations. Rewrite using `[herm_transpose, ← isIntegralElt_iff]`. Conclude with `hL.2.1 y hy x hx`.

Rewrite using `[herm_transpose]`. Conclude with `(hle σ k i).trans (le_max_right _ _)`. Use `⟨𝒮, h1, fun L hL hsd => ?_, h3, fun ℓ M hf hℓ hd hr hfℓ hM0 hM => ?_⟩` and prove the remaining obligations. Take `⟨L₀, hL₀, γ, hγ, hm⟩` from `h2 L ⟨hL, hsd⟩`. Use `⟨L₀, hL₀, γ, fun x y => by rw [← herm_transpose, hγ, herm_transpose], hm, ?_⟩` and prove the remaining obligations.

Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Establish `h : (γ : Matrix (Fin r) (Fin r) K) *ᵥ (((γ⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) *ᵥ x) = x`. Rewrite using `[mulVec_mulVec, Units.mul_inv, one_mulVec]`.

Conclude with `⟨_, (hm _).2 (h.symm ▸ hx), h⟩`. Introduce and unpack `⟨y, hy, rfl⟩`. Conclude with `(hm y).1 hy`. Establish `h : M ^ (2 * fdeg K * r ^ 2) * 𝒮.card ≤ Real.exp (20 * (fdeg K * r * ℓ) ^ 2)` using `le_trans (mul_le_mul_of_nonneg_left h3 (by positivity)) (pow_mul_bound_le_exp (fdeg K) r (d := dE K) hf hℓ (abs_nonneg _) hd hr hfℓ hM0.le hM)`. Use `⟨h, ?_⟩` and prove the remaining obligations.

Establish `h0` using `sq_nonneg (fdeg K * r * ℓ)`. Break down `(show 0 ≤ M ^ (2 * fdeg K * r ^ 2) * 𝒮.card by positivity).eq_or_lt with h' | h'` into its components or cases. Rewrite using `[← h', Real.log_zero]`. Check the signs of the components of the expression. Combine the linear relations using `[(Real.log_le_iff_le_exp h').2 h]`.
-/
theorem exists_finset_selfDual_classes (S : HermForm K r) :
    ∃ 𝒮 : Finset (Submodule (𝓞 K) (Fin r → K)),
      (∀ L ∈ 𝒮, IsLattice L ∧ IsSelfDual S L) ∧
      (∀ L, IsLattice L → IsSelfDual S L → ∃ L₀ ∈ 𝒮, ∃ γ : GL (Fin r) K,
        (∀ x y, S.h ((γ : Matrix (Fin r) (Fin r) K) *ᵥ x)
          ((γ : Matrix (Fin r) (Fin r) K) *ᵥ y) = S.h x y) ∧
        (∀ x, x ∈ L₀ ↔ (γ : Matrix (Fin r) (Fin r) K) *ᵥ x ∈ L) ∧
        L = L₀.map ((Matrix.toLin' (γ : Matrix (Fin r) (Fin r) K)).restrictScalars (𝓞 K))) ∧
      (𝒮.card : ℝ) ≤
        (1 + 2 * max 1 ((2 * fdeg K * r : ℝ) ^ 4 * dE K ^ 2 / (4 * fdeg K))) ^
            (2 * fdeg K * r ^ 2) *
          (r * max 1 ((2 * fdeg K * r : ℝ) ^ 4 * dE K ^ 2 / (4 * fdeg K))) ^
            (2 * fdeg K * r ^ 2) ∧
      ∀ ℓ M : ℝ, 16 ≤ fdeg K → 2 ≤ ℓ → Real.log (dE K) ≤ 4 * fdeg K * ℓ → Real.log r ≤ ℓ →
        Real.log (fdeg K) ≤ 2 * ℓ → 0 < M → Real.log M ≤ 30 * ℓ →
        M ^ (2 * fdeg K * r ^ 2) * 𝒮.card ≤ Real.exp (20 * (fdeg K * r * ℓ) ^ 2) ∧
        Real.log (M ^ (2 * fdeg K * r ^ 2) * 𝒮.card) ≤ 41 * (fdeg K * r * ℓ) ^ 2 := by
  obtain ⟨𝒮, h1, h2, h3⟩ := exists_finset_classes (G := S.Gᵀ) {L | IsLattice L ∧ IsSelfDual S L}
    (B := max 1 ((2 * fdeg K * r : ℝ) ^ 4 * dE K ^ 2 / (4 * fdeg K))) (by positivity)
    fun L hL => by
      obtain ⟨v, hv, hli, hle⟩ := exists_bounded_basis hL.1 hL.2
      refine ⟨by rw [det_transpose]; exact SemiPt.detG_ne_zero S L hL.1 hL.2,
        fun x hx y hy => ?_, v, hv, hli, fun σ i k => ?_⟩
      · rw [herm_transpose, ← isIntegralElt_iff]
        exact hL.2.1 y hy x hx
      · rw [herm_transpose]
        exact (hle σ k i).trans (le_max_right _ _)
  refine ⟨𝒮, h1, fun L hL hsd => ?_, h3, fun ℓ M hf hℓ hd hr hfℓ hM0 hM => ?_⟩
  · obtain ⟨L₀, hL₀, γ, hγ, hm⟩ := h2 L ⟨hL, hsd⟩
    refine ⟨L₀, hL₀, γ, fun x y => by rw [← herm_transpose, hγ, herm_transpose], hm, ?_⟩
    ext x
    constructor
    · intro hx
      have h : (γ : Matrix (Fin r) (Fin r) K) *ᵥ
          (((γ⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) *ᵥ x) = x := by
        rw [mulVec_mulVec, Units.mul_inv, one_mulVec]
      exact ⟨_, (hm _).2 (h.symm ▸ hx), h⟩
    · rintro ⟨y, hy, rfl⟩
      exact (hm y).1 hy
  · have h : M ^ (2 * fdeg K * r ^ 2) * 𝒮.card ≤ Real.exp (20 * (fdeg K * r * ℓ) ^ 2) :=
      le_trans (mul_le_mul_of_nonneg_left h3 (by positivity))
        (pow_mul_bound_le_exp (fdeg K) r (d := dE K) hf hℓ (abs_nonneg _) hd hr hfℓ hM0.le hM)
    refine ⟨h, ?_⟩
    have h0 := sq_nonneg (fdeg K * r * ℓ)
    rcases (show 0 ≤ M ^ (2 * fdeg K * r ^ 2) * 𝒮.card by positivity).eq_or_lt with h' | h'
    · rw [← h', Real.log_zero]
      positivity
    · linarith [(Real.log_le_iff_le_exp h').2 h]

/- English proof (translation)
Establish `hsw : ∀ x y, IsIntegralElt ((hermFormOf G hG).h x y) ↔ IsIntegral ℤ (herm G x y)`. Introduce `x y`. Rewrite using `[← hermFormOf_h G hG, ← isIntegralElt_iff]`. Apply the tactic sequence `constructor <;> intro h <;> rw [wa_symm] <;> exact SemiPt.isIntegralElt_c _ h`. Establish `hsd : ∀ L : Submodule (𝓞 K) (Fin r → K), IsSelfDual (hermFormOf G hG) L ↔ (∀ x ∈ L, ∀ y ∈ L, IsIntegral ℤ (herm G x y)) ∧ ∀ x, (∀ y ∈ L, IsIntegral ℤ (herm G x y)) → x ∈ L` using `fun L => by`.

Simplify using `only [IsSelfDual, IsIntegralOn, hsw]`. Take `⟨𝒮, h1, h2, h3⟩` from `exists_finset_selfDual_classes (hermFormOf G hG)`. Use `⟨𝒮, fun L hL => ⟨(h1 L hL).1, (hsd L).1 (h1 L hL).2⟩, fun L a b c => ?_, h3⟩` and prove the remaining obligations. Take `⟨L₀, hL₀, γ, hγ, hm, -⟩` from `h2 L a ((hsd L).2 ⟨b, c⟩)`. Conclude with `⟨L₀, hL₀, γ, fun x y => by rw [← hermFormOf_h G hG, hγ, hermFormOf_h], hm⟩`.
-/
theorem exists_finset_selfDual_classes_herm (G : Matrix (Fin r) (Fin r) K)
    (hG : ∀ a b, cc (G a b) = G b a) :
    ∃ 𝒮 : Finset (Submodule (𝓞 K) (Fin r → K)),
      (∀ L ∈ 𝒮, IsLattice L ∧ (∀ x ∈ L, ∀ y ∈ L, IsIntegral ℤ (herm G x y)) ∧
        ∀ x, (∀ y ∈ L, IsIntegral ℤ (herm G x y)) → x ∈ L) ∧
      (∀ L, IsLattice L → (∀ x ∈ L, ∀ y ∈ L, IsIntegral ℤ (herm G x y)) →
        (∀ x, (∀ y ∈ L, IsIntegral ℤ (herm G x y)) → x ∈ L) → ∃ L₀ ∈ 𝒮, ∃ γ : GL (Fin r) K,
        (∀ x y, herm G ((γ : Matrix (Fin r) (Fin r) K) *ᵥ x)
          ((γ : Matrix (Fin r) (Fin r) K) *ᵥ y) = herm G x y) ∧
        ∀ x, x ∈ L₀ ↔ (γ : Matrix (Fin r) (Fin r) K) *ᵥ x ∈ L) ∧
      (𝒮.card : ℝ) ≤
        (1 + 2 * max 1 ((2 * fdeg K * r : ℝ) ^ 4 * dE K ^ 2 / (4 * fdeg K))) ^
            (2 * fdeg K * r ^ 2) *
          (r * max 1 ((2 * fdeg K * r : ℝ) ^ 4 * dE K ^ 2 / (4 * fdeg K))) ^
            (2 * fdeg K * r ^ 2) ∧
      ∀ ℓ M : ℝ, 16 ≤ fdeg K → 2 ≤ ℓ → Real.log (dE K) ≤ 4 * fdeg K * ℓ → Real.log r ≤ ℓ →
        Real.log (fdeg K) ≤ 2 * ℓ → 0 < M → Real.log M ≤ 30 * ℓ →
        M ^ (2 * fdeg K * r ^ 2) * 𝒮.card ≤ Real.exp (20 * (fdeg K * r * ℓ) ^ 2) ∧
        Real.log (M ^ (2 * fdeg K * r ^ 2) * 𝒮.card) ≤ 41 * (fdeg K * r * ℓ) ^ 2 := by
  have hsw : ∀ x y, IsIntegralElt ((hermFormOf G hG).h x y) ↔ IsIntegral ℤ (herm G x y) := by
    intro x y
    rw [← hermFormOf_h G hG, ← isIntegralElt_iff]
    constructor <;> intro h <;> rw [wa_symm] <;> exact SemiPt.isIntegralElt_c _ h
  have hsd : ∀ L : Submodule (𝓞 K) (Fin r → K), IsSelfDual (hermFormOf G hG) L ↔
      (∀ x ∈ L, ∀ y ∈ L, IsIntegral ℤ (herm G x y)) ∧
        ∀ x, (∀ y ∈ L, IsIntegral ℤ (herm G x y)) → x ∈ L := fun L => by
    simp only [IsSelfDual, IsIntegralOn, hsw]
  obtain ⟨𝒮, h1, h2, h3⟩ := exists_finset_selfDual_classes (hermFormOf G hG)
  refine ⟨𝒮, fun L hL => ⟨(h1 L hL).1, (hsd L).1 (h1 L hL).2⟩, fun L a b c => ?_, h3⟩
  obtain ⟨L₀, hL₀, γ, hγ, hm, -⟩ := h2 L a ((hsd L).2 ⟨b, c⟩)
  exact ⟨L₀, hL₀, γ, fun x y => by rw [← hermFormOf_h G hG, hγ, hermFormOf_h], hm⟩

noncomputable def hyperbolicHermForm (K : Type) [Field K] [NumberField K] [IsCMField K] :
    HermForm K 2 :=
  hermFormOf !![0, 1; 1, 0] fun a b => by fin_cases a <;> fin_cases b <;> simp [cc]

/- English proof (translation)
Establish `hh : ∀ x y : Fin 2 → K, (hyperbolicHermForm K).h x y = y 0 * cc (x 1) + y 1 * cc (x 0)` using `fun x y => by`. Rewrite using `[hyperbolicHermForm, hermFormOf_h]`. Simplify using `[herm, Fin.sum_univ_two]`. Establish `hc : ∀ {x : K}, IsIntegral ℤ x → IsIntegral ℤ (cc x)` using `TraceDualMin.isIntegral_cc`. Establish `he : ∀ a : Fin 2, (Pi.single a 1 : Fin 2 → K) ∈ intLat K 2` using `fun a => (mem_intLat _).2 fun b => isIntegralElt_iff.2 (by`.

Rewrite using `[Pi.single_apply]`. Use `split_ifs`. Use `exacts [isIntegral_one, isIntegral_zero])`. Use `⟨by simp [hh, cc], ⟨?_, ?_⟩, fun x hx y hy => ?_, fun x hx => ?_⟩` and prove the remaining obligations. Use `Submodule.fg_pi fun _ => ?_` and prove the remaining obligations.

Rewrite using `[Submodule.one_eq_span]`. Conclude with `Submodule.fg_span_singleton 1`. Rewrite using `[eq_top_iff, ← (Pi.basisFun K (Fin 2)).span_eq]`. Use `span_mono ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨a, rfl⟩`.

Rewrite using `[Pi.basisFun_apply]`. Conclude with `he a`. Simplify using `only [mem_intLat, isIntegralElt_iff] at hx hy ⊢`. Rewrite using `[hh]`. Conclude with `((hy 0).mul (hc (hx 1))).add ((hy 1).mul (hc (hx 0)))`.

Establish `h0` using `hc (isIntegralElt_iff.1 (hx _ (he 0)))`. Establish `h1` using `hc (isIntegralElt_iff.1 (hx _ (he 1)))`. Simplify using `only [hh, cc] at h0 h1`. Use `(mem_intLat _).2 fun a => isIntegralElt_iff.2 ?_` and prove the remaining obligations. Use `fin_cases a`.

Simplify using `using h1`. Simplify using `using h0`.
-/
theorem isSelfDual_hyperbolicHermForm :
    (hyperbolicHermForm K).h ![1, 0] ![1, 0] = 0 ∧ IsLattice (intLat K 2) ∧
      IsSelfDual (hyperbolicHermForm K) (intLat K 2) := by
  have hh : ∀ x y : Fin 2 → K,
      (hyperbolicHermForm K).h x y = y 0 * cc (x 1) + y 1 * cc (x 0) := fun x y => by
    rw [hyperbolicHermForm, hermFormOf_h]
    simp [herm, Fin.sum_univ_two]
  have hc : ∀ {x : K}, IsIntegral ℤ x → IsIntegral ℤ (cc x) := TraceDualMin.isIntegral_cc
  have he : ∀ a : Fin 2, (Pi.single a 1 : Fin 2 → K) ∈ intLat K 2 := fun a =>
    (mem_intLat _).2 fun b => isIntegralElt_iff.2 (by
      rw [Pi.single_apply]
      split_ifs
      exacts [isIntegral_one, isIntegral_zero])
  refine ⟨by simp [hh, cc], ⟨?_, ?_⟩, fun x hx y hy => ?_, fun x hx => ?_⟩
  · refine Submodule.fg_pi fun _ => ?_
    rw [Submodule.one_eq_span]
    exact Submodule.fg_span_singleton 1
  · rw [eq_top_iff, ← (Pi.basisFun K (Fin 2)).span_eq]
    refine span_mono ?_
    rintro _ ⟨a, rfl⟩
    rw [Pi.basisFun_apply]
    exact he a
  · simp only [mem_intLat, isIntegralElt_iff] at hx hy ⊢
    rw [hh]
    exact ((hy 0).mul (hc (hx 1))).add ((hy 1).mul (hc (hx 0)))
  · have h0 := hc (isIntegralElt_iff.1 (hx _ (he 0)))
    have h1 := hc (isIntegralElt_iff.1 (hx _ (he 1)))
    simp only [hh, cc] at h0 h1
    refine (mem_intLat _).2 fun a => isIntegralElt_iff.2 ?_
    fin_cases a
    · simpa using h1
    · simpa using h0

end GlobalTheory
