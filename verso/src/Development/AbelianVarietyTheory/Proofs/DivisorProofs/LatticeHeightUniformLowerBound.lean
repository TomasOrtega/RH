import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLineReps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeVectorContentIdealNormProductStatement
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.EisMidHt.LowBd

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}

/- English proof (translation)
Use `⟨∑ k, ∑ j, ‖N k j‖ ^ 2 + 1, by positivity, fun t i => ?_⟩` and prove the remaining obligations. Establish `ht : t = N *ᵥ (M *ᵥ t)` using `by rw [Matrix.mulVec_mulVec, hNM, Matrix.one_mulVec]`. Establish `h1 : ‖t i‖ ≤ ∑ j, ‖N i j‖ * ‖(M *ᵥ t) j‖` using `by conv_lhs => rw [ht]`. Simplify using `only [Matrix.mulVec, dotProduct]`. Use `(norm_sum_le _ _).trans (le_of_eq ?_)` and prove the remaining obligations.

Simplify using `[norm_mul]`. Establish `h2` using `Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => ‖N i j‖) (fun j => ‖(M *ᵥ t) j‖)`. Establish `h3 : ∑ j, ‖N i j‖ ^ 2 ≤ ∑ k, ∑ j, ‖N k j‖ ^ 2 + 1`. Use `Finset.single_le_sum (f := fun k => ∑ j, ‖N k j‖ ^ 2) (fun k _ => by positivity) (Finset.mem_univ i)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem sq_le_of_left_inv (M N : Matrix (Fin n) (Fin n) ℂ) (hNM : N * M = 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : Fin n → ℂ) (i : Fin n), ‖t i‖ ^ 2 ≤ C * ∑ j, ‖(M *ᵥ t) j‖ ^ 2 := by
  refine ⟨∑ k, ∑ j, ‖N k j‖ ^ 2 + 1, by positivity, fun t i => ?_⟩
  have ht : t = N *ᵥ (M *ᵥ t) := by rw [Matrix.mulVec_mulVec, hNM, Matrix.one_mulVec]
  have h1 : ‖t i‖ ≤ ∑ j, ‖N i j‖ * ‖(M *ᵥ t) j‖ := by
    conv_lhs => rw [ht]
    simp only [Matrix.mulVec, dotProduct]
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    simp [norm_mul]
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => ‖N i j‖) (fun j => ‖(M *ᵥ t) j‖)
  have h3 : ∑ j, ‖N i j‖ ^ 2 ≤ ∑ k, ∑ j, ‖N k j‖ ^ 2 + 1 := by
    have := Finset.single_le_sum (f := fun k => ∑ j, ‖N k j‖ ^ 2) (fun k _ => by positivity) (Finset.mem_univ i)
    linarith
  calc ‖t i‖ ^ 2 ≤ (∑ j, ‖N i j‖ * ‖(M *ᵥ t) j‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ (∑ j, ‖N i j‖ ^ 2) * ∑ j, ‖(M *ᵥ t) j‖ ^ 2 := h2
    _ ≤ _ := mul_le_mul_of_nonneg_right h3 (by positivity)

/- English proof (translation)
Establish `h1` using `congrArg (infEmb τ) (GlobalTheory.Doubling.algebraMap_norm_eq h x)`. Rewrite `h1` using `[Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, infEmb_tmul, map_one, mul_one, map_mul, ← infEmb_sigR h τ, Complex.mul_conj']`. Rewrite using `[h1]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem extEmb_norm (h : IsCMExt F E σ) {w : InfinitePlace F} (τ : EmbOver E w) (x : w.Completion ⊗[F] E) :
    InfinitePlace.Completion.extensionEmbedding w (Algebra.norm w.Completion x) = ((‖infEmb τ x‖ ^ 2 : ℝ) : ℂ) := by
  have h1 := congrArg (infEmb τ) (GlobalTheory.Doubling.algebraMap_norm_eq h x)
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, infEmb_tmul, map_one, mul_one, map_mul,
    ← infEmb_sigR h τ, Complex.mul_conj'] at h1
  rw [h1]; push_cast; ring

/- English proof (translation)
Rewrite using `[← (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _), map_sum]`. Simplify using `only [extEmb_norm h τ]`. Rewrite using `[← Complex.ofReal_sum, Complex.norm_of_nonneg (Finset.sum_nonneg fun i _ => by positivity)]`.
-/
theorem norm_sum_norm (h : IsCMExt F E σ) {w : InfinitePlace F} (τ : EmbOver E w)
    (z : Fin n → w.Completion ⊗[F] E) :
    ‖∑ i, Algebra.norm w.Completion (z i)‖ = ∑ i, ‖infEmb τ (z i)‖ ^ 2 := by
  rw [← (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _), map_sum]
  simp only [extEmb_norm h τ]
  rw [← Complex.ofReal_sum, Complex.norm_of_nonneg (Finset.sum_nonneg fun i _ => by positivity)]

/- English proof (translation)
Simplify using `[adVec, inclR, compInf, infEmb_tmul]`.
-/
theorem infEmb_compInf_adVec {w : InfinitePlace F} (τ : EmbOver E w) (y : Fin n → E) (k : Fin n) :
    infEmb τ (compInf F E w (adVec F y k)) = τ.1 (y k) := by
  simp [adVec, inclR, compInf, infEmb_tmul]

/- English proof (translation)
Use `h.1` as an intermediate fact. Rewrite using `[InfinitePlace.mult, if_pos (IsTotallyReal.isReal w)]`.
-/
theorem mult_eq_one (h : IsCMExt F E σ) (w : InfinitePlace F) : w.mult = 1 := by
  have := h.1
  rw [InfinitePlace.mult, if_pos (IsTotallyReal.isReal w)]

/- English proof (translation)
Simplify using `only [normInf]`. Rewrite using `[mult_eq_one h w, pow_one, norm_sum_norm h τ]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[RingHom.map_mulVec]`. Use `congr 3`.

Use function extensionality and compare the values at `k`. Conclude with `infEmb_compInf_adVec τ y k`.
-/
theorem normInf_adVec_eq (h : IsCMExt F E σ) (a : GL (Fin n) (AF F ⊗[F] E)) (w : InfinitePlace F)
    (τ : EmbOver E w) (y : Fin n → E) :
    normInf a w (fun i => compInf F E w (adVec F y i)) =
      ∑ j, ‖((((Formalism.UG.bc (compInf F E w) a)⁻¹ : GL (Fin n) (w.Completion ⊗[F] E)).1.map (infEmb τ)) *ᵥ
        fun k => τ.1 (y k)) j‖ ^ 2 := by
  simp only [normInf]
  rw [mult_eq_one h w, pow_one, norm_sum_norm h τ]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [RingHom.map_mulVec]
  congr 3
  funext k; exact infEmb_compInf_adVec τ y k

/- English proof (translation)
Establish `e1 : infEmb τ (inclR (F` using `F) w.Completion x) = τ.1 x := by simp [inclR, infEmb_tmul]`. Establish `e2 : InfinitePlace.Completion.extensionEmbedding w (algebraMap F w.Completion (Algebra.norm F x)) = w.embedding (Algebra.norm F x)` using `InfinitePlace.Completion.extensionEmbedding_coe w ((WithAbs.equiv w.1).symm _)`. Establish `h1` using `extEmb_norm h τ (inclR (F := F) w.Completion x)`. Rewrite `h1` using `[GlobalTheory.Doubling.norm_inclR, e2, e1]`. Establish `h2` using `congrArg norm h1`.

Rewrite `h2` using `[InfinitePlace.norm_embedding_eq, Complex.norm_of_nonneg (by positivity)]`. Then use the resulting hypothesis.
-/
theorem place_norm_eq (h : IsCMExt F E σ) {w : InfinitePlace F} (τ : EmbOver E w) (x : E) :
    w (Algebra.norm F x) = ‖τ.1 x‖ ^ 2 := by
  have e1 : infEmb τ (inclR (F := F) w.Completion x) = τ.1 x := by simp [inclR, infEmb_tmul]
  have e2 : InfinitePlace.Completion.extensionEmbedding w (algebraMap F w.Completion (Algebra.norm F x)) =
      w.embedding (Algebra.norm F x) := InfinitePlace.Completion.extensionEmbedding_coe w ((WithAbs.equiv w.1).symm _)
  have h1 := extEmb_norm h τ (inclR (F := F) w.Completion x)
  rw [GlobalTheory.Doubling.norm_inclR, e2, e1] at h1
  have h2 := congrArg norm h1
  rwa [InfinitePlace.norm_embedding_eq, Complex.norm_of_nonneg (by positivity)] at h2

/- English proof (translation)
Take `⟨τ⟩ : Nonempty (EmbOver E w)` from `inferInstance`. Use `set b : GL (Fin n) (w.Completion ⊗[F] E) := (Formalism.UG.bc (compInf F E w) a)⁻¹ with hb`. Take `⟨C, hC, hCb⟩` from `sq_le_of_left_inv (b.1.map (infEmb τ)) ((b⁻¹ : GL (Fin n) _).1.map (infEmb τ)) (by`. Rewrite using `[← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)])`. Use `⟨C⁻¹, inv_pos.2 hC, fun y i => ?_⟩` and prove the remaining obligations.

Rewrite using `[normInf_adVec_eq h a w τ y, place_norm_eq h τ, inv_mul_le_iff₀ hC]`. Conclude with `hCb (fun k => τ.1 (y k)) i`.
-/
theorem normInf_lower (h : IsCMExt F E σ) (a : GL (Fin n) (AF F ⊗[F] E)) (w : InfinitePlace F) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (y : Fin n → E) (i : Fin n),
      κ * w (Algebra.norm F (y i)) ≤ normInf a w (fun j => compInf F E w (adVec F y j)) := by
  obtain ⟨τ⟩ : Nonempty (EmbOver E w) := inferInstance
  set b : GL (Fin n) (w.Completion ⊗[F] E) := (Formalism.UG.bc (compInf F E w) a)⁻¹ with hb
  obtain ⟨C, hC, hCb⟩ := sq_le_of_left_inv (b.1.map (infEmb τ)) ((b⁻¹ : GL (Fin n) _).1.map (infEmb τ)) (by
    rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)])
  refine ⟨C⁻¹, inv_pos.2 hC, fun y i => ?_⟩
  rw [normInf_adVec_eq h a w τ y, place_norm_eq h τ, inv_mul_le_iff₀ hC]
  exact hCb (fun k => τ.1 (y k)) i

/- English proof (translation)
Use `InfinitePlace.prod_eq_abs_norm (Algebra.norm F x)` as an intermediate fact. Simplify using `only [mult_eq_one h, pow_one] at this`. Rewrite using `[this, Algebra.norm_norm]`. Use `push_cast`. Both sides reduce to the same expression.
-/
theorem prod_place_norm (h : IsCMExt F E σ) (x : E) :
    ∏ w : InfinitePlace F, w (Algebra.norm F x) = |((Algebra.norm ℚ x : ℚ) : ℝ)| := by
  have := InfinitePlace.prod_eq_abs_norm (Algebra.norm F x)
  simp only [mult_eq_one h, pow_one] at this
  rw [this, Algebra.norm_norm]
  push_cast; rfl

end GlobalTheory.EisMidHt.LowBd

namespace GlobalTheory.EisMidHt.LowBd

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}

/- English proof (translation)
Take `⟨S, rfl⟩` from `hL`. Take `⟨⟨d, hd⟩, hds⟩` from `IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 E)) (S.biUnion fun l => Finset.univ.image fun i => l i)`. Use `⟨d, nonZeroDivisors.ne_zero hd, fun l hl => ?_⟩` and prove the remaining obligations. Proceed by induction on `hl using Submodule.span_induction with`. Consider the case `mem l hl`.

Introduce `i`. Take `⟨z, hz⟩` from `hds (l i) (Finset.mem_biUnion.2 ⟨l, hl, Finset.mem_image_of_mem _ (Finset.mem_univ i)⟩)`. Conclude with `⟨z, hz.trans (Algebra.smul_def _ _)⟩`. Consider the case `zero => intro i; exact ⟨0, by simp⟩`. Consider the case `add x y _ _ hx hy`.

Introduce `i`. Take `⟨z, hz⟩` from `hx i`. Take `⟨z', hz'⟩` from `hy i`. Conclude with `⟨z + z', by rw [map_add, hz, hz', Pi.add_apply, mul_add]⟩`. Consider the case `smul r x _ hx`.

Introduce `i`. Take `⟨z, hz⟩` from `hx i`. Use `⟨r * z, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, hz, Pi.smul_apply, Algebra.smul_def]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_den (L : Submodule (𝓞 E) (Fin n → E)) (hL : L.FG) :
    ∃ d : 𝓞 E, d ≠ 0 ∧ ∀ l ∈ L, ∀ i, ∃ z : 𝓞 E, algebraMap (𝓞 E) E z = (d : E) * l i := by
  classical
  obtain ⟨S, rfl⟩ := hL
  obtain ⟨⟨d, hd⟩, hds⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 E))
    (S.biUnion fun l => Finset.univ.image fun i => l i)
  refine ⟨d, nonZeroDivisors.ne_zero hd, fun l hl => ?_⟩
  induction hl using Submodule.span_induction with
  | mem l hl =>
    intro i
    obtain ⟨z, hz⟩ := hds (l i) (Finset.mem_biUnion.2 ⟨l, hl, Finset.mem_image_of_mem _ (Finset.mem_univ i)⟩)
    exact ⟨z, hz.trans (Algebra.smul_def _ _)⟩
  | zero => intro i; exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    intro i
    obtain ⟨z, hz⟩ := hx i
    obtain ⟨z', hz'⟩ := hy i
    exact ⟨z + z', by rw [map_add, hz, hz', Pi.add_apply, mul_add]⟩
  | smul r x _ hx =>
    intro i
    obtain ⟨z, hz⟩ := hx i
    refine ⟨r * z, ?_⟩
    rw [map_mul, hz, Pi.smul_apply, Algebra.smul_def]
    ring

/- English proof (translation)
Use `set J := FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) ((d : E) * y i) * I with hJ`. Establish `hle : J ≤ 1`. Rewrite using `[hJ, FractionalIdeal.mul_le]`. Introduce `p hp q hq`. Take `⟨r, rfl⟩` from `(FractionalIdeal.mem_spanSingleton _).1 hp`.

Take `⟨z, hz⟩` from `hd _ ((hI q).1 hq) i`. Rewrite using `[FractionalIdeal.mem_one_iff]`. Use `⟨r * z, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, hz, Pi.smul_apply, smul_eq_mul, Algebra.smul_def]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hd' : (d : E) ≠ 0` using `by exact_mod_cast hd0`. Establish `hJ0 : J ≠ 0` using `mul_ne_zero (by`. Rewrite using `[Ne, FractionalIdeal.spanSingleton_eq_zero_iff]`. Conclude with `mul_ne_zero hd' hi) hI0`. Take `⟨J₀, hJ₀⟩` from `FractionalIdeal.le_one_iff_exists_coeIdeal.1 hle`.

Establish `hJ₀0 : J₀ ≠ ⊥`. Introduce and unpack `rfl`. Apply `hJ0` to reduce the goal to its premises. Rewrite using `[← hJ₀, FractionalIdeal.coeIdeal_bot]`. Establish `h1 : (1 : ℚ) ≤ FractionalIdeal.absNorm J`.

Rewrite using `[← hJ₀, FractionalIdeal.coeIdeal_absNorm]`. Conclude with `Nat.one_le_iff_ne_zero.2 (mt Ideal.absNorm_eq_zero_iff.1 hJ₀0)` after adjusting the coercions. Rewrite `h1` using `[hJ, map_mul, FractionalIdeal.absNorm_span_singleton, map_mul, abs_mul]`. Conclude with `h1` after adjusting the coercions.
-/
theorem absNorm_lower {L : Submodule (𝓞 E) (Fin n → E)} {d : 𝓞 E}
    (hd : ∀ l ∈ L, ∀ i, ∃ z : 𝓞 E, algebraMap (𝓞 E) E z = (d : E) * l i) (hd0 : d ≠ 0)
    {y : Fin n → E} {i : Fin n} (hi : y i ≠ 0) {I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E} (hI0 : I ≠ 0)
    (hI : ∀ c : E, c ∈ I ↔ c • y ∈ L) :
    1 ≤ |((Algebra.norm ℚ (d : E) : ℚ) : ℝ)| * |((Algebra.norm ℚ (y i) : ℚ) : ℝ)| * (FractionalIdeal.absNorm I : ℝ) := by
  set J := FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) ((d : E) * y i) * I with hJ
  have hle : J ≤ 1 := by
    rw [hJ, FractionalIdeal.mul_le]
    intro p hp q hq
    obtain ⟨r, rfl⟩ := (FractionalIdeal.mem_spanSingleton _).1 hp
    obtain ⟨z, hz⟩ := hd _ ((hI q).1 hq) i
    rw [FractionalIdeal.mem_one_iff]
    refine ⟨r * z, ?_⟩
    rw [map_mul, hz, Pi.smul_apply, smul_eq_mul, Algebra.smul_def]
    ring
  have hd' : (d : E) ≠ 0 := by exact_mod_cast hd0
  have hJ0 : J ≠ 0 := mul_ne_zero (by
    rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]; exact mul_ne_zero hd' hi) hI0
  obtain ⟨J₀, hJ₀⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.1 hle
  have hJ₀0 : J₀ ≠ ⊥ := by
    rintro rfl; apply hJ0; rw [← hJ₀, FractionalIdeal.coeIdeal_bot]
  have h1 : (1 : ℚ) ≤ FractionalIdeal.absNorm J := by
    rw [← hJ₀, FractionalIdeal.coeIdeal_absNorm]
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (mt Ideal.absNorm_eq_zero_iff.1 hJ₀0)
  rw [hJ, map_mul, FractionalIdeal.absNorm_span_singleton, map_mul, abs_mul] at h1
  exact_mod_cast h1

end GlobalTheory.EisMidHt.LowBd

open GlobalTheory.EisMidHt.LowBd in

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ n L a h hL`. Take `⟨d, hd0, hd⟩` from `exists_den L hL.fg`. Use `choose κ hκ hκb using fun w => normInf_lower h a w`. Establish `hK : 0 < ∏ w, κ w` using `Finset.prod_pos fun w _ => hκ w`. Establish `hd' : (d : E) ≠ 0` using `by exact_mod_cast hd0`.

Establish `hNd : 0 < |((Algebra.norm ℚ (d : E) : ℚ) : ℝ)|` using `abs_pos.2 (by exact_mod_cast (Algebra.norm_ne_zero_iff.2 hd'))`. Use `⟨(∏ w, κ w) / |((Algebra.norm ℚ (d : E) : ℚ) : ℝ)|, div_pos hK hNd, fun y hy => ?_, fun y hy w => ?_⟩` and prove the remaining obligations. Take `⟨i, hi⟩` from `Function.ne_iff.1 hy`. Take `⟨I, hI0, hI, hfin⟩` from `GlobalTheory.T.lattice_vector_content_ideal_norm_product F E n L hL y hy`. Establish `h1` using `absNorm_lower hd hd0 hi hI0 hI`.

Establish `h2 : (∏ w, κ w) * |((Algebra.norm ℚ (y i) : ℚ) : ℝ)| ≤ ∏ w, normInf a w (fun j => compInf F E w (adVec F y j))`. Rewrite using `[← prod_place_norm h (y i), ← Finset.prod_mul_distrib]`. Conclude with `Finset.prod_le_prod (fun w _ => mul_nonneg (hκ w).le (by positivity)) fun w _ => hκb w y i`. Establish `hIpos : 0 < (FractionalIdeal.absNorm I : ℝ)`. Assume the negation of the conclusion as `hneg`.

Use `push_neg at hneg`. Establish `: |((Algebra.norm ℚ (d : E) : ℚ) : ℝ)| * |((Algebra.norm ℚ (y i) : ℚ) : ℝ)| * (FractionalIdeal.absNorm I : ℝ) ≤ 0` using `mul_nonpos_of_nonneg_of_nonpos (by positivity) hneg`. Combine the linear equalities and inequalities to obtain the conclusion. Unfold `ht`. Rewrite using `[hfin, div_le_iff₀ hNd]`.

Combine the equalities or inequalities in the displayed calculation. Take `⟨i, hi⟩` from `Function.ne_iff.1 hy`. Establish `hw : 0 < w (Algebra.norm F (y i))`. Rewrite using `[InfinitePlace.pos_iff]`. Conclude with `Algebra.norm_ne_zero_iff.2 hi`.

Conclude with `(mul_pos (hκ w) hw).trans_le (hκb w y i)`.
-/
theorem GlobalTheory.EisMidHt.ht_adVec_lower_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)), IsCMExt F E σ → Submodule.IsLattice E L →
      ∃ δ : ℝ, 0 < δ ∧ (∀ y : Fin n → E, y ≠ 0 → δ ≤ GlobalTheory.EisMidHt.ht L a (GlobalTheory.EisMidHt.adVec F y)) ∧
        ∀ y : Fin n → E, y ≠ 0 → ∀ w : InfinitePlace F,
          0 < GlobalTheory.EisMidHt.normInf a w (fun i => compInf F E w (GlobalTheory.EisMidHt.adVec F y i)) := by
  intro F E _ _ _ _ _ σ n L a h hL
  obtain ⟨d, hd0, hd⟩ := exists_den L hL.fg
  choose κ hκ hκb using fun w => normInf_lower h a w
  have hK : 0 < ∏ w, κ w := Finset.prod_pos fun w _ => hκ w
  have hd' : (d : E) ≠ 0 := by exact_mod_cast hd0
  have hNd : 0 < |((Algebra.norm ℚ (d : E) : ℚ) : ℝ)| :=
    abs_pos.2 (by exact_mod_cast (Algebra.norm_ne_zero_iff.2 hd'))
  refine ⟨(∏ w, κ w) / |((Algebra.norm ℚ (d : E) : ℚ) : ℝ)|, div_pos hK hNd, fun y hy => ?_, fun y hy w => ?_⟩
  · obtain ⟨i, hi⟩ := Function.ne_iff.1 hy
    obtain ⟨I, hI0, hI, hfin⟩ := GlobalTheory.T.lattice_vector_content_ideal_norm_product F E n L hL y hy
    have h1 := absNorm_lower hd hd0 hi hI0 hI
    have h2 : (∏ w, κ w) * |((Algebra.norm ℚ (y i) : ℚ) : ℝ)| ≤
        ∏ w, normInf a w (fun j => compInf F E w (adVec F y j)) := by
      rw [← prod_place_norm h (y i), ← Finset.prod_mul_distrib]
      exact Finset.prod_le_prod (fun w _ => mul_nonneg (hκ w).le (by positivity)) fun w _ => hκb w y i
    have hIpos : 0 < (FractionalIdeal.absNorm I : ℝ) := by
      by_contra hneg
      push_neg at hneg
      have : |((Algebra.norm ℚ (d : E) : ℚ) : ℝ)| * |((Algebra.norm ℚ (y i) : ℚ) : ℝ)| *
          (FractionalIdeal.absNorm I : ℝ) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) hneg
      linarith
    unfold ht
    rw [hfin, div_le_iff₀ hNd]
    calc (∏ w, κ w) ≤ (∏ w, κ w) * (|((Algebra.norm ℚ (d : E) : ℚ) : ℝ)| * |((Algebra.norm ℚ (y i) : ℚ) : ℝ)| *
          (FractionalIdeal.absNorm I : ℝ)) := le_mul_of_one_le_right hK.le h1
      _ = (∏ w, κ w) * |((Algebra.norm ℚ (y i) : ℚ) : ℝ)| * (FractionalIdeal.absNorm I : ℝ) *
          |((Algebra.norm ℚ (d : E) : ℚ) : ℝ)| := by ring
      _ ≤ (∏ w, normInf a w (fun j => compInf F E w (adVec F y j))) * (FractionalIdeal.absNorm I : ℝ) *
          |((Algebra.norm ℚ (d : E) : ℚ) : ℝ)| := by gcongr
      _ = _ := by ring
  · obtain ⟨i, hi⟩ := Function.ne_iff.1 hy
    have hw : 0 < w (Algebra.norm F (y i)) := by
      rw [InfinitePlace.pos_iff]; exact Algebra.norm_ne_zero_iff.2 hi
    exact (mul_pos (hκ w) hw).trans_le (hκb w y i)
