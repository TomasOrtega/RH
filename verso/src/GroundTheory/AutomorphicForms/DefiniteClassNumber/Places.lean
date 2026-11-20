import Mathlib
import GroundTheory.AutomorphicForms.DefiniteClassNumber.HermTraceSelfOfHermValue

noncomputable section

namespace GroundTheory.Automorphic

open Module Matrix TensorProduct NumberField NumberField.InfinitePlace

variable {K : Type*} [Field K] [NumberField K]

section TotallyReal

abbrev realEmb (hreal : ∀ w : InfinitePlace K, w.IsReal) (w : InfinitePlace K) : K →+* ℝ :=
  embedding_of_isReal (hreal w)

omit [NumberField K] in
/- English proof (translation)
Rewrite using `[Completion.algebraMap_apply]`. Conclude with `Completion.extensionEmbeddingOfIsReal_coe (hreal w) _`.
-/
theorem realEmb_eq_extension (hreal : ∀ w : InfinitePlace K, w.IsReal) (w : InfinitePlace K)
    (k : K) : Completion.extensionEmbeddingOfIsReal (hreal w) (algebraMap K w.Completion k) =
      realEmb hreal w k := by
  rw [Completion.algebraMap_apply]
  exact Completion.extensionEmbeddingOfIsReal_coe (hreal w) _

def embeddingsEquivPlaces (hreal : ∀ w : InfinitePlace K, w.IsReal) :
    (K →+* ℂ) ≃ InfinitePlace K where
  toFun := InfinitePlace.mk
  invFun w := w.embedding
  left_inv φ := by
    show (InfinitePlace.mk φ).embedding = φ
    rcases embedding_mk_eq φ with h | h
    · exact h
    · have hr := isReal_iff.1 (hreal (InfinitePlace.mk φ))
      rw [ComplexEmbedding.isReal_iff, h] at hr
      have hφ : ComplexEmbedding.conjugate (ComplexEmbedding.conjugate φ) = φ := star_star φ
      rw [h]
      exact hr.symm.trans hφ
  right_inv w := mk_embedding w

/- English proof (translation)
Establish `h1` using `trace_eq_sum_embeddings ℂ (K := ℚ) (L := K) (x := t)`. Establish `h2 : ∑ σ : K →ₐ[ℚ] ℂ, σ t = ∑ φ : K →+* ℂ, φ t` using `(Fintype.sum_equiv (RingHom.equivRatAlgHom K ℂ) _ _ fun φ => rfl).symm`. Establish `h3 : ∑ φ : K →+* ℂ, φ t = ∑ w : InfinitePlace K, w.embedding t` using `Fintype.sum_equiv (embeddingsEquivPlaces hreal) _ _ fun φ => by`. Use `(embeddingsEquivPlaces hreal).left_inv φ` as an intermediate fact. Conclude with `(congrFun (congrArg DFunLike.coe this) t).symm`.

Apply `Complex.ofReal_injective` to reduce the goal to its premises. Rewrite using `[Complex.ofReal_ratCast, ← eq_ratCast (algebraMap ℚ ℂ), h1, h2, h3, Complex.ofReal_sum]`. Conclude with `Finset.sum_congr rfl fun w _ => (embedding_of_isReal_apply (hreal w) t).symm`.
-/
theorem trace_eq_sum_realEmb (hreal : ∀ w : InfinitePlace K, w.IsReal) (t : K) :
    (Algebra.trace ℚ K t : ℝ) = ∑ w, realEmb hreal w t := by
  have h1 := trace_eq_sum_embeddings ℂ (K := ℚ) (L := K) (x := t)
  have h2 : ∑ σ : K →ₐ[ℚ] ℂ, σ t = ∑ φ : K →+* ℂ, φ t :=
    (Fintype.sum_equiv (RingHom.equivRatAlgHom K ℂ) _ _ fun φ => rfl).symm
  have h3 : ∑ φ : K →+* ℂ, φ t = ∑ w : InfinitePlace K, w.embedding t :=
    Fintype.sum_equiv (embeddingsEquivPlaces hreal) _ _ fun φ => by
      have := (embeddingsEquivPlaces hreal).left_inv φ
      exact (congrFun (congrArg DFunLike.coe this) t).symm
  apply Complex.ofReal_injective
  rw [Complex.ofReal_ratCast, ← eq_ratCast (algebraMap ℚ ℂ), h1, h2, h3, Complex.ofReal_sum]
  exact Finset.sum_congr rfl fun w _ => (embedding_of_isReal_apply (hreal w) t).symm

/- English proof (translation)
Set `ψ` to `fun w : InfinitePlace K => Completion.ringEquivRealOfIsReal (hreal w)`. Establish `hψc : ∀ w, Continuous (Completion.extensionEmbeddingOfIsReal (hreal w))` using `fun w => (Completion.isometry_extensionEmbeddingOfIsReal (hreal w)).continuous`. Set `U : Set (InfiniteAdeleRing K)` to `⋂ w, {q | 0 < ε w * Completion.extensionEmbeddingOfIsReal (hreal w) (q w)}`. Establish `hU : IsOpen U` using `isOpen_iInter_of_finite fun w => isOpen_lt continuous_const (continuous_const.mul ((hψc w).comp (continuous_apply w)))`. Set `p : InfiniteAdeleRing K` to `fun w => (ψ w).symm (ε w)`.

Establish `hp : p ∈ U`. Simplify using `only [U, Set.mem_iInter, Set.mem_ofPred_eq]`. Introduce `w`. Establish `: Completion.extensionEmbeddingOfIsReal (hreal w) (p w) = ε w` using `(ψ w).apply_symm_apply (ε w)`. Rewrite using `[this]`.

Conclude with `mul_self_pos.2 (hε w)`. Take `⟨θ, hθ⟩` from `(InfiniteAdeleRing.denseRange_algebraMap (K := K)).exists_mem_open hU ⟨p, hp⟩`. Use `⟨θ, fun w => ?_⟩` and prove the remaining obligations. Use `Set.mem_iInter.1 hθ w` as an intermediate fact. Simplify using `only [Set.mem_ofPred_eq] at this`.

Rewrite `this` using `[show (algebraMap K (InfiniteAdeleRing K) θ) w = algebraMap K w.Completion θ from rfl, realEmb_eq_extension]`. Then use the resulting hypothesis.
-/
theorem exists_forall_pos_mul_realEmb (hreal : ∀ w : InfinitePlace K, w.IsReal)
    (ε : InfinitePlace K → ℝ) (hε : ∀ w, ε w ≠ 0) :
    ∃ θ : K, ∀ w, 0 < ε w * realEmb hreal w θ := by
  let ψ := fun w : InfinitePlace K => Completion.ringEquivRealOfIsReal (hreal w)
  have hψc : ∀ w, Continuous (Completion.extensionEmbeddingOfIsReal (hreal w)) := fun w =>
    (Completion.isometry_extensionEmbeddingOfIsReal (hreal w)).continuous
  let U : Set (InfiniteAdeleRing K) :=
    ⋂ w, {q | 0 < ε w * Completion.extensionEmbeddingOfIsReal (hreal w) (q w)}
  have hU : IsOpen U := isOpen_iInter_of_finite fun w =>
    isOpen_lt continuous_const (continuous_const.mul ((hψc w).comp (continuous_apply w)))
  let p : InfiniteAdeleRing K := fun w => (ψ w).symm (ε w)
  have hp : p ∈ U := by
    simp only [U, Set.mem_iInter, Set.mem_ofPred_eq]
    intro w
    have : Completion.extensionEmbeddingOfIsReal (hreal w) (p w) = ε w :=
      (ψ w).apply_symm_apply (ε w)
    rw [this]
    exact mul_self_pos.2 (hε w)
  obtain ⟨θ, hθ⟩ := (InfiniteAdeleRing.denseRange_algebraMap (K := K)).exists_mem_open hU ⟨p, hp⟩
  refine ⟨θ, fun w => ?_⟩
  have := Set.mem_iInter.1 hθ w
  simp only [Set.mem_ofPred_eq] at this
  rwa [show (algebraMap K (InfiniteAdeleRing K) θ) w = algebraMap K w.Completion θ from rfl,
    realEmb_eq_extension] at this

end TotallyReal

section Form

variable {E : Type*} [CommRing E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι E)
variable {κ : Type*} [Fintype κ] (b : Basis κ K E)

def traceGram : Matrix (ι × κ) (ι × κ) K :=
  fun a c => hermTrace K H K (stdVec K b a) (stdVec K b c)

variable (R : Type*) [CommRing R] [Algebra K R]

def vecOfCoords (c : ι × κ → R) : ι → R ⊗[K] E :=
  fun i => (Algebra.TensorProduct.basis R b).equivFun.symm fun k => c (i, k)

omit [NumberField K] [Algebra.IsQuadraticExtension K E] [Fintype ι] [DecidableEq ι] in
/- English proof (translation)
Use function extensionality and compare the values at `a`. Simplify using `only [vecCoords, vecOfCoords]`. Rewrite using `[← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]`.
-/
theorem vecCoords_vecOfCoords (c : ι × κ → R) : vecCoords R b (vecOfCoords b R c) = c := by
  funext a
  simp only [vecCoords, vecOfCoords]
  rw [← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]

omit [NumberField K] [Algebra.IsQuadraticExtension K E] [Fintype ι] [DecidableEq ι] in
/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `only [vecCoords, vecOfCoords]`. Use `conv_rhs => rw [← (Algebra.TensorProduct.basis R b).equivFun.symm_apply_apply (x i)]`. Both sides reduce to the same expression.
-/
theorem vecOfCoords_vecCoords (x : ι → R ⊗[K] E) : vecOfCoords b R (vecCoords R b x) = x := by
  funext i
  simp only [vecCoords, vecOfCoords]
  conv_rhs => rw [← (Algebra.TensorProduct.basis R b).equivFun.symm_apply_apply (x i)]
  rfl

variable {H b}

omit [NumberField K] in

/- English proof (translation)
The claim follows from `hermTrace_eq_sum H b x y`.
-/
theorem hermTrace_eq_sum_traceGram (x y : ι → R ⊗[K] E) :
    hermTrace K H R x y = ∑ a : ι × κ, ∑ c : ι × κ, vecCoords R b x a * vecCoords R b y c *
      algebraMap K R (traceGram H b a c) :=
  hermTrace_eq_sum H b x y

omit [NumberField K] in

/- English proof (translation)
Set `ψ` to `Completion.ringEquivRealOfIsReal hw`. Establish `key : ∀ v : ι × κ → ℝ, ψ (hermTrace K H w.Completion (vecOfCoords b w.Completion (fun a => ψ.symm (v a))) (vecOfCoords b w.Completion (fun a => ψ.symm (v a)))) = ∑ a, ∑ c, v a * v c * embedding_of_isReal hw (traceGram H b a c)`. Introduce `v`. Rewrite using `[hermTrace_eq_sum_traceGram (H := H) (b := b) w.Completion, vecCoords_vecOfCoords b w.Completion (fun a => ψ.symm (v a)), map_sum]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations.

Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_mul, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]`. Use `congr 1`. Rewrite using `[Completion.ringEquivRealOfIsReal_apply, Completion.algebraMap_apply]`.

Conclude with `Completion.extensionEmbeddingOfIsReal_coe hw _`. Establish `hne : ∀ v : ι × κ → ℝ, v ≠ 0 → vecOfCoords b w.Completion (fun a => ψ.symm (v a)) ≠ 0`. Introduce `v hv h`. Apply `hv` to reduce the goal to its premises. Use function extensionality and compare the values at `a`.

Use `congrFun (vecCoords_vecOfCoords b w.Completion (fun a => ψ.symm (v a))) a` as an intermediate fact. Rewrite `this` using `[h]`. Establish `h0 : vecCoords w.Completion b (0 : ι → w.Completion ⊗[K] E) a = 0`. Simplify using `[vecCoords]`. Rewrite `this` using `[h0]`.

Use `congrArg ψ this` as an intermediate fact. Rewrite `this` using `[RingEquiv.apply_symm_apply, map_zero]`. Conclude with `this.symm`. Break down `hdef with hpos | hneg` into its components or cases. Use `⟨1, one_ne_zero, fun v hv => ?_⟩` and prove the remaining obligations.

Take `⟨t, ht, htpos⟩` from `hpos _ (hne v hv)`. Rewrite using `[one_mul, ← key, hermTrace_self_of_hermValue ht, map_mul, map_ofNat]`. Establish `: ψ t = Completion.extensionEmbeddingOfIsReal hw t` using `rfl`. Rewrite using `[this]`. Check the signs of the components of the expression.

Use `⟨-1, by norm_num, fun v hv => ?_⟩` and prove the remaining obligations. Take `⟨t, ht, htneg⟩` from `hneg _ (hne v hv)`. Rewrite using `[← key, hermTrace_self_of_hermValue ht, map_mul, map_ofNat]`. Establish `: ψ t = Completion.extensionEmbeddingOfIsReal hw t` using `rfl`. Rewrite using `[this]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem exists_sign_traceGram {w : InfinitePlace K} (hw : w.IsReal)
    (hdef : IsHermDefiniteAt H w hw) :
    ∃ ε : ℝ, ε ≠ 0 ∧ ∀ v : ι × κ → ℝ, v ≠ 0 →
      0 < ε * ∑ a, ∑ c, v a * v c * embedding_of_isReal hw (traceGram H b a c) := by
  let ψ := Completion.ringEquivRealOfIsReal hw
  have key : ∀ v : ι × κ → ℝ, ψ (hermTrace K H w.Completion (vecOfCoords b w.Completion
      (fun a => ψ.symm (v a))) (vecOfCoords b w.Completion (fun a => ψ.symm (v a)))) =
      ∑ a, ∑ c, v a * v c * embedding_of_isReal hw (traceGram H b a c) := by
    intro v
    rw [hermTrace_eq_sum_traceGram (H := H) (b := b) w.Completion,
      vecCoords_vecOfCoords b w.Completion (fun a => ψ.symm (v a)), map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [map_mul, map_mul, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
    congr 1
    rw [Completion.ringEquivRealOfIsReal_apply, Completion.algebraMap_apply]
    exact Completion.extensionEmbeddingOfIsReal_coe hw _
  have hne : ∀ v : ι × κ → ℝ, v ≠ 0 →
      vecOfCoords b w.Completion (fun a => ψ.symm (v a)) ≠ 0 := by
    intro v hv h
    apply hv
    funext a
    have := congrFun (vecCoords_vecOfCoords b w.Completion (fun a => ψ.symm (v a))) a
    rw [h] at this
    have h0 : vecCoords w.Completion b (0 : ι → w.Completion ⊗[K] E) a = 0 := by
      simp [vecCoords]
    rw [h0] at this
    have := congrArg ψ this
    rw [RingEquiv.apply_symm_apply, map_zero] at this
    exact this.symm
  rcases hdef with hpos | hneg
  · refine ⟨1, one_ne_zero, fun v hv => ?_⟩
    obtain ⟨t, ht, htpos⟩ := hpos _ (hne v hv)
    rw [one_mul, ← key, hermTrace_self_of_hermValue ht, map_mul, map_ofNat]
    have : ψ t = Completion.extensionEmbeddingOfIsReal hw t := rfl
    rw [this]
    positivity
  · refine ⟨-1, by norm_num, fun v hv => ?_⟩
    obtain ⟨t, ht, htneg⟩ := hneg _ (hne v hv)
    rw [← key, hermTrace_self_of_hermValue ht, map_mul, map_ofNat]
    have : ψ t = Completion.extensionEmbeddingOfIsReal hw t := rfl
    rw [this]
    linarith

/- English proof (translation)
Establish `hreal : ∀ w : InfinitePlace K, w.IsReal` using `fun w => (hdef w).1`. Use `choose ε hε hεpos using fun w => exists_sign_traceGram (b := b) (hdef w).1 (hdef w).2`. Take `⟨θ, hθ⟩` from `exists_forall_pos_mul_realEmb hreal ε hε`. Use `⟨θ, fun w hw v hv => ?_⟩` and prove the remaining obligations. Establish `h1` using `hεpos w v hv`.

Establish `h2` using `hθ w`. Establish `: ∑ a, ∑ c, v a * v c * embedding_of_isReal hw (θ * traceGram H b a c) = realEmb hreal w θ * ∑ a, ∑ c, v a * v c * embedding_of_isReal (hdef w).1 (traceGram H b a c)`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Use `mul_pos h1 h2` as an intermediate fact.

Use polynomial arithmetic with `[sq_nonneg (ε w)]`.
-/
theorem exists_theta_posDef (hdef : ∀ w : InfinitePlace K, ∃ hw : w.IsReal, IsHermDefiniteAt H w hw) :
    ∃ θ : K, ∀ (w : InfinitePlace K) (hw : w.IsReal) (v : ι × κ → ℝ), v ≠ 0 →
      0 < ∑ a, ∑ c, v a * v c * embedding_of_isReal hw (θ * traceGram H b a c) := by
  have hreal : ∀ w : InfinitePlace K, w.IsReal := fun w => (hdef w).1
  choose ε hε hεpos using fun w => exists_sign_traceGram (b := b) (hdef w).1 (hdef w).2
  obtain ⟨θ, hθ⟩ := exists_forall_pos_mul_realEmb hreal ε hε
  refine ⟨θ, fun w hw v hv => ?_⟩
  have h1 := hεpos w v hv
  have h2 := hθ w
  have : ∑ a, ∑ c, v a * v c * embedding_of_isReal hw (θ * traceGram H b a c) =
      realEmb hreal w θ * ∑ a, ∑ c, v a * v c * embedding_of_isReal (hdef w).1 (traceGram H b a c) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [map_mul]
    ring
  rw [this]
  have := mul_pos h1 h2
  nlinarith [sq_nonneg (ε w)]

omit [NumberField K] [Fintype κ] in

/- English proof (translation)
Use extensionality with `a c`. Conclude with `hermTrace_comm hH _ _`.
-/
theorem traceGram_transpose (hH : IsHermitianFor (conjHom K E) H) :
    (traceGram H b)ᵀ = traceGram H b := by
  ext a c
  exact hermTrace_comm hH _ _

/- English proof (translation)
Establish `hv : (fun a => embedding_of_isReal hw (vecCoords K b x a)) ≠ 0`. Introduce `h`. Apply `hx` to reduce the goal to its premises. Rewrite using `[← vecOfCoords_vecCoords b K x]`. Establish `: vecCoords K b x = 0`.

Use function extensionality and compare the values at `a`. Use `congrFun h a` as an intermediate fact. Simplify using `using this`. Rewrite using `[this]`. Use function extensionality and compare the values at `i`.

Simplify using `[vecOfCoords]`. Use `hθ w hw _ hv` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Rewrite using `[hermTrace_eq_sum_traceGram (H := H) (b := b) K, Finset.mul_sum, map_sum]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.mul_sum, map_sum]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[Algebra.algebraMap_self, RingHom.id_apply]`. Simplify using `only [map_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem realEmb_mul_hermTrace_pos {θ : K}
    (hθ : ∀ (w : InfinitePlace K) (hw : w.IsReal) (v : ι × κ → ℝ), v ≠ 0 →
      0 < ∑ a, ∑ c, v a * v c * embedding_of_isReal hw (θ * traceGram H b a c))
    {w : InfinitePlace K} (hw : w.IsReal) {x : ι → K ⊗[K] E} (hx : x ≠ 0) :
    0 < embedding_of_isReal hw (θ * hermTrace K H K x x) := by
  have hv : (fun a => embedding_of_isReal hw (vecCoords K b x a)) ≠ 0 := by
    intro h
    apply hx
    rw [← vecOfCoords_vecCoords b K x]
    have : vecCoords K b x = 0 := by
      funext a
      have := congrFun h a
      simpa using this
    rw [this]
    funext i
    simp [vecOfCoords]
  have := hθ w hw _ hv
  convert this using 1
  rw [hermTrace_eq_sum_traceGram (H := H) (b := b) K, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Algebra.algebraMap_self, RingHom.id_apply]
  simp only [map_mul]
  ring

/- English proof (translation)
Distinguish the cases in `hx : x = 0`. Substitute `hx` using the available equality. Establish `: hermTrace K H K (0 : ι → K ⊗[K] E) 0 = 0`. Rewrite using `[← hermTraceBilin_apply, map_zero]`. Rewrite using `[this, mul_zero, map_zero]`.

Conclude with `(realEmb_mul_hermTrace_pos hθ hw hx).le`.
-/
theorem realEmb_mul_hermTrace_nonneg {θ : K}
    (hθ : ∀ (w : InfinitePlace K) (hw : w.IsReal) (v : ι × κ → ℝ), v ≠ 0 →
      0 < ∑ a, ∑ c, v a * v c * embedding_of_isReal hw (θ * traceGram H b a c))
    {w : InfinitePlace K} (hw : w.IsReal) (x : ι → K ⊗[K] E) :
    0 ≤ embedding_of_isReal hw (θ * hermTrace K H K x x) := by
  by_cases hx : x = 0
  · subst hx
    have : hermTrace K H K (0 : ι → K ⊗[K] E) 0 = 0 := by
      rw [← hermTraceBilin_apply, map_zero]
    rw [this, mul_zero, map_zero]
  · exact (realEmb_mul_hermTrace_pos hθ hw hx).le

variable (H b) in

def ratGram (θ : K) :
    Matrix ((ι × κ) × Free.ChooseBasisIndex ℤ (𝓞 K)) ((ι × κ) × Free.ChooseBasisIndex ℤ (𝓞 K)) ℚ :=
  fun j j' => Algebra.trace ℚ K (θ * integralBasis K j.2 * integralBasis K j'.2 * traceGram H b j.1 j'.1)

omit [Fintype κ] in
/- English proof (translation)
Use extensionality with `j j'`. Simplify using `only [transpose_apply, ratGram]`. Use `congrFun (congrFun (traceGram_transpose (b := b) hH) j.1) j'.1` as an intermediate fact. Rewrite `this` using `[transpose_apply]`. Rewrite using `[this]`.

Put the polynomial expressions in normal form.
-/
theorem ratGram_transpose (hH : IsHermitianFor (conjHom K E) H) (θ : K) :
    (ratGram H b θ)ᵀ = ratGram H b θ := by
  ext j j'
  simp only [transpose_apply, ratGram]
  have := congrFun (congrFun (traceGram_transpose (b := b) hH) j.1) j'.1
  rw [transpose_apply] at this
  rw [this]
  ring_nf

/- English proof (translation)
Establish `hli` using `(mixedEmbedding.latticeBasis K).linearIndependent`. Establish `hker : LinearMap.ker (LinearMap.fst ℝ ({w : InfinitePlace K // w.IsReal} → ℝ) ({w : InfinitePlace K // w.IsComplex} → ℂ)) = ⊥`. Rewrite using `[LinearMap.ker_eq_bot']`. Introduce and unpack `⟨x, y⟩ h`. Simplify using `only [LinearMap.fst_apply] at h`.

Substitute `h` using the available equality. Establish `: y = 0` using `funext fun w => absurd (hreal w.1) (not_isReal_iff_isComplex.2 w.2)`. Rewrite using `[this]`. Both sides reduce to the same expression. Use `hli.map' _ hker` as an intermediate fact.

Establish `heq : (fun t : Free.ChooseBasisIndex ℤ (𝓞 K) => fun w : {w : InfinitePlace K // w.IsReal} => embedding_of_isReal w.2 (integralBasis K t)) = (LinearMap.fst ℝ ({w : InfinitePlace K // w.IsReal} → ℝ) ({w : InfinitePlace K // w.IsComplex} → ℂ)) ∘ (mixedEmbedding.latticeBasis K)`. Use function extensionality and compare the values at `t w`. Simplify using `only [Function.comp_apply, mixedEmbedding.latticeBasis_apply, LinearMap.fst_apply]`. Rewrite using `[mixedEmbedding.mixedEmbedding_apply_isReal]`. Rewrite using `[heq]`.

Conclude with `this`.
-/
theorem linearIndependent_realEmb_integralBasis (hreal : ∀ w : InfinitePlace K, w.IsReal) :
    LinearIndependent ℝ fun t : Free.ChooseBasisIndex ℤ (𝓞 K) =>
      fun w : {w : InfinitePlace K // w.IsReal} => embedding_of_isReal w.2 (integralBasis K t) := by
  have hli := (mixedEmbedding.latticeBasis K).linearIndependent
  have hker : LinearMap.ker (LinearMap.fst ℝ ({w : InfinitePlace K // w.IsReal} → ℝ)
      ({w : InfinitePlace K // w.IsComplex} → ℂ)) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    rintro ⟨x, y⟩ h
    simp only [LinearMap.fst_apply] at h
    subst h
    have : y = 0 := funext fun w => absurd (hreal w.1) (not_isReal_iff_isComplex.2 w.2)
    rw [this]; rfl
  have := hli.map' _ hker
  have heq : (fun t : Free.ChooseBasisIndex ℤ (𝓞 K) =>
      fun w : {w : InfinitePlace K // w.IsReal} => embedding_of_isReal w.2 (integralBasis K t)) =
      (LinearMap.fst ℝ ({w : InfinitePlace K // w.IsReal} → ℝ)
        ({w : InfinitePlace K // w.IsComplex} → ℂ)) ∘ (mixedEmbedding.latticeBasis K) := by
    funext t w
    simp only [Function.comp_apply, mixedEmbedding.latticeBasis_apply, LinearMap.fst_apply]
    rw [mixedEmbedding.mixedEmbedding_apply_isReal]
  rw [heq]
  exact this

/- English proof (translation)
Use `set ω := integralBasis K`. Set `u : InfinitePlace K → ι × κ → ℝ` to `fun w a => ∑ t, v (a, t) * realEmb hreal w (ω t)`. Establish `hexp : v ⬝ᵥ ((ratGram H b θ).map (Rat.cast : ℚ → ℝ) *ᵥ v) = ∑ w, ∑ a, ∑ c, u w a * u w c * realEmb hreal w (θ * traceGram H b a c)`. Simplify using `only [dotProduct, mulVec, Matrix.map_apply, ratGram, trace_eq_sum_realEmb hreal, Finset.mul_sum, Finset.sum_mul]`. Establish `step : ∀ f : (ι × κ) × Free.ChooseBasisIndex ℤ (𝓞 K) → (ι × κ) × Free.ChooseBasisIndex ℤ (𝓞 K) → InfinitePlace K → ℝ, ∑ x, ∑ y, ∑ i, f x y i = ∑ i, ∑ x, ∑ y, f x y i`.

Introduce `f`. Combine the equalities or inequalities in the displayed calculation. Establish `swap4 : ∀ F : ι × κ → Free.ChooseBasisIndex ℤ (𝓞 K) → ι × κ → Free.ChooseBasisIndex ℤ (𝓞 K) → ℝ, ∑ a, ∑ t, ∑ c, ∑ t', F a t c t' = ∑ a, ∑ c, ∑ t, ∑ t', F a t c t'` using `fun F => Finset.sum_congr rfl fun a _ => Finset.sum_comm`. Rewrite using `[step]`. Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations.

Simplify using `only [u, Finset.sum_mul, Finset.mul_sum]`. Simplify using `only [Fintype.sum_prod_type (α₁ := ι × κ) (α₂ := Free.ChooseBasisIndex ℤ (𝓞 K))]`. Establish `swap2 : ∀ F : Free.ChooseBasisIndex ℤ (𝓞 K) → Free.ChooseBasisIndex ℤ (𝓞 K) → ℝ, ∑ t, ∑ t', F t t' = ∑ t', ∑ t, F t t'` using `fun F => Finset.sum_comm`. Rewrite using `[swap4]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations.

Rewrite using `[swap2]`. Use `Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun t' _ => ?_` and prove the remaining obligations. Simplify using `only [map_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hexp]`.

Establish `hnonneg : ∀ w, 0 ≤ ∑ a, ∑ c, u w a * u w c * realEmb hreal w (θ * traceGram H b a c)`. Introduce `w`. Distinguish the cases in `hu : u w = 0`. Simplify using `[hu]`. Conclude with `(hθ w (hreal w) (u w) hu).le`.

Choose the witnesses or unpack the hypotheses as in `⟨w, hw⟩ : ∃ w, u w ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push Not at h`. Apply `hv` to reduce the goal to its premises. Use function extensionality and compare the values at `⟨a, t⟩`.

Establish `hli` using `linearIndependent_realEmb_integralBasis hreal`. Establish `hsum : (∑ t, v (a, t) • (fun w : {w : InfinitePlace K // w.IsReal} => embedding_of_isReal w.2 (ω t)) : {w : InfinitePlace K // w.IsReal} → ℝ) = 0`. Use function extensionality and compare the values at `w'`. Use `congrFun (h w'.1) a` as an intermediate fact. Simplify `this` using `[u, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]`.

Conclude with `Fintype.linearIndependent_iff.1 hli (fun t => v (a, t)) hsum t`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem ratGram_posDef (hreal : ∀ w : InfinitePlace K, w.IsReal) {θ : K}
    (hθ : ∀ (w : InfinitePlace K) (hw : w.IsReal) (v : ι × κ → ℝ), v ≠ 0 →
      0 < ∑ a, ∑ c, v a * v c * embedding_of_isReal hw (θ * traceGram H b a c))
    (v : (ι × κ) × Free.ChooseBasisIndex ℤ (𝓞 K) → ℝ) (hv : v ≠ 0) :
    0 < v ⬝ᵥ ((ratGram H b θ).map (Rat.cast : ℚ → ℝ) *ᵥ v) := by
  set ω := integralBasis K
  let u : InfinitePlace K → ι × κ → ℝ := fun w a => ∑ t, v (a, t) * realEmb hreal w (ω t)
  have hexp : v ⬝ᵥ ((ratGram H b θ).map (Rat.cast : ℚ → ℝ) *ᵥ v) =
      ∑ w, ∑ a, ∑ c, u w a * u w c * realEmb hreal w (θ * traceGram H b a c) := by
    simp only [dotProduct, mulVec, Matrix.map_apply, ratGram, trace_eq_sum_realEmb hreal,
      Finset.mul_sum, Finset.sum_mul]
    have step : ∀ f : (ι × κ) × Free.ChooseBasisIndex ℤ (𝓞 K) →
        (ι × κ) × Free.ChooseBasisIndex ℤ (𝓞 K) → InfinitePlace K → ℝ,
        ∑ x, ∑ y, ∑ i, f x y i = ∑ i, ∑ x, ∑ y, f x y i := by
      intro f
      calc ∑ x, ∑ y, ∑ i, f x y i = ∑ x, ∑ i, ∑ y, f x y i :=
            Finset.sum_congr rfl fun x _ => Finset.sum_comm
        _ = ∑ i, ∑ x, ∑ y, f x y i := Finset.sum_comm
    have swap4 : ∀ F : ι × κ → Free.ChooseBasisIndex ℤ (𝓞 K) → ι × κ →
        Free.ChooseBasisIndex ℤ (𝓞 K) → ℝ,
        ∑ a, ∑ t, ∑ c, ∑ t', F a t c t' = ∑ a, ∑ c, ∑ t, ∑ t', F a t c t' :=
      fun F => Finset.sum_congr rfl fun a _ => Finset.sum_comm
    rw [step]
    refine Finset.sum_congr rfl fun w _ => ?_
    simp only [u, Finset.sum_mul, Finset.mul_sum]
    simp only [Fintype.sum_prod_type (α₁ := ι × κ) (α₂ := Free.ChooseBasisIndex ℤ (𝓞 K))]
    have swap2 : ∀ F : Free.ChooseBasisIndex ℤ (𝓞 K) → Free.ChooseBasisIndex ℤ (𝓞 K) → ℝ,
        ∑ t, ∑ t', F t t' = ∑ t', ∑ t, F t t' := fun F => Finset.sum_comm
    rw [swap4]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
    rw [swap2]
    refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun t' _ => ?_
    simp only [map_mul]
    ring
  rw [hexp]
  have hnonneg : ∀ w, 0 ≤ ∑ a, ∑ c, u w a * u w c * realEmb hreal w (θ * traceGram H b a c) := by
    intro w
    by_cases hu : u w = 0
    · simp [hu]
    · exact (hθ w (hreal w) (u w) hu).le
  obtain ⟨w, hw⟩ : ∃ w, u w ≠ 0 := by
    by_contra h
    push Not at h
    apply hv
    funext ⟨a, t⟩
    have hli := linearIndependent_realEmb_integralBasis hreal
    have hsum : (∑ t, v (a, t) • (fun w : {w : InfinitePlace K // w.IsReal} =>
        embedding_of_isReal w.2 (ω t)) : {w : InfinitePlace K // w.IsReal} → ℝ) = 0 := by
      funext w'
      have := congrFun (h w'.1) a
      simpa [u, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using this
    exact Fintype.linearIndependent_iff.1 hli (fun t => v (a, t)) hsum t
  calc 0 < ∑ a, ∑ c, u w a * u w c * realEmb hreal w (θ * traceGram H b a c) := hθ w (hreal w) (u w) hw
    _ ≤ _ := Finset.single_le_sum (fun w _ => hnonneg w) (Finset.mem_univ w)

end Form

end GroundTheory.Automorphic
