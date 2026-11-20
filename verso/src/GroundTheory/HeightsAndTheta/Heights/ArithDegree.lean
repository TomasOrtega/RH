import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HermitianTensor

namespace GroundTheory.Heights₂.Heights

open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt Matrix

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

instance (σ : K →+* ℂ) : Module.IsTorsionFree (𝓞 K) (ComplexAt σ) := by
  refine ⟨fun a ha z w hzw ↦ ?_⟩
  have ha0 : a ≠ 0 := ha.ne_zero
  have h1 : σ (a : K) ≠ 0 := by
    rw [map_ne_zero]; exact_mod_cast ha0
  simp only [smul_def] at hzw
  exact mul_left_cancel₀ (M₀ := ℂ) h1 hzw

/- English proof (translation)
The claim follows from `inferInstance`.
-/
example (σ : K →+* ℂ) : Module.Flat (𝓞 K) (ComplexAt σ) := inferInstance

variable {E : Type*} [AddCommGroup E] [Module (𝓞 K) E] [Module.Finite (𝓞 K) E]
  [Module.Projective (𝓞 K) E]

/- English proof (translation)
The claim follows from `inferInstance`.
-/
example : Module.IsTorsionFree (𝓞 K) E := inferInstance

omit [Module.Projective (𝓞 K) E] in

/- English proof (translation)
Use `set N := Submodule.span (𝓞 K) (Set.range s)`. Establish `hN : Module.rank (𝓞 K) N = Fintype.card ι` using `by classical`. Rewrite using `[rank_span hs, Cardinal.mk_fintype, Set.card_range_of_injective hs.injective]`. Establish `hE : Module.rank (𝓞 K) E = Module.finrank (𝓞 K) E` using `(Module.finrank_eq_rank _ _).symm`. Establish `hQ` using `rank_quotient_add_rank_of_isDomain N`.

Rewrite `hQ` using `[hN, hE, hcard]`. Establish `hlt : Module.rank (𝓞 K) (E ⧸ N) < Cardinal.aleph0`. Use `lt_of_le_of_lt (le_self_add.trans hQ.le) Cardinal.natCast_lt_aleph0` and prove the remaining obligations. Take `⟨m, hm⟩` from `Cardinal.lt_aleph0.mp hlt`. Rewrite `hQ` using `[hm]`.

Normalize the coercions in `at hQ`. Establish `hQ0 : Module.rank (𝓞 K) (E ⧸ N) = 0` using `by rw [hm]; norm_cast; omega`. Establish `htors : ∀ x : E ⧸ N, ∃ n : ℤ, n ≠ 0 ∧ n • x = 0`. Introduce `x`. Take `⟨a, ha, hax⟩` from `(rank_eq_zero_iff.mp hQ0) x`.

Establish `hI : Ideal.span ({a} : Set (𝓞 K)) ≠ ⊥`. Rewrite using `[Ne, Ideal.span_singleton_eq_bot]` and apply the resulting hypothesis. Establish `hmem` using `Ideal.absNorm_mem (Ideal.span ({a} : Set (𝓞 K)))`. Take `⟨b, hb⟩` from `Ideal.mem_span_singleton'.mp hmem`. Use `⟨(Ideal.absNorm (Ideal.span ({a} : Set (𝓞 K))) : ℤ), ?_, ?_⟩` and prove the remaining obligations.

Conclude with `Ideal.absNorm_eq_zero_iff.not.mpr hI` after adjusting the coercions. Rewrite using `[← Int.cast_smul_eq_zsmul (𝓞 K), Int.cast_natCast, ← hb, mul_smul, hax, smul_zero]`. Establish `: Module.Finite ℤ (E ⧸ N)` using `Module.Finite.trans (𝓞 K) (E ⧸ N)`. Use `Module.finite_of_fg_torsion _ fun x ↦ ?_` and prove the remaining obligations. Take `⟨n, hn, hnx⟩` from `htors x`.

Conclude with `⟨⟨n, mem_nonZeroDivisors_of_ne_zero hn⟩, hnx⟩`.
-/
theorem finite_quotient_span {ι : Type*} [Fintype ι] {s : ι → E} (hs : LinearIndependent (𝓞 K) s)
    (hcard : Fintype.card ι = Module.finrank (𝓞 K) E) :
    Finite (E ⧸ Submodule.span (𝓞 K) (Set.range s)) := by
  set N := Submodule.span (𝓞 K) (Set.range s)
  have hN : Module.rank (𝓞 K) N = Fintype.card ι := by
    classical
    rw [rank_span hs, Cardinal.mk_fintype, Set.card_range_of_injective hs.injective]
  have hE : Module.rank (𝓞 K) E = Module.finrank (𝓞 K) E := (Module.finrank_eq_rank _ _).symm
  have hQ := rank_quotient_add_rank_of_isDomain N
  rw [hN, hE, hcard] at hQ
  have hlt : Module.rank (𝓞 K) (E ⧸ N) < Cardinal.aleph0 := by
    refine lt_of_le_of_lt (le_self_add.trans hQ.le) Cardinal.natCast_lt_aleph0
  obtain ⟨m, hm⟩ := Cardinal.lt_aleph0.mp hlt
  rw [hm] at hQ
  norm_cast at hQ
  have hQ0 : Module.rank (𝓞 K) (E ⧸ N) = 0 := by rw [hm]; norm_cast; omega
  have htors : ∀ x : E ⧸ N, ∃ n : ℤ, n ≠ 0 ∧ n • x = 0 := by
    intro x
    obtain ⟨a, ha, hax⟩ := (rank_eq_zero_iff.mp hQ0) x
    have hI : Ideal.span ({a} : Set (𝓞 K)) ≠ ⊥ := by
      rwa [Ne, Ideal.span_singleton_eq_bot]
    have hmem := Ideal.absNorm_mem (Ideal.span ({a} : Set (𝓞 K)))
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp hmem
    refine ⟨(Ideal.absNorm (Ideal.span ({a} : Set (𝓞 K))) : ℤ), ?_, ?_⟩
    · exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr hI
    · rw [← Int.cast_smul_eq_zsmul (𝓞 K), Int.cast_natCast, ← hb, mul_smul, hax, smul_zero]
  have : Module.Finite ℤ (E ⧸ N) := Module.Finite.trans (𝓞 K) (E ⧸ N)
  refine Module.finite_of_fg_torsion _ fun x ↦ ?_
  obtain ⟨n, hn, hnx⟩ := htors x
  exact ⟨⟨n, mem_nonZeroDivisors_of_ne_zero hn⟩, hnx⟩

def fibreVec (h : HermitianMetric K E) (σ : K →+* ℂ) (e : E) : FibreSpace h σ :=
  FibreSpace.equiv h σ ((1 : ComplexAt σ) ⊗ₜ e)

section FibreVec

variable (h : HermitianMetric K E) (σ : K →+* ℂ)

/- English proof (translation)
Simplify using `only [fibreVec, tmul_add, map_add]`.
-/
theorem fibreVec_add (e f : E) : fibreVec h σ (e + f) = fibreVec h σ e + fibreVec h σ f := by
  simp only [fibreVec, tmul_add, map_add]

/- English proof (translation)
Simplify using `only [fibreVec]`. Rewrite using `[← map_smul, ← TensorProduct.smul_tmul, smul_tmul', smul_def, complex_smul_def]`.
-/
theorem fibreVec_smul (a : 𝓞 K) (e : E) :
    fibreVec h σ (a • e) = (σ (a : K)) • fibreVec h σ e := by
  simp only [fibreVec]
  rw [← map_smul, ← TensorProduct.smul_tmul, smul_tmul', smul_def, complex_smul_def]

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty => simp [fibreVec]`. Consider the case `insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, fibreVec_add, fibreVec_smul, ih]`.
-/
theorem fibreVec_sum {ι : Type*} (S : Finset ι) (c : ι → 𝓞 K) (s : ι → E) :
    fibreVec h σ (∑ i ∈ S, c i • s i) = ∑ i ∈ S, (σ (c i : K)) • fibreVec h σ (s i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [fibreVec]
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, fibreVec_add, fibreVec_smul, ih]

/- English proof (translation)
Use `set N := Submodule.span (𝓞 K) (Set.range s)`. Set `b : Module.Basis ι (𝓞 K) N` to `Module.Basis.span hs`. Set `bC` to `Algebra.TensorProduct.basis (ComplexAt σ) b`. Set `f : ComplexAt σ ⊗[𝓞 K] N →ₗ[ComplexAt σ] ComplexAt σ ⊗[𝓞 K] E` to `AlgebraTensorModule.lTensor (ComplexAt σ) (ComplexAt σ) N.subtype`. Establish `hf : Function.Injective f` using `Module.Flat.lTensor_preserves_injective_linearMap N.subtype N.injective_subtype`.

Establish `h1 : LinearIndependent (ComplexAt σ) (fun i ↦ f (bC i))` using `bC.linearIndependent.map' f (LinearMap.ker_eq_bot.mpr hf)`. Establish `h2 : (fun i ↦ f (bC i)) = fun i ↦ (1 : ComplexAt σ) ⊗ₜ[𝓞 K] s i`. Use function extensionality and compare the values at `i`. Simplify using `only [bC, f, b, Algebra.TensorProduct.basis_apply, AlgebraTensorModule.lTensor_tmul, Submodule.subtype_apply]`. Rewrite using `[Module.Basis.span_apply]`.

Rewrite `h1` using `[h2]`. Establish `h3 : LinearIndependent ℂ (fun i ↦ (1 : ComplexAt σ) ⊗ₜ[𝓞 K] s i)` using `h1.restrict_scalars (R := ℂ) (fun a c hac ↦ by`. Simplify using `only [complex_smul_def, mul_one] at hac`. Conclude with `hac)`. Conclude with `h3.map' (FibreSpace.equiv h σ).toLinearMap (FibreSpace.equiv h σ).ker`.
-/
theorem linearIndependent_fibreVec {ι : Type*} {s : ι → E} (hs : LinearIndependent (𝓞 K) s) :
    LinearIndependent ℂ (fun i ↦ fibreVec h σ (s i)) := by
  set N := Submodule.span (𝓞 K) (Set.range s)
  let b : Module.Basis ι (𝓞 K) N := Module.Basis.span hs
  let bC := Algebra.TensorProduct.basis (ComplexAt σ) b
  let f : ComplexAt σ ⊗[𝓞 K] N →ₗ[ComplexAt σ] ComplexAt σ ⊗[𝓞 K] E :=
    AlgebraTensorModule.lTensor (ComplexAt σ) (ComplexAt σ) N.subtype
  have hf : Function.Injective f :=
    Module.Flat.lTensor_preserves_injective_linearMap N.subtype N.injective_subtype
  have h1 : LinearIndependent (ComplexAt σ) (fun i ↦ f (bC i)) :=
    bC.linearIndependent.map' f (LinearMap.ker_eq_bot.mpr hf)
  have h2 : (fun i ↦ f (bC i)) = fun i ↦ (1 : ComplexAt σ) ⊗ₜ[𝓞 K] s i := by
    funext i
    simp only [bC, f, b, Algebra.TensorProduct.basis_apply, AlgebraTensorModule.lTensor_tmul,
      Submodule.subtype_apply]
    rw [Module.Basis.span_apply]
  rw [h2] at h1
  have h3 : LinearIndependent ℂ (fun i ↦ (1 : ComplexAt σ) ⊗ₜ[𝓞 K] s i) :=
    h1.restrict_scalars (R := ℂ) (fun a c hac ↦ by
      simp only [complex_smul_def, mul_one] at hac; exact hac)
  exact h3.map' (FibreSpace.equiv h σ).toLinearMap (FibreSpace.equiv h σ).ker

end FibreVec

section Gram

/- English proof (translation)
Use extensionality with `j k`. Simplify using `only [gram_apply, sum_inner, inner_sum, inner_smul_left, inner_smul_right, mul_apply, conjTranspose_apply, Finset.sum_mul, Finset.mul_sum, RCLike.star_def]`. Use `Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun l _ ↦ ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gram_comb {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {ι : Type*}
    [Fintype ι] (v : ι → V) (B : Matrix ι ι ℂ) :
    gram ℂ (fun j ↦ ∑ i, B i j • v i) = Bᴴ * gram ℂ v * B := by
  ext j k
  simp only [gram_apply, sum_inner, inner_sum, inner_smul_left, inner_smul_right, mul_apply,
    conjTranspose_apply, Finset.sum_mul, Finset.mul_sum, RCLike.star_def]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun l _ ↦ ?_
  ring

end Gram

def gramDet (h : HermitianMetric K E) (σ : K →+* ℂ) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → E) : ℝ :=
  (det (gram ℂ fun i ↦ fibreVec h σ (s i))).re

section GramDet

variable (h : HermitianMetric K E) (σ : K →+* ℂ) {ι : Type*} [Fintype ι] [DecidableEq ι]

/- English proof (translation)
Use `(posDef_gram_of_linearIndependent (linearIndependent_fibreVec h σ hs)).det_pos` as an intermediate fact. Conclude with `(RCLike.pos_iff.mp this).1`.
-/
theorem gramDet_pos {s : ι → E} (hs : LinearIndependent (𝓞 K) s) : 0 < gramDet h σ s := by
  have := (posDef_gram_of_linearIndependent (linearIndependent_fibreVec h σ hs)).det_pos
  exact (RCLike.pos_iff.mp this).1

/- English proof (translation)
Use `set τ : 𝓞 K →+* ℂ := σ.comp (algebraMap (𝓞 K) K)`. Establish `hv : (fun j ↦ fibreVec h σ (∑ i, A i j • s i)) = fun j ↦ ∑ i, (τ.mapMatrix A) i j • fibreVec h σ (s i)`. Use function extensionality and compare the values at `j`. Rewrite using `[fibreVec_sum]`. Both sides reduce to the same expression.

Establish `hz : τ A.det = σ (A.det : K)` using `rfl`. Simplify using `only [gramDet]`. Rewrite using `[hv, gram_comb, det_mul, det_mul, det_conjTranspose, ← RingHom.map_det, hz, mul_comm _ (σ (A.det : K)), ← mul_assoc, RCLike.star_def, Complex.mul_conj, Complex.re_ofReal_mul, Complex.normSq_eq_norm_sq]`.
-/
theorem gramDet_comb (A : Matrix ι ι (𝓞 K)) (s : ι → E) :
    gramDet h σ (fun j ↦ ∑ i, A i j • s i) = ‖σ (A.det : K)‖ ^ 2 * gramDet h σ s := by
  set τ : 𝓞 K →+* ℂ := σ.comp (algebraMap (𝓞 K) K)
  have hv : (fun j ↦ fibreVec h σ (∑ i, A i j • s i)) =
      fun j ↦ ∑ i, (τ.mapMatrix A) i j • fibreVec h σ (s i) := by
    funext j; rw [fibreVec_sum]; rfl
  have hz : τ A.det = σ (A.det : K) := rfl
  simp only [gramDet]
  rw [hv, gram_comb, det_mul, det_mul, det_conjTranspose, ← RingHom.map_det, hz,
    mul_comm _ (σ (A.det : K)), ← mul_assoc, RCLike.star_def, Complex.mul_conj,
    Complex.re_ofReal_mul, Complex.normSq_eq_norm_sq]

/- English proof (translation)
Simplify using `only [gramDet]`. Establish `: (gram ℂ fun i ↦ fibreVec h σ ((s ∘ e) i)) = (gram ℂ fun i ↦ fibreVec h σ (s i)).submatrix e e`. Use extensionality with `i j`. Both sides reduce to the same expression. Rewrite using `[this, det_submatrix_equiv_self]`.
-/
theorem gramDet_reindex {ι' : Type*} [Fintype ι'] [DecidableEq ι'] (e : ι' ≃ ι) (s : ι → E) :
    gramDet h σ (s ∘ e) = gramDet h σ s := by
  simp only [gramDet]
  have : (gram ℂ fun i ↦ fibreVec h σ ((s ∘ e) i)) =
      (gram ℂ fun i ↦ fibreVec h σ (s i)).submatrix e e := by
    ext i j; rfl
  rw [this, det_submatrix_equiv_self]

end GramDet

def degreeWith (h : HermitianMetric K E) {ι : Type*} [Fintype ι] [DecidableEq ι] (s : ι → E) : ℝ :=
  Real.log (Nat.card (E ⧸ Submodule.span (𝓞 K) (Set.range s))) -
    (1 / 2) * ∑ σ : K →+* ℂ, Real.log (gramDet h σ s)

section Index

omit [NumberField K] [Module.Finite (𝓞 K) E] [Module.Projective (𝓞 K) E] in

/- English proof (translation)
Rewrite using `[← Submodule.card_quotient_mul_card_quotient (LinearMap.range Φ) (LinearMap.range (Φ ∘ₗ g)) (LinearMap.range_comp_le_range _ _)]`. Use `congr 1`. Establish `hker : LinearMap.ker ((LinearMap.range (Φ ∘ₗ g)).mkQ ∘ₗ Φ) = LinearMap.range g`. Use extensionality with `x`. Simplify using `only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, LinearMap.mem_range]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy⟩`. Conclude with `⟨y, hΦ hy⟩`. Introduce and unpack `⟨y, rfl⟩`. Conclude with `⟨y, rfl⟩`.

Rewrite using `[← LinearMap.range_comp, ← hker]`. Conclude with `Nat.card_congr (LinearMap.quotKerEquivRange _).toEquiv.symm`.
-/
theorem card_quotient_range_comp {M : Type*} [AddCommGroup M] [Module (𝓞 K) M]
    (Φ : M →ₗ[𝓞 K] E) (hΦ : Function.Injective Φ) (g : M →ₗ[𝓞 K] M) :
    Nat.card (E ⧸ LinearMap.range (Φ ∘ₗ g)) =
      Nat.card (M ⧸ LinearMap.range g) * Nat.card (E ⧸ LinearMap.range Φ) := by
  rw [← Submodule.card_quotient_mul_card_quotient (LinearMap.range Φ) (LinearMap.range (Φ ∘ₗ g))
    (LinearMap.range_comp_le_range _ _)]
  congr 1
  have hker : LinearMap.ker ((LinearMap.range (Φ ∘ₗ g)).mkQ ∘ₗ Φ) = LinearMap.range g := by
    ext x
    simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, LinearMap.mem_range]
    constructor
    · rintro ⟨y, hy⟩; exact ⟨y, hΦ hy⟩
    · rintro ⟨y, rfl⟩; exact ⟨y, rfl⟩
  rw [← LinearMap.range_comp, ← hker]
  exact Nat.card_congr (LinearMap.quotKerEquivRange _).toEquiv.symm

/- English proof (translation)
Establish `hinj : Function.Injective A.mulVecLin`. Introduce `x y hxy`. Assume the negation of the conclusion as `hne`. Use `hA (Matrix.exists_mulVec_eq_zero_iff.mp ⟨x - y, sub_ne_zero.mpr hne, ?_⟩)` and prove the remaining obligations. Rewrite using `[mulVec_sub]`.

Conclude with `sub_eq_zero.mpr hxy`. Use `set N := LinearMap.range A.mulVecLin`. Set `e : (ι → 𝓞 K) ≃ₗ[ℤ] N.restrictScalars ℤ` to `(LinearEquiv.ofInjective A.mulVecLin hinj).restrictScalars ℤ`. Establish `h1` using `Submodule.natAbs_det_equiv (N.restrictScalars ℤ) e`. Rewrite using `[← Nat.card_congr (Submodule.Quotient.restrictScalarsEquiv ℤ N).toEquiv, ← h1]`.

Establish `h2 : (N.restrictScalars ℤ).subtype ∘ₗ (e : (ι → 𝓞 K) →+ N.restrictScalars ℤ).toIntLinearMap = A.mulVecLin.restrictScalars ℤ`. Use extensionality with `x`. Both sides reduce to the same expression. Rewrite using `[h2, LinearMap.det_restrictScalars, ← Matrix.toLin'_apply', LinearMap.det_toLin']`.
-/
theorem card_quotient_mulVecLin {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι (𝓞 K))
    (hA : A.det ≠ 0) :
    Nat.card ((ι → 𝓞 K) ⧸ LinearMap.range A.mulVecLin) = (Algebra.norm ℤ A.det).natAbs := by
  have hinj : Function.Injective A.mulVecLin := by
    intro x y hxy
    by_contra hne
    refine hA (Matrix.exists_mulVec_eq_zero_iff.mp ⟨x - y, sub_ne_zero.mpr hne, ?_⟩)
    rw [mulVec_sub]
    exact sub_eq_zero.mpr hxy
  set N := LinearMap.range A.mulVecLin
  let e : (ι → 𝓞 K) ≃ₗ[ℤ] N.restrictScalars ℤ :=
    (LinearEquiv.ofInjective A.mulVecLin hinj).restrictScalars ℤ
  have h1 := Submodule.natAbs_det_equiv (N.restrictScalars ℤ) e
  rw [← Nat.card_congr (Submodule.Quotient.restrictScalarsEquiv ℤ N).toEquiv, ← h1]
  have h2 : (N.restrictScalars ℤ).subtype ∘ₗ (e : (ι → 𝓞 K) →+ N.restrictScalars ℤ).toIntLinearMap
      = A.mulVecLin.restrictScalars ℤ := by
    ext x; rfl
  rw [h2, LinearMap.det_restrictScalars, ← Matrix.toLin'_apply', LinearMap.det_toLin']

end Index

/- English proof (translation)
Establish `h1 : (((Algebra.norm ℚ (d : K) : ℚ) : ℂ)) = ∏ σ : K →+* ℂ, σ (d : K)`. Use `Algebra.norm_eq_prod_embeddings ℚ ℂ (d : K)` as an intermediate fact. Rewrite `this` using `[eq_ratCast]`. Rewrite using `[this]`. Conclude with `(Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) _ _ fun σ ↦ rfl).symm`.

Establish `h2 : ((Algebra.norm ℤ d).natAbs : ℝ) = ‖∏ σ : K →+* ℂ, σ (d : K)‖`. Rewrite using `[← h1, ← Algebra.coe_norm_int, Nat.cast_natAbs, Complex.norm_ratCast]`. Use `push_cast`. Both sides reduce to the same expression. Rewrite using `[h2, norm_prod, Real.log_prod]`.

Introduce `σ _`. Rewrite using `[norm_ne_zero_iff, map_ne_zero]`. Conclude with `hd` after adjusting the coercions.
-/
theorem sum_log_norm_embedding (d : 𝓞 K) (hd : d ≠ 0) :
    ∑ σ : K →+* ℂ, Real.log ‖σ (d : K)‖ = Real.log ((Algebra.norm ℤ d).natAbs : ℝ) := by
  have h1 : (((Algebra.norm ℚ (d : K) : ℚ) : ℂ)) = ∏ σ : K →+* ℂ, σ (d : K) := by
    have := Algebra.norm_eq_prod_embeddings ℚ ℂ (d : K)
    rw [eq_ratCast] at this
    rw [this]
    exact (Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) _ _ fun σ ↦ rfl).symm
  have h2 : ((Algebra.norm ℤ d).natAbs : ℝ) = ‖∏ σ : K →+* ℂ, σ (d : K)‖ := by
    rw [← h1, ← Algebra.coe_norm_int, Nat.cast_natAbs, Complex.norm_ratCast]
    push_cast; rfl
  rw [h2, norm_prod, Real.log_prod]
  intro σ _
  rw [norm_ne_zero_iff, map_ne_zero]
  exact_mod_cast hd

section Degree

variable (h : HermitianMetric K E)

omit [NumberField K] [Module.Finite (𝓞 K) E] [Module.Projective (𝓞 K) E] in

/- English proof (translation)
Use `LinearMap.ext fun x ↦ ?_` and prove the remaining obligations. Simplify using `only [LinearMap.comp_apply, Matrix.mulVecLin_apply, Fintype.linearCombination_apply, Matrix.mulVec, dotProduct, Finset.sum_smul, Finset.smul_sum, smul_smul]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun i _ ↦ by rw [mul_comm]`.
-/
theorem linearCombination_comb {ι : Type*} [Fintype ι] (s : ι → E) (A : Matrix ι ι (𝓞 K)) :
    Fintype.linearCombination (𝓞 K) s ∘ₗ A.mulVecLin =
      Fintype.linearCombination (𝓞 K) (fun j ↦ ∑ i, A i j • s i) := by
  refine LinearMap.ext fun x ↦ ?_
  simp only [LinearMap.comp_apply, Matrix.mulVecLin_apply, Fintype.linearCombination_apply,
    Matrix.mulVec, dotProduct, Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun i _ ↦ by rw [mul_comm]

/- English proof (translation)
Simplify using `only [degreeWith, gramDet_reindex, e.surjective.range_comp]`.
-/
theorem degreeWith_reindex {ι ι' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι']
    [DecidableEq ι'] (e : ι' ≃ ι) (s : ι → E) : degreeWith h (s ∘ e) = degreeWith h s := by
  simp only [degreeWith, gramDet_reindex, e.surjective.range_comp]

/- English proof (translation)
Establish `hinj` using `hs.fintypeLinearCombination_injective`. Establish `hfin` using `finite_quotient_span hs hcard`. Establish `hc : Nat.card (E ⧸ Submodule.span (𝓞 K) (Set.range (fun j ↦ ∑ i, A i j • s i))) = (Algebra.norm ℤ A.det).natAbs * Nat.card (E ⧸ Submodule.span (𝓞 K) (Set.range s))`. Rewrite using `[← Fintype.range_linearCombination, ← linearCombination_comb, card_quotient_range_comp _ hinj, card_quotient_mulVecLin A hA, Fintype.range_linearCombination]`. Establish `hcpos : (0 : ℝ) < Nat.card (E ⧸ Submodule.span (𝓞 K) (Set.range s))`.

Conclude with `Nat.card_pos` after adjusting the coercions. Establish `hN : (0 : ℝ) < (Algebra.norm ℤ A.det).natAbs`. Establish `: Algebra.norm ℤ A.det ≠ 0` using `Algebra.norm_ne_zero_iff.mpr hA`. Conclude with `Int.natAbs_pos.mpr this` after adjusting the coercions. Establish `hσ : ∀ σ : K →+* ℂ, ‖σ (A.det : K)‖ ≠ 0` using `fun σ ↦ by`.

Rewrite using `[norm_ne_zero_iff, map_ne_zero]`. Conclude with `hA` after adjusting the coercions. Establish `hlog : ∀ σ : K →+* ℂ, Real.log (gramDet h σ (fun j ↦ ∑ i, A i j • s i)) = 2 * Real.log ‖σ (A.det : K)‖ + Real.log (gramDet h σ s)` using `fun σ ↦ by`. Rewrite using `[gramDet_comb, Real.log_mul (pow_ne_zero 2 (hσ σ)) (gramDet_pos h σ hs).ne', Real.log_pow]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Simplify using `only [degreeWith]`. Rewrite using `[hc, Nat.cast_mul, Real.log_mul hN.ne' hcpos.ne']`. Simplify using `only [hlog]`. Rewrite using `[Finset.sum_add_distrib, ← Finset.mul_sum, sum_log_norm_embedding _ hA]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem degreeWith_comb {ι : Type*} [Fintype ι] [DecidableEq ι] {s : ι → E}
    (hs : LinearIndependent (𝓞 K) s) (hcard : Fintype.card ι = Module.finrank (𝓞 K) E)
    (A : Matrix ι ι (𝓞 K)) (hA : A.det ≠ 0) :
    degreeWith h (fun j ↦ ∑ i, A i j • s i) = degreeWith h s := by
  have hinj := hs.fintypeLinearCombination_injective
  have hfin := finite_quotient_span hs hcard
  have hc : Nat.card (E ⧸ Submodule.span (𝓞 K) (Set.range (fun j ↦ ∑ i, A i j • s i))) =
      (Algebra.norm ℤ A.det).natAbs * Nat.card (E ⧸ Submodule.span (𝓞 K) (Set.range s)) := by
    rw [← Fintype.range_linearCombination, ← linearCombination_comb,
      card_quotient_range_comp _ hinj, card_quotient_mulVecLin A hA, Fintype.range_linearCombination]
  have hcpos : (0 : ℝ) < Nat.card (E ⧸ Submodule.span (𝓞 K) (Set.range s)) := by
    exact_mod_cast Nat.card_pos
  have hN : (0 : ℝ) < (Algebra.norm ℤ A.det).natAbs := by
    have : Algebra.norm ℤ A.det ≠ 0 := Algebra.norm_ne_zero_iff.mpr hA
    exact_mod_cast Int.natAbs_pos.mpr this
  have hσ : ∀ σ : K →+* ℂ, ‖σ (A.det : K)‖ ≠ 0 := fun σ ↦ by
    rw [norm_ne_zero_iff, map_ne_zero]; exact_mod_cast hA
  have hlog : ∀ σ : K →+* ℂ, Real.log (gramDet h σ (fun j ↦ ∑ i, A i j • s i)) =
      2 * Real.log ‖σ (A.det : K)‖ + Real.log (gramDet h σ s) := fun σ ↦ by
    rw [gramDet_comb, Real.log_mul (pow_ne_zero 2 (hσ σ)) (gramDet_pos h σ hs).ne', Real.log_pow]
    push_cast; ring
  simp only [degreeWith]
  rw [hc, Nat.cast_mul, Real.log_mul hN.ne' hcpos.ne']
  simp only [hlog]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_log_norm_embedding _ hA]
  ring

/- English proof (translation)
Establish `hfin` using `finite_quotient_span hs hcard`. Use `set n := Nat.card (E ⧸ Submodule.span (𝓞 K) (Set.range s))`. Establish `hn : n ≠ 0` using `Nat.card_pos.ne'`. Establish `hmem : ∀ j, (n : 𝓞 K) • t j ∈ Submodule.span (𝓞 K) (Set.range s)`. Introduce `j`.

Use `card_nsmul_eq_zero' (G := E ⧸ Submodule.span (𝓞 K) (Set.range s)) (x := Submodule.Quotient.mk (t j))` as an intermediate fact. Rewrite `this` using `[← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]`. Rewrite using `[Nat.cast_smul_eq_nsmul]` and apply the resulting hypothesis. Use `choose c hc using fun j ↦ (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).mp (hmem j)`. Set `A : Matrix ι ι (𝓞 K)` to `Matrix.of fun i j ↦ c j i`.

Set `D : Matrix ι ι (𝓞 K)` to `(n : 𝓞 K) • 1`. Establish `hu1 : (fun j ↦ ∑ i, A i j • s i) = fun j ↦ (n : 𝓞 K) • t j` using `funext hc`. Establish `hu2 : (fun j ↦ ∑ i, D i j • t i) = fun j ↦ (n : 𝓞 K) • t j`. Use function extensionality and compare the values at `j`. Simplify using `[D, Matrix.smul_apply, Matrix.one_apply, ite_smul, Finset.sum_ite_eq']`.

Establish `hn' : (n : 𝓞 K) ≠ 0` using `Nat.cast_ne_zero.mpr hn`. Establish `hD : D.det ≠ 0`. Simplify using `only [D, det_smul, det_one, mul_one]`. Conclude with `pow_ne_zero _ hn'`. Establish `hA : A.det ≠ 0`.

Introduce `h0`. Take `⟨x, hx0, hx⟩` from `Matrix.exists_mulVec_eq_zero_iff.mpr h0`. Apply `hx0` to reduce the goal to its premises. Establish `key : (n : 𝓞 K) • Fintype.linearCombination (𝓞 K) t x = 0`. Establish `e1` using `congrArg (· x) (linearCombination_comb s A)`.

Simplify using `only [LinearMap.comp_apply, Matrix.mulVecLin_apply, hx, map_zero, hu1] at e1`. Rewrite using `[← map_smul, e1, Fintype.linearCombination_apply, Fintype.linearCombination_apply]`. Use `Finset.sum_congr rfl fun i _ ↦ ?_` and prove the remaining obligations. Rewrite using `[Pi.smul_apply, smul_eq_mul, smul_smul, mul_comm]`. Establish `key2 : Fintype.linearCombination (𝓞 K) t x = 0` using `(smul_eq_zero.mp key).resolve_left hn'`.

Conclude with `ht.fintypeLinearCombination_injective (key2.trans (map_zero _).symm)`. Rewrite using `[← degreeWith_comb h ht hcard D hD, hu2, ← hu1, degreeWith_comb h hs hcard A hA]`.
-/
theorem degreeWith_eq_of_linearIndependent {ι : Type*} [Fintype ι] [DecidableEq ι] {s t : ι → E}
    (hs : LinearIndependent (𝓞 K) s) (ht : LinearIndependent (𝓞 K) t)
    (hcard : Fintype.card ι = Module.finrank (𝓞 K) E) : degreeWith h t = degreeWith h s := by
  have hfin := finite_quotient_span hs hcard
  set n := Nat.card (E ⧸ Submodule.span (𝓞 K) (Set.range s))
  have hn : n ≠ 0 := Nat.card_pos.ne'
  have hmem : ∀ j, (n : 𝓞 K) • t j ∈ Submodule.span (𝓞 K) (Set.range s) := by
    intro j
    have := card_nsmul_eq_zero' (G := E ⧸ Submodule.span (𝓞 K) (Set.range s))
      (x := Submodule.Quotient.mk (t j))
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at this
    rwa [Nat.cast_smul_eq_nsmul]
  choose c hc using fun j ↦ (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).mp (hmem j)
  let A : Matrix ι ι (𝓞 K) := Matrix.of fun i j ↦ c j i
  let D : Matrix ι ι (𝓞 K) := (n : 𝓞 K) • 1
  have hu1 : (fun j ↦ ∑ i, A i j • s i) = fun j ↦ (n : 𝓞 K) • t j := funext hc
  have hu2 : (fun j ↦ ∑ i, D i j • t i) = fun j ↦ (n : 𝓞 K) • t j := by
    funext j
    simp [D, Matrix.smul_apply, Matrix.one_apply, ite_smul, Finset.sum_ite_eq']
  have hn' : (n : 𝓞 K) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hD : D.det ≠ 0 := by
    simp only [D, det_smul, det_one, mul_one]
    exact pow_ne_zero _ hn'
  have hA : A.det ≠ 0 := by
    intro h0
    obtain ⟨x, hx0, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    apply hx0
    have key : (n : 𝓞 K) • Fintype.linearCombination (𝓞 K) t x = 0 := by
      have e1 := congrArg (· x) (linearCombination_comb s A)
      simp only [LinearMap.comp_apply, Matrix.mulVecLin_apply, hx, map_zero, hu1] at e1
      rw [← map_smul, e1, Fintype.linearCombination_apply, Fintype.linearCombination_apply]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [Pi.smul_apply, smul_eq_mul, smul_smul, mul_comm]
    have key2 : Fintype.linearCombination (𝓞 K) t x = 0 := (smul_eq_zero.mp key).resolve_left hn'
    exact ht.fintypeLinearCombination_injective (key2.trans (map_zero _).symm)
  rw [← degreeWith_comb h ht hcard D hD, hu2, ← hu1, degreeWith_comb h hs hcard A hA]

omit [NumberField K] [Module.Projective (𝓞 K) E] in

/- English proof (translation)
Take `⟨S, hS, hli⟩` from `exists_set_linearIndependent_of_isDomain (𝓞 K) E`. Rewrite `hS` using `[← Module.finrank_eq_rank]`. Take `⟨e⟩` from `Cardinal.mk_eq_nat_iff.mp hS`. Conclude with `⟨fun i ↦ (e.symm i : E), hli.comp _ e.symm.injective⟩`.
-/
theorem exists_linearIndependent_fin :
    ∃ s : Fin (Module.finrank (𝓞 K) E) → E, LinearIndependent (𝓞 K) s := by
  obtain ⟨S, hS, hli⟩ := exists_set_linearIndependent_of_isDomain (𝓞 K) E
  rw [← Module.finrank_eq_rank] at hS
  obtain ⟨e⟩ := Cardinal.mk_eq_nat_iff.mp hS
  exact ⟨fun i ↦ (e.symm i : E), hli.comp _ e.symm.injective⟩

end Degree

def arithDegree (h : HermitianMetric K E) : ℝ :=
  degreeWith h (exists_linearIndependent_fin (K := K) (E := E)).choose

/- English proof (translation)
Set `e : ι ≃ Fin (Module.finrank (𝓞 K) E)` to `Fintype.equivFinOfCardEq hcard`. Rewrite using `[← degreeWith_reindex h e.symm s]`. Conclude with `(degreeWith_eq_of_linearIndependent h (exists_linearIndependent_fin (K := K) (E := E)).choose_spec (hs.comp e.symm e.symm.injective) (Fintype.card_fin _)).symm`.
-/
theorem arithDegree_eq (h : HermitianMetric K E) {ι : Type*} [Fintype ι] [DecidableEq ι]
    {s : ι → E} (hs : LinearIndependent (𝓞 K) s)
    (hcard : Fintype.card ι = Module.finrank (𝓞 K) E) : arithDegree h = degreeWith h s := by
  let e : ι ≃ Fin (Module.finrank (𝓞 K) E) := Fintype.equivFinOfCardEq hcard
  rw [← degreeWith_reindex h e.symm s]
  exact (degreeWith_eq_of_linearIndependent h
    (exists_linearIndependent_fin (K := K) (E := E)).choose_spec
    (hs.comp e.symm e.symm.injective) (Fintype.card_fin _)).symm

/- English proof (translation)
Rewrite using `[@norm_sq_eq_re_inner ℂ]`. Both sides reduce to the same expression.
-/
theorem norm_fibreVec_sq (h : HermitianMetric K E) (σ : K →+* ℂ) (e : E) :
    ‖fibreVec h σ e‖ ^ 2 = ((h.form σ).inner ((1 : ComplexAt σ) ⊗ₜ e) (1 ⊗ₜ e)).re := by
  rw [@norm_sq_eq_re_inner ℂ]
  rfl

/- English proof (translation)
Establish `hli : LinearIndependent (𝓞 K) (fun _ : Fin 1 ↦ s)` using `linearIndependent_unique_iff.mpr hs`. Rewrite using `[arithDegree_eq h hli (by simp [hE]), degreeWith, Set.range_const]`. Use `congr 1`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun σ _ ↦ ?_` and prove the remaining obligations.

Simplify using `only [gramDet, det_unique, gram_apply]`. Establish `hv : (inner ℂ (fibreVec h σ s) (fibreVec h σ s)).re = ‖fibreVec h σ s‖ ^ 2` using `(norm_sq_eq_re_inner (𝕜 := ℂ) _).symm`. Rewrite using `[hv, Real.log_pow]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem arithDegree_line (h : HermitianMetric K E) (hE : Module.finrank (𝓞 K) E = 1) {s : E}
    (hs : s ≠ 0) :
    arithDegree h = Real.log (Nat.card (E ⧸ Submodule.span (𝓞 K) {s})) -
      ∑ σ : K →+* ℂ, Real.log ‖fibreVec h σ s‖ := by
  have hli : LinearIndependent (𝓞 K) (fun _ : Fin 1 ↦ s) := linearIndependent_unique_iff.mpr hs
  rw [arithDegree_eq h hli (by simp [hE]), degreeWith, Set.range_const]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ ↦ ?_
  simp only [gramDet, det_unique, gram_apply]
  have hv : (inner ℂ (fibreVec h σ s) (fibreVec h σ s)).re = ‖fibreVec h σ s‖ ^ 2 :=
    (norm_sq_eq_re_inner (𝕜 := ℂ) _).symm
  rw [hv, Real.log_pow]
  push_cast; ring

/- English proof (translation)
Rewrite using `[← arithDegree_line h hE hs, ← arithDegree_line h hE ht]`.
-/
theorem degree_line_indep (h : HermitianMetric K E) (hE : Module.finrank (𝓞 K) E = 1) {s t : E}
    (hs : s ≠ 0) (ht : t ≠ 0) :
    Real.log (Nat.card (E ⧸ Submodule.span (𝓞 K) {s})) - ∑ σ : K →+* ℂ, Real.log ‖fibreVec h σ s‖ =
      Real.log (Nat.card (E ⧸ Submodule.span (𝓞 K) {t})) -
        ∑ σ : K →+* ℂ, Real.log ‖fibreVec h σ t‖ := by
  rw [← arithDegree_line h hE hs, ← arithDegree_line h hE ht]

/- English proof (translation)
Rewrite using `[arithDegree_line _ (Module.finrank_self (𝓞 K)) one_ne_zero]`. Establish `h1 : Submodule.span (𝓞 K) {(1 : 𝓞 K)} = ⊤`. Rewrite using `[← Ideal.span, Ideal.span_singleton_one]`. Establish `h2 : ∀ σ : K →+* ℂ, ‖fibreVec (HermitianMetric.integers K) σ 1‖ = 1`. Introduce `σ`.

Use `norm_fibreVec_sq (HermitianMetric.integers K) σ 1` as an intermediate fact. Rewrite `this` using `[HermitianMetric.integers_inner]`. Simplify using `only [map_one, one_mul] at this`. Rewrite `this` using `[Complex.one_re]`. Establish `h4` using `norm_nonneg (fibreVec (HermitianMetric.integers K) σ 1)`.

Use polynomial arithmetic with `[sq_nonneg (‖fibreVec (HermitianMetric.integers K) σ 1‖ - 1)]`. Simplify using `only [h1, h2, Real.log_one, Finset.sum_const_zero, sub_zero]`. Rewrite using `[Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨0⟩⟩]`. Simplify using the standard rewrite rules.
-/
theorem arithDegree_integers : arithDegree (HermitianMetric.integers K) = 0 := by
  rw [arithDegree_line _ (Module.finrank_self (𝓞 K)) one_ne_zero]
  have h1 : Submodule.span (𝓞 K) {(1 : 𝓞 K)} = ⊤ := by
    rw [← Ideal.span, Ideal.span_singleton_one]
  have h2 : ∀ σ : K →+* ℂ, ‖fibreVec (HermitianMetric.integers K) σ 1‖ = 1 := by
    intro σ
    have := norm_fibreVec_sq (HermitianMetric.integers K) σ 1
    rw [HermitianMetric.integers_inner] at this
    simp only [map_one, one_mul] at this
    rw [Complex.one_re] at this
    have h4 := norm_nonneg (fibreVec (HermitianMetric.integers K) σ 1)
    nlinarith [sq_nonneg (‖fibreVec (HermitianMetric.integers K) σ 1‖ - 1)]
  simp only [h1, h2, Real.log_one, Finset.sum_const_zero, sub_zero]
  rw [Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨0⟩⟩]
  · simp

section Scale

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

@[instance_reducible]
def coreScale (hV : InnerProductSpace.Core ℂ V) (c : ℝ) (hc : 0 < c) :
    InnerProductSpace.Core ℂ V where
  inner x y := ((c ^ 2 : ℝ) : ℂ) * hV.inner x y
  conj_inner_symm x y := by
    rw [map_mul, Complex.conj_ofReal, hV.conj_inner_symm]
  re_inner_nonneg x := by
    change 0 ≤ Complex.re _
    rw [Complex.re_ofReal_mul]
    exact mul_nonneg (by positivity) (hV.re_inner_nonneg x)
  add_left x y z := by
    simp only [hV.add_left]
    ring
  smul_left x y r := by
    simp only [hV.smul_left]
    ring
  definite x hx := by
    have hc2 : ((c ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (pow_pos hc 2).ne'
    exact hV.definite x ((mul_eq_zero.mp hx).resolve_left hc2)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coreScale_inner (hV : InnerProductSpace.Core ℂ V) (c : ℝ) (hc : 0 < c) (x y : V) :
    (coreScale hV c hc).inner x y = ((c ^ 2 : ℝ) : ℂ) * hV.inner x y := rfl

end Scale

def HermitianMetric.scale (h : HermitianMetric K E) (c : ℝ) (hc : 0 < c) : HermitianMetric K E where
  form σ := coreScale (h.form σ) c hc
  form_conj σ x y := by
    rw [coreScale_inner, coreScale_inner, h.form_conj, map_mul, Complex.conj_ofReal]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem HermitianMetric.scale_inner (h : HermitianMetric K E) (c : ℝ) (hc : 0 < c)
    (σ : K →+* ℂ) (x y : Fibre σ E) :
    ((h.scale c hc).form σ).inner x y = ((c ^ 2 : ℝ) : ℂ) * (h.form σ).inner x y := rfl

/- English proof (translation)
Simplify using `only [gramDet]`. Establish `: (gram ℂ fun i ↦ fibreVec (h.scale c hc) σ (s i)) = ((c ^ 2 : ℝ) : ℂ) • gram ℂ fun i ↦ fibreVec h σ (s i)`. Use extensionality with `i j`. Both sides reduce to the same expression. Rewrite using `[this, det_smul, ← Complex.ofReal_pow, Complex.re_ofReal_mul, pow_mul]`.
-/
theorem gramDet_scale (h : HermitianMetric K E) (c : ℝ) (hc : 0 < c) (σ : K →+* ℂ) {ι : Type*}
    [Fintype ι] [DecidableEq ι] (s : ι → E) :
    gramDet (h.scale c hc) σ s = c ^ (2 * Fintype.card ι) * gramDet h σ s := by
  simp only [gramDet]
  have : (gram ℂ fun i ↦ fibreVec (h.scale c hc) σ (s i)) =
      ((c ^ 2 : ℝ) : ℂ) • gram ℂ fun i ↦ fibreVec h σ (s i) := by
    ext i j
    rfl
  rw [this, det_smul, ← Complex.ofReal_pow, Complex.re_ofReal_mul, pow_mul]

/- English proof (translation)
Take `⟨s, hs⟩` from `exists_linearIndependent_fin (K := K) (E := E)`. Rewrite using `[arithDegree_eq (h.scale c hc) hs (Fintype.card_fin _), arithDegree_eq h hs (Fintype.card_fin _)]`. Simplify using `only [degreeWith, gramDet_scale, Fintype.card_fin]`. Establish `hlog : ∀ σ : K →+* ℂ, Real.log (c ^ (2 * Module.finrank (𝓞 K) E) * gramDet h σ s) = 2 * Module.finrank (𝓞 K) E * Real.log c + Real.log (gramDet h σ s)` using `fun σ ↦ by`. Rewrite using `[Real.log_mul (pow_pos hc _).ne' (gramDet_pos h σ hs).ne', Real.log_pow]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [hlog]`. Rewrite using `[Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, NumberField.Embeddings.card, nsmul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem arithDegree_scale (h : HermitianMetric K E) (c : ℝ) (hc : 0 < c) :
    arithDegree (h.scale c hc) =
      arithDegree h - Module.finrank (𝓞 K) E * Module.finrank ℚ K * Real.log c := by
  obtain ⟨s, hs⟩ := exists_linearIndependent_fin (K := K) (E := E)
  rw [arithDegree_eq (h.scale c hc) hs (Fintype.card_fin _), arithDegree_eq h hs (Fintype.card_fin _)]
  simp only [degreeWith, gramDet_scale, Fintype.card_fin]
  have hlog : ∀ σ : K →+* ℂ, Real.log (c ^ (2 * Module.finrank (𝓞 K) E) * gramDet h σ s) =
      2 * Module.finrank (𝓞 K) E * Real.log c + Real.log (gramDet h σ s) := fun σ ↦ by
    rw [Real.log_mul (pow_pos hc _).ne' (gramDet_pos h σ hs).ne', Real.log_pow]
    push_cast; ring
  simp only [hlog]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, NumberField.Embeddings.card,
    nsmul_eq_mul]
  ring

/- English proof (translation)
Rewrite using `[arithDegree_scale, arithDegree_integers, Module.finrank_self, Module.finrank_self]`. Simplify using the standard rewrite rules.
-/
theorem arithDegree_ratIntegers_scale (c : ℝ) (hc : 0 < c) :
    arithDegree ((HermitianMetric.integers ℚ).scale c hc) = -Real.log c := by
  rw [arithDegree_scale, arithDegree_integers, Module.finrank_self, Module.finrank_self]
  simp

/- English proof (translation)
Rewrite using `[← arithDegree_line _ (Module.finrank_self (𝓞 ℚ)) hn, arithDegree_ratIntegers_scale]`.
-/
example (c : ℝ) (hc : 0 < c) (n : 𝓞 ℚ) (hn : n ≠ 0) :
    Real.log (Nat.card (𝓞 ℚ ⧸ Submodule.span (𝓞 ℚ) {n})) -
      ∑ σ : ℚ →+* ℂ, Real.log ‖fibreVec ((HermitianMetric.integers ℚ).scale c hc) σ n‖ =
      -Real.log c := by
  rw [← arithDegree_line _ (Module.finrank_self (𝓞 ℚ)) hn, arithDegree_ratIntegers_scale]

/- English proof (translation)
The claim follows from `arithDegree_ratIntegers_scale 2 two_pos`.
-/
example : arithDegree ((HermitianMetric.integers ℚ).scale 2 two_pos) = -Real.log 2 :=
  arithDegree_ratIntegers_scale 2 two_pos

end

end GroundTheory.Heights₂.Heights
