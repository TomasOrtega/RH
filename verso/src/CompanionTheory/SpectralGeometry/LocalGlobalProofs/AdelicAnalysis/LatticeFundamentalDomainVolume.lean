import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.FD

open scoped Pointwise

variable {F : Type} [Field F] [NumberField F]

def scaleMap (ρ : InfinitePlace F → (F →+* ℝ)) (N : ℕ) : 𝓞 F →+ (InfinitePlace F → ℝ) where
  toFun r := fun w => ρ w ((N : F) * (r : F))
  map_zero' := by ext w; simp
  map_add' a b := by ext w; simp [mul_add]

/- English proof (translation)
Establish `h : {y | ∃ r : 𝓞 F, y = fun w => ρ w ((N : F) * (r : F))} = ((scaleMap ρ N).range : Set (InfinitePlace F → ℝ))`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨r, rfl⟩`. Conclude with `⟨r, rfl⟩`.

Introduce and unpack `⟨r, rfl⟩`. Conclude with `⟨r, rfl⟩`. Rewrite using `[latR, h, AddSubgroup.closure_eq]`.
-/
theorem latR_eq_range (ρ : InfinitePlace F → (F →+* ℝ)) (N : ℕ) :
    latR ρ N = (scaleMap ρ N).range := by
  have h : {y | ∃ r : 𝓞 F, y = fun w => ρ w ((N : F) * (r : F))}
      = ((scaleMap ρ N).range : Set (InfinitePlace F → ℝ)) := by
    ext y
    constructor
    · rintro ⟨r, rfl⟩
      exact ⟨r, rfl⟩
    · rintro ⟨r, rfl⟩
      exact ⟨r, rfl⟩
  rw [latR, h, AddSubgroup.closure_eq]

/- English proof (translation)
Rewrite using `[latR_eq_range]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨r, rfl⟩`. Conclude with `⟨r, rfl⟩`. Introduce and unpack `⟨r, rfl⟩`.

Conclude with `⟨r, rfl⟩`.
-/
theorem mem_latR_iff (ρ : InfinitePlace F → (F →+* ℝ)) (N : ℕ) (y : InfinitePlace F → ℝ) :
    y ∈ latR ρ N ↔ ∃ r : 𝓞 F, y = fun w => ρ w ((N : F) * (r : F)) := by
  rw [latR_eq_range]
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨r, rfl⟩
  · rintro ⟨r, rfl⟩
    exact ⟨r, rfl⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `w w' h`. Use `congrArg InfinitePlace.mk h` as an intermediate fact. Simplify using `using this`. Introduce `φ`.

Establish `hr : ComplexEmbedding.IsReal φ` using `InfinitePlace.isReal_mk_iff.1 (hF.isReal (InfinitePlace.mk φ))`. Conclude with `⟨InfinitePlace.mk φ, InfinitePlace.embedding_mk_eq_of_isReal hr⟩`.
-/
theorem embedding_bijective (hF : IsTotallyReal F) :
    Function.Bijective (fun w : InfinitePlace F => (w.embedding : F →+* ℂ)) := by
  constructor
  · intro w w' h
    have := congrArg InfinitePlace.mk h
    simpa using this
  · intro φ
    have hr : ComplexEmbedding.IsReal φ :=
      InfinitePlace.isReal_mk_iff.1 (hF.isReal (InfinitePlace.mk φ))
    exact ⟨InfinitePlace.mk φ, InfinitePlace.embedding_mk_eq_of_isReal hr⟩

def placeEquiv (hF : IsTotallyReal F) : InfinitePlace F ≃ (F →ₐ[ℚ] ℂ) :=
  (Equiv.ofBijective _ (embedding_bijective hF)).trans (RingHom.equivRatAlgHom F ℂ)

/- English proof (translation)
Rewrite using `[Fintype.card_congr (placeEquiv hF), AlgHom.card]`.
-/
theorem card_places (hF : IsTotallyReal F) :
    Fintype.card (InfinitePlace F) = Module.finrank ℚ F := by
  rw [Fintype.card_congr (placeEquiv hF), AlgHom.card]

/- English proof (translation)
Establish `hc : Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 F)) = Fintype.card (InfinitePlace F)`. Rewrite using `[card_places hF, ← Module.finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank]`. Set `e0` to `Fintype.equivOfCardEq hc`. Set `bq` to `(integralBasis F).reindex e0`. Use `⟨(RingOfIntegers.basis F).reindex e0, ?_⟩` and prove the remaining obligations.

Establish `h` using `Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ ℂ bq (placeEquiv hF)`. Establish `hd : Algebra.discr ℚ bq = (discr F : ℚ)`. Rewrite using `[coe_discr]`. Establish `h0` using `Algebra.discr_reindex ℚ (integralBasis F) e0`. Rewrite `h0` using `[← Module.Basis.coe_reindex]`. Then use the resulting hypothesis.

Establish `hM : Algebra.embeddingsMatrixReindex ℚ ℂ bq (placeEquiv hF) = (Matrix.of fun i w => ρ w (((RingOfIntegers.basis F).reindex e0 i : 𝓞 F) : F)).map Complex.ofRealHom`. Use extensionality with `i w`. Simplify using `[Algebra.embeddingsMatrixReindex, Algebra.embeddingsMatrix, placeEquiv, bq, hρ, integralBasis_apply, Module.Basis.reindex_apply]`. Rewrite `h` using `[hM, hd, ← RingHom.mapMatrix_apply, ← RingHom.map_det]`. Establish `h2 : (((discr F : ℝ)) : ℂ) = (((Matrix.det (Matrix.of fun i w => ρ w (((RingOfIntegers.basis F).reindex e0 i : 𝓞 F) : F))) ^ 2 : ℝ) : ℂ)`.

Simplify using `using h`. Conclude with `h2.symm` after adjusting the coercions.
-/
theorem exists_integral_basis [DecidableEq (InfinitePlace F)] (hF : IsTotallyReal F) (ρ : InfinitePlace F → (F →+* ℝ))
    (hρ : ∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) :
    ∃ B : Module.Basis (InfinitePlace F) ℤ (𝓞 F),
      (Matrix.det (Matrix.of fun i w => ρ w ((B i : 𝓞 F) : F))) ^ 2 = (discr F : ℝ) := by
  classical
  have hc : Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 F)) = Fintype.card (InfinitePlace F) := by
    rw [card_places hF, ← Module.finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank]
  let e0 := Fintype.equivOfCardEq hc
  let bq := (integralBasis F).reindex e0
  refine ⟨(RingOfIntegers.basis F).reindex e0, ?_⟩
  have h := Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ ℂ bq (placeEquiv hF)
  have hd : Algebra.discr ℚ bq = (discr F : ℚ) := by
    rw [coe_discr]
    have h0 := Algebra.discr_reindex ℚ (integralBasis F) e0
    rwa [← Module.Basis.coe_reindex] at h0
  have hM : Algebra.embeddingsMatrixReindex ℚ ℂ bq (placeEquiv hF) =
      (Matrix.of fun i w => ρ w (((RingOfIntegers.basis F).reindex e0 i : 𝓞 F) : F)).map
        Complex.ofRealHom := by
    ext i w
    simp [Algebra.embeddingsMatrixReindex, Algebra.embeddingsMatrix, placeEquiv, bq, hρ,
      integralBasis_apply, Module.Basis.reindex_apply]
  rw [hM, hd, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at h
  have h2 : (((discr F : ℝ)) : ℂ) = (((Matrix.det (Matrix.of fun i w =>
      ρ w (((RingOfIntegers.basis F).reindex e0 i : 𝓞 F) : F))) ^ 2 : ℝ) : ℂ) := by
    simpa using h
  exact_mod_cast h2.symm

/- English proof (translation)
Establish `hl : LinearIndependent ℝ A.row` using `Matrix.linearIndependent_rows_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det A).2 (isUnit_iff_ne_zero.2 h))`. Use `⟨basisOfLinearIndependentOfCardEqFinrank hl (by simp), fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[coe_basisOfLinearIndependentOfCardEqFinrank]`. Both sides reduce to the same expression.
-/
theorem exists_real_basis {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] (A : Matrix ι ι ℝ) (h : A.det ≠ 0) :
    ∃ b : Module.Basis ι ℝ (ι → ℝ), ∀ i, b i = A i := by
  have hl : LinearIndependent ℝ A.row :=
    Matrix.linearIndependent_rows_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det A).2 (isUnit_iff_ne_zero.2 h))
  refine ⟨basisOfLinearIndependentOfCardEqFinrank hl (by simp), fun i => ?_⟩
  rw [coe_basisOfLinearIndependentOfCardEqFinrank]
  rfl

/- English proof (translation)
Take `⟨z, hz⟩ : ∃ z : ℤ, algebraMap ℤ ℚ z = Algebra.trace ℚ F (a : F)` from `IsIntegrallyClosed.isIntegral_iff.1 (Algebra.isIntegral_trace (R := ℤ) (L := ℚ) (F := F) (RingOfIntegers.isIntegral_coe a))`. Use `⟨z, ?_⟩` and prove the remaining obligations. Establish `h` using `trace_eq_sum_embeddings (K := ℚ) (L := F) ℂ (x := (a : F))`. Rewrite `h` using `[← (placeEquiv hF).sum_comp, ← hz]`. Establish `h2 : ((z : ℝ) : ℂ) = ((∑ w, ρ w (a : F) : ℝ) : ℂ)`.

Use `push_cast`. Simplify using `only [hρ]`. Simplify `h` using `[placeEquiv]`. Conclude with `h2.symm` after adjusting the coercions.
-/
theorem sum_places_int (hF : IsTotallyReal F) (ρ : InfinitePlace F → (F →+* ℝ))
    (hρ : ∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) (a : 𝓞 F) :
    ∃ z : ℤ, ∑ w, ρ w (a : F) = (z : ℝ) := by
  obtain ⟨z, hz⟩ : ∃ z : ℤ, algebraMap ℤ ℚ z = Algebra.trace ℚ F (a : F) :=
    IsIntegrallyClosed.isIntegral_iff.1
      (Algebra.isIntegral_trace (R := ℤ) (L := ℚ) (F := F) (RingOfIntegers.isIntegral_coe a))
  refine ⟨z, ?_⟩
  have h := trace_eq_sum_embeddings (K := ℚ) (L := F) ℂ (x := (a : F))
  rw [← (placeEquiv hF).sum_comp, ← hz] at h
  have h2 : ((z : ℝ) : ℂ) = ((∑ w, ρ w (a : F) : ℝ) : ℂ) := by
    push_cast
    simp only [hρ]
    simpa [placeEquiv] using h
  exact_mod_cast h2.symm

/- English proof (translation)
Use `set f : (InfinitePlace F → ℝ) → ℂ := fun x => Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, ρ w β * x w : ℝ) : ℂ)) with hf`. Establish `hadd : ∀ x y, f (x + y) = f x * f y`. Introduce `x y`. Simplify using `only [hf, Pi.add_apply, mul_add, Finset.sum_add_distrib, Complex.ofReal_add, Complex.exp_add]`. Establish `hper : ∀ (g : latR ρ N) x, f (g +ᵥ x) = f x`.

Introduce and unpack `⟨g, hg⟩ x`. Take `⟨s, rfl⟩` from `(mem_latR_iff ρ N g).1 hg`. Take `⟨r, hr⟩` from `hint`. Take `⟨z, hz⟩` from `sum_places_int hF ρ hρ (r * s)`. Establish `hrs : ((r * s : 𝓞 F) : F) = (N : F) * β * (s : F)`.

Rewrite using `[← hr]`. Use `first`. Consider the case `rfl`. Consider the case `simp`. Establish `h1 : f (fun w => ρ w ((N : F) * (s : F))) = 1`.

Establish `: (∑ w, ρ w β * ρ w ((N : F) * (s : F))) = (z : ℝ)`. Rewrite using `[← hz]`. Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations. Rewrite using `[← map_mul]`. Use `congr 1`.

Rewrite using `[hrs]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [hf, this]`. Use `Complex.exp_int_mul_two_pi_mul_I z` as an intermediate fact. Rewrite using `[← this]`.

Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use `show f ((fun w => ρ w ((N : F) * (s : F))) + x) = f x`. Rewrite using `[hadd, h1, one_mul]`.

Take `⟨w0⟩ : Nonempty (InfinitePlace F)` from `inferInstance`. Establish `hρ0 : ρ w0 β ≠ 0`. Simplify using `using hβ`. Set `x0 : InfinitePlace F → ℝ` to `Pi.single w0 (1 / (2 * ρ w0 β))`. Establish `hx0 : f x0 = -1`.

Establish `: (∑ w, ρ w β * x0 w) = 1 / 2`. Rewrite using `[Finset.sum_eq_single w0]`. Simplify using `only [x0, Pi.single_eq_same]`. Clear the denominators using the available nonvanishing facts. Introduce `b _ hb`.

Simplify using `[x0, Pi.single_eq_of_ne hb]`. Simplify using the standard rewrite rules. Simplify using `only [hf, this]`. Rewrite using `[← Complex.exp_pi_mul_I]`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hD' : IsAddFundamentalDomain (latR ρ N) (x0 +ᵥ D) volume` using `hD.vadd_of_comm x0`. Establish `heq : ∫ x in x0 +ᵥ D, f x = ∫ x in D, f x` using `hD'.setIntegral_eq hD hper`. Establish `htr : ∫ x in x0 +ᵥ D, f x = ∫ x in D, f (x0 + x)`.

Use `(measurePreserving_add_left (volume : Measure (InfinitePlace F → ℝ)) x0).setIntegral_image_emb (measurableEmbedding_addLeft x0) f D` as an intermediate fact. Rewrite using `[← this, ← Set.image_vadd]`. Both sides reduce to the same expression. Establish `hmul : ∫ x in D, f (x0 + x) = - ∫ x in D, f x`. Simplify using `only [hadd, hx0]`.

Rewrite using `[integral_const_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `h2 : ∫ x in D, f x = - ∫ x in D, f x`. Rewrite using `[← hmul, ← htr, heq]`. Establish `h3 : (2 : ℂ) * ∫ x in D, f x = 0`.

Take the linear combination `h2`. Simplify using `using h3`.
-/
theorem integral_char_eq_zero (hF : IsTotallyReal F) (ρ : InfinitePlace F → (F →+* ℝ))
    (hρ : ∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) (N : ℕ)
    [Countable (latR ρ N)]
    (D : Set (InfinitePlace F → ℝ)) (hD : IsAddFundamentalDomain (latR ρ N) D volume)
    (β : F) (hβ : β ≠ 0) (hint : ∃ r : 𝓞 F, (r : F) = (N : F) * β) :
    ∫ x in D, Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, ρ w β * x w : ℝ) : ℂ)) = 0 := by
  classical
  set f : (InfinitePlace F → ℝ) → ℂ := fun x =>
    Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, ρ w β * x w : ℝ) : ℂ)) with hf
  have hadd : ∀ x y, f (x + y) = f x * f y := by
    intro x y
    simp only [hf, Pi.add_apply, mul_add, Finset.sum_add_distrib, Complex.ofReal_add, Complex.exp_add]
  have hper : ∀ (g : latR ρ N) x, f (g +ᵥ x) = f x := by
    rintro ⟨g, hg⟩ x
    obtain ⟨s, rfl⟩ := (mem_latR_iff ρ N g).1 hg
    obtain ⟨r, hr⟩ := hint
    obtain ⟨z, hz⟩ := sum_places_int hF ρ hρ (r * s)
    have hrs : ((r * s : 𝓞 F) : F) = (N : F) * β * (s : F) := by
      rw [← hr]
      first
        | rfl
        | simp
    have h1 : f (fun w => ρ w ((N : F) * (s : F))) = 1 := by
      have : (∑ w, ρ w β * ρ w ((N : F) * (s : F))) = (z : ℝ) := by
        rw [← hz]
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [← map_mul]
        congr 1
        rw [hrs]
        ring
      simp only [hf, this]
      have := Complex.exp_int_mul_two_pi_mul_I z
      rw [← this]
      congr 1
      push_cast
      ring
    show f ((fun w => ρ w ((N : F) * (s : F))) + x) = f x
    rw [hadd, h1, one_mul]
  obtain ⟨w0⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hρ0 : ρ w0 β ≠ 0 := by
    simpa using hβ
  let x0 : InfinitePlace F → ℝ := Pi.single w0 (1 / (2 * ρ w0 β))
  have hx0 : f x0 = -1 := by
    have : (∑ w, ρ w β * x0 w) = 1 / 2 := by
      rw [Finset.sum_eq_single w0]
      · simp only [x0, Pi.single_eq_same]
        field_simp
      · intro b _ hb
        simp [x0, Pi.single_eq_of_ne hb]
      · simp
    simp only [hf, this]
    rw [← Complex.exp_pi_mul_I]
    congr 1
    push_cast
    ring
  have hD' : IsAddFundamentalDomain (latR ρ N) (x0 +ᵥ D) volume := hD.vadd_of_comm x0
  have heq : ∫ x in x0 +ᵥ D, f x = ∫ x in D, f x := hD'.setIntegral_eq hD hper
  have htr : ∫ x in x0 +ᵥ D, f x = ∫ x in D, f (x0 + x) := by
    have := (measurePreserving_add_left (volume : Measure (InfinitePlace F → ℝ)) x0).setIntegral_image_emb
      (measurableEmbedding_addLeft x0) f D
    rw [← this, ← Set.image_vadd]
    rfl
  have hmul : ∫ x in D, f (x0 + x) = - ∫ x in D, f x := by
    simp only [hadd, hx0]
    rw [integral_const_mul]
    ring
  have h2 : ∫ x in D, f x = - ∫ x in D, f x := by
    rw [← hmul, ← htr, heq]
  have h3 : (2 : ℂ) * ∫ x in D, f x = 0 := by
    linear_combination h2
  simpa using h3

end GlobalTheory.CompanionTheory.SW.FD

/- English proof (translation)
Introduce `F _ _ hF ρ hρ N hN`. Take `⟨B, hB⟩` from `GlobalTheory.CompanionTheory.SW.FD.exists_integral_basis hF ρ hρ`. Use `set M : Matrix (InfinitePlace F) (InfinitePlace F) ℝ := Matrix.of fun i w => ρ w ((B i : 𝓞 F) : F) with hM`. Establish `hN' : (N : ℝ) ≠ 0` using `by exact_mod_cast hN.ne'`. Establish `hdisc : (discr F : ℝ) ≠ 0` using `by exact_mod_cast discr_ne_zero F`.

Establish `hdet : M.det ≠ 0`. Introduce `h`. Apply `hdisc` to reduce the goal to its premises. Rewrite using `[← hB, h]`. Simplify using the standard rewrite rules.

Establish `hAdet : ((N : ℝ) • M).det ≠ 0`. Rewrite using `[Matrix.det_smul]`. Conclude with `mul_ne_zero (pow_ne_zero _ hN') hdet`. Take `⟨b, hb⟩` from `GlobalTheory.CompanionTheory.SW.FD.exists_real_basis _ hAdet`. Establish `hbi : ∀ i, b i = GlobalTheory.CompanionTheory.SW.FD.scaleMap ρ N (B i)`.

Introduce `i`. Rewrite using `[hb]`. Use extensionality with `w`. Simplify using `[GlobalTheory.CompanionTheory.SW.FD.scaleMap, hM]`. Establish `hspan : latR ρ N = (Submodule.span ℤ (Set.range b)).toAddSubgroup`.

Rewrite using `[GlobalTheory.CompanionTheory.SW.FD.latR_eq_range, Submodule.span_int_eq_addSubgroupClosure]`. Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `_ ⟨r, rfl⟩`. Rewrite using `[← B.sum_repr r, map_sum]`. Use `AddSubgroup.sum_mem _ fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[map_zsmul, ← hbi]`. Conclude with `AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (Set.mem_range_self i)) _`. Rewrite using `[AddSubgroup.closure_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `⟨B i, (hbi i).symm⟩`.

Establish `hfd : IsAddFundamentalDomain (latR ρ N) (ZSpan.fundamentalDomain b) volume`. Rewrite using `[hspan]`. Conclude with `ZSpan.isAddFundamentalDomain' b volume`. Establish `hcount : Countable (latR ρ N)` using `by haveI : Countable (𝓞 F) := B.equivFun.toEquiv.injective.countable`. Rewrite using `[GlobalTheory.CompanionTheory.SW.FD.latR_eq_range]`.

Conclude with `(Set.countable_range (GlobalTheory.CompanionTheory.SW.FD.scaleMap ρ N)).to_subtype`. Use `⟨⟨_, hfd⟩, hcount, GlobalTheory.CompanionTheory.SW.FD.mem_latR_iff ρ N, fun D hD => ⟨?_, fun β hβ hint => GlobalTheory.CompanionTheory.SW.FD.integral_char_eq_zero hF ρ hρ N D hD β hβ hint⟩⟩` and prove the remaining obligations. Rewrite using `[hD.measure_eq hfd, ZSpan.volume_fundamentalDomain]`. Establish `hof : Matrix.of (b : InfinitePlace F → InfinitePlace F → ℝ) = (N : ℝ) • M`. Use extensionality with `i w`.

Rewrite using `[Matrix.of_apply, hb]`. Rewrite using `[hof, Matrix.det_smul, GlobalTheory.CompanionTheory.SW.FD.card_places hF, abs_mul, abs_of_nonneg (by positivity)]`. Use `congr 2`. Rewrite using `[kap, inv_inv, ← hB, abs_of_nonneg (sq_nonneg M.det), Real.sqrt_sq_eq_abs]`.
-/
theorem GlobalTheory.CompanionTheory.SW.FD.main : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ ρ : InfinitePlace F → (F →+* ℝ), (∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) → ∀ N : ℕ, 0 < N → (∃ D : Set (InfinitePlace F → ℝ), IsAddFundamentalDomain (latR ρ N) D volume) ∧ Countable (latR ρ N) ∧ (∀ y, y ∈ latR ρ N ↔ ∃ r : 𝓞 F, y = fun w => ρ w ((N : F) * (r : F))) ∧ ∀ D : Set (InfinitePlace F → ℝ), IsAddFundamentalDomain (latR ρ N) D volume → volume D = ENNReal.ofReal ((N : ℝ) ^ Module.finrank ℚ F * (kap F)⁻¹) ∧ ∀ β : F, β ≠ 0 → (∃ r : 𝓞 F, (r : F) = (N : F) * β) → ∫ x in D, Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, ρ w β * x w : ℝ) : ℂ)) = 0 := by
  intro F _ _ hF ρ hρ N hN
  classical
  obtain ⟨B, hB⟩ := GlobalTheory.CompanionTheory.SW.FD.exists_integral_basis hF ρ hρ
  set M : Matrix (InfinitePlace F) (InfinitePlace F) ℝ :=
    Matrix.of fun i w => ρ w ((B i : 𝓞 F) : F) with hM
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hdisc : (discr F : ℝ) ≠ 0 := by exact_mod_cast discr_ne_zero F
  have hdet : M.det ≠ 0 := by
    intro h
    apply hdisc
    rw [← hB, h]
    simp
  have hAdet : ((N : ℝ) • M).det ≠ 0 := by
    rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ hN') hdet
  obtain ⟨b, hb⟩ := GlobalTheory.CompanionTheory.SW.FD.exists_real_basis _ hAdet
  have hbi : ∀ i, b i = GlobalTheory.CompanionTheory.SW.FD.scaleMap ρ N (B i) := by
    intro i
    rw [hb]
    ext w
    simp [GlobalTheory.CompanionTheory.SW.FD.scaleMap, hM]
  have hspan : latR ρ N = (Submodule.span ℤ (Set.range b)).toAddSubgroup := by
    rw [GlobalTheory.CompanionTheory.SW.FD.latR_eq_range, Submodule.span_int_eq_addSubgroupClosure]
    apply le_antisymm
    · rintro _ ⟨r, rfl⟩
      rw [← B.sum_repr r, map_sum]
      refine AddSubgroup.sum_mem _ fun i _ => ?_
      rw [map_zsmul, ← hbi]
      exact AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (Set.mem_range_self i)) _
    · rw [AddSubgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      exact ⟨B i, (hbi i).symm⟩
  have hfd : IsAddFundamentalDomain (latR ρ N) (ZSpan.fundamentalDomain b) volume := by
    rw [hspan]
    exact ZSpan.isAddFundamentalDomain' b volume
  have hcount : Countable (latR ρ N) := by
    haveI : Countable (𝓞 F) := B.equivFun.toEquiv.injective.countable
    rw [GlobalTheory.CompanionTheory.SW.FD.latR_eq_range]
    exact (Set.countable_range (GlobalTheory.CompanionTheory.SW.FD.scaleMap ρ N)).to_subtype
  refine ⟨⟨_, hfd⟩, hcount, GlobalTheory.CompanionTheory.SW.FD.mem_latR_iff ρ N, fun D hD => ⟨?_, fun β hβ hint =>
    GlobalTheory.CompanionTheory.SW.FD.integral_char_eq_zero hF ρ hρ N D hD β hβ hint⟩⟩
  rw [hD.measure_eq hfd, ZSpan.volume_fundamentalDomain]
  have hof : Matrix.of (b : InfinitePlace F → InfinitePlace F → ℝ) = (N : ℝ) • M := by
    ext i w
    rw [Matrix.of_apply, hb]
  rw [hof, Matrix.det_smul, GlobalTheory.CompanionTheory.SW.FD.card_places hF, abs_mul, abs_of_nonneg (by positivity)]
  congr 2
  rw [kap, inv_inv, ← hB, abs_of_nonneg (sq_nonneg M.det), Real.sqrt_sq_eq_abs]
