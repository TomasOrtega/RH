import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.WhitKOfSteps

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula.KWhit

open PositivityTheory.SiegelWeilFormula

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

/- English proof (translation)
Establish `hne : μ ≠ 0`. Introduce `h0`. Use `IsOpen.measure_ne_zero μ isOpen_univ Set.univ_nonempty` as an intermediate fact. Simplify using `[h0] at this`. Establish `aem : ∀ g' : G, AEMeasurable (fun x => g' + x) μ`.

Introduce `g'`. Assume the negation of the conclusion as `hc`. Use `Measure.IsAddLeftInvariant.map_add_left_eq_self (μ := μ) g'` as an intermediate fact. Rewrite `this` using `[Measure.map_of_not_aemeasurable hc]`. Conclude with `hne this.symm`.

Establish `hmap : Measure.map (fun x => g + x) μ = μ` using `Measure.IsAddLeftInvariant.map_add_left_eq_self g`. Distinguish the cases in `hf : AEStronglyMeasurable f μ`. Use `conv_rhs => rw [← hmap]`. Rewrite using `[integral_map (aem g) (by rwa [hmap])]`. Establish `hf' : ¬ AEStronglyMeasurable (fun x => f (g + x)) μ`.

Introduce `h`. Apply `hf` to reduce the goal to its premises. Establish `h2 : AEStronglyMeasurable (fun x => f (g + x)) (Measure.map (fun x => -g + x) μ)`. Rewrite using `[Measure.IsAddLeftInvariant.map_add_left_eq_self]` and apply the resulting hypothesis. Use `h2.comp_aemeasurable (aem (-g))` as an intermediate fact.

Simplify `this` using `[Function.comp_def, add_neg_cancel_left]`. Rewrite using `[integral_non_aestronglyMeasurable hf, integral_non_aestronglyMeasurable hf']`.
-/
theorem integral_add_left_haar {G : Type} [MeasurableSpace G] [TopologicalSpace G] [AddGroup G] (μ : Measure G)
    [μ.IsAddHaarMeasure] (g : G) (f : G → ℂ) : ∫ x, f (g + x) ∂μ = ∫ x, f x ∂μ := by
  have hne : μ ≠ 0 := by
    intro h0
    have := IsOpen.measure_ne_zero μ isOpen_univ Set.univ_nonempty
    simp [h0] at this
  have aem : ∀ g' : G, AEMeasurable (fun x => g' + x) μ := by
    intro g'
    by_contra hc
    have := Measure.IsAddLeftInvariant.map_add_left_eq_self (μ := μ) g'
    rw [Measure.map_of_not_aemeasurable hc] at this
    exact hne this.symm
  have hmap : Measure.map (fun x => g + x) μ = μ := Measure.IsAddLeftInvariant.map_add_left_eq_self g
  by_cases hf : AEStronglyMeasurable f μ
  · conv_rhs => rw [← hmap]
    rw [integral_map (aem g) (by rwa [hmap])]
  · have hf' : ¬ AEStronglyMeasurable (fun x => f (g + x)) μ := by
      intro h
      apply hf
      have h2 : AEStronglyMeasurable (fun x => f (g + x)) (Measure.map (fun x => -g + x) μ) := by
        rwa [Measure.IsAddLeftInvariant.map_add_left_eq_self]
      have := h2.comp_aemeasurable (aem (-g))
      simpa [Function.comp_def, add_neg_cancel_left] using this
    rw [integral_non_aestronglyMeasurable hf, integral_non_aestronglyMeasurable hf']

/- English proof (translation)
Take `⟨H, ⟨U, hsU, hU, hmer, σ', heq⟩, han, rfl⟩` from `hh`. Use `⟨fun z => c * H z, ⟨U, hsU, hU, fun z hz => (MeromorphicAt.const c z).mul (hmer z hz), σ', ?_⟩, analyticAt_const.mul han, rfl⟩` and prove the remaining obligations. Introduce `z hz`. Simplify using `only [heq hz]`.
-/
theorem holValueAt_const_mul {h : ℂ → ℂ} {s v : ℂ} (c : ℂ) (hh : HolValueAt h s v) :
    HolValueAt (fun z => c * h z) s (c * v) := by
  obtain ⟨H, ⟨U, hsU, hU, hmer, σ', heq⟩, han, rfl⟩ := hh
  refine ⟨fun z => c * H z, ⟨U, hsU, hU, fun z hz => (MeromorphicAt.const c z).mul (hmer z hz), σ', ?_⟩,
    analyticAt_const.mul han, rfl⟩
  intro z hz
  simp only [heq hz]

/- English proof (translation)
Simplify using `only [incM, ← Matrix.map_mul, Units.mul_inv]`. Conclude with `Matrix.map_one _ (map_zero _) (map_one _)`.
-/
theorem incM_mul_inv (d : SD σ) : incM F d.b.1 * incM F (d.b⁻¹).1 = 1 := by
  simp only [incM, ← Matrix.map_mul, Units.mul_inv]
  exact Matrix.map_one _ (map_zero _) (map_one _)

/- English proof (translation)
Simplify using `only [incM, ← Matrix.map_mul, Units.inv_mul]`. Conclude with `Matrix.map_one _ (map_zero _) (map_one _)`.
-/
theorem incM_inv_mul (d : SD σ) : incM F (d.b⁻¹).1 * incM F d.b.1 = 1 := by
  simp only [incM, ← Matrix.map_mul, Units.inv_mul]
  exact Matrix.map_one _ (map_zero _) (map_one _)

/- English proof (translation)
Establish `h1` using `incM_mul_inv d`. Establish `e : mat2 (x * y) = mat2 x * mat2 y` using `rfl`. Simplify using `only [inFrame, e]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[h1, Matrix.mul_one]`.

Simplify using `only [Matrix.mul_assoc]`. Use `_ = _ := by simp only [Matrix.mul_assoc]`.
-/
theorem inFrame_mul (d : SD σ) (x y : d.G) : inFrame d.b (x * y) = inFrame d.b x * inFrame d.b y := by
  have h1 := incM_mul_inv d
  have e : mat2 (x * y) = mat2 x * mat2 y := rfl
  simp only [inFrame, e]
  calc incM F (d.b⁻¹).1 * (mat2 x * mat2 y) * incM F d.b.1
      = incM F (d.b⁻¹).1 * mat2 x * (incM F d.b.1 * incM F (d.b⁻¹).1) * mat2 y * incM F d.b.1 := by
        rw [h1, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]

/- English proof (translation)
Simplify using `only [inFrame, ← Matrix.mul_assoc, incM_mul_inv d, Matrix.one_mul]`. Rewrite using `[Matrix.mul_assoc, incM_mul_inv d, Matrix.mul_one]`.
-/
theorem matrix_eq_frame_conjugate (d : SD σ) (x : d.G) : mat2 x = incM F d.b.1 * inFrame d.b x * incM F (d.b⁻¹).1 := by
  simp only [inFrame, ← Matrix.mul_assoc, incM_mul_inv d, Matrix.one_mul]
  rw [Matrix.mul_assoc, incM_mul_inv d, Matrix.mul_one]

/- English proof (translation)
Introduce `x y h`. Establish `: mat2 x = mat2 y` using `by rw [matrix_eq_frame_conjugate d x, matrix_eq_frame_conjugate d y, h]`. Conclude with `Subtype.ext (Units.ext this)`.
-/
theorem inFrame_injective (d : SD σ) : Function.Injective (inFrame (σ := σ) (Y := d.Y) d.b) := by
  intro x y h
  have : mat2 x = mat2 y := by rw [matrix_eq_frame_conjugate d x, matrix_eq_frame_conjugate d y, h]
  exact Subtype.ext (Units.ext this)

/- English proof (translation)
The claim follows from `d.ok.dbl.weil.2.1.pres g Φ h`.
-/
theorem om_mem_sch (d : SD σ) (g : d.G) {Φ : d.Fn} (h : Φ ∈ d.sch) : d.om g Φ ∈ d.sch :=
  d.ok.dbl.weil.2.1.pres g Φ h

/- English proof (translation)
Simplify using `[SD.sec0, map_mul, Module.End.mul_apply]`.
-/
theorem section_mul_weil_action (d : SD σ) (Φ : d.Fn) (g k : d.G) : d.sec0 Φ (g * k) = d.sec0 (d.om k Φ) g := by
  simp [SD.sec0, map_mul, Module.End.mul_apply]

/- English proof (translation)
Take `⟨p, t, hp, k', hk', rfl⟩` from `d.ok.hgt.iwa g`. Rewrite using `[mul_assoc, d.ok.hgt.val p t hp _ (d.K.mul_mem hk' hk), d.ok.hgt.val p t hp _ hk']`.
-/
theorem a_mul_K (d : SD σ) (g k : d.G) (hk : k ∈ d.K) : d.a (g * k) = d.a g := by
  obtain ⟨p, t, hp, k', hk', rfl⟩ := d.ok.hgt.iwa g
  rw [mul_assoc, d.ok.hgt.val p t hp _ (d.K.mul_mem hk' hk), d.ok.hgt.val p t hp _ hk']

/- English proof (translation)
Use `⟨om_mem_sch d k hΦ.1, ?_⟩` and prove the remaining obligations. Establish `hfd : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : d.K => d.om k.1 Φ))` using `hΦ.2`. Use `Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (Set.range fun k : d.K => d.om k.1 Φ)) (Submodule.span_le.2 ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨k', rfl⟩`. Use `Submodule.subset_span ⟨⟨k'.1 * k, d.K.mul_mem k'.2 hk⟩, ?_⟩` and prove the remaining obligations.

Simplify using `[map_mul, Module.End.mul_apply]`.
-/
theorem kfin_om (d : SD σ) {Φ : d.Fn} (hΦ : d.KFin Φ) {k : d.G} (hk : k ∈ d.K) : d.KFin (d.om k Φ) := by
  refine ⟨om_mem_sch d k hΦ.1, ?_⟩
  have hfd : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : d.K => d.om k.1 Φ)) := hΦ.2
  refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (Set.range fun k : d.K => d.om k.1 Φ))
    (Submodule.span_le.2 ?_)
  rintro _ ⟨k', rfl⟩
  refine Submodule.subset_span ⟨⟨k'.1 * k, d.K.mul_mem k'.2 hk⟩, ?_⟩
  simp [map_mul, Module.End.mul_apply]

section Forms

variable {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]

/- English proof (translation)
Establish `h1 : Yᵀ * Xᵀ = 1` using `by rw [← Matrix.transpose_mul, hXY, Matrix.transpose_one]`. Establish `h2 : X.map c * Y.map c = 1` using `by rw [← Matrix.map_mul, hXY, Matrix.map_one _ (map_zero c) (map_one c)]`. Simplify using `only [Matrix.transpose_mul, Matrix.map_mul]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`.

Use `_ = Xᵀ * J * X.map c := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one, hM]`.
-/
theorem form_conj_in (c : R →+* R) {X Y M J : Matrix ι ι R} (hXY : X * Y = 1) (hM : Mᵀ * J * M.map c = J) :
    (Y * M * X)ᵀ * (Xᵀ * J * X.map c) * (Y * M * X).map c = Xᵀ * J * X.map c := by
  have h1 : Yᵀ * Xᵀ = 1 := by rw [← Matrix.transpose_mul, hXY, Matrix.transpose_one]
  have h2 : X.map c * Y.map c = 1 := by rw [← Matrix.map_mul, hXY, Matrix.map_one _ (map_zero c) (map_one c)]
  simp only [Matrix.transpose_mul, Matrix.map_mul]
  calc _ = Xᵀ * (Mᵀ * ((Yᵀ * Xᵀ) * J * (X.map c * Y.map c)) * M.map c) * X.map c := by
        simp only [Matrix.mul_assoc]
    _ = Xᵀ * J * X.map c := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one, hM]

/- English proof (translation)
Establish `h1 : Yᵀ * Xᵀ = 1` using `by rw [← Matrix.transpose_mul, hXY, Matrix.transpose_one]`. Establish `h2 : X.map c * Y.map c = 1` using `by rw [← Matrix.map_mul, hXY, Matrix.map_one _ (map_zero c) (map_one c)]`. Simplify using `only [Matrix.transpose_mul, Matrix.map_mul]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem form_conj_out (c : R →+* R) {X Y N J : Matrix ι ι R} (hXY : X * Y = 1)
    (hN : Nᵀ * (Xᵀ * J * X.map c) * N.map c = Xᵀ * J * X.map c) :
    (X * N * Y)ᵀ * J * (X * N * Y).map c = J := by
  have h1 : Yᵀ * Xᵀ = 1 := by rw [← Matrix.transpose_mul, hXY, Matrix.transpose_one]
  have h2 : X.map c * Y.map c = 1 := by rw [← Matrix.map_mul, hXY, Matrix.map_one _ (map_zero c) (map_one c)]
  simp only [Matrix.transpose_mul, Matrix.map_mul]
  calc _ = Yᵀ * (Nᵀ * (Xᵀ * J * X.map c) * N.map c) * Y.map c := by simp only [Matrix.mul_assoc]
    _ = (Yᵀ * Xᵀ) * J * (X.map c * Y.map c) := by rw [hN]; simp only [Matrix.mul_assoc]
    _ = J := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]

/- English proof (translation)
Simplify using `only [Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply, Matrix.transpose_zero, Matrix.map_zero _ (map_zero c), Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.mul_one, Matrix.fromBlocks_inj] at h ⊢`. Conclude with `⟨h.1, h.2.1, h.2.2.1, trivial⟩`.
-/
theorem block_diag_form (c : R →+* R) {κ : Type} [Fintype κ] [DecidableEq κ] (A B D C' : Matrix κ κ R)
    (h : (Matrix.fromBlocks A B 0 D)ᵀ * Matrix.fromBlocks 0 1 C' 0 * (Matrix.fromBlocks A B 0 D).map c =
      Matrix.fromBlocks 0 1 C' 0) :
    (Matrix.fromBlocks A 0 0 D)ᵀ * Matrix.fromBlocks 0 1 C' 0 * (Matrix.fromBlocks A 0 0 D).map c =
      Matrix.fromBlocks 0 1 C' 0 := by
  simp only [Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply, Matrix.transpose_zero,
    Matrix.map_zero _ (map_zero c), Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.mul_one,
    Matrix.fromBlocks_inj] at h ⊢
  exact ⟨h.1, h.2.1, h.2.2.1, trivial⟩

end Forms

local notation:70 X:70 " ⬝ " Y:71 => @HMul.hMul _ _ _ Matrix.instHMulOfFintypeOfMulOfAddCommMonoid X Y

omit [NumberField E] in
/- English proof (translation)
The claim follows from `Matrix.map_mul`.
-/
theorem incM_mul' {a b c : Type} [Fintype b] (X : Matrix a b E) (Y : Matrix b c E) :
    incM F (X ⬝ Y) = incM F X ⬝ incM F Y := Matrix.map_mul

/- English proof (translation)
Take `⟨⟨ε, hε⟩, -⟩` from `d.ok.frame`. Use `⟨incM F (((ε : ℤ) : E) • (1 : Matrix (Fin d.n) (Fin d.n) E)), ?_⟩` and prove the remaining obligations. Establish `e1 : (incM F d.b.1).map (cA σ) = incM F (d.b.1.map σ)`. Use extensionality with `i j`. Simplify using `[incM, cA, inclR, Algebra.TensorProduct.map_tmul]`.

Establish `e2 : dbl (incM F d.Y.J) = incM F (dbl d.Y.J)`. Simplify using `[dbl, incM, Matrix.fromBlocks_map, Matrix.map_neg]`. Establish `key : incM F (d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ) = (incM F d.b.1)ᵀ * incM F (dbl d.Y.J) * incM F (d.b.1.map σ)`. Simplify using `only [incM, Matrix.map_mul, Matrix.transpose_map]`. Rewrite using `[e1, e2, ← key, hε]`.

Simplify using `[incM, Matrix.fromBlocks_map]`.
-/
theorem frame_form (d : SD σ) : ∃ C' : Matrix (Fin d.n) (Fin d.n) (AE F E),
    (incM F d.b.1)ᵀ * dbl (incM F d.Y.J) * (incM F d.b.1).map (cA σ) = Matrix.fromBlocks 0 1 C' 0 := by
  obtain ⟨⟨ε, hε⟩, -⟩ := d.ok.frame
  refine ⟨incM F (((ε : ℤ) : E) • (1 : Matrix (Fin d.n) (Fin d.n) E)), ?_⟩
  have e1 : (incM F d.b.1).map (cA σ) = incM F (d.b.1.map σ) := by
    ext i j
    simp [incM, cA, inclR, Algebra.TensorProduct.map_tmul]
  have e2 : dbl (incM F d.Y.J) = incM F (dbl d.Y.J) := by
    simp [dbl, incM, Matrix.fromBlocks_map, Matrix.map_neg]
  have key : incM F (d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ) =
      (incM F d.b.1)ᵀ * incM F (dbl d.Y.J) * incM F (d.b.1.map σ) := by
    simp only [incM, Matrix.map_mul, Matrix.transpose_map]
  rw [e1, e2, ← key, hε]
  simp [incM, Matrix.fromBlocks_map]

/- English proof (translation)
Take `⟨-, tb, htb⟩` from `d.ok.frame`. Set `E1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E)` to `Matrix.fromRows 1 0`. Set `DC : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E)` to `diagCols (Fin d.n)`. Establish `htb' : d.b.1.toCols₁ = (diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) E) ⬝ tb.1` using `htb`. Establish `hp' : mat2 p ⬝ DC = DC ⬝ t.1` using `hp`.

Establish `hcol : ∀ M : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E), M ⬝ E1 = M.toCols₁`. Introduce `M`. Use extensionality with `i j`. Simplify using `[E1, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, Matrix.toCols₁]`. Establish `h1 : incM F d.b.1 ⬝ E1 = incM F (d.b.1.toCols₁)`.

Rewrite using `[hcol]`. Use extensionality with `i j`. Both sides reduce to the same expression. Establish `h2 : incM F ((diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) E) ⬝ tb.1) = DC ⬝ incM F tb.1`. Rewrite using `[incM_mul']`.

Use `congr 1`. Use extensionality with `i j`. Apply the tactic sequence `cases i <;> simp [DC, diagCols, incM, Matrix.one_apply, apply_ite] <;> split_ifs <;> simp_all`. Establish `hb : incM F d.b.1 ⬝ E1 = DC ⬝ incM F tb.1` using `h1.trans ((congrArg (incM F) htb').trans h2)`. Establish `hTb : incM F tb.1 ⬝ incM F (tb⁻¹).1 = 1`.

Rewrite using `[← incM_mul', Units.mul_inv]`. Conclude with `Matrix.map_one _ (map_zero _) (map_one _)`. Establish `hBB : incM F (d.b⁻¹).1 ⬝ incM F d.b.1 = 1` using `incM_inv_mul d`. Establish `hdc : DC = incM F d.b.1 ⬝ E1 ⬝ incM F (tb⁻¹).1`. Rewrite using `[hb, Matrix.mul_assoc, hTb, Matrix.mul_one]`.

Establish `key : inFrame d.b p ⬝ E1 = E1 ⬝ (incM F (tb⁻¹).1 ⬝ t.1 ⬝ incM F tb.1)`. Establish `e0 : inFrame d.b p = incM F (d.b⁻¹).1 ⬝ mat2 p ⬝ incM F d.b.1` using `rfl`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[e0]`. Simplify using `only [Matrix.mul_assoc]`.

Use `_ = incM F (d.b⁻¹).1 ⬝ ((mat2 p ⬝ DC) ⬝ incM F tb.1) := by`. Rewrite using `[hb, Matrix.mul_assoc]`. Use `_ = incM F (d.b⁻¹).1 ⬝ ((DC ⬝ t.1) ⬝ incM F tb.1) := by rw [hp']`. Use `_ = (incM F (d.b⁻¹).1 ⬝ incM F d.b.1) ⬝ E1 ⬝ (incM F (tb⁻¹).1 ⬝ t.1 ⬝ incM F tb.1) := by`. Rewrite using `[hdc]`.

Simplify using `only [Matrix.mul_assoc]`. Use `_ = _ := by rw [hBB, Matrix.one_mul]`. Use extensionality with `i j`. Use `congrFun (congrFun key (Sum.inr i)) j` as an intermediate fact. Rewrite `this` using `[hcol]`.

Simplify `this` using `[E1, Matrix.toBlocks₂₁, Matrix.toCols₁, Matrix.mul_apply, Fintype.sum_sum_type]`.
-/
theorem parabolic_lower_block_zero (d : SD σ) (p : d.G) (t : GL (Fin d.n) (AE F E)) (hp : IsPar p t) :
    (inFrame d.b p).toBlocks₂₁ = 0 := by
  obtain ⟨-, tb, htb⟩ := d.ok.frame
  let E1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E) := Matrix.fromRows 1 0
  let DC : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E) := diagCols (Fin d.n)
  have htb' : d.b.1.toCols₁ = (diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) E) ⬝ tb.1 := htb
  have hp' : mat2 p ⬝ DC = DC ⬝ t.1 := hp
  have hcol : ∀ M : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E), M ⬝ E1 = M.toCols₁ := by
    intro M
    ext i j
    simp [E1, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, Matrix.toCols₁]
  have h1 : incM F d.b.1 ⬝ E1 = incM F (d.b.1.toCols₁) := by
    rw [hcol]
    ext i j
    rfl
  have h2 : incM F ((diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) E) ⬝ tb.1) = DC ⬝ incM F tb.1 := by
    rw [incM_mul']
    congr 1
    ext i j
    cases i <;> simp [DC, diagCols, incM, Matrix.one_apply, apply_ite] <;> split_ifs <;> simp_all
  have hb : incM F d.b.1 ⬝ E1 = DC ⬝ incM F tb.1 := h1.trans ((congrArg (incM F) htb').trans h2)
  have hTb : incM F tb.1 ⬝ incM F (tb⁻¹).1 = 1 := by
    rw [← incM_mul', Units.mul_inv]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hBB : incM F (d.b⁻¹).1 ⬝ incM F d.b.1 = 1 := incM_inv_mul d
  have hdc : DC = incM F d.b.1 ⬝ E1 ⬝ incM F (tb⁻¹).1 := by
    rw [hb, Matrix.mul_assoc, hTb, Matrix.mul_one]
  have key : inFrame d.b p ⬝ E1 = E1 ⬝ (incM F (tb⁻¹).1 ⬝ t.1 ⬝ incM F tb.1) := by
    have e0 : inFrame d.b p = incM F (d.b⁻¹).1 ⬝ mat2 p ⬝ incM F d.b.1 := rfl
    calc inFrame d.b p ⬝ E1 = incM F (d.b⁻¹).1 ⬝ (mat2 p ⬝ (incM F d.b.1 ⬝ E1)) := by
          rw [e0]; simp only [Matrix.mul_assoc]
      _ = incM F (d.b⁻¹).1 ⬝ ((mat2 p ⬝ DC) ⬝ incM F tb.1) := by
          rw [hb, Matrix.mul_assoc]
      _ = incM F (d.b⁻¹).1 ⬝ ((DC ⬝ t.1) ⬝ incM F tb.1) := by rw [hp']
      _ = (incM F (d.b⁻¹).1 ⬝ incM F d.b.1) ⬝ E1 ⬝ (incM F (tb⁻¹).1 ⬝ t.1 ⬝ incM F tb.1) := by
          rw [hdc]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [hBB, Matrix.one_mul]
  ext i j
  have := congrFun (congrFun key (Sum.inr i)) j
  rw [hcol] at this
  simpa [E1, Matrix.toBlocks₂₁, Matrix.toCols₁, Matrix.mul_apply, Fintype.sum_sum_type] using this

/- English proof (translation)
Establish `h21` using `parabolic_lower_block_zero d p t hp`. Use `set g := inFrame d.b p with hg`. Use `set A := g.toBlocks₁₁`. Use `set B := g.toBlocks₁₂`. Use `set D := g.toBlocks₂₂`.

Establish `hgb : g = Matrix.fromBlocks A B 0 D` using `by rw [← h21, Matrix.fromBlocks_toBlocks]`. Establish `hBm : IsUnit (incM F d.b.1)` using `(Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_exists_inv.2 ⟨_, by rw [← Matrix.det_mul, incM_mul_inv d, Matrix.det_one]⟩)`. Establish `hBi : IsUnit (incM F (d.b⁻¹).1)` using `(Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_exists_inv.2 ⟨_, by rw [← Matrix.det_mul, incM_inv_mul d, Matrix.det_one]⟩)`. Establish `hug : IsUnit g` using `(hBi.mul (Units.isUnit p.1)).mul hBm`. Establish `hdet : IsUnit (A.det * D.det)`.

Rewrite using `[← Matrix.det_fromBlocks_zero₂₁ A B D, ← hgb]`. Conclude with `(Matrix.isUnit_iff_isUnit_det g).1 hug`. Establish `hA : IsUnit A.det` using `isUnit_of_mul_isUnit_left hdet`. Establish `hD : IsUnit D.det` using `isUnit_of_mul_isUnit_right hdet`. Use `set Md : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E) := Matrix.fromBlocks A 0 0 D with hMd_def`.

Establish `hMd : IsUnit Md` using `(Matrix.isUnit_iff_isUnit_det _).2 (by rw [hMd_def, Matrix.det_fromBlocks_zero₂₁]; exact hA.mul hD)`. Take `⟨C', hC'⟩` from `frame_form d`. Establish `hP : (mat2 p)ᵀ * dbl (incM F d.Y.J) * (mat2 p).map (cA σ).toRingHom = dbl (incM F d.Y.J)` using `p.2`. Establish `hgf` using `form_conj_in (cA σ).toRingHom (incM_mul_inv d) hP`. Establish `hC'' : (incM F d.b.1)ᵀ * dbl (incM F d.Y.J) * (incM F d.b.1).map (cA σ).toRingHom = Matrix.fromBlocks 0 1 C' 0` using `hC'`.

Rewrite `hgf` using `[hC'']`. Establish `hgf' : gᵀ * Matrix.fromBlocks 0 1 C' 0 * g.map (cA σ).toRingHom = Matrix.fromBlocks 0 1 C' 0` using `hgf`. Rewrite `hgf'` using `[hgb]`. Establish `hMdf` using `block_diag_form (cA σ).toRingHom A B D C' hgf'`. Rewrite `hMdf` using `[← hC'']`.

Establish `hM0mem` using `form_conj_out (cA σ).toRingHom (incM_mul_inv d) hMdf`. Establish `hM0u : IsUnit (incM F d.b.1 * Md * incM F (d.b⁻¹).1)` using `(hBm.mul hMd).mul hBi`. Set `u : GL (Fin d.n ⊕ Fin d.n) (AE F E)` to `hM0u.unit`. Establish `hu : (u : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) = incM F d.b.1 * Md * incM F (d.b⁻¹).1` using `IsUnit.unit_spec hM0u`. Establish `hmem : u ∈ UG (cA σ) (dbl (incM F d.Y.J))` using `by show (u : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E))ᵀ * dbl (incM F d.Y.J) * (u : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)).map (cA σ) = dbl (incM F d.Y.J)`.

Rewrite using `[hu]`. Conclude with `hM0mem`. Set `m0 : d.G` to `⟨u, hmem⟩`. Establish `hm0 : inFrame d.b m0 = Md` using `by show incM F (d.b⁻¹).1 * (u : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) * incM F d.b.1 = Md`. Rewrite using `[hu]`.

Simplify using `only [← Matrix.mul_assoc, incM_inv_mul d, Matrix.one_mul]`. Rewrite using `[Matrix.mul_assoc, incM_inv_mul d, Matrix.mul_one]`. Establish `hAu` using `(Matrix.isUnit_iff_isUnit_det A).2 hA`. Establish `hDu` using `(Matrix.isUnit_iff_isUnit_det D).2 hD`. Use `⟨p * m0⁻¹, m0, B * D⁻¹, ?_, ⟨hAu.unit, hDu.unit, ?_⟩, (inv_mul_cancel_right p m0).symm⟩` and prove the remaining obligations.

Establish `e` using `inFrame_mul d (p * m0⁻¹) m0`. Rewrite `e` using `[inv_mul_cancel_right, hm0]`. Apply `(hMd.mul_left_inj).1` to reduce the goal to its premises. Rewrite using `[← e, ← hg, hgb, hMd_def, Matrix.fromBlocks_multiply]`. Simplify using `[Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hD]`.

Rewrite using `[hm0, IsUnit.unit_spec, IsUnit.unit_spec]`.
-/
theorem par_decomp (d : SD σ) (p : d.G) (t : GL (Fin d.n) (AE F E)) (hp : IsPar p t) :
    ∃ (n0 m0 : d.G) (β₀ : Mx F E d.n d.n), inFrame d.b n0 = Matrix.fromBlocks 1 β₀ 0 1 ∧ IsLevi d m0 ∧ p = n0 * m0 := by
  have h21 := parabolic_lower_block_zero d p t hp
  set g := inFrame d.b p with hg
  set A := g.toBlocks₁₁
  set B := g.toBlocks₁₂
  set D := g.toBlocks₂₂
  have hgb : g = Matrix.fromBlocks A B 0 D := by rw [← h21, Matrix.fromBlocks_toBlocks]
  have hBm : IsUnit (incM F d.b.1) := (Matrix.isUnit_iff_isUnit_det _).2
    (isUnit_iff_exists_inv.2 ⟨_, by rw [← Matrix.det_mul, incM_mul_inv d, Matrix.det_one]⟩)
  have hBi : IsUnit (incM F (d.b⁻¹).1) := (Matrix.isUnit_iff_isUnit_det _).2
    (isUnit_iff_exists_inv.2 ⟨_, by rw [← Matrix.det_mul, incM_inv_mul d, Matrix.det_one]⟩)
  have hug : IsUnit g := (hBi.mul (Units.isUnit p.1)).mul hBm
  have hdet : IsUnit (A.det * D.det) := by
    rw [← Matrix.det_fromBlocks_zero₂₁ A B D, ← hgb]
    exact (Matrix.isUnit_iff_isUnit_det g).1 hug
  have hA : IsUnit A.det := isUnit_of_mul_isUnit_left hdet
  have hD : IsUnit D.det := isUnit_of_mul_isUnit_right hdet
  set Md : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E) := Matrix.fromBlocks A 0 0 D with hMd_def
  have hMd : IsUnit Md := (Matrix.isUnit_iff_isUnit_det _).2 (by rw [hMd_def, Matrix.det_fromBlocks_zero₂₁]; exact hA.mul hD)
  obtain ⟨C', hC'⟩ := frame_form d
  have hP : (mat2 p)ᵀ * dbl (incM F d.Y.J) * (mat2 p).map (cA σ).toRingHom = dbl (incM F d.Y.J) := p.2
  have hgf := form_conj_in (cA σ).toRingHom (incM_mul_inv d) hP
  have hC'' : (incM F d.b.1)ᵀ * dbl (incM F d.Y.J) * (incM F d.b.1).map (cA σ).toRingHom =
      Matrix.fromBlocks 0 1 C' 0 := hC'
  rw [hC''] at hgf
  have hgf' : gᵀ * Matrix.fromBlocks 0 1 C' 0 * g.map (cA σ).toRingHom = Matrix.fromBlocks 0 1 C' 0 := hgf
  rw [hgb] at hgf'
  have hMdf := block_diag_form (cA σ).toRingHom A B D C' hgf'
  rw [← hC''] at hMdf
  have hM0mem := form_conj_out (cA σ).toRingHom (incM_mul_inv d) hMdf
  have hM0u : IsUnit (incM F d.b.1 * Md * incM F (d.b⁻¹).1) := (hBm.mul hMd).mul hBi
  let u : GL (Fin d.n ⊕ Fin d.n) (AE F E) := hM0u.unit
  have hu : (u : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) =
      incM F d.b.1 * Md * incM F (d.b⁻¹).1 := IsUnit.unit_spec hM0u
  have hmem : u ∈ UG (cA σ) (dbl (incM F d.Y.J)) := by
    show (u : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E))ᵀ * dbl (incM F d.Y.J) *
      (u : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)).map (cA σ) = dbl (incM F d.Y.J)
    rw [hu]
    exact hM0mem
  let m0 : d.G := ⟨u, hmem⟩
  have hm0 : inFrame d.b m0 = Md := by
    show incM F (d.b⁻¹).1 * (u : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) * incM F d.b.1 = Md
    rw [hu]
    simp only [← Matrix.mul_assoc, incM_inv_mul d, Matrix.one_mul]
    rw [Matrix.mul_assoc, incM_inv_mul d, Matrix.mul_one]
  have hAu := (Matrix.isUnit_iff_isUnit_det A).2 hA
  have hDu := (Matrix.isUnit_iff_isUnit_det D).2 hD
  refine ⟨p * m0⁻¹, m0, B * D⁻¹, ?_, ⟨hAu.unit, hDu.unit, ?_⟩, (inv_mul_cancel_right p m0).symm⟩
  · have e := inFrame_mul d (p * m0⁻¹) m0
    rw [inv_mul_cancel_right, hm0] at e
    apply (hMd.mul_left_inj).1
    rw [← e, ← hg, hgb, hMd_def, Matrix.fromBlocks_multiply]
    simp [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hD]
  · rw [hm0, IsUnit.unit_spec, IsUnit.unit_spec]

/- English proof (translation)
Establish `hg : (mat g⁻¹)ᵀ * incM F d.A.J * (mat g⁻¹).map (cA σ) = incM F d.A.J` using `(g⁻¹).2`. Establish `hm : (mat g⁻¹ * X).map (cA σ) = (mat g⁻¹).map (cA σ) * X.map (cA σ)` using `Matrix.map_mul (f := (cA σ).toRingHom)`. Simplify using `only [SD.gram, Matrix.transpose_mul, hm]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`.

Use `_ = _ := by rw [hg]`.
-/
theorem gram_mat_inv (d : SD σ) (g : UA σ d.A.J) (X : Mx F E d.m d.n) :
    d.gram (mat g⁻¹ * X) (mat g⁻¹ * X) = d.gram X X := by
  have hg : (mat g⁻¹)ᵀ * incM F d.A.J * (mat g⁻¹).map (cA σ) = incM F d.A.J := (g⁻¹).2
  have hm : (mat g⁻¹ * X).map (cA σ) = (mat g⁻¹).map (cA σ) * X.map (cA σ) :=
    Matrix.map_mul (f := (cA σ).toRingHom)
  simp only [SD.gram, Matrix.transpose_mul, hm]
  calc Xᵀ * (mat g⁻¹)ᵀ * incM F d.A.J * ((mat g⁻¹).map (cA σ) * X.map (cA σ))
      = Xᵀ * ((mat g⁻¹)ᵀ * incM F d.A.J * (mat g⁻¹).map (cA σ)) * X.map (cA σ) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [hg]

/- English proof (translation)
Establish `h1 : d.tt (β₀ * ((-2 : ℤ) • T)) = (-2 : AF F) * d.tt (T * β₀)`. Simplify using `only [SD.tt, Matrix.mul_smul, Matrix.trace_smul, map_zsmul, Matrix.trace_mul_comm β₀ T]`. Rewrite using `[zsmul_eq_mul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[h1, ← mul_assoc, mul_neg, invOf_mul_self, neg_one_mul, neg_neg]`.
-/
theorem phase (d : SD σ) (T β₀ : Mx F E d.n d.n) :
    -(⅟(2 : AF F) * d.tt (β₀ * ((-2 : ℤ) • T))) = d.tt (T * β₀) := by
  have h1 : d.tt (β₀ * ((-2 : ℤ) • T)) = (-2 : AF F) * d.tt (T * β₀) := by
    simp only [SD.tt, Matrix.mul_smul, Matrix.trace_smul, map_zsmul, Matrix.trace_mul_comm β₀ T]
    rw [zsmul_eq_mul]
    push_cast
    ring
  rw [h1, ← mul_assoc, mul_neg, invOf_mul_self, neg_one_mul, neg_neg]

/- English proof (translation)
Establish `hP` using `(hT.2.1 F E σ d Ψ hΨ).1 n0 β₀ hn`. Establish `hpt : ∀ (g : UA σ d.A.J) (X : Matrix (Fin d.m) (Fin d.n) E), d.gram (incM F X) (incM F X) = (-2 : ℤ) • T.1.1 → d.T (d.om n0 Ψ) (mat g⁻¹ * incM F X) = d.B.ψ (d.tt (T.1.1 * β₀)) * d.T Ψ (mat g⁻¹ * incM F X)`. Introduce `g X hX`. Rewrite using `[hP, gram_mat_inv, hX, phase]`. Establish `hs : ∀ g : UA σ d.A.J, (∑' X : {X : Matrix (Fin d.m) (Fin d.n) E // d.gram (incM F X) (incM F X) = (-2 : ℤ) • T.1.1}, d.T (d.om n0 Ψ) (mat g⁻¹ * incM F X.1)) = d.B.ψ (d.tt (T.1.1 * β₀)) * ∑' X : {X : Matrix (Fin d.m) (Fin d.n) E // d.gram (incM F X) (incM F X) = (-2 : ℤ) • T.1.1} …`.

Introduce `g`. Rewrite using `[← tsum_mul_left]`. Conclude with `tsum_congr fun X => hpt g X.1 X.2`. Simplify using `only [SD.orb]`. Repeatedly rewrite using `[hs]`.

Simplify using `only [MeasureTheory.average]`. Conclude with `integral_const_mul _ _`.
-/
theorem orb_n (hT : TAll) (d : SD σ) (T : nF σ d.Y d.b) {Ψ : d.Fn} (hΨ : Ψ ∈ d.sch) (n0 : d.G) (β₀ : Mx F E d.n d.n)
    (hn : inFrame d.b n0 = Matrix.fromBlocks 1 β₀ 0 1) :
    d.orb T (d.om n0 Ψ) = d.B.ψ (d.tt (T.1.1 * β₀)) * d.orb T Ψ := by
  have hP := (hT.2.1 F E σ d Ψ hΨ).1 n0 β₀ hn
  have hpt : ∀ (g : UA σ d.A.J) (X : Matrix (Fin d.m) (Fin d.n) E),
      d.gram (incM F X) (incM F X) = (-2 : ℤ) • T.1.1 →
      d.T (d.om n0 Ψ) (mat g⁻¹ * incM F X) = d.B.ψ (d.tt (T.1.1 * β₀)) * d.T Ψ (mat g⁻¹ * incM F X) := by
    intro g X hX
    rw [hP, gram_mat_inv, hX, phase]
  have hs : ∀ g : UA σ d.A.J,
      (∑' X : {X : Matrix (Fin d.m) (Fin d.n) E // d.gram (incM F X) (incM F X) = (-2 : ℤ) • T.1.1},
        d.T (d.om n0 Ψ) (mat g⁻¹ * incM F X.1)) = d.B.ψ (d.tt (T.1.1 * β₀)) *
      ∑' X : {X : Matrix (Fin d.m) (Fin d.n) E // d.gram (incM F X) (incM F X) = (-2 : ℤ) • T.1.1},
        d.T Ψ (mat g⁻¹ * incM F X.1) := by
    intro g
    rw [← tsum_mul_left]
    exact tsum_congr fun X => hpt g X.1 X.2
  simp only [SD.orb]
  simp_rw [hs]
  simp only [MeasureTheory.average]
  exact integral_const_mul _ _

/- English proof (translation)
Use `hcd.2.1` as an intermediate fact. Establish `hβ₀ : β₀ ∈ nA σ d.Y d.b` using `AddSubgroup.subset_closure ⟨n0, hn⟩`. Set `b₀ : nA σ d.Y d.b` to `⟨β₀, hβ₀⟩`. Establish `hnb : ∀ β, nb β * n0 = nb (b₀ + β)`. Introduce `β`.

Apply `inFrame_injective d` to reduce the goal to its premises. Rewrite using `[inFrame_mul, hcd.1 β, hn, hcd.1 (b₀ + β)]`. Simplify using `[Matrix.fromBlocks_multiply, add_comm, b₀]`. Establish `htt : ∀ β : nA σ d.Y d.b, d.tt (T.1.1 * (b₀ + β).1) = d.tt (T.1.1 * β₀) + d.tt (T.1.1 * β.1)`. Introduce `β`.

Simplify using `[SD.tt, Matrix.mul_add, Matrix.trace_add, map_add, b₀]`. Combine the equalities or inequalities in the displayed calculation. Use `congr 1`. Use function extensionality and compare the values at `β`. Simplify using `only`.

Rewrite using `[← hnb β, htt β, ← AddChar.map_add_eq_mul, show -(d.tt (T.1.1 * β₀) + d.tt (T.1.1 * β.1)) + d.tt (T.1.1 * β₀) = -d.tt (T.1.1 * β.1) by abel]`. Simplify using `only [mul_assoc]`. Use `_ = ∫ β, f (w * nb β * m0) * (d.B.ψ (-d.tt (T.1.1 * β.1)) * d.B.ψ (d.tt (T.1.1 * β₀))) ∂lam := integral_add_left_haar lam b₀ (fun β' : nA σ d.Y d.b => f (w * nb β' * m0) * (d.B.ψ (-d.tt (T.1.1 * β'.1)) * d.B.ψ (d.tt (T.1.1 * β₀))))`. Use `_ = _ := by`. Rewrite using `[← integral_const_mul]`.

Use `congr 1`. Use function extensionality and compare the values at `β`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem int_n (d : SD σ) (nb : nA σ d.Y d.b → d.G) (lam : Measure (nA σ d.Y d.b)) (𝓖 : Set (nA σ d.Y d.b))
    (hcd : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) (T : nF σ d.Y d.b) (w n0 m0 : d.G) (β₀ : Mx F E d.n d.n)
    (hn : inFrame d.b n0 = Matrix.fromBlocks 1 β₀ 0 1) (f : d.G → ℂ) :
    ∫ β, f (w * nb β * (n0 * m0)) * d.B.ψ (-d.tt (T.1.1 * β.1)) ∂lam =
      d.B.ψ (d.tt (T.1.1 * β₀)) * ∫ β, f (w * nb β * m0) * d.B.ψ (-d.tt (T.1.1 * β.1)) ∂lam := by
  have := hcd.2.1
  have hβ₀ : β₀ ∈ nA σ d.Y d.b := AddSubgroup.subset_closure ⟨n0, hn⟩
  let b₀ : nA σ d.Y d.b := ⟨β₀, hβ₀⟩
  have hnb : ∀ β, nb β * n0 = nb (b₀ + β) := by
    intro β
    apply inFrame_injective d
    rw [inFrame_mul, hcd.1 β, hn, hcd.1 (b₀ + β)]
    simp [Matrix.fromBlocks_multiply, add_comm, b₀]
  have htt : ∀ β : nA σ d.Y d.b, d.tt (T.1.1 * (b₀ + β).1) = d.tt (T.1.1 * β₀) + d.tt (T.1.1 * β.1) := by
    intro β
    simp [SD.tt, Matrix.mul_add, Matrix.trace_add, map_add, b₀]
  calc ∫ β, f (w * nb β * (n0 * m0)) * d.B.ψ (-d.tt (T.1.1 * β.1)) ∂lam
      = ∫ β, (fun β' : nA σ d.Y d.b => f (w * nb β' * m0) * (d.B.ψ (-d.tt (T.1.1 * β'.1)) *
          d.B.ψ (d.tt (T.1.1 * β₀)))) (b₀ + β) ∂lam := by
        congr 1
        funext β
        dsimp only
        rw [← hnb β, htt β, ← AddChar.map_add_eq_mul,
          show -(d.tt (T.1.1 * β₀) + d.tt (T.1.1 * β.1)) + d.tt (T.1.1 * β₀) = -d.tt (T.1.1 * β.1) by abel]
        simp only [mul_assoc]
    _ = ∫ β, f (w * nb β * m0) * (d.B.ψ (-d.tt (T.1.1 * β.1)) * d.B.ψ (d.tt (T.1.1 * β₀))) ∂lam :=
        integral_add_left_haar lam b₀ (fun β' : nA σ d.Y d.b => f (w * nb β' * m0) *
          (d.B.ψ (-d.tt (T.1.1 * β'.1)) * d.B.ψ (d.tt (T.1.1 * β₀))))
    _ = _ := by
        rw [← integral_const_mul]
        congr 1
        funext β
        ring

/- English proof (translation)
Introduce `hT hL F E _ _ _ _ _ σ d hnm hE Φ hΦ nb lam 𝓖 hcd ε w hw T hTnd x`. Take `⟨p, t, hp, k, hk, rfl⟩` from `d.ok.hgt.iwa x`. Take `⟨n0, m0, β₀, hn, hm, rfl⟩` from `par_decomp d p t hp`. Establish `key` using `hL F E σ d hnm hE (d.om k Φ) (kfin_om d hΦ hk) m0 hm nb lam 𝓖 hcd ε w hw T hTnd`. Establish `e1 : (fun z => ∫ β, flat d.a (d.sec0 Φ) (s0 d.m d.n) z (w * nb β * (n0 * m0 * k)) * d.B.ψ (-d.tt (T.1.1 * β.1)) ∂lam) = fun z => d.B.ψ (d.tt (T.1.1 * β₀)) * ∫ β, flat d.a (d.sec0 (d.om k Φ)) (s0 d.m d.n) z (w * nb β * m0) * d.B.ψ (-d.tt (T.1.1 * β.1)) ∂lam`.

Use function extensionality and compare the values at `z`. Rewrite using `[← int_n d nb lam 𝓖 hcd T w n0 m0 β₀ hn]`. Use `congr 1`. Use function extensionality and compare the values at `β`. Simplify using `only [flat]`.

Rewrite using `[show w * nb β * (n0 * m0 * k) = (w * nb β * (n0 * m0)) * k by simp only [mul_assoc], a_mul_K d _ k hk, section_mul_weil_action]`. Establish `e2 : d.orb T (d.om (n0 * m0 * k) Φ) = d.B.ψ (d.tt (T.1.1 * β₀)) * d.orb T (d.om m0 (d.om k Φ))`. Rewrite using `[map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]`. Conclude with `orb_n hT d T (om_mem_sch d _ (om_mem_sch d _ hΦ.1)) n0 β₀ hn`. Rewrite using `[e1, e2]`.

Conclude with `holValueAt_const_mul _ key`.
-/
theorem iwaRed : IwaRed := by
  intro hT hL F E _ _ _ _ _ σ d hnm hE Φ hΦ nb lam 𝓖 hcd ε w hw T hTnd x
  obtain ⟨p, t, hp, k, hk, rfl⟩ := d.ok.hgt.iwa x
  obtain ⟨n0, m0, β₀, hn, hm, rfl⟩ := par_decomp d p t hp
  have key := hL F E σ d hnm hE (d.om k Φ) (kfin_om d hΦ hk) m0 hm nb lam 𝓖 hcd ε w hw T hTnd
  have e1 : (fun z => ∫ β, flat d.a (d.sec0 Φ) (s0 d.m d.n) z (w * nb β * (n0 * m0 * k)) *
      d.B.ψ (-d.tt (T.1.1 * β.1)) ∂lam) = fun z => d.B.ψ (d.tt (T.1.1 * β₀)) *
      ∫ β, flat d.a (d.sec0 (d.om k Φ)) (s0 d.m d.n) z (w * nb β * m0) * d.B.ψ (-d.tt (T.1.1 * β.1)) ∂lam := by
    funext z
    rw [← int_n d nb lam 𝓖 hcd T w n0 m0 β₀ hn]
    congr 1
    funext β
    simp only [flat]
    rw [show w * nb β * (n0 * m0 * k) = (w * nb β * (n0 * m0)) * k by simp only [mul_assoc], a_mul_K d _ k hk,
      section_mul_weil_action]
  have e2 : d.orb T (d.om (n0 * m0 * k) Φ) = d.B.ψ (d.tt (T.1.1 * β₀)) * d.orb T (d.om m0 (d.om k Φ)) := by
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
    exact orb_n hT d T (om_mem_sch d _ (om_mem_sch d _ hΦ.1)) n0 β₀ hn
  rw [e1, e2]
  exact holValueAt_const_mul _ key

end PositivityTheory.SiegelWeilFormula.KWhit

end
