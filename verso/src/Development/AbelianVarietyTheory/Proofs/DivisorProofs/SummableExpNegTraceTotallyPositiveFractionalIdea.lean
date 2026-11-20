import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
open NumberField Complex
open scoped nonZeroDivisors
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization

noncomputable section

namespace GlobalTheory.LatExpSum

/- English proof (translation)
Establish `h` using `trace_eq_sum_embeddings (K := ℚ) (E := ℂ) (x := x)`. Rewrite `h` using `[← Fintype.sum_equiv (RingHom.equivRatAlgHom F ℂ) (fun f => f x) (fun φ => φ x) (fun _ => by simp [RingHom.equivRatAlgHom_apply])]`. Rewrite `h` using `[eq_ratCast]`. Establish `h2 : ∑ φ : F →+* ℂ, φ x = ∑ τ : Emb F, ((τ x : ℝ) : ℂ)`. Use `(Fintype.sum_bijective (fun τ : Emb F => (ofRealHom.comp τ : F →+* ℂ)) ⟨?_, ?_⟩ _ _ (fun _ => rfl)).symm` and prove the remaining obligations.

Introduce `τ τ' hτ`. Use extensionality with `y`. Use `DFunLike.congr_fun hτ y` as an intermediate fact. Simplify using `using this`. Introduce `φ`.

Establish `hr : ComplexEmbedding.IsReal φ` using `IsTotallyReal.complexEmbedding_isReal φ`. Conclude with `⟨hr.embedding, by ext y; simp⟩`. Rewrite `h` using `[h2, ← ofReal_sum]`. Conclude with `h` after adjusting the coercions.
-/
theorem trace_eq_sum_emb (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (x : F) :
    ((Algebra.trace ℚ F x : ℚ) : ℝ) = ∑ τ : Emb F, τ x := by
  have h := trace_eq_sum_embeddings (K := ℚ) (E := ℂ) (x := x)
  rw [← Fintype.sum_equiv (RingHom.equivRatAlgHom F ℂ) (fun f => f x) (fun φ => φ x)
    (fun _ => by simp [RingHom.equivRatAlgHom_apply])] at h
  rw [eq_ratCast] at h
  have h2 : ∑ φ : F →+* ℂ, φ x = ∑ τ : Emb F, ((τ x : ℝ) : ℂ) := by
    refine (Fintype.sum_bijective (fun τ : Emb F => (ofRealHom.comp τ : F →+* ℂ)) ⟨?_, ?_⟩ _ _ (fun _ => rfl)).symm
    · intro τ τ' hτ
      ext y
      have := DFunLike.congr_fun hτ y
      simpa using this
    · intro φ
      have hr : ComplexEmbedding.IsReal φ := IsTotallyReal.complexEmbedding_isReal φ
      exact ⟨hr.embedding, by ext y; simp⟩
  rw [h2, ← ofReal_sum] at h
  exact_mod_cast h

/- English proof (translation)
Use `summable_of_sum_le (c := ∏ i, ∑' x, f i x) (fun n => Finset.prod_nonneg fun i _ => h0 i _) fun s => ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem summable_pi_prod {ι : Type} [Fintype ι] {f : ι → ℤ → ℝ} (h0 : ∀ i x, 0 ≤ f i x)
    (hf : ∀ i, Summable (f i)) : Summable fun n : ι → ℤ => ∏ i, f i (n i) := by
  classical
  refine summable_of_sum_le (c := ∏ i, ∑' x, f i x)
    (fun n => Finset.prod_nonneg fun i _ => h0 i _) fun s => ?_
  calc ∑ n ∈ s, ∏ i, f i (n i)
      ≤ ∑ n ∈ Fintype.piFinset fun i => s.image (· i), ∏ i, f i (n i) :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (fun n hn => Fintype.mem_piFinset.mpr fun i => Finset.mem_image_of_mem _ hn)
          fun n _ _ => Finset.prod_nonneg fun i _ => h0 i _
    _ = ∏ i, ∑ x ∈ s.image (· i), f i x := (Finset.prod_univ_sum _ _).symm
    _ ≤ _ := Finset.prod_le_prod (fun i _ => Finset.sum_nonneg fun x _ => h0 i x)
        fun i _ => (hf i).sum_le_tsum _ fun x _ => h0 i x

/- English proof (translation)
Establish `hg : Summable fun n : ℕ => Real.exp (-ε) ^ n` using `summable_geometric_of_lt_one (Real.exp_pos _).le (Real.exp_lt_one_iff.mpr (by linarith))`. Apply `Summable.of_nat_of_neg` to reduce the goal to its premises. Use `hg.congr fun n => ?_` and prove the remaining obligations. Rewrite using `[← Real.exp_nat_mul]; push_cast; rw [abs_of_nonneg (by positivity)]; ring_nf`. Use `hg.congr fun n => ?_` and prove the remaining obligations.

Rewrite using `[← Real.exp_nat_mul]; push_cast; rw [abs_neg, abs_of_nonneg (by positivity)]; ring_nf`.
-/
theorem summable_exp_neg_abs {ε : ℝ} (hε : 0 < ε) : Summable fun n : ℤ => Real.exp (-ε * |(n : ℝ)|) := by
  have hg : Summable fun n : ℕ => Real.exp (-ε) ^ n :=
    summable_geometric_of_lt_one (Real.exp_pos _).le (Real.exp_lt_one_iff.mpr (by linarith))
  apply Summable.of_nat_of_neg
  · refine hg.congr fun n => ?_
    rw [← Real.exp_nat_mul]; push_cast; rw [abs_of_nonneg (by positivity)]; ring_nf
  · refine hg.congr fun n => ?_
    rw [← Real.exp_nat_mul]; push_cast; rw [abs_neg, abs_of_nonneg (by positivity)]; ring_nf

end GlobalTheory.LatExpSum

namespace GlobalTheory.LatExpSum

/- English proof (translation)
Rewrite using `[← Algebra.traceForm_apply]`. Use `symm`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [map_sum, map_smul, smul_eq_mul]`. Use `_ = b.repr y i := by simp [LinearMap.BilinForm.apply_dualBasis_left]`.
-/
theorem repr_eq_trace (F : Type) [Field F] [NumberField F] {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℚ F) (y : F) (i : ι) :
    b.repr y i = Algebra.trace ℚ F ((Algebra.traceForm ℚ F).dualBasis (traceForm_nondegenerate ℚ F) b i * y) := by
  rw [← Algebra.traceForm_apply]
  symm
  calc _ = (Algebra.traceForm ℚ F) ((Algebra.traceForm ℚ F).dualBasis (traceForm_nondegenerate ℚ F) b i) (∑ j, b.repr y j • b j) := by rw [b.sum_repr]
    _ = ∑ j, b.repr y j * (Algebra.traceForm ℚ F) ((Algebra.traceForm ℚ F).dualBasis (traceForm_nondegenerate ℚ F) b i) (b j) := by
      simp only [map_sum, map_smul, smul_eq_mul]
    _ = b.repr y i := by simp [LinearMap.BilinForm.apply_dualBasis_left]
end GlobalTheory.LatExpSum

namespace GlobalTheory.LatExpSum

/- English proof (translation)
Introduce `F _ _ _ L δ hδ`. Take `⟨a, ha, hint⟩` from `L.isFractional`. Establish `hz : ∀ x : {x : F // x ∈ L ∧ ∀ τ : Emb F, 0 < τ x}, ∃ w : 𝓞 F, algebraMap (𝓞 F) F w = algebraMap (𝓞 F) F a * x.1` using `fun x => by`. Take `⟨w, hw⟩` from `hint x.1 x.2.1`. Conclude with `⟨w, by rw [hw, Algebra.smul_def]⟩`.

Use `choose z hz using hz`. Set `b` to `integralBasis F`. Set `d` to `(Algebra.traceForm ℚ F).dualBasis (traceForm_nondegenerate ℚ F) b`. Establish `hrepr : ∀ (y : F) i, b.repr y i = Algebra.trace ℚ F (d i * y)` using `fun y i => repr_eq_trace F b y i`. Set `c : {x : F // x ∈ L ∧ ∀ τ : Emb F, 0 < τ x} → Module.Free.ChooseBasisIndex ℤ (𝓞 F) → ℤ` to `fun x => (RingOfIntegers.basis F).repr (z x)`.

Establish `hc : ∀ x i, ((c x i : ℚ)) = Algebra.trace ℚ F ((d i * algebraMap (𝓞 F) F a) * x.1)`. Introduce `x i`. Use `integralBasis_repr_apply (K := F) (z x) i` as an intermediate fact. Rewrite `this` using `[hz x]`. Rewrite using `[mul_assoc, ← hrepr]`.

Rewrite using `[this, eq_intCast]`. Set `Mi : Module.Free.ChooseBasisIndex ℤ (𝓞 F) → ℝ` to `fun i => ∑ τ : Emb F, |τ (d i * algebraMap (𝓞 F) F a)|`. Establish `hMi : ∀ i, 0 ≤ Mi i` using `fun i => Finset.sum_nonneg fun τ _ => abs_nonneg _`. Set `M : ℝ` to `∑ i, Mi i + 1`. Establish `hM : 0 < M`.

Use `Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => hMi i` as an intermediate fact. Use `show 0 < ∑ i, Mi i + 1`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hbound : ∀ x, ∑ i, |(c x i : ℝ)| ≤ M * ∑ τ : Emb F, τ x.1`. Introduce `x`.

Establish `hT : 0 ≤ ∑ τ : Emb F, τ x.1` using `Finset.sum_nonneg fun τ _ => (x.2.2 τ).le`. Establish `h1 : ∀ i, |(c x i : ℝ)| ≤ Mi i * ∑ τ : Emb F, τ x.1`. Introduce `i`. Establish `e : (c x i : ℝ) = ∑ τ : Emb F, τ (d i * algebraMap (𝓞 F) F a) * τ x.1`. Establish `h` using `congrArg (fun q : ℚ => (q : ℝ)) (hc x i)`.

Simplify using `only [Rat.cast_intCast] at h`. Rewrite using `[h, trace_eq_sum_emb]`. Simplify using `only [map_mul]`. Rewrite using `[e]`. Combine the equalities or inequalities in the displayed calculation.

Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[abs_mul, abs_of_pos (x.2.2 τ)]`. Use `_ ≤ ∑ τ : Emb F, |τ (d i * algebraMap (𝓞 F) F a)| * ∑ σ : Emb F, σ x.1 := Finset.sum_le_sum fun τ _ => mul_le_mul_of_nonneg_left (Finset.single_le_sum (f := fun σ : Emb F => σ x.1) (fun σ _ => (x.2.2 σ).le) (Finset.mem_univ τ)) (abs_nonneg _)`. Use `_ = Mi i * ∑ τ : Emb F, τ x.1 := by rw [Finset.sum_mul]`. Combine the equalities or inequalities in the displayed calculation.

Establish `ha0 : algebraMap (𝓞 F) F a ≠ 0` using `(map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 F) F)).2 (nonZeroDivisors.ne_zero ha)`. Establish `hinj : Function.Injective c`. Introduce `x y hxy`. Establish `h1 : z x = z y` using `(RingOfIntegers.basis F).repr.injective (Finsupp.ext fun i => congrFun hxy i)`. Establish `h2 : algebraMap (𝓞 F) F a * x.1 = algebraMap (𝓞 F) F a * y.1` using `by rw [← hz, ← hz, h1]`.

Conclude with `Subtype.ext (mul_left_cancel₀ ha0 h2)`. Establish `hε : 0 < δ / M` using `div_pos hδ hM`. Establish `hg : Summable fun n : Module.Free.ChooseBasisIndex ℤ (𝓞 F) → ℤ => ∏ i, Real.exp (-(δ / M) * |(n i : ℝ)|)` using `summable_pi_prod (f := fun _ x => Real.exp (-(δ / M) * |(x : ℝ)|)) (fun _ _ => (Real.exp_pos _).le) fun _ => summable_exp_neg_abs hε`. Use `(hg.comp_injective hinj).of_nonneg_of_le (fun _ => (Real.exp_pos _).le) fun x => ?_` and prove the remaining obligations. Simplify using `only [Function.comp_apply]`.

Rewrite using `[← Real.exp_sum, Real.exp_le_exp, ← Finset.mul_sum]`. Establish `h3 : δ / M * ∑ i, |(c x i : ℝ)| ≤ δ * ∑ τ : Emb F, τ x.1`. Combine the equalities or inequalities in the displayed calculation. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem summable_exp_neg_trace : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (L : FractionalIdeal (𝓞 F)⁰ F) (δ : ℝ), 0 < δ → Summable (fun x : {x : F // x ∈ L ∧ ∀ τ : Emb F, 0 < τ x} => Real.exp (-δ * ∑ τ : Emb F, τ x.1)) := by
  intro F _ _ _ L δ hδ
  classical
  obtain ⟨a, ha, hint⟩ := L.isFractional
  have hz : ∀ x : {x : F // x ∈ L ∧ ∀ τ : Emb F, 0 < τ x}, ∃ w : 𝓞 F,
      algebraMap (𝓞 F) F w = algebraMap (𝓞 F) F a * x.1 := fun x => by
    obtain ⟨w, hw⟩ := hint x.1 x.2.1
    exact ⟨w, by rw [hw, Algebra.smul_def]⟩
  choose z hz using hz
  let b := integralBasis F
  let d := (Algebra.traceForm ℚ F).dualBasis (traceForm_nondegenerate ℚ F) b
  have hrepr : ∀ (y : F) i, b.repr y i = Algebra.trace ℚ F (d i * y) := fun y i => repr_eq_trace F b y i
  let c : {x : F // x ∈ L ∧ ∀ τ : Emb F, 0 < τ x} → Module.Free.ChooseBasisIndex ℤ (𝓞 F) → ℤ :=
    fun x => (RingOfIntegers.basis F).repr (z x)
  have hc : ∀ x i, ((c x i : ℚ)) = Algebra.trace ℚ F ((d i * algebraMap (𝓞 F) F a) * x.1) := by
    intro x i
    have := integralBasis_repr_apply (K := F) (z x) i
    rw [hz x] at this
    rw [mul_assoc, ← hrepr]
    rw [this, eq_intCast]
  let Mi : Module.Free.ChooseBasisIndex ℤ (𝓞 F) → ℝ := fun i => ∑ τ : Emb F, |τ (d i * algebraMap (𝓞 F) F a)|
  have hMi : ∀ i, 0 ≤ Mi i := fun i => Finset.sum_nonneg fun τ _ => abs_nonneg _
  let M : ℝ := ∑ i, Mi i + 1
  have hM : 0 < M := by
    have := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => hMi i
    show 0 < ∑ i, Mi i + 1
    linarith
  have hbound : ∀ x, ∑ i, |(c x i : ℝ)| ≤ M * ∑ τ : Emb F, τ x.1 := by
    intro x
    have hT : 0 ≤ ∑ τ : Emb F, τ x.1 := Finset.sum_nonneg fun τ _ => (x.2.2 τ).le
    have h1 : ∀ i, |(c x i : ℝ)| ≤ Mi i * ∑ τ : Emb F, τ x.1 := by
      intro i
      have e : (c x i : ℝ) = ∑ τ : Emb F, τ (d i * algebraMap (𝓞 F) F a) * τ x.1 := by
        have h := congrArg (fun q : ℚ => (q : ℝ)) (hc x i)
        simp only [Rat.cast_intCast] at h
        rw [h, trace_eq_sum_emb]
        simp only [map_mul]
      rw [e]
      calc |∑ τ : Emb F, τ (d i * algebraMap (𝓞 F) F a) * τ x.1|
          ≤ ∑ τ : Emb F, |τ (d i * algebraMap (𝓞 F) F a) * τ x.1| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ τ : Emb F, |τ (d i * algebraMap (𝓞 F) F a)| * τ x.1 := by
          refine Finset.sum_congr rfl fun τ _ => ?_
          rw [abs_mul, abs_of_pos (x.2.2 τ)]
        _ ≤ ∑ τ : Emb F, |τ (d i * algebraMap (𝓞 F) F a)| * ∑ σ : Emb F, σ x.1 :=
          Finset.sum_le_sum fun τ _ => mul_le_mul_of_nonneg_left
            (Finset.single_le_sum (f := fun σ : Emb F => σ x.1) (fun σ _ => (x.2.2 σ).le) (Finset.mem_univ τ)) (abs_nonneg _)
        _ = Mi i * ∑ τ : Emb F, τ x.1 := by rw [Finset.sum_mul]
    calc ∑ i, |(c x i : ℝ)| ≤ ∑ i, Mi i * ∑ τ : Emb F, τ x.1 := Finset.sum_le_sum fun i _ => h1 i
      _ = (∑ i, Mi i) * ∑ τ : Emb F, τ x.1 := by rw [Finset.sum_mul]
      _ ≤ M * ∑ τ : Emb F, τ x.1 := mul_le_mul_of_nonneg_right (by simp [M]) hT
  have ha0 : algebraMap (𝓞 F) F a ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 F) F)).2 (nonZeroDivisors.ne_zero ha)
  have hinj : Function.Injective c := by
    intro x y hxy
    have h1 : z x = z y := (RingOfIntegers.basis F).repr.injective (Finsupp.ext fun i => congrFun hxy i)
    have h2 : algebraMap (𝓞 F) F a * x.1 = algebraMap (𝓞 F) F a * y.1 := by rw [← hz, ← hz, h1]
    exact Subtype.ext (mul_left_cancel₀ ha0 h2)
  have hε : 0 < δ / M := div_pos hδ hM
  have hg : Summable fun n : Module.Free.ChooseBasisIndex ℤ (𝓞 F) → ℤ => ∏ i, Real.exp (-(δ / M) * |(n i : ℝ)|) :=
    summable_pi_prod (f := fun _ x => Real.exp (-(δ / M) * |(x : ℝ)|)) (fun _ _ => (Real.exp_pos _).le) fun _ => summable_exp_neg_abs hε
  refine (hg.comp_injective hinj).of_nonneg_of_le (fun _ => (Real.exp_pos _).le) fun x => ?_
  simp only [Function.comp_apply]
  rw [← Real.exp_sum, Real.exp_le_exp, ← Finset.mul_sum]
  have h3 : δ / M * ∑ i, |(c x i : ℝ)| ≤ δ * ∑ τ : Emb F, τ x.1 := by
    calc δ / M * ∑ i, |(c x i : ℝ)| ≤ δ / M * (M * ∑ τ : Emb F, τ x.1) := mul_le_mul_of_nonneg_left (hbound x) hε.le
      _ = δ * ∑ τ : Emb F, τ x.1 := by field_simp
  linarith

end GlobalTheory.LatExpSum
