import Development.AutomorphicArithmetic.Foundations.Convolution.BlockEvaluation.TruncSpec
import Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.PowLeExpEventually

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology GroundTheory.Automorphic GroundTheory.Automorphic.Reduction UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci PositivityTheory.Rg.Fx PositivityTheory.Rg.Tf.Core

/- English proof (translation)
Use `tendsto_atTop.2 fun M => ?_` and prove the remaining obligations. Use `filter_upwards [hfac 1, eventually_ge_atTop M.factorial] with j hj hM`. Assume the negation of the conclusion as `hlt`. Establish `h1 : (d j).factorial ≤ M.factorial` using `Nat.factorial_le (not_le.1 hlt).le`. Establish `h2 : ((d j).factorial : ℝ) ≤ j` using `by exact_mod_cast h1.trans hM`.

Establish `h3` using `Real.add_one_le_exp (j : ℝ)`. Rewrite `hj` using `[one_mul]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private lemma abs_d_atTop (d : ℕ → ℕ)
    (hfac : ∀ B : ℝ, ∀ᶠ j : ℕ in atTop, Real.exp (B * j) ≤ (d j).factorial) :
    Tendsto d atTop atTop := by
  refine tendsto_atTop.2 fun M => ?_
  filter_upwards [hfac 1, eventually_ge_atTop M.factorial] with j hj hM
  by_contra hlt
  have h1 : (d j).factorial ≤ M.factorial := Nat.factorial_le (not_le.1 hlt).le
  have h2 : ((d j).factorial : ℝ) ≤ j := by exact_mod_cast h1.trans hM
  have h3 := Real.add_one_le_exp (j : ℝ)
  rw [one_mul] at hj
  linarith

/- English proof (translation)
Rewrite using `[Finset.sum_product, ← Finset.sum_fiberwise_of_maps_to hA]`. Use `Finset.sum_congr rfl fun α _ => ?_` and prove the remaining obligations. Simplify using `only [Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations.

Take `⟨hi1, hi2⟩` from `Finset.mem_filter.1 hi`. Rewrite using `[ht i hi1, hi2, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun ζ _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma abs_sum_eq {T : Type} [DecidableEq ℝ] (s : Finset T) (a : T → ℝ) (A : Finset ℝ)
    (Z : Finset ℂ) (hA : ∀ i ∈ s, a i ∈ A) (v : T → ℂ) (C : T → ℂ → ℂ) (t : T → ℂ)
    (f g : ℝ → ℂ) (n : ℕ) (ht : ∀ i ∈ s, t i = ∑ ζ ∈ Z, C i ζ * ζ ^ n) :
    ∑ q ∈ A ×ˢ Z, (∑ i ∈ s with a i = q.1, v i * C i q.2) * f q.1 * g q.1 * q.2 ^ n =
      ∑ i ∈ s, v i * f (a i) * g (a i) * t i := by
  rw [Finset.sum_product, ← Finset.sum_fiberwise_of_maps_to hA]
  refine Finset.sum_congr rfl fun α _ => ?_
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i hi => ?_
  obtain ⟨hi1, hi2⟩ := Finset.mem_filter.1 hi
  rw [ht i hi1, hi2, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ζ _ => ?_
  ring

/- English proof (translation)
Introduce `T a τ act good x hx hx1 p hp c₁ d hd hfac hτ H`. Establish `hdt` using `abs_d_atTop d hfac`. Establish `hτ' : ∀ i, ∃ (s : Finset ℂ) (c : ℂ → ℂ), 0 ∉ s ∧ (act i → 0 < a i → ∀ᶠ j : ℕ in atTop, ∀ Z : Finset ℂ, s ⊆ Z → τ i j = ∑ ζ ∈ Z, c ζ * ζ ^ j)`. Introduce `i`. Distinguish the cases in `h : act i ∧ 0 < a i`.

Take `⟨s, c, h0, hc⟩` from `hτ i h.1 h.2`. Use `⟨s, fun ζ => if ζ ∈ s then c ζ else 0, h0, fun _ _ => ?_⟩` and prove the remaining obligations. Use `filter_upwards [hc] with j hj Z hZ`. Rewrite using `[hj, ← Finset.sum_subset hZ]`. Conclude with `Finset.sum_congr rfl fun ζ hζ => by simp [hζ]`.

Introduce `ζ _ hζ`. Simplify using `[hζ]`. Conclude with `⟨∅, 0, by simp, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩`. Use `choose S C hS0 hSC using hτ'`. Establish `hF : {i | act i ∧ good i ∧ a i = x}.Finite`.

Take `⟨s, -, -, -, -, hs, -⟩` from `H (x / 2) (by linarith) (by linarith)`. Use `s.finite_toSet.subset fun i hi => ?_` and prove the remaining obligations. Conclude with `(hs i).2 ⟨by rw [hi.2.2]; linarith, hi.1⟩`. Use `⟨hF, ?_⟩` and prove the remaining obligations. Establish `key : ∀ ζ₀ : ℂ, ζ₀ ≠ 0 → ∑ i ∈ hF.toFinset, C i ζ₀ = 0`.

Introduce `ζ₀ hζ₀`. Take `⟨η, hη, hηx, hE⟩` from `UpperTheory.ConvolutionTheory.FX.exponents2 d hd hfac p hp c₁ (-Real.log ‖ζ₀‖) x hx hx1`. Take `⟨N, hE⟩` from `hE η hη le_rfl`. Take `⟨s, u, u', k, hk, hs, hu, hg, hng, hb⟩` from `H η hη hηx`. Use `set A : Finset ℝ := insert x (s.image a) with hA`.

Use `set Z : Finset ℂ := insert ζ₀ (s.biUnion S) with hZ`. Establish `hAη : ∀ α ∈ A, η < α`. Introduce `α hα`. Break down `Finset.mem_insert.1 hα with rfl | hα` into its components or cases. Conclude with `hηx`.

Take `⟨i, hi, rfl⟩` from `Finset.mem_image.1 hα`. Conclude with `((hs i).1 hi).1`. Establish `hZ0 : ∀ ζ ∈ Z, ζ ≠ 0`. Introduce `ζ hζ`. Break down `Finset.mem_insert.1 hζ with rfl | hζ` into its components or cases.

Conclude with `hζ₀`. Take `⟨i, -, hi⟩` from `Finset.mem_biUnion.1 hζ`. Introduce and unpack `rfl`. Conclude with `hS0 i hi`. Establish `hev : ∀ᶠ j : ℕ in atTop, ∀ i ∈ s, τ i j = ∑ ζ ∈ Z, C i ζ * ζ ^ j`.

Use `(Filter.eventually_all_finset s).2 fun i hi => ?_` and prove the remaining obligations. Use `filter_upwards [hSC i ((hs i).1 hi).2 (hη.trans ((hs i).1 hi).1)] with j hj`. Conclude with `hj Z ((Finset.subset_biUnion_of_mem S hi).trans (Finset.subset_insert _ _))`. Take `⟨J, hJ⟩` from `eventually_atTop.1 hev`. Establish `hmem : (x, ζ₀) ∈ A ×ˢ Z` using `Finset.mem_product.2 ⟨Finset.mem_insert_self _ _, Finset.mem_insert_self _ _⟩`.

Establish `main` using `hE (A ×ˢ Z : Finset (ℝ × ℂ)) (fun q => q.1.1) (fun q => q.1.2) (fun q => hAη _ (Finset.mem_product.1 q.2).1) (fun q => hZ0 _ (Finset.mem_product.1 q.2).2) (fun q q' h => Subtype.ext h) (fun j q => ∑ i ∈ s with a i = q.1.1, u i (d j) * C i q.1.2) (fun q => ∑ i ∈ s with a i = q.1.1 …`. Take `⟨K, hK⟩` from `hb N s₀`. Use `⟨K, ?_⟩` and prove the remaining obligations. Use `filter_upwards [hK, eventually_ge_atTop J] with j hj hjJ m hm m' hm'`. Establish `e` using `abs_sum_eq s a A Z (fun i hi => Finset.mem_insert_of_mem (Finset.mem_image_of_mem a hi)) (fun i => u i (d j)) C (fun i => τ i (j + m')) (fun α => (α : ℂ) ^ d j) (fun α => (cheb η (j / p + m) α : ℂ)) (j + m') (hJ (j + m') (by omega))`.

Rewrite `e` using `[← Finset.sum_coe_sort]`. Conclude with `(congrArg norm e).trans_le (hj m hm m' hm'))`. Use the proof step `⟨(x, ζ₀), hmem⟩ le_rfl`. Use the proof step `(by simp only [neg_neg]; rw [Real.exp_log (norm_pos_iff.2 hζ₀)])`. Establish `e : ∑ i ∈ s with a i = x, u' i * C i ζ₀ = k * ∑ i ∈ hF.toFinset, C i ζ₀`.

Rewrite using `[Finset.mul_sum]`. Use `symm`. Use `Finset.sum_subset_zero_on_sdiff ?_ ?_ ?_` and prove the remaining obligations. Introduce `i hi`. Establish `hi` using `hF.mem_toFinset.1 hi`.

Conclude with `Finset.mem_filter.2 ⟨(hs i).2 ⟨by rw [hi.2.2]; exact hηx, hi.1⟩, hi.2.2⟩`. Introduce `i hi`. Take `⟨hi1, hi2⟩` from `Finset.mem_sdiff.1 hi`. Take `⟨hi3, hi4⟩` from `Finset.mem_filter.1 hi1`. Rewrite using `[hng i hi3 fun h => hi2 (hF.mem_toFinset.2 ⟨((hs i).1 hi3).2, h, hi4⟩), zero_mul]`.

Introduce `i hi`. Establish `hi` using `hF.mem_toFinset.1 hi`. Rewrite using `[hg i ((hs i).2 ⟨by rw [hi.2.2]; exact hηx, hi.1⟩) hi.2.1 hi.2.2]`. Conclude with `(mul_eq_zero.1 (e.symm.trans main)).resolve_left hk`. Establish `hev : ∀ᶠ j : ℕ in atTop, ∀ i ∈ hF.toFinset, τ i j = ∑ ζ ∈ hF.toFinset.biUnion S, C i ζ * ζ ^ j`.

Use `(Filter.eventually_all_finset _).2 fun i hi => ?_` and prove the remaining obligations. Establish `hi'` using `hF.mem_toFinset.1 hi`. Use `filter_upwards [hSC i hi'.1 (by rw [hi'.2.2]; exact hx)] with j hj`. Conclude with `hj _ (Finset.subset_biUnion_of_mem S hi)`. Use `filter_upwards [hev] with j hj`.

Use `(finsum_mem_eq_finite_toFinset_sum (fun i => τ i j) hF).trans ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_congr rfl hj, Finset.sum_comm]`. Use `Finset.sum_eq_zero fun ζ hζ => ?_` and prove the remaining obligations. Take `⟨i, -, hi⟩` from `Finset.mem_biUnion.1 hζ`. Rewrite using `[← Finset.sum_mul, key ζ (by rintro rfl; exact hS0 i hi), zero_mul]`.
-/
theorem UpperTheory.ConvolutionTheory.Ci.abs :
    ∀ (T : Type) (a : T → ℝ) (τ : T → ℕ → ℂ) (act good : T → Prop) (x : ℝ), 0 < x → x ≤ 1 → ∀ (p : ℕ), 0 < p → ∀ (c₁ : ℝ) (d : ℕ → ℕ),
      Tendsto (fun j : ℕ => (d j : ℝ) / j) atTop (𝓝 0) → (∀ B : ℝ, ∀ᶠ j : ℕ in atTop, Real.exp (B * j) ≤ (d j).factorial) →
      (∀ i, act i → 0 < a i → ∃ (s : Finset ℂ) (c : ℂ → ℂ), 0 ∉ s ∧ ∀ᶠ j : ℕ in atTop, τ i j = ∑ ζ ∈ s, c ζ * ζ ^ j) →
      (∀ η : ℝ, 0 < η → η < x → ∃ (s : Finset T) (u : T → ℕ → ℂ) (u' : T → ℂ) (k : ℂ), k ≠ 0 ∧ (∀ i, i ∈ s ↔ η < a i ∧ act i) ∧
        (∀ i ∈ s, Tendsto (u i) atTop (𝓝 (u' i))) ∧ (∀ i ∈ s, good i → a i = x → u' i = k) ∧ (∀ i ∈ s, ¬ good i → u' i = 0) ∧
        ∀ (N : ℝ) (s₀ : ℕ), ∃ K : ℝ, ∀ᶠ j : ℕ in atTop, ∀ m ≤ s₀, ∀ m' ≤ s₀,
          ‖∑ i ∈ s, u i (d j) * (a i : ℂ) ^ d j * (cheb η (j / p + m) (a i) : ℂ) * τ i (j + m')‖ ≤
            K ^ (d j + 1) * (Real.exp (c₁ * j) * (1 + (4 / η) ^ (j / p) / (d j).factorial) + (4 / η) ^ (j / p) * Real.exp (-N * j))) →
      {i | act i ∧ good i ∧ a i = x}.Finite ∧ ∀ᶠ j : ℕ in atTop, ∑ᶠ i ∈ {i | act i ∧ good i ∧ a i = x}, τ i j = 0 := by
  intro T a τ act good x hx hx1 p hp c₁ d hd hfac hτ H
  classical
  have hdt := abs_d_atTop d hfac
  have hτ' : ∀ i, ∃ (s : Finset ℂ) (c : ℂ → ℂ), 0 ∉ s ∧ (act i → 0 < a i →
      ∀ᶠ j : ℕ in atTop, ∀ Z : Finset ℂ, s ⊆ Z → τ i j = ∑ ζ ∈ Z, c ζ * ζ ^ j) := by
    intro i
    by_cases h : act i ∧ 0 < a i
    · obtain ⟨s, c, h0, hc⟩ := hτ i h.1 h.2
      refine ⟨s, fun ζ => if ζ ∈ s then c ζ else 0, h0, fun _ _ => ?_⟩
      filter_upwards [hc] with j hj Z hZ
      rw [hj, ← Finset.sum_subset hZ]
      · exact Finset.sum_congr rfl fun ζ hζ => by simp [hζ]
      · intro ζ _ hζ; simp [hζ]
    · exact ⟨∅, 0, by simp, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose S C hS0 hSC using hτ'
  have hF : {i | act i ∧ good i ∧ a i = x}.Finite := by
    obtain ⟨s, -, -, -, -, hs, -⟩ := H (x / 2) (by linarith) (by linarith)
    refine s.finite_toSet.subset fun i hi => ?_
    exact (hs i).2 ⟨by rw [hi.2.2]; linarith, hi.1⟩
  refine ⟨hF, ?_⟩
  have key : ∀ ζ₀ : ℂ, ζ₀ ≠ 0 → ∑ i ∈ hF.toFinset, C i ζ₀ = 0 := by
    intro ζ₀ hζ₀
    obtain ⟨η, hη, hηx, hE⟩ :=
      UpperTheory.ConvolutionTheory.FX.exponents2 d hd hfac p hp c₁ (-Real.log ‖ζ₀‖) x hx hx1
    obtain ⟨N, hE⟩ := hE η hη le_rfl
    obtain ⟨s, u, u', k, hk, hs, hu, hg, hng, hb⟩ := H η hη hηx
    set A : Finset ℝ := insert x (s.image a) with hA
    set Z : Finset ℂ := insert ζ₀ (s.biUnion S) with hZ
    have hAη : ∀ α ∈ A, η < α := by
      intro α hα
      rcases Finset.mem_insert.1 hα with rfl | hα
      · exact hηx
      · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hα
        exact ((hs i).1 hi).1
    have hZ0 : ∀ ζ ∈ Z, ζ ≠ 0 := by
      intro ζ hζ
      rcases Finset.mem_insert.1 hζ with rfl | hζ
      · exact hζ₀
      · obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 hζ
        rintro rfl
        exact hS0 i hi
    have hev : ∀ᶠ j : ℕ in atTop, ∀ i ∈ s, τ i j = ∑ ζ ∈ Z, C i ζ * ζ ^ j := by
      refine (Filter.eventually_all_finset s).2 fun i hi => ?_
      filter_upwards [hSC i ((hs i).1 hi).2 (hη.trans ((hs i).1 hi).1)] with j hj
      exact hj Z ((Finset.subset_biUnion_of_mem S hi).trans (Finset.subset_insert _ _))
    obtain ⟨J, hJ⟩ := eventually_atTop.1 hev
    have hmem : (x, ζ₀) ∈ A ×ˢ Z :=
      Finset.mem_product.2 ⟨Finset.mem_insert_self _ _, Finset.mem_insert_self _ _⟩
    have main := hE (A ×ˢ Z : Finset (ℝ × ℂ)) (fun q => q.1.1) (fun q => q.1.2)
      (fun q => hAη _ (Finset.mem_product.1 q.2).1) (fun q => hZ0 _ (Finset.mem_product.1 q.2).2)
      (fun q q' h => Subtype.ext h)
      (fun j q => ∑ i ∈ s with a i = q.1.1, u i (d j) * C i q.1.2)
      (fun q => ∑ i ∈ s with a i = q.1.1, u' i * C i q.1.2)
      (fun q => tendsto_finset_sum _ fun i hi =>
        ((hu i (Finset.mem_filter.1 hi).1).comp hdt).mul_const _)
      (fun s₀ => by
        obtain ⟨K, hK⟩ := hb N s₀
        refine ⟨K, ?_⟩
        filter_upwards [hK, eventually_ge_atTop J] with j hj hjJ m hm m' hm'
        have e := abs_sum_eq s a A Z
          (fun i hi => Finset.mem_insert_of_mem (Finset.mem_image_of_mem a hi))
          (fun i => u i (d j)) C (fun i => τ i (j + m')) (fun α => (α : ℂ) ^ d j)
          (fun α => (cheb η (j / p + m) α : ℂ)) (j + m') (hJ (j + m') (by omega))
        rw [← Finset.sum_coe_sort] at e
        exact (congrArg norm e).trans_le (hj m hm m' hm'))
      ⟨(x, ζ₀), hmem⟩ le_rfl
      (by simp only [neg_neg]; rw [Real.exp_log (norm_pos_iff.2 hζ₀)])
    have e : ∑ i ∈ s with a i = x, u' i * C i ζ₀ = k * ∑ i ∈ hF.toFinset, C i ζ₀ := by
      rw [Finset.mul_sum]
      symm
      refine Finset.sum_subset_zero_on_sdiff ?_ ?_ ?_
      · intro i hi
        have hi := hF.mem_toFinset.1 hi
        exact Finset.mem_filter.2 ⟨(hs i).2 ⟨by rw [hi.2.2]; exact hηx, hi.1⟩, hi.2.2⟩
      · intro i hi
        obtain ⟨hi1, hi2⟩ := Finset.mem_sdiff.1 hi
        obtain ⟨hi3, hi4⟩ := Finset.mem_filter.1 hi1
        rw [hng i hi3 fun h => hi2 (hF.mem_toFinset.2 ⟨((hs i).1 hi3).2, h, hi4⟩), zero_mul]
      · intro i hi
        have hi := hF.mem_toFinset.1 hi
        rw [hg i ((hs i).2 ⟨by rw [hi.2.2]; exact hηx, hi.1⟩) hi.2.1 hi.2.2]
    exact (mul_eq_zero.1 (e.symm.trans main)).resolve_left hk
  have hev : ∀ᶠ j : ℕ in atTop, ∀ i ∈ hF.toFinset,
      τ i j = ∑ ζ ∈ hF.toFinset.biUnion S, C i ζ * ζ ^ j := by
    refine (Filter.eventually_all_finset _).2 fun i hi => ?_
    have hi' := hF.mem_toFinset.1 hi
    filter_upwards [hSC i hi'.1 (by rw [hi'.2.2]; exact hx)] with j hj
    exact hj _ (Finset.subset_biUnion_of_mem S hi)
  filter_upwards [hev] with j hj
  refine (finsum_mem_eq_finite_toFinset_sum (fun i => τ i j) hF).trans ?_
  rw [Finset.sum_congr rfl hj, Finset.sum_comm]
  refine Finset.sum_eq_zero fun ζ hζ => ?_
  obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 hζ
  rw [← Finset.sum_mul, key ζ (by rintro rfl; exact hS0 i hi), zero_mul]
