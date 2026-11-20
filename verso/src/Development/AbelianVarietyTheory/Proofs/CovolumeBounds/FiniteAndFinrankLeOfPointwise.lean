import Mathlib

open MeasureTheory Module
open scoped InnerProductSpace BigOperators

namespace GlobalTheory.Bergman

section Pointwise

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/- English proof (translation)
Establish `h1 : l f = ∑ i, ⟪b i, f⟫_ℂ • l (b i)` using `by conv_lhs => rw [← b.sum_repr' f]`. Simplify using `[map_sum, map_smul]`. Establish `h2 : ‖l f‖ ≤ ∑ i, ‖l (b i)‖ * ‖⟪b i, f⟫_ℂ‖`. Rewrite using `[h1]`. Use `(norm_sum_le _ _).trans (le_of_eq ?_)` and prove the remaining obligations.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[norm_smul, mul_comm]`. Establish `h3 : ∑ i, ‖⟪b i, f⟫_ℂ‖ ^ 2 = ‖f‖ ^ 2` using `b.sum_sq_norm_inner_right f`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem norm_sq_le_sum_mul {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    (b : OrthonormalBasis ι ℂ V) (l : V →ₗ[ℂ] E) (f : V) :
    ‖l f‖ ^ 2 ≤ (∑ i, ‖l (b i)‖ ^ 2) * ‖f‖ ^ 2 := by
  have h1 : l f = ∑ i, ⟪b i, f⟫_ℂ • l (b i) := by
    conv_lhs => rw [← b.sum_repr' f]
    simp [map_sum, map_smul]
  have h2 : ‖l f‖ ≤ ∑ i, ‖l (b i)‖ * ‖⟪b i, f⟫_ℂ‖ := by
    rw [h1]
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [norm_smul, mul_comm]
  have h3 : ∑ i, ‖⟪b i, f⟫_ℂ‖ ^ 2 = ‖f‖ ^ 2 := b.sum_sq_norm_inner_right f
  calc ‖l f‖ ^ 2 ≤ (∑ i, ‖l (b i)‖ * ‖⟪b i, f⟫_ℂ‖) ^ 2 := by gcongr
    _ ≤ (∑ i, ‖l (b i)‖ ^ 2) * ∑ i, ‖⟪b i, f⟫_ℂ‖ ^ 2 := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    _ = _ := by rw [h3]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/- English proof (translation)
Establish `key : ∑ i, ⟪l (b i), l (b i)⟫_ℂ = ∑ j, ⟪l (c j), l (c j)⟫_ℂ`. Establish `hb : ∀ i, ⟪l (b i), l (b i)⟫_ℂ = ∑ j, ⟪b i, c j⟫_ℂ * ⟪l (c j), l (b i)⟫_ℂ`. Introduce `i`. Use `conv_lhs => enter [2]`. Rewrite using `[← c.sum_repr' (b i)]`.

Simplify using `[map_sum, map_smul, sum_inner, inner_smul_left, mul_comm]`. Establish `hc : ∀ j, ⟪l (c j), l (c j)⟫_ℂ = ∑ i, ⟪b i, c j⟫_ℂ * ⟪l (c j), l (b i)⟫_ℂ`. Introduce `j`. Use `conv_lhs => enter [3]`. Rewrite using `[← b.sum_repr' (c j)]`.

Simplify using `[map_sum, map_smul, inner_sum, inner_smul_right]`. Repeatedly rewrite using `[hb, hc]`. Conclude with `Finset.sum_comm`. Rewrite `key` using `[inner_self_eq_norm_sq_to_K]`. Conclude with `key` after adjusting the coercions.
-/
theorem sum_norm_sq_eq (b : OrthonormalBasis ι ℂ V) (c : OrthonormalBasis κ ℂ V)
    (l : V →ₗ[ℂ] E) : ∑ i, ‖l (b i)‖ ^ 2 = ∑ j, ‖l (c j)‖ ^ 2 := by
  have key : ∑ i, ⟪l (b i), l (b i)⟫_ℂ = ∑ j, ⟪l (c j), l (c j)⟫_ℂ := by
    have hb : ∀ i, ⟪l (b i), l (b i)⟫_ℂ = ∑ j, ⟪b i, c j⟫_ℂ * ⟪l (c j), l (b i)⟫_ℂ := by
      intro i
      conv_lhs => enter [2]; rw [← c.sum_repr' (b i)]
      simp [map_sum, map_smul, sum_inner, inner_smul_left, mul_comm]
    have hc : ∀ j, ⟪l (c j), l (c j)⟫_ℂ = ∑ i, ⟪b i, c j⟫_ℂ * ⟪l (c j), l (b i)⟫_ℂ := by
      intro j
      conv_lhs => enter [3]; rw [← b.sum_repr' (c j)]
      simp [map_sum, map_smul, inner_sum, inner_smul_right]
    simp_rw [hb, hc]
    exact Finset.sum_comm
  simp_rw [inner_self_eq_norm_sq_to_K] at key
  exact_mod_cast key

/- English proof (translation)
Establish `h1 : ∀ i, ‖l (b i)‖ ^ 2 = ∑ k, ‖⟪b i, LinearMap.adjoint l (e k)⟫_ℂ‖ ^ 2`. Introduce `i`. Rewrite using `[← e.sum_sq_norm_inner_left]`. Simplify using `[LinearMap.adjoint_inner_right]`. Repeatedly rewrite using `[h1]`.

Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun k _ => b.sum_sq_norm_inner_right _`.
-/
theorem sum_norm_sq_eq_adjoint [FiniteDimensional ℂ V] [FiniteDimensional ℂ E]
    (b : OrthonormalBasis ι ℂ V) (e : OrthonormalBasis κ ℂ E) (l : V →ₗ[ℂ] E) :
    ∑ i, ‖l (b i)‖ ^ 2 = ∑ k, ‖LinearMap.adjoint l (e k)‖ ^ 2 := by
  have h1 : ∀ i, ‖l (b i)‖ ^ 2 = ∑ k, ‖⟪b i, LinearMap.adjoint l (e k)⟫_ℂ‖ ^ 2 := by
    intro i
    rw [← e.sum_sq_norm_inner_left]
    simp [LinearMap.adjoint_inner_right]
  simp_rw [h1]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => b.sum_sq_norm_inner_right _

/- English proof (translation)
Establish `h1 : ⟪LinearMap.adjoint l e, LinearMap.adjoint l e⟫_ℂ = ⟪e, l (LinearMap.adjoint l e)⟫_ℂ` using `LinearMap.adjoint_inner_left _ _ _`. Establish `h2` using `norm_inner_le_norm (𝕜 := ℂ) e (l (LinearMap.adjoint l e))`. Rewrite `h2` using `[← h1, inner_self_eq_norm_sq_to_K, he, one_mul]`. Simplify using `using h2`.
-/
theorem adjoint_sq_sq_le [FiniteDimensional ℂ V] [FiniteDimensional ℂ E] (l : V →ₗ[ℂ] E)
    {e : E} (he : ‖e‖ = 1) :
    ‖LinearMap.adjoint l e‖ ^ 2 ≤ ‖l (LinearMap.adjoint l e)‖ := by
  have h1 : ⟪LinearMap.adjoint l e, LinearMap.adjoint l e⟫_ℂ
      = ⟪e, l (LinearMap.adjoint l e)⟫_ℂ := LinearMap.adjoint_inner_left _ _ _
  have h2 := norm_inner_le_norm (𝕜 := ℂ) e (l (LinearMap.adjoint l e))
  rw [← h1, inner_self_eq_norm_sq_to_K, he, one_mul] at h2
  simpa using h2

/- English proof (translation)
Use `haveI : FiniteDimensional ℂ V := Module.Finite.of_basis b.toBasis`. Rewrite using `[sum_norm_sq_eq_adjoint b (stdOrthonormalBasis ℂ E) l]`. Establish `: ∀ k, ‖LinearMap.adjoint l (stdOrthonormalBasis ℂ E k)‖ ^ 2 ≤ C`. Introduce `k`. Establish `h1` using `adjoint_sq_sq_le l ((stdOrthonormalBasis ℂ E).orthonormal.1 k)`.

Use `set u := LinearMap.adjoint l (stdOrthonormalBasis ℂ E k)`. Establish `h2` using `h u`. Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`. Establish `hpos : 0 < ‖u‖ ^ 2` using `lt_of_le_of_lt hC hlt`.

Establish `h3 : (‖u‖ ^ 2) ^ 2 ≤ ‖l u‖ ^ 2` using `by gcongr`. Use the polynomial consequences of the given equalities and inequalities. Combine the equalities or inequalities in the displayed calculation.
-/
theorem sum_norm_sq_le [FiniteDimensional ℂ E] (b : OrthonormalBasis ι ℂ V) (l : V →ₗ[ℂ] E)
    {C : ℝ} (hC : 0 ≤ C) (h : ∀ f, ‖l f‖ ^ 2 ≤ C * ‖f‖ ^ 2) :
    ∑ i, ‖l (b i)‖ ^ 2 ≤ finrank ℂ E * C := by
  haveI : FiniteDimensional ℂ V := Module.Finite.of_basis b.toBasis
  rw [sum_norm_sq_eq_adjoint b (stdOrthonormalBasis ℂ E) l]
  have : ∀ k, ‖LinearMap.adjoint l (stdOrthonormalBasis ℂ E k)‖ ^ 2 ≤ C := by
    intro k
    have h1 := adjoint_sq_sq_le l ((stdOrthonormalBasis ℂ E).orthonormal.1 k)
    set u := LinearMap.adjoint l (stdOrthonormalBasis ℂ E k)
    have h2 := h u
    by_contra hlt
    push_neg at hlt
    have hpos : 0 < ‖u‖ ^ 2 := lt_of_le_of_lt hC hlt
    have h3 : (‖u‖ ^ 2) ^ 2 ≤ ‖l u‖ ^ 2 := by gcongr
    nlinarith
  calc _ ≤ ∑ _k : Fin (finrank ℂ E), C := Finset.sum_le_sum fun k _ => this k
    _ = _ := by simp

end Pointwise

section Hilbert

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
variable {E : X → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℂ (E x)]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/- English proof (translation)
Rewrite using `[integral_finset_sum _ fun i _ => hint (b i)]`. Repeatedly rewrite using `[← hnorm, b.orthonormal.1]`. Simplify using `[finrank_eq_card_basis b.toBasis]`.
-/
theorem integral_sum_eq_finrank' {ι : Type*} [Fintype ι] (l : ∀ x, V →ₗ[ℂ] E x)
    (hint : ∀ f, Integrable (fun x => ‖l x f‖ ^ 2) μ)
    (hnorm : ∀ f, ‖f‖ ^ 2 = ∫ x, ‖l x f‖ ^ 2 ∂μ) (b : OrthonormalBasis ι ℂ V) :
    ∫ x, ∑ i, ‖l x (b i)‖ ^ 2 ∂μ = finrank ℂ V := by
  rw [integral_finset_sum _ fun i _ => hint (b i)]
  simp_rw [← hnorm, b.orthonormal.1]
  simp [finrank_eq_card_basis b.toBasis]

/- English proof (translation)
Rewrite using `[← integral_sum_eq_finrank' l hint hnorm (stdOrthonormalBasis ℂ V)]`. Combine the equalities or inequalities in the displayed calculation. Use `integral_mono (integrable_finset_sum _ fun i _ => hint _) (integrable_const _) ?_` and prove the remaining obligations. Introduce `x`. Use `(sum_norm_sq_le _ (l x) hC fun f => h f x).trans ?_` and prove the remaining obligations.

Establish `: (finrank ℂ (E x) : ℝ) ≤ r` using `by exact_mod_cast hr x`. Conclude with `mul_le_mul_of_nonneg_right this hC`. Use `_ = _ := by simp [mul_comm]`.
-/
theorem finrank_le_of_finite' [IsFiniteMeasure μ] [FiniteDimensional ℂ V]
    [∀ x, FiniteDimensional ℂ (E x)] {r : ℕ} (hr : ∀ x, finrank ℂ (E x) ≤ r)
    (l : ∀ x, V →ₗ[ℂ] E x) (hint : ∀ f, Integrable (fun x => ‖l x f‖ ^ 2) μ)
    (hnorm : ∀ f, ‖f‖ ^ 2 = ∫ x, ‖l x f‖ ^ 2 ∂μ) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ f x, ‖l x f‖ ^ 2 ≤ C * ‖f‖ ^ 2) :
    (finrank ℂ V : ℝ) ≤ r * C * μ.real Set.univ := by
  rw [← integral_sum_eq_finrank' l hint hnorm (stdOrthonormalBasis ℂ V)]
  calc _ ≤ ∫ _x, (r * C : ℝ) ∂μ := by
        refine integral_mono (integrable_finset_sum _ fun i _ => hint _) (integrable_const _) ?_
        intro x
        refine (sum_norm_sq_le _ (l x) hC fun f => h f x).trans ?_
        have : (finrank ℂ (E x) : ℝ) ≤ r := by exact_mod_cast hr x
        exact mul_le_mul_of_nonneg_right this hC
    _ = _ := by simp [mul_comm]

/- English proof (translation)
Establish `hfin : FiniteDimensional ℂ V`. Establish `hrank : Module.rank ℂ V ≤ (⌊r * C * μ.real Set.univ⌋₊ : ℕ)`. Use `rank_le fun s hs => ?_` and prove the remaining obligations. Set `W : Submodule ℂ V` to `Submodule.span ℂ (s : Set V)`. Establish `hW : finrank ℂ W = s.card` using `finrank_span_finset_eq_card hs`.

Use `finrank_le_of_finite' (μ := μ) (V := W) hr (fun x => (l x).comp W.subtype) (fun f => hint f) (fun f => hnorm f) hC (fun f x => h f x)` as an intermediate fact. Rewrite `this` using `[hW]`. Conclude with `Nat.le_floor this`. Conclude with `Module.rank_lt_aleph0_iff.1 (hrank.trans_lt (Cardinal.nat_lt_aleph0 _))`. Conclude with `⟨hfin, finrank_le_of_finite' hr l hint hnorm hC h⟩`.
-/
theorem finite_and_finrank_le' [IsFiniteMeasure μ]
    [∀ x, FiniteDimensional ℂ (E x)] {r : ℕ} (hr : ∀ x, finrank ℂ (E x) ≤ r)
    (l : ∀ x, V →ₗ[ℂ] E x) (hint : ∀ f, Integrable (fun x => ‖l x f‖ ^ 2) μ)
    (hnorm : ∀ f, ‖f‖ ^ 2 = ∫ x, ‖l x f‖ ^ 2 ∂μ) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ f x, ‖l x f‖ ^ 2 ≤ C * ‖f‖ ^ 2) :
    FiniteDimensional ℂ V ∧ (finrank ℂ V : ℝ) ≤ r * C * μ.real Set.univ := by
  have hfin : FiniteDimensional ℂ V := by
    have hrank : Module.rank ℂ V ≤ (⌊r * C * μ.real Set.univ⌋₊ : ℕ) := by
      refine rank_le fun s hs => ?_
      let W : Submodule ℂ V := Submodule.span ℂ (s : Set V)
      have hW : finrank ℂ W = s.card := finrank_span_finset_eq_card hs
      have := finrank_le_of_finite' (μ := μ) (V := W) hr (fun x => (l x).comp W.subtype)
        (fun f => hint f) (fun f => hnorm f) hC (fun f x => h f x)
      rw [hW] at this
      exact Nat.le_floor this
    exact Module.rank_lt_aleph0_iff.1 (hrank.trans_lt (Cardinal.nat_lt_aleph0 _))
  exact ⟨hfin, finrank_le_of_finite' hr l hint hnorm hC h⟩

/- English proof (translation)
Use `haveI : FiniteDimensional ℂ V := Module.Finite.of_basis b.toBasis`. Establish `hconst : ∀ y, ∑ i, ‖l y (b i)‖ ^ 2 = ∑ i, ‖l x (b i)‖ ^ 2`. Introduce `y`. Take `⟨u, hu, hl⟩` from `hhom x y`. Set `u' : V ≃ₗᵢ[ℂ] V` to `(⟨u, hu⟩ : V →ₗᵢ[ℂ] V).toLinearIsometryEquiv rfl`.

Rewrite using `[sum_norm_sq_eq b (b.map u') (l y)]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← hl]`. Both sides reduce to the same expression. Rewrite using `[← integral_sum_eq_finrank' l hint hnorm b]`.

Repeatedly rewrite using `[hconst]`. Simplify using the standard rewrite rules.
-/
theorem sum_eq_finrank_of_homogeneous' [IsProbabilityMeasure μ] {ι : Type*} [Fintype ι]
    (l : ∀ x, V →ₗ[ℂ] E x) (hint : ∀ f, Integrable (fun x => ‖l x f‖ ^ 2) μ)
    (hnorm : ∀ f, ‖f‖ ^ 2 = ∫ x, ‖l x f‖ ^ 2 ∂μ)
    (hhom : ∀ x y, ∃ u : V →ₗ[ℂ] V, (∀ f, ‖u f‖ = ‖f‖) ∧ ∀ f, ‖l y (u f)‖ = ‖l x f‖)
    (b : OrthonormalBasis ι ℂ V) (x : X) :
    ∑ i, ‖l x (b i)‖ ^ 2 = finrank ℂ V := by
  haveI : FiniteDimensional ℂ V := Module.Finite.of_basis b.toBasis
  have hconst : ∀ y, ∑ i, ‖l y (b i)‖ ^ 2 = ∑ i, ‖l x (b i)‖ ^ 2 := by
    intro y
    obtain ⟨u, hu, hl⟩ := hhom x y
    let u' : V ≃ₗᵢ[ℂ] V := (⟨u, hu⟩ : V →ₗᵢ[ℂ] V).toLinearIsometryEquiv rfl
    rw [sum_norm_sq_eq b (b.map u') (l y)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hl]
    rfl
  rw [← integral_sum_eq_finrank' l hint hnorm b]
  simp_rw [hconst]
  simp

end Hilbert

section Plain

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
variable {E : X → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℂ (E x)]
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/- English proof (translation)
Establish `hc : ∀ f, Integrable (fun x => ((‖l x f‖ : ℂ)) ^ 2) μ` using `fun f => by`. Use `(hint f).ofReal (𝕜 := ℂ)` as an intermediate fact. Simplify using `using this`. Establish `: (fun x => ⟪l x f, l x g⟫_ℂ) = fun x => (((‖l x (f + g)‖ : ℂ)) ^ 2 - ((‖l x (f - g)‖ : ℂ)) ^ 2 + (((‖l x (f - Complex.I • g)‖ : ℂ)) ^ 2 - ((‖l x (f + Complex.I • g)‖ : ℂ)) ^ 2) * Complex.I) / 4`. Use function extensionality and compare the values at `x`.

Simplify using `using inner_eq_sum_norm_sq_div_four (𝕜 := ℂ) (l x f) (l x g)`. Rewrite using `[this]`. Conclude with `(((hc _).sub (hc _)).add (((hc _).sub (hc _)).mul_const _)).div_const _`.
-/
theorem integrable_inner (l : ∀ x, V →ₗ[ℂ] E x)
    (hint : ∀ f, Integrable (fun x => ‖l x f‖ ^ 2) μ) (f g : V) :
    Integrable (fun x => ⟪l x f, l x g⟫_ℂ) μ := by
  have hc : ∀ f, Integrable (fun x => ((‖l x f‖ : ℂ)) ^ 2) μ := fun f => by
    have := (hint f).ofReal (𝕜 := ℂ)
    simpa using this
  have : (fun x => ⟪l x f, l x g⟫_ℂ) = fun x =>
      (((‖l x (f + g)‖ : ℂ)) ^ 2 - ((‖l x (f - g)‖ : ℂ)) ^ 2 +
        (((‖l x (f - Complex.I • g)‖ : ℂ)) ^ 2 - ((‖l x (f + Complex.I • g)‖ : ℂ)) ^ 2)
          * Complex.I) / 4 := by
    funext x
    simpa using inner_eq_sum_norm_sq_div_four (𝕜 := ℂ) (l x f) (l x g)
  rw [this]
  exact (((hc _).sub (hc _)).add (((hc _).sub (hc _)).mul_const _)).div_const _

/- English proof (translation)
Rewrite using `[← integral_complex_ofReal]`. Simplify using `[inner_self_eq_norm_sq_to_K]`.
-/
theorem integral_inner_self (l : ∀ x, V →ₗ[ℂ] E x) (f : V) :
    ∫ x, ⟪l x f, l x f⟫_ℂ ∂μ = ((∫ x, ‖l x f‖ ^ 2 ∂μ : ℝ) : ℂ) := by
  rw [← integral_complex_ofReal]
  simp [inner_self_eq_norm_sq_to_K]

@[reducible] noncomputable def l2InnerCore (μ : Measure X) (l : ∀ x, V →ₗ[ℂ] E x)
    (hint : ∀ f, Integrable (fun x => ‖l x f‖ ^ 2) μ)
    (hpos : ∀ f, ∫ x, ‖l x f‖ ^ 2 ∂μ = 0 → f = 0) : InnerProductSpace.Core ℂ V where
  inner f g := ∫ x, ⟪l x f, l x g⟫_ℂ ∂μ
  conj_inner_symm f g := by
    rw [← integral_conj]
    simp
  re_inner_nonneg f := by
    rw [integral_inner_self]
    simpa using integral_nonneg fun x => by positivity
  add_left f g h := by
    rw [← integral_add (integrable_inner l hint _ _) (integrable_inner l hint _ _)]
    simp [inner_add_left]
  smul_left f g c := by
    rw [← integral_const_mul]
    simp [inner_smul_left, mul_comm]
  definite f hf := by
    rw [integral_inner_self] at hf
    exact hpos f (by exact_mod_cast hf)

/- English proof (translation)
Use `letI := (l2InnerCore μ l hint hpos).toNormedAddCommGroup`. Use `letI : InnerProductSpace ℂ V := InnerProductSpace.ofCore (l2InnerCore μ l hint hpos).toCore`. Establish `h : ⟪f, f⟫_ℂ = ∫ x, ⟪l x f, l x f⟫_ℂ ∂μ` using `rfl`. Rewrite `h` using `[integral_inner_self, inner_self_eq_norm_sq_to_K]`. Conclude with `Complex.ofReal_injective (by simpa using h)`.
-/
theorem l2_inner_product_norm_sq_eq_integral (l : ∀ x, V →ₗ[ℂ] E x)
    (hint : ∀ f, Integrable (fun x => ‖l x f‖ ^ 2) μ)
    (hpos : ∀ f, ∫ x, ‖l x f‖ ^ 2 ∂μ = 0 → f = 0) (f : V) :
    letI := (l2InnerCore μ l hint hpos).toNormedAddCommGroup
    ‖f‖ ^ 2 = ∫ x, ‖l x f‖ ^ 2 ∂μ := by
  letI := (l2InnerCore μ l hint hpos).toNormedAddCommGroup
  letI : InnerProductSpace ℂ V := InnerProductSpace.ofCore (l2InnerCore μ l hint hpos).toCore
  have h : ⟪f, f⟫_ℂ = ∫ x, ⟪l x f, l x f⟫_ℂ ∂μ := rfl
  rw [integral_inner_self, inner_self_eq_norm_sq_to_K] at h
  exact Complex.ofReal_injective (by simpa using h)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/- English proof (translation)
Use `letI := (l2InnerCore μ l hint hpos).toNormedAddCommGroup`. Use `letI : InnerProductSpace ℂ V := InnerProductSpace.ofCore (l2InnerCore μ l hint hpos).toCore`. Conclude with `⟨(stdOrthonormalBasis ℂ V).toBasis, orthonormal_iff_ite.1 (stdOrthonormalBasis ℂ V).orthonormal⟩`.
-/
theorem exists_orthonormal_basis [FiniteDimensional ℂ V] (l : ∀ x, V →ₗ[ℂ] E x)
    (hint : ∀ f, Integrable (fun x => ‖l x f‖ ^ 2) μ)
    (hpos : ∀ f, ∫ x, ‖l x f‖ ^ 2 ∂μ = 0 → f = 0) :
    ∃ b : Basis (Fin (finrank ℂ V)) ℂ V,
      ∀ i j, ∫ x, ⟪l x (b i), l x (b j)⟫_ℂ ∂μ = if i = j then 1 else 0 := by
  letI := (l2InnerCore μ l hint hpos).toNormedAddCommGroup
  letI : InnerProductSpace ℂ V := InnerProductSpace.ofCore (l2InnerCore μ l hint hpos).toCore
  exact ⟨(stdOrthonormalBasis ℂ V).toBasis,
    orthonormal_iff_ite.1 (stdOrthonormalBasis ℂ V).orthonormal⟩

/- English proof (translation)
Use `letI := (l2InnerCore μ l hint hpos).toNormedAddCommGroup`. Use `letI : InnerProductSpace ℂ V := InnerProductSpace.ofCore (l2InnerCore μ l hint hpos).toCore`. Use `norm_sq_le_sum_mul (b.toOrthonormalBasis (orthonormal_iff_ite.2 hb)) (l x) f` as an intermediate fact. Rewrite `this` using `[l2_inner_product_norm_sq_eq_integral l hint hpos f]`. Simplify using `using this`.
-/
theorem norm_sq_le_bergman_mul (l : ∀ x, V →ₗ[ℂ] E x)
    (hint : ∀ f, Integrable (fun x => ‖l x f‖ ^ 2) μ)
    (hpos : ∀ f, ∫ x, ‖l x f‖ ^ 2 ∂μ = 0 → f = 0) (b : Basis ι ℂ V)
    (hb : ∀ i j, ∫ x, ⟪l x (b i), l x (b j)⟫_ℂ ∂μ = if i = j then 1 else 0) (f : V) (x : X) :
    ‖l x f‖ ^ 2 ≤ (∑ i, ‖l x (b i)‖ ^ 2) * ∫ y, ‖l y f‖ ^ 2 ∂μ := by
  letI := (l2InnerCore μ l hint hpos).toNormedAddCommGroup
  letI : InnerProductSpace ℂ V := InnerProductSpace.ofCore (l2InnerCore μ l hint hpos).toCore
  have := norm_sq_le_sum_mul (b.toOrthonormalBasis (orthonormal_iff_ite.2 hb)) (l x) f
  rw [l2_inner_product_norm_sq_eq_integral l hint hpos f] at this
  simpa using this

/- English proof (translation)
Establish `hint : ∀ f, Integrable (fun x => ‖l x f‖ ^ 2) μ` using `fun f => Integrable.of_bound ((hmeas f).pow 2) (C * ∫ y, ‖l y f‖ ^ 2 ∂μ) (Filter.Eventually.of_forall fun x => by`. Rewrite using `[Real.norm_of_nonneg (by positivity)]; exact h f x)`. Establish `hpos : ∀ f, ∫ x, ‖l x f‖ ^ 2 ∂μ = 0 → f = 0` using `fun f hf => hsep f fun x => by`. Use `h f x` as an intermediate fact. Rewrite `this` using `[hf, mul_zero]`.

Conclude with `norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm this (by positivity)))`. Use `letI := (l2InnerCore μ l hint hpos).toNormedAddCommGroup`. Use `letI : InnerProductSpace ℂ V := InnerProductSpace.ofCore (l2InnerCore μ l hint hpos).toCore`. Conclude with `finite_and_finrank_le' hr l hint (l2_inner_product_norm_sq_eq_integral l hint hpos) hC fun f x => by rw [l2_inner_product_norm_sq_eq_integral l hint hpos f]; exact h f x`.
-/
theorem finite_and_finrank_le_mul [IsFiniteMeasure μ]
    [∀ x, FiniteDimensional ℂ (E x)] {r : ℕ} (hr : ∀ x, finrank ℂ (E x) ≤ r)
    (l : ∀ x, V →ₗ[ℂ] E x) (hmeas : ∀ f, AEStronglyMeasurable (fun x => ‖l x f‖) μ)
    (hsep : ∀ f, (∀ x, l x f = 0) → f = 0) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ f x, ‖l x f‖ ^ 2 ≤ C * ∫ y, ‖l y f‖ ^ 2 ∂μ) :
    FiniteDimensional ℂ V ∧ (finrank ℂ V : ℝ) ≤ r * C * μ.real Set.univ := by
  have hint : ∀ f, Integrable (fun x => ‖l x f‖ ^ 2) μ := fun f =>
    Integrable.of_bound ((hmeas f).pow 2) (C * ∫ y, ‖l y f‖ ^ 2 ∂μ)
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_of_nonneg (by positivity)]; exact h f x)
  have hpos : ∀ f, ∫ x, ‖l x f‖ ^ 2 ∂μ = 0 → f = 0 := fun f hf => hsep f fun x => by
    have := h f x
    rw [hf, mul_zero] at this
    exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm this (by positivity)))
  letI := (l2InnerCore μ l hint hpos).toNormedAddCommGroup
  letI : InnerProductSpace ℂ V := InnerProductSpace.ofCore (l2InnerCore μ l hint hpos).toCore
  exact finite_and_finrank_le' hr l hint (l2_inner_product_norm_sq_eq_integral l hint hpos) hC
    fun f x => by rw [l2_inner_product_norm_sq_eq_integral l hint hpos f]; exact h f x

/- English proof (translation)
Simplify using `using finite_and_finrank_le_mul hE l hmeas hsep hC h`.
-/
theorem finite_and_finrank_le [IsProbabilityMeasure μ]
    [∀ x, FiniteDimensional ℂ (E x)] (hE : ∀ x, finrank ℂ (E x) ≤ 1)
    (l : ∀ x, V →ₗ[ℂ] E x) (hmeas : ∀ f, AEStronglyMeasurable (fun x => ‖l x f‖) μ)
    (hsep : ∀ f, (∀ x, l x f = 0) → f = 0) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ f x, ‖l x f‖ ^ 2 ≤ C * ∫ y, ‖l y f‖ ^ 2 ∂μ) :
    FiniteDimensional ℂ V ∧ (finrank ℂ V : ℝ) ≤ C := by
  simpa using finite_and_finrank_le_mul hE l hmeas hsep hC h

section Transitive

variable {G : Type*} [Group G] [MulAction G X] [MulAction.IsPretransitive G X]
  [MeasurableConstSMul G X] [SMulInvariantMeasure G X μ] [IsProbabilityMeasure μ]

/- English proof (translation)
Use `letI := (l2InnerCore μ l hint hpos).toNormedAddCommGroup`. Use `letI : InnerProductSpace ℂ V := InnerProductSpace.ofCore (l2InnerCore μ l hint hpos).toCore`. Use `sum_eq_finrank_of_homogeneous' l hint (l2_inner_product_norm_sq_eq_integral l hint hpos) ?_ (b.toOrthonormalBasis (orthonormal_iff_ite.2 hb)) x` as an intermediate fact. Simplify using `using this`. Introduce `x y`.

Take `⟨g, rfl⟩` from `MulAction.exists_smul_eq G x y`. Use `⟨ρ g, fun f => ?_, hρ g x⟩` and prove the remaining obligations. Rewrite using `[← pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero, l2_inner_product_norm_sq_eq_integral l hint hpos, l2_inner_product_norm_sq_eq_integral l hint hpos, ← integral_smul_eq_self (μ := μ) _ (g := g)]`. Repeatedly rewrite using `[hρ]`.
-/
theorem bergman_eq_finrank_of_transitive (l : ∀ x, V →ₗ[ℂ] E x)
    (hint : ∀ f, Integrable (fun x => ‖l x f‖ ^ 2) μ)
    (hpos : ∀ f, ∫ x, ‖l x f‖ ^ 2 ∂μ = 0 → f = 0)
    (ρ : G → V →ₗ[ℂ] V) (hρ : ∀ g x f, ‖l (g • x) (ρ g f)‖ = ‖l x f‖) (b : Basis ι ℂ V)
    (hb : ∀ i j, ∫ x, ⟪l x (b i), l x (b j)⟫_ℂ ∂μ = if i = j then 1 else 0) (x : X) :
    ∑ i, ‖l x (b i)‖ ^ 2 = finrank ℂ V := by
  letI := (l2InnerCore μ l hint hpos).toNormedAddCommGroup
  letI : InnerProductSpace ℂ V := InnerProductSpace.ofCore (l2InnerCore μ l hint hpos).toCore
  have := sum_eq_finrank_of_homogeneous' l hint (l2_inner_product_norm_sq_eq_integral l hint hpos) ?_
    (b.toOrthonormalBasis (orthonormal_iff_ite.2 hb)) x
  · simpa using this
  intro x y
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G x y
  refine ⟨ρ g, fun f => ?_, hρ g x⟩
  rw [← pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero, l2_inner_product_norm_sq_eq_integral l hint hpos,
    l2_inner_product_norm_sq_eq_integral l hint hpos, ← integral_smul_eq_self (μ := μ) _ (g := g)]
  simp_rw [hρ]

/- English proof (translation)
Take `⟨b, hb⟩` from `exists_orthonormal_basis l hint hpos`. Rewrite using `[← bergman_eq_finrank_of_transitive l hint hpos ρ hρ b hb x]`. Conclude with `norm_sq_le_bergman_mul l hint hpos b hb f x`.
-/
theorem norm_sq_le_finrank_mul [FiniteDimensional ℂ V] (l : ∀ x, V →ₗ[ℂ] E x)
    (hint : ∀ f, Integrable (fun x => ‖l x f‖ ^ 2) μ)
    (hpos : ∀ f, ∫ x, ‖l x f‖ ^ 2 ∂μ = 0 → f = 0)
    (ρ : G → V →ₗ[ℂ] V) (hρ : ∀ g x f, ‖l (g • x) (ρ g f)‖ = ‖l x f‖) (f : V) (x : X) :
    ‖l x f‖ ^ 2 ≤ finrank ℂ V * ∫ y, ‖l y f‖ ^ 2 ∂μ := by
  obtain ⟨b, hb⟩ := exists_orthonormal_basis l hint hpos
  rw [← bergman_eq_finrank_of_transitive l hint hpos ρ hρ b hb x]
  exact norm_sq_le_bergman_mul l hint hpos b hb f x

end Transitive

end Plain

section Seminorm

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/- English proof (translation)
Use `choose l hl using hp`. Rewrite `hmeas`, `hsep`, `h` using `[hl]`. Conclude with `finite_and_finrank_le (E := fun _ => ℂ) (fun _ => by simp) l hmeas (fun f hf => hsep f fun x => by simp [hf x]) hC h`.
-/
theorem finite_and_finrank_le_of_pointwise (p : X → V → ℝ)
    (hp : ∀ x, ∃ l : V →ₗ[ℂ] ℂ, ∀ f, p x f = ‖l f‖)
    (hmeas : ∀ f, AEStronglyMeasurable (fun x => p x f) μ)
    (hsep : ∀ f, (∀ x, p x f = 0) → f = 0) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ f x, p x f ^ 2 ≤ C * ∫ y, p y f ^ 2 ∂μ) :
    FiniteDimensional ℂ V ∧ (finrank ℂ V : ℝ) ≤ C := by
  choose l hl using hp
  simp_rw [hl] at hmeas hsep h
  exact finite_and_finrank_le (E := fun _ => ℂ) (fun _ => by simp) l hmeas
    (fun f hf => hsep f fun x => by simp [hf x]) hC h

end Seminorm

section Functions

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

variable [IsProbabilityMeasure μ]

/- English proof (translation)
The claim follows from `norm_sq_le_finrank_mul (E := fun _ => ℂ) (G := G) (fun x => (LinearMap.proj x).comp V.subtype) (fun f => hint f f.2) (fun f hf => Subtype.ext (hpos f f.2 hf)) (fun g => (LinearMap.funLeft ℂ ℂ fun x => g⁻¹ • x).restrict fun f hf => hG g⁻¹ f hf) (fun g x f => by change ‖(f : X → ℂ) …`.
-/
theorem norm_sq_le_finrank_mul_fun {G : Type*} [Group G] [MulAction G X]
    [MulAction.IsPretransitive G X] [MeasurableConstSMul G X] [SMulInvariantMeasure G X μ]
    (V : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ V]
    (hint : ∀ f ∈ V, Integrable (fun x => ‖f x‖ ^ 2) μ)
    (hpos : ∀ f ∈ V, ∫ x, ‖f x‖ ^ 2 ∂μ = 0 → f = 0)
    (hG : ∀ g : G, ∀ f ∈ V, (fun x => f (g • x)) ∈ V) {f : X → ℂ} (hf : f ∈ V) (x : X) :
    ‖f x‖ ^ 2 ≤ finrank ℂ V * ∫ y, ‖f y‖ ^ 2 ∂μ :=
  norm_sq_le_finrank_mul (E := fun _ => ℂ) (G := G)
    (fun x => (LinearMap.proj x).comp V.subtype) (fun f => hint f f.2)
    (fun f hf => Subtype.ext (hpos f f.2 hf))
    (fun g => (LinearMap.funLeft ℂ ℂ fun x => g⁻¹ • x).restrict fun f hf => hG g⁻¹ f hf)
    (fun g x f => by
      change ‖(f : X → ℂ) (g⁻¹ • g • x)‖ = ‖(f : X → ℂ) x‖
      rw [inv_smul_smul]) ⟨f, hf⟩ x

end Functions

/- English proof (translation)
Use `haveI : IsProbabilityMeasure ((2 : ENNReal)⁻¹ • (Measure.count : Measure (Fin 2))) := ⟨by simp [ENNReal.inv_mul_cancel]⟩`. Use `haveI : MeasurableConstSMul (Equiv.Perm (Fin 2)) (Fin 2) := ⟨fun _ => measurable_from_top⟩`. Use `haveI : SMulInvariantMeasure (Equiv.Perm (Fin 2)) (Fin 2) (Measure.count : Measure (Fin 2)) := ⟨fun g s _ => by`. Rewrite using `[Measure.count_apply MeasurableSet.of_discrete, Measure.count_apply MeasurableSet.of_discrete]`. Conclude with `congrArg _ (Set.encard_preimage_of_bijective g.bijective s)⟩`.

Use `norm_sq_le_finrank_mul_fun (G := Equiv.Perm (Fin 2)) ⊤ (fun _ _ => Integrable.of_finite) (fun f _ hf => ?_) (fun _ _ _ => trivial) trivial x` and prove the remaining obligations. Rewrite `hf` using `[integral_smul_measure, integral_count]`. Simplify using `only [Fin.sum_univ_two, smul_eq_mul, mul_eq_zero] at hf`. Establish `h : ‖f 0‖ ^ 2 + ‖f 1‖ ^ 2 = 0` using `hf.resolve_left (by simp)`. Establish `h0 : ‖f 0‖ = 0` using `by nlinarith [norm_nonneg (f 0), norm_nonneg (f 1)]`.

Establish `h1 : ‖f 1‖ = 0` using `by nlinarith [norm_nonneg (f 0), norm_nonneg (f 1)]`. Use extensionality with `i`. Use `fin_cases i`. Simplify using `using h0`. Simplify using `using h1`.
-/
example (f : Fin 2 → ℂ) (x : Fin 2) :
    ‖f x‖ ^ 2 ≤ finrank ℂ (⊤ : Submodule ℂ (Fin 2 → ℂ)) *
      ∫ y, ‖f y‖ ^ 2 ∂((2 : ENNReal)⁻¹ • (Measure.count : Measure (Fin 2))) := by
  haveI : IsProbabilityMeasure ((2 : ENNReal)⁻¹ • (Measure.count : Measure (Fin 2))) :=
    ⟨by simp [ENNReal.inv_mul_cancel]⟩
  haveI : MeasurableConstSMul (Equiv.Perm (Fin 2)) (Fin 2) := ⟨fun _ => measurable_from_top⟩
  haveI : SMulInvariantMeasure (Equiv.Perm (Fin 2)) (Fin 2) (Measure.count : Measure (Fin 2)) :=
    ⟨fun g s _ => by
      rw [Measure.count_apply MeasurableSet.of_discrete, Measure.count_apply MeasurableSet.of_discrete]
      exact congrArg _ (Set.encard_preimage_of_bijective g.bijective s)⟩
  refine norm_sq_le_finrank_mul_fun (G := Equiv.Perm (Fin 2)) ⊤ (fun _ _ => Integrable.of_finite)
    (fun f _ hf => ?_) (fun _ _ _ => trivial) trivial x
  rw [integral_smul_measure, integral_count] at hf
  simp only [Fin.sum_univ_two, smul_eq_mul, mul_eq_zero] at hf
  have h : ‖f 0‖ ^ 2 + ‖f 1‖ ^ 2 = 0 := hf.resolve_left (by simp)
  have h0 : ‖f 0‖ = 0 := by nlinarith [norm_nonneg (f 0), norm_nonneg (f 1)]
  have h1 : ‖f 1‖ = 0 := by nlinarith [norm_nonneg (f 0), norm_nonneg (f 1)]
  ext i
  fin_cases i
  · simpa using h0
  · simpa using h1

end GlobalTheory.Bergman
