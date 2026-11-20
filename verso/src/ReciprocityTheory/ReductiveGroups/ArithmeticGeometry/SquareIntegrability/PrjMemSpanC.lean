import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ExistsShortRealSpan

namespace ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
noncomputable section
variable {E : Type} [Field E] [NumberField E]

namespace ChA

/- English proof (translation)
Establish `hq : ∀ x : V, ∀ j, inner ℂ (v j) (x - ∑ i, inner ℂ (v i) x • v i) = 0`. Introduce `x j`. Rewrite using `[inner_sub_right, hv.inner_right_fintype, sub_self]`. Establish `hpr : ∀ i, inner ℂ (v i) p = inner ℂ (v i) (p - pt)`. Introduce `i`.

Rewrite using `[inner_sub_right, hpt i, sub_zero]`. Use `⟨hq p, ?_, ?_⟩` and prove the remaining obligations. Use `set r := p - pt with hr`. Establish `hqeq : (∑ i, inner ℂ (v i) p • v i) = ∑ i, inner ℂ (v i) r • v i`. Repeatedly rewrite using `[hpr]`.

Establish `hres : ‖r - ∑ i, inner ℂ (v i) r • v i‖ ≤ ‖r‖`. Establish `horth : inner ℂ (∑ i, inner ℂ (v i) r • v i) (r - ∑ i, inner ℂ (v i) r • v i) = 0`. Rewrite using `[sum_inner]`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Rewrite using `[inner_smul_left, hq r i, mul_zero]`.

Establish `hpy` using `norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth`. Rewrite `hpy` using `[add_sub_cancel]`. Use polynomial arithmetic with `[norm_nonneg (r - ∑ i, inner ℂ (v i) r • v i), norm_nonneg r, sq_nonneg ‖∑ i, inner ℂ (v i) r • v i‖]`. Establish `hdecomp : p - ∑ i, inner ℂ (v i) p • v i = pt + (r - ∑ i, inner ℂ (v i) r • v i)`. Rewrite using `[hqeq, hr]`.

Normalize the expressions using the abelian group laws. Rewrite using `[hdecomp]`. Establish `h1` using `norm_sub_norm_le pt (-(r - ∑ i, inner ℂ (v i) r • v i))`. Rewrite `h1` using `[norm_neg, sub_neg_eq_add]`. Combine the linear equalities and inequalities to obtain the conclusion.

Combine the equalities or inequalities in the displayed calculation.
-/
lemma gs_step {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {k : ℕ} (v : Fin k → V)
    (hv : Orthonormal ℂ v) (p pt : V) (hpt : ∀ i, inner ℂ (v i) pt = 0) (δ : ℝ)
    (he : ‖p - pt‖ ≤ δ) :
    (∀ j, inner ℂ (v j) (p - ∑ i, inner ℂ (v i) p • v i) = 0) ∧
      ‖pt‖ - δ ≤ ‖p - ∑ i, inner ℂ (v i) p • v i‖ ∧ ∑ i, ‖inner ℂ (v i) p‖ ^ 2 ≤ δ ^ 2 := by
  have hq : ∀ x : V, ∀ j, inner ℂ (v j) (x - ∑ i, inner ℂ (v i) x • v i) = 0 := by
    intro x j
    rw [inner_sub_right, hv.inner_right_fintype, sub_self]
  have hpr : ∀ i, inner ℂ (v i) p = inner ℂ (v i) (p - pt) := by
    intro i
    rw [inner_sub_right, hpt i, sub_zero]
  refine ⟨hq p, ?_, ?_⟩
  · set r := p - pt with hr
    have hqeq : (∑ i, inner ℂ (v i) p • v i) = ∑ i, inner ℂ (v i) r • v i := by
      simp_rw [hpr]
    have hres : ‖r - ∑ i, inner ℂ (v i) r • v i‖ ≤ ‖r‖ := by
      have horth : inner ℂ (∑ i, inner ℂ (v i) r • v i) (r - ∑ i, inner ℂ (v i) r • v i) = 0 := by
        rw [sum_inner]
        refine Finset.sum_eq_zero fun i _ => ?_
        rw [inner_smul_left, hq r i, mul_zero]
      have hpy := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth
      rw [add_sub_cancel] at hpy
      nlinarith [norm_nonneg (r - ∑ i, inner ℂ (v i) r • v i), norm_nonneg r,
        sq_nonneg ‖∑ i, inner ℂ (v i) r • v i‖]
    have hdecomp : p - ∑ i, inner ℂ (v i) p • v i = pt + (r - ∑ i, inner ℂ (v i) r • v i) := by
      rw [hqeq, hr]
      abel
    rw [hdecomp]
    have h1 := norm_sub_norm_le pt (-(r - ∑ i, inner ℂ (v i) r • v i))
    rw [norm_neg, sub_neg_eq_add] at h1
    linarith
  · calc ∑ i, ‖inner ℂ (v i) p‖ ^ 2 = ∑ i, ‖inner ℂ (v i) (p - pt)‖ ^ 2 := by simp_rw [hpr]
      _ ≤ ‖p - pt‖ ^ 2 := hv.sum_inner_products_le (p - pt)
      _ ≤ δ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) he 2

/- English proof (translation)
Establish `hMc : ∀ c : ℂ, ∀ y ∈ I, Mc σ c y ∈ Submodule.span ℂ (I : Set (Vsp dim))`. Introduce `c y hy`. Take `⟨r, hr⟩` from `Mc_comb (dim := dim) σ c`. Rewrite using `[hr]`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations.

Conclude with `Submodule.smul_of_tower_mem _ (r i) (Submodule.subset_span (hIs _ _ hy))`. Use `prj_mem_of_span σ _ (I : Set (Vsp dim)) (fun y hy => ?_) hy` and prove the remaining obligations. Rewrite using `[prj_eq_Mc]`. Conclude with `Submodule.smul_mem _ _ (Submodule.sub_mem _ (hMc 1 y hy) (Submodule.smul_mem _ _ (hMc _ y hy)))`.
-/
lemma prj_mem_spanC [IsCMField E] {dim : (E →+* ℂ) → ℕ} {I : Submodule ℤ (Vsp dim)}
    (hIs : ∀ (α : 𝓞 E) x, x ∈ I → act α x ∈ I) (σ : E →+* ℂ) {y : Vsp dim} (hy : y ∈ IR I) :
    prj σ y ∈ Submodule.span ℂ (I : Set (Vsp dim)) := by
  have hMc : ∀ c : ℂ, ∀ y ∈ I, Mc σ c y ∈ Submodule.span ℂ (I : Set (Vsp dim)) := by
    intro c y hy
    obtain ⟨r, hr⟩ := Mc_comb (dim := dim) σ c
    rw [hr]
    refine Submodule.sum_mem _ fun i _ => ?_
    exact Submodule.smul_of_tower_mem _ (r i) (Submodule.subset_span (hIs _ _ hy))
  refine prj_mem_of_span σ _ (I : Set (Vsp dim)) (fun y hy => ?_) hy
  rw [prj_eq_Mc]
  exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (hMc 1 y hy) (Submodule.smul_mem _ _ (hMc _ y hy)))

def Wk {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) (χ : ℕ → Vsp dim) (k : ℕ) : Submodule ℂ (Vsp dim) :=
  Submodule.span ℂ ((fun i => prj σ (χ i)) '' Set.Iio k)

/- English proof (translation)
The claim follows from `Submodule.span_mono (Set.image_mono (Set.Iio_subset_Iio h))`.
-/
lemma Wk_mono {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) (χ : ℕ → Vsp dim) {a b : ℕ} (h : a ≤ b) :
    Wk σ χ a ≤ Wk σ χ b := Submodule.span_mono (Set.image_mono (Set.Iio_subset_Iio h))

/- English proof (translation)
The claim follows from `Submodule.subset_span ⟨j, h, rfl⟩`.
-/
lemma prj_mem_Wk {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) (χ : ℕ → Vsp dim) {j k : ℕ} (h : j < k) :
    prj σ (χ j) ∈ Wk σ χ k := Submodule.subset_span ⟨j, h, rfl⟩

/- English proof (translation)
Unfold `Wk`. Use `congr 1`. Use `Set.image_congr fun i hi => ?_` and prove the remaining obligations. Rewrite using `[Function.update_of_ne (ne_of_lt (lt_of_lt_of_le hi hj))]`.
-/
lemma Wk_update {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) (χ : ℕ → Vsp dim) {j k : ℕ} (hj : j ≤ k)
    (c : Vsp dim) : Wk σ (Function.update χ k c) j = Wk σ χ j := by
  unfold Wk
  congr 1
  refine Set.image_congr fun i hi => ?_
  rw [Function.update_of_ne (ne_of_lt (lt_of_lt_of_le hi hj))]

/- English proof (translation)
Unfold `Wk`. Establish `himg : (fun i => prj σ (χ i)) '' Set.Iio k = ↑((Finset.range k).image fun i => prj σ (χ i))`. Rewrite using `[Finset.coe_image, Finset.coe_range]`. Rewrite using `[himg]`. Conclude with `(finrank_span_finset_le_card _).trans (Finset.card_image_le.trans (by simp))`.
-/
lemma finrank_Wk {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) (χ : ℕ → Vsp dim) (k : ℕ) :
    Module.finrank ℂ (Wk σ χ k) ≤ k := by
  classical
  unfold Wk
  have himg : (fun i => prj σ (χ i)) '' Set.Iio k = ↑((Finset.range k).image fun i => prj σ (χ i)) := by
    rw [Finset.coe_image, Finset.coe_range]
  rw [himg]
  exact (finrank_span_finset_le_card _).trans (Finset.card_image_le.trans (by simp))

/- English proof (translation)
Rewrite using `[Wk, Submodule.span_le]`. Introduce and unpack `_ ⟨i, hi, rfl⟩`. Conclude with `⟨prj_mem_spanC hIs σ (Xg_IR (hχ i hi)), prj_inPart σ _⟩`.
-/
lemma Wk_le [IsCMField E] {dim : (E →+* ℂ) → ℕ} {L I : Submodule ℤ (Vsp dim)}
    (hIs : ∀ (α : 𝓞 E) x, x ∈ I → act α x ∈ I) (σ : E →+* ℂ) (χ : ℕ → Vsp dim) (k : ℕ)
    (hχ : ∀ s < k, χ s ∈ Xg L I) :
    Wk σ χ k ≤ (Submodule.span ℂ (I : Set (Vsp dim)) ⊓ partSub σ : Submodule ℂ (Vsp dim)) := by
  rw [Wk, Submodule.span_le]
  rintro _ ⟨i, hi, rfl⟩
  exact ⟨prj_mem_spanC hIs σ (Xg_IR (hχ i hi)), prj_inPart σ _⟩

end ChA
end
end ReciprocityTheory.ChartRestriction.G.I2
