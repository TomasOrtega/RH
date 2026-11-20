import Mathlib

namespace ReciprocityTheory.ChartRestriction.G.T0

open Module Submodule

/- English proof (translation)
Use `choose m hm using hint`. Establish `hPI` using `IsPrincipalIdealRing.principal (Ideal.span (Set.range m))`. Take `⟨g, hg⟩` from `Submodule.IsPrincipal.principal (Ideal.span (Set.range m))`. Establish `hgI : g ∈ Ideal.span (Set.range m)`. Rewrite using `[hg]`.

Conclude with `Submodule.mem_span_singleton_self g`. Take `⟨c, hc⟩` from `(Submodule.mem_span_range_iff_exists_fun ℤ).1 hgI`. Simplify using `only [smul_eq_mul] at hc`. Establish `hdiv : ∀ j, ∃ a : ℤ, a * g = m j`. Introduce `j`.

Establish `hj : m j ∈ Ideal.span (Set.range m)` using `Ideal.subset_span ⟨j, rfl⟩`. Rewrite `hj` using `[hg]`. Take `⟨a, ha⟩` from `Submodule.mem_span_singleton.1 hj`. Conclude with `⟨a, by simpa using ha⟩`. Use `choose a ha using hdiv`.

Establish `hne : ∃ j, m j ≠ 0`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Apply `hy1` to reduce the goal to its premises. Establish `h0 : ∀ x, inner ℝ y1 x = 0`.

Introduce `x`. Rewrite using `[← b.sum_repr x, inner_sum]`. Simplify using `[inner_smul_right, hm, hcon]`. Conclude with `inner_self_eq_zero.1 (h0 y1)`. Establish `hg0 : g ≠ 0`.

Introduce and unpack `rfl`. Take `⟨j, hj⟩` from `hne`. Conclude with `hj (by rw [← ha j, mul_zero])`. Establish `hgR : (g : ℝ) ≠ 0` using `Int.cast_ne_zero.2 hg0`. Use `⟨(g : ℝ)⁻¹ • y1, ∑ i, c i • b i, (Submodule.mem_span_range_iff_exists_fun ℤ).2 ⟨c, rfl⟩, smul_ne_zero (inv_ne_zero hgR) hy1, fun j => ⟨a j, ?_⟩, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[real_inner_smul_left, hm, ← ha j]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Rewrite using `[norm_smul, norm_inv, Real.norm_eq_abs]`. Establish `h1 : (1 : ℝ) ≤ |(g : ℝ)|`.

Rewrite using `[← Int.cast_abs]`. Conclude with `Int.one_le_abs hg0` after adjusting the coercions. Conclude with `mul_le_of_le_one_left (norm_nonneg _) (inv_le_one_of_one_le₀ h1)`. Rewrite using `[inner_sum]`. Repeatedly rewrite using `[← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_right, real_inner_smul_left, hm]`.

Establish `h2 : ∑ i, (c i : ℝ) * ((g : ℝ)⁻¹ * (m i : ℝ)) = (g : ℝ)⁻¹ * ((∑ i, c i * m i : ℤ) : ℝ)`. Use `push_cast`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[h2, hc]`. Conclude with `inv_mul_cancel₀ hgR`.
-/
theorem gtC_prim {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
    (b : Basis (Fin n) ℝ E) (y1 : E) (hy1 : y1 ≠ 0)
    (hint : ∀ j, ∃ m : ℤ, inner ℝ y1 (b j) = m) :
    ∃ y0 : E, ∃ xu ∈ span ℤ (Set.range b), y0 ≠ 0 ∧ (∀ j, ∃ m : ℤ, inner ℝ y0 (b j) = m) ∧
      ‖y0‖ ≤ ‖y1‖ ∧ inner ℝ y0 xu = 1 := by
  classical
  choose m hm using hint
  have hPI := IsPrincipalIdealRing.principal (Ideal.span (Set.range m))
  obtain ⟨g, hg⟩ := Submodule.IsPrincipal.principal (Ideal.span (Set.range m))
  have hgI : g ∈ Ideal.span (Set.range m) := by
    rw [hg]
    exact Submodule.mem_span_singleton_self g
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hgI
  simp only [smul_eq_mul] at hc
  have hdiv : ∀ j, ∃ a : ℤ, a * g = m j := by
    intro j
    have hj : m j ∈ Ideal.span (Set.range m) := Ideal.subset_span ⟨j, rfl⟩
    rw [hg] at hj
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hj
    exact ⟨a, by simpa using ha⟩
  choose a ha using hdiv
  have hne : ∃ j, m j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hy1
    have h0 : ∀ x, inner ℝ y1 x = 0 := by
      intro x
      rw [← b.sum_repr x, inner_sum]
      simp [inner_smul_right, hm, hcon]
    exact inner_self_eq_zero.1 (h0 y1)
  have hg0 : g ≠ 0 := by
    rintro rfl
    obtain ⟨j, hj⟩ := hne
    exact hj (by rw [← ha j, mul_zero])
  have hgR : (g : ℝ) ≠ 0 := Int.cast_ne_zero.2 hg0
  refine ⟨(g : ℝ)⁻¹ • y1, ∑ i, c i • b i,
    (Submodule.mem_span_range_iff_exists_fun ℤ).2 ⟨c, rfl⟩,
    smul_ne_zero (inv_ne_zero hgR) hy1, fun j => ⟨a j, ?_⟩, ?_, ?_⟩
  · rw [real_inner_smul_left, hm, ← ha j]
    push_cast
    field_simp
  · rw [norm_smul, norm_inv, Real.norm_eq_abs]
    have h1 : (1 : ℝ) ≤ |(g : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs hg0
    exact mul_le_of_le_one_left (norm_nonneg _) (inv_le_one_of_one_le₀ h1)
  · rw [inner_sum]
    simp_rw [← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_right, real_inner_smul_left, hm]
    have h2 : ∑ i, (c i : ℝ) * ((g : ℝ)⁻¹ * (m i : ℝ)) = (g : ℝ)⁻¹ * ((∑ i, c i * m i : ℤ) : ℝ) := by
      push_cast
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [h2, hc]
    exact inv_mul_cancel₀ hgR

/- English proof (translation)
Establish `hintL : ∀ v ∈ span ℤ (Set.range b), ∃ k : ℤ, inner ℝ y0 v = k`. Introduce `v hv`. Take `⟨c, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun ℤ).1 hv`. Use `choose k hk using hint`. Use `⟨∑ i, c i * k i, ?_⟩` and prove the remaining obligations.

Rewrite using `[inner_sum]`. Use `push_cast`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_right, hk]`. Establish `hPW : ∀ v : EuclideanSpace ℝ (Fin (m + 1)), v - inner ℝ y0 v • xu ∈ (ℝ ∙ y0)ᗮ`.

Introduce `v`. Rewrite using `[Submodule.mem_orthogonal_singleton_iff_inner_right, inner_sub_right, real_inner_smul_right, h1, mul_one, sub_self]`. Establish `hPL : ∀ v ∈ span ℤ (Set.range b), v - inner ℝ y0 v • xu ∈ span ℤ (Set.range b)`. Introduce `v hv`. Take `⟨k, hk⟩` from `hintL v hv`.

Rewrite using `[hk, Int.cast_smul_eq_zsmul]`. Conclude with `sub_mem hv (Submodule.smul_mem _ k hxu)`. Set `K : Submodule ℤ (ℝ ∙ y0)ᗮ` to `(span ℤ (Set.range b)).comap (((ℝ ∙ y0)ᗮ).subtype.restrictScalars ℤ)`. Establish `hKmem : ∀ x : (ℝ ∙ y0)ᗮ, x ∈ K ↔ (x : EuclideanSpace ℝ (Fin (m + 1))) ∈ span ℤ (Set.range b)` using `fun x => Iff.rfl`. Establish `: DiscreteTopology K`.

Set `f : K → span ℤ (Set.range b)` to `fun x => ⟨((x : (ℝ ∙ y0)ᗮ) : EuclideanSpace ℝ (Fin (m + 1))), (hKmem x).1 x.2⟩`. Use `DiscreteTopology.of_continuous_injective (f := f) ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _) ?_` and prove the remaining obligations. Introduce `x y hxy`. Establish `hv` using `congrArg Subtype.val hxy`. Conclude with `Subtype.ext (Subtype.ext hv)`.

Establish `: IsZLattice ℝ K`. Use `⟨eq_top_iff.2 fun w _ => ?_⟩` and prove the remaining obligations. Establish `hw0 : inner ℝ y0 (w : EuclideanSpace ℝ (Fin (m + 1))) = 0` using `Submodule.mem_orthogonal_singleton_iff_inner_right.1 w.2`. Establish `hw0' : ∑ j, b.repr (w : EuclideanSpace ℝ (Fin (m + 1))) j * inner ℝ y0 (b j) = 0`. Rewrite using `[← hw0]`.

Use `conv_rhs => rw [← b.sum_repr (w : EuclideanSpace ℝ (Fin (m + 1)))]`. Rewrite using `[inner_sum]`. Repeatedly rewrite using `[real_inner_smul_right]`. Establish `hsum : w = ∑ j, b.repr (w : EuclideanSpace ℝ (Fin (m + 1))) j • (⟨b j - inner ℝ y0 (b j) • xu, hPW (b j)⟩ : (ℝ ∙ y0)ᗮ)`. Apply `Subtype.ext` to reduce the goal to its premises.

Simplify using `only [Submodule.coe_sum, Submodule.coe_smul, smul_sub, Finset.sum_sub_distrib]`. Repeatedly rewrite using `[smul_smul]`. Rewrite using `[← Finset.sum_smul, hw0', zero_smul, sub_zero, b.sum_repr]`. Rewrite using `[hsum]`. Use `Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)` and prove the remaining obligations.

Conclude with `(hKmem _).2 (hPL (b j) (Submodule.subset_span ⟨j, rfl⟩))`. Establish `: Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) = m + 1)` using `⟨finrank_euclideanSpace_fin⟩`. Establish `hrank : Module.finrank ℤ K = m`. Rewrite using `[ZLattice.rank ℝ K, Submodule.finrank_orthogonal_span_singleton (n := m) hy0]`. Set `bK : Basis (Fin m) ℤ K` to `Module.finBasisOfFinrankEq ℤ K hrank`.

Use `⟨bK.ofZLatticeBasis ℝ K, ?_, ?_⟩` and prove the remaining obligations. Introduce `x hx`. Rewrite `hx` using `[Basis.ofZLatticeBasis_span]`. Conclude with `(hKmem x).1 hx`. Introduce `v hv`.

Use `⟨⟨v - inner ℝ y0 v • xu, hPW v⟩, ?_, rfl⟩` and prove the remaining obligations. Rewrite using `[Basis.ofZLatticeBasis_span]`. Conclude with `(hKmem _).2 (hPL v hv)`.
-/
theorem gtD_lat {m : ℕ} (b : Basis (Fin (m + 1)) ℝ (EuclideanSpace ℝ (Fin (m + 1))))
    (y0 xu : EuclideanSpace ℝ (Fin (m + 1))) (hy0 : y0 ≠ 0) (hxu : xu ∈ span ℤ (Set.range b))
    (h1 : inner ℝ y0 xu = 1) (hint : ∀ j, ∃ k : ℤ, inner ℝ y0 (b j) = k) :
    ∃ bW : Basis (Fin m) ℝ (ℝ ∙ y0)ᗮ,
      (∀ x ∈ span ℤ (Set.range bW),
        ((x : (ℝ ∙ y0)ᗮ) : EuclideanSpace ℝ (Fin (m + 1))) ∈ span ℤ (Set.range b)) ∧
      (∀ v ∈ span ℤ (Set.range b), ∃ p ∈ span ℤ (Set.range bW),
        (p : EuclideanSpace ℝ (Fin (m + 1))) = v - inner ℝ y0 v • xu) := by
  classical
  have hintL : ∀ v ∈ span ℤ (Set.range b), ∃ k : ℤ, inner ℝ y0 v = k := by
    intro v hv
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hv
    choose k hk using hint
    refine ⟨∑ i, c i * k i, ?_⟩
    rw [inner_sum]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_right, hk]
  have hPW : ∀ v : EuclideanSpace ℝ (Fin (m + 1)), v - inner ℝ y0 v • xu ∈ (ℝ ∙ y0)ᗮ := by
    intro v
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right, inner_sub_right, real_inner_smul_right, h1,
      mul_one, sub_self]
  have hPL : ∀ v ∈ span ℤ (Set.range b), v - inner ℝ y0 v • xu ∈ span ℤ (Set.range b) := by
    intro v hv
    obtain ⟨k, hk⟩ := hintL v hv
    rw [hk, Int.cast_smul_eq_zsmul]
    exact sub_mem hv (Submodule.smul_mem _ k hxu)
  let K : Submodule ℤ (ℝ ∙ y0)ᗮ :=
    (span ℤ (Set.range b)).comap (((ℝ ∙ y0)ᗮ).subtype.restrictScalars ℤ)
  have hKmem : ∀ x : (ℝ ∙ y0)ᗮ,
      x ∈ K ↔ (x : EuclideanSpace ℝ (Fin (m + 1))) ∈ span ℤ (Set.range b) := fun x => Iff.rfl
  have : DiscreteTopology K := by
    let f : K → span ℤ (Set.range b) := fun x =>
      ⟨((x : (ℝ ∙ y0)ᗮ) : EuclideanSpace ℝ (Fin (m + 1))), (hKmem x).1 x.2⟩
    refine DiscreteTopology.of_continuous_injective (f := f)
      ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _) ?_
    intro x y hxy
    have hv := congrArg Subtype.val hxy
    exact Subtype.ext (Subtype.ext hv)
  have : IsZLattice ℝ K := by
    refine ⟨eq_top_iff.2 fun w _ => ?_⟩
    have hw0 : inner ℝ y0 (w : EuclideanSpace ℝ (Fin (m + 1))) = 0 :=
      Submodule.mem_orthogonal_singleton_iff_inner_right.1 w.2
    have hw0' : ∑ j, b.repr (w : EuclideanSpace ℝ (Fin (m + 1))) j * inner ℝ y0 (b j) = 0 := by
      rw [← hw0]
      conv_rhs => rw [← b.sum_repr (w : EuclideanSpace ℝ (Fin (m + 1)))]
      rw [inner_sum]
      simp_rw [real_inner_smul_right]
    have hsum : w = ∑ j, b.repr (w : EuclideanSpace ℝ (Fin (m + 1))) j •
        (⟨b j - inner ℝ y0 (b j) • xu, hPW (b j)⟩ : (ℝ ∙ y0)ᗮ) := by
      apply Subtype.ext
      simp only [Submodule.coe_sum, Submodule.coe_smul, smul_sub, Finset.sum_sub_distrib]
      simp_rw [smul_smul]
      rw [← Finset.sum_smul, hw0', zero_smul, sub_zero, b.sum_repr]
    rw [hsum]
    refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    exact (hKmem _).2 (hPL (b j) (Submodule.subset_span ⟨j, rfl⟩))
  have : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) = m + 1) := ⟨finrank_euclideanSpace_fin⟩
  have hrank : Module.finrank ℤ K = m := by
    rw [ZLattice.rank ℝ K, Submodule.finrank_orthogonal_span_singleton (n := m) hy0]
  let bK : Basis (Fin m) ℤ K := Module.finBasisOfFinrankEq ℤ K hrank
  refine ⟨bK.ofZLatticeBasis ℝ K, ?_, ?_⟩
  · intro x hx
    rw [Basis.ofZLatticeBasis_span] at hx
    exact (hKmem x).1 hx
  · intro v hv
    refine ⟨⟨v - inner ℝ y0 v • xu, hPW v⟩, ?_, rfl⟩
    rw [Basis.ofZLatticeBasis_span]
    exact (hKmem _).2 (hPL v hv)

end ReciprocityTheory.ChartRestriction.G.T0
