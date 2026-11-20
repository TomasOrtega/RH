import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.EmbComb

namespace ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
noncomputable section

namespace ChA

/- English proof (translation)
Establish `hcpt : IsCompact (Metric.closedBall (0 : V) R)` using `isCompact_closedBall 0 R`. Take `⟨t, htfin, hcov⟩` from `(Metric.totallyBounded_iff.mp hcpt.totallyBounded) (1 / 2) (by norm_num)`. Establish `hT : ∀ x ∈ {x | x ∈ S ∧ ‖x‖ ≤ R}, ∃ y ∈ t, dist x y < 1 / 2`. Introduce `x hx`. Establish `hx' : x ∈ Metric.closedBall (0 : V) R`.

Rewrite using `[mem_closedBall_zero_iff]`. Conclude with `hx.2`. Use `hcov hx'` as an intermediate fact. Simplify using `only [Set.mem_iUnion, Metric.mem_ball, exists_prop] at this`. Conclude with `this`.

Use `choose! f hf hfx using hT`. Use `Set.Finite.of_finite_image (f := f) (htfin.subset ?_) ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Conclude with `hf x hx`. Introduce `x hx y hy hxy`.

Assume the negation of the conclusion as `hne`. Establish `hsep` using `hS x hx.1 y hy.1 hne`. Establish `h1` using `hfx x hx`. Establish `h2` using `hfx y hy`. Rewrite `h1` using `[hxy]`.

Establish `hlt : dist x y < 1`. Combine the equalities or inequalities in the displayed calculation. Rewrite `hlt` using `[dist_eq_norm]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma finite_sep {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (S : Set V) (hS : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ ‖x - y‖) (R : ℝ) :
    {x | x ∈ S ∧ ‖x‖ ≤ R}.Finite := by
  classical
  have hcpt : IsCompact (Metric.closedBall (0 : V) R) := isCompact_closedBall 0 R
  obtain ⟨t, htfin, hcov⟩ :=
    (Metric.totallyBounded_iff.mp hcpt.totallyBounded) (1 / 2) (by norm_num)
  have hT : ∀ x ∈ {x | x ∈ S ∧ ‖x‖ ≤ R}, ∃ y ∈ t, dist x y < 1 / 2 := by
    intro x hx
    have hx' : x ∈ Metric.closedBall (0 : V) R := by
      rw [mem_closedBall_zero_iff]; exact hx.2
    have := hcov hx'
    simp only [Set.mem_iUnion, Metric.mem_ball, exists_prop] at this
    exact this
  choose! f hf hfx using hT
  refine Set.Finite.of_finite_image (f := f) (htfin.subset ?_) ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact hf x hx
  · intro x hx y hy hxy
    by_contra hne
    have hsep := hS x hx.1 y hy.1 hne
    have h1 := hfx x hx
    have h2 := hfx y hy
    rw [hxy] at h1
    have hlt : dist x y < 1 := by
      calc dist x y ≤ dist x (f y) + dist y (f y) := dist_triangle_right _ _ _
        _ < 1 / 2 + 1 / 2 := add_lt_add h1 h2
        _ = 1 := by norm_num
    rw [dist_eq_norm] at hlt
    linarith

/- English proof (translation)
Introduce `x hx y hy hne`. Conclude with `hG (x - y) (G.sub_mem (hS hx) (hS hy)) (sub_ne_zero.mpr hne)`.
-/
lemma sep_of_group {V : Type} [NormedAddCommGroup V] (G : AddSubgroup V)
    (hG : ∀ g ∈ G, g ≠ 0 → 1 ≤ ‖g‖) (S : Set V) (hS : S ⊆ G) :
    ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ ‖x - y‖ := by
  intro x hx y hy hne
  exact hG (x - y) (G.sub_mem (hS hx) (hS hy)) (sub_ne_zero.mpr hne)

/- English proof (translation)
Establish `hsep` using `sep_of_group G hG (G : Set V) subset_rfl`. Establish `hfin : {x | x ∈ (G : Set V) ∧ ‖x‖ ≤ 2 * ‖p‖}.Finite` using `finite_sep _ hsep _`. Establish `hne : ({x | x ∈ (G : Set V) ∧ ‖x‖ ≤ 2 * ‖p‖} : Set V).Nonempty` using `⟨0, G.zero_mem, by simp⟩`. Take `⟨w, hw, hmin⟩` from `Set.exists_min_image _ (fun w => ‖p - w‖) hfin hne`. Use `⟨w, hw.1, fun w' hw' => ?_⟩` and prove the remaining obligations.

Distinguish the cases in `h : ‖w'‖ ≤ 2 * ‖p‖`. Conclude with `hmin w' ⟨hw', h⟩`. Use `push Not at h`. Establish `h0` using `hmin 0 ⟨G.zero_mem, by simp⟩`. Simplify using `only [sub_zero] at h0`.

Establish `h3 : ‖w'‖ - ‖p‖ ≤ ‖p - w'‖`. Rewrite using `[norm_sub_rev]`. Conclude with `norm_sub_norm_le w' p`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma exists_closest {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (G : AddSubgroup V) (hG : ∀ g ∈ G, g ≠ 0 → 1 ≤ ‖g‖) (p : V) :
    ∃ w ∈ G, ∀ w' ∈ G, ‖p - w‖ ≤ ‖p - w'‖ := by
  classical
  have hsep := sep_of_group G hG (G : Set V) subset_rfl
  have hfin : {x | x ∈ (G : Set V) ∧ ‖x‖ ≤ 2 * ‖p‖}.Finite := finite_sep _ hsep _
  have hne : ({x | x ∈ (G : Set V) ∧ ‖x‖ ≤ 2 * ‖p‖} : Set V).Nonempty :=
    ⟨0, G.zero_mem, by simp⟩
  obtain ⟨w, hw, hmin⟩ := Set.exists_min_image _ (fun w => ‖p - w‖) hfin hne
  refine ⟨w, hw.1, fun w' hw' => ?_⟩
  by_cases h : ‖w'‖ ≤ 2 * ‖p‖
  · exact hmin w' ⟨hw', h⟩
  · push Not at h
    have h0 := hmin 0 ⟨G.zero_mem, by simp⟩
    simp only [sub_zero] at h0
    have h3 : ‖w'‖ - ‖p‖ ≤ ‖p - w'‖ := by
      rw [norm_sub_rev]; exact norm_sub_norm_le w' p
    linarith

/- English proof (translation)
Take `⟨b, hbG, hbspan, hbli⟩` from `exists_linearIndependent ℝ G`. Establish `hbfin : b.Finite` using `LinearIndependent.setFinite hbli`. Set `_ : Fintype b` to `hbfin.fintype`. Set `e` to `Fintype.equivFin b`. Set `v : Fin (Fintype.card b) → V` to `fun i => (e.symm i : V)`.

Establish `hv : LinearIndependent ℝ v` using `hbli.comp _ e.symm.injective`. Establish `hvG : ∀ i, v i ∈ G` using `fun i => hbG (e.symm i).2`. Establish `hrange : Set.range v = b`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨i, rfl⟩`. Conclude with `(e.symm i).2`. Introduce `hx`. Conclude with `⟨e ⟨x, hx⟩, by simp [v]⟩`. Establish `hn : Fintype.card b ≤ D`.

Establish `h` using `finrank_span_set_eq_card (R := ℝ) hbli`. Rewrite `h` using `[hbspan, Set.toFinset_card]`. Use linear arithmetic over natural numbers and integers. Establish `hz' : z ∈ Submodule.span ℝ (Set.range v)`. Rewrite using `[hrange, hbspan]`.

Conclude with `hz`. Take `⟨c, hc⟩` from `hNP V (Fintype.card b) v hv z hz'`. Use `⟨∑ i, (c i : ℝ) • v i, ?_, ?_⟩` and prove the remaining obligations. Use `AddSubgroup.sum_mem _ (fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[Int.cast_smul_eq_zsmul]`.

Conclude with `AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (hvG i)) _`. Establish `hsum : ∑ i, ‖v i‖ ^ 2 ≤ (Fintype.card b : ℝ) * ℓ ^ 2`. Combine the equalities or inequalities in the displayed calculation. Establish `h1` using `hG (v i) (hvG i)`. Use the proof step `gcongr)`.

Use `_ = (Fintype.card b : ℝ) * ℓ ^ 2 := by simp`. Establish `hnD : (Fintype.card b : ℝ) ≤ D` using `by exact_mod_cast hn`. Establish `hl : 0 ≤ ℓ ^ 2` using `sq_nonneg ℓ`. Use the polynomial consequences of the given equalities and inequalities.
-/
lemma cover (hNP : Ext.NearestPlane) {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (G : Set V) (ℓ : ℝ) (hG : ∀ g ∈ G, ‖g‖ ≤ ℓ) (D : ℕ)
    (hD : Module.finrank ℝ (Submodule.span ℝ G) ≤ D) {z : V} (hz : z ∈ Submodule.span ℝ G) :
    ∃ g ∈ AddSubgroup.closure G, ‖z - g‖ ^ 2 ≤ D * ℓ ^ 2 / 4 := by
  classical
  obtain ⟨b, hbG, hbspan, hbli⟩ := exists_linearIndependent ℝ G
  have hbfin : b.Finite := LinearIndependent.setFinite hbli
  let _ : Fintype b := hbfin.fintype
  let e := Fintype.equivFin b
  let v : Fin (Fintype.card b) → V := fun i => (e.symm i : V)
  have hv : LinearIndependent ℝ v := hbli.comp _ e.symm.injective
  have hvG : ∀ i, v i ∈ G := fun i => hbG (e.symm i).2
  have hrange : Set.range v = b := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (e.symm i).2
    · intro hx
      exact ⟨e ⟨x, hx⟩, by simp [v]⟩
  have hn : Fintype.card b ≤ D := by
    have h := finrank_span_set_eq_card (R := ℝ) hbli
    rw [hbspan, Set.toFinset_card] at h
    omega
  have hz' : z ∈ Submodule.span ℝ (Set.range v) := by
    rw [hrange, hbspan]; exact hz
  obtain ⟨c, hc⟩ := hNP V (Fintype.card b) v hv z hz'
  refine ⟨∑ i, (c i : ℝ) • v i, ?_, ?_⟩
  · refine AddSubgroup.sum_mem _ (fun i _ => ?_)
    rw [Int.cast_smul_eq_zsmul]
    exact AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (hvG i)) _
  · have hsum : ∑ i, ‖v i‖ ^ 2 ≤ (Fintype.card b : ℝ) * ℓ ^ 2 := by
      calc ∑ i, ‖v i‖ ^ 2 ≤ ∑ _i : Fin (Fintype.card b), ℓ ^ 2 :=
            Finset.sum_le_sum (fun i _ => by
              have h1 := hG (v i) (hvG i)
              gcongr)
        _ = (Fintype.card b : ℝ) * ℓ ^ 2 := by simp
    have hnD : (Fintype.card b : ℝ) ≤ D := by exact_mod_cast hn
    have hl : 0 ≤ ℓ ^ 2 := sq_nonneg ℓ
    nlinarith

end ChA
end
end ReciprocityTheory.ChartRestriction.G.I2
