import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.ThStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.GeometricSideEstimate

open UpperTheory.V.Lit.Geo

/- English proof (translation)
Use `⟨h.1, fun s t hs hst => ⟨(h.2 s t hs hst).1, (h.2 s t hs hst).2.trans ?_⟩⟩` and prove the remaining obligations. Use `mul_le_mul_of_nonneg_right (pow_le_pow_right₀ ((one_le_div hs).2 hst) hNM) ?_` and prove the remaining obligations. Conclude with `tsum_nonneg fun i => (Real.exp_pos _).le`.
-/
private theorem scale_mono {ι : Type} {q : ι → ℝ} {N M : ℕ} (h : Scale q N) (hNM : N ≤ M) : Scale q M := by
  refine ⟨h.1, fun s t hs hst => ⟨(h.2 s t hs hst).1, (h.2 s t hs hst).2.trans ?_⟩⟩
  refine mul_le_mul_of_nonneg_right (pow_le_pow_right₀ ((one_le_div hs).2 hst) hNM) ?_
  exact tsum_nonneg fun i => (Real.exp_pos _).le

/- English proof (translation)
Use `⟨fun i => h.1 _, fun s t hs hst => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Conclude with `(e.summable_iff (f := fun k => Real.exp (-Real.pi * (s * q k)))).2 (h.2 s t hs hst).1`. Rewrite using `[e.tsum_eq (fun k => Real.exp (-Real.pi * (s * q k))), e.tsum_eq (fun k => Real.exp (-Real.pi * (t * q k)))]`. Conclude with `(h.2 s t hs hst).2`.
-/
private theorem scale_equiv {ι κ : Type} (e : ι ≃ κ) {q : κ → ℝ} {N : ℕ} (h : Scale q N) :
    Scale (fun i => q (e i)) N := by
  refine ⟨fun i => h.1 _, fun s t hs hst => ⟨?_, ?_⟩⟩
  · exact (e.summable_iff (f := fun k => Real.exp (-Real.pi * (s * q k)))).2 (h.2 s t hs hst).1
  · rw [e.tsum_eq (fun k => Real.exp (-Real.pi * (s * q k))), e.tsum_eq (fun k => Real.exp (-Real.pi * (t * q k)))]
    exact (h.2 s t hs hst).2

/- English proof (translation)
Introduce `A V _ _ _ _ φ ε hε hφ`. Set `W : Submodule ℝ V` to `Submodule.span ℝ (Set.range φ)`. Set `L : Submodule ℤ W` to `(φ.range.comap W.subtype.toAddMonoidHom).toIntSubmodule`. Establish `hmem : ∀ w : W, w ∈ L ↔ (w : V) ∈ Set.range φ` using `fun w => Iff.rfl`. Establish `hnorm : ∀ y : L, y ≠ 0 → ε ≤ ‖y‖`.

Introduce `y hy`. Take `⟨a, ha⟩` from `(hmem y).1 y.2`. Establish `ha0 : a ≠ 0`. Introduce and unpack `rfl`. Apply `hy` to reduce the goal to its premises.

Apply `Subtype.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `using ha.symm`. Use `hφ a ha0` as an intermediate fact. Rewrite `this` using `[ha]`.

Conclude with `this`. Use `haveI : DiscreteTopology L := by`. Apply `discreteTopology_of_isOpen_singleton_zero` to reduce the goal to its premises. Rewrite using `[Metric.isOpen_singleton_iff]`. Use `⟨ε, hε, fun y hy => ?_⟩` and prove the remaining obligations.

Assume the negation of the conclusion as `hne`. Rewrite `hy` using `[dist_zero_right]`. Combine the linear relations using `[hnorm y hne]`. Use `haveI : IsZLattice ℝ L := by`. Use `⟨?_⟩` and prove the remaining obligations.

Establish `hs : (L : Set W) = ((↑) : W → V) ⁻¹' Set.range φ` using `rfl`. Rewrite using `[hs]`. Conclude with `Submodule.span_span_coe_preimage`. Establish `hinj : Function.Injective φ`. Introduce `a b hab`.

Assume the negation of the conclusion as `hne`. Establish `h0` using `hφ (a - b) (sub_ne_zero.mpr hne)`. Rewrite `h0` using `[map_sub, hab, sub_self, norm_zero]`. Combine the linear equalities and inequalities to obtain the conclusion. Set `e : A ≃ L` to `Equiv.ofBijective (fun a => ⟨⟨φ a, Submodule.subset_span ⟨a, rfl⟩⟩, ⟨a, rfl⟩⟩) ⟨fun a b hab => hinj (congrArg (fun y : L => ((y : W) : V)) hab), fun y => by`.

Take `⟨a, ha⟩` from `(hmem y).1 y.2`. Conclude with `⟨a, Subtype.ext (Subtype.ext ha)⟩⟩`. Establish `hL` using `UpperTheory.geometric_side_estimate W L`. Establish `h1` using `scale_equiv e hL`. Conclude with `scale_mono h1 (Submodule.finrank_le W)`.
-/
theorem UpperTheory.scaling_invariance_of_geometric_functional :
    ScaleGen := by
  intro A V _ _ _ _ φ ε hε hφ
  let W : Submodule ℝ V := Submodule.span ℝ (Set.range φ)
  let L : Submodule ℤ W := (φ.range.comap W.subtype.toAddMonoidHom).toIntSubmodule
  have hmem : ∀ w : W, w ∈ L ↔ (w : V) ∈ Set.range φ := fun w => Iff.rfl
  have hnorm : ∀ y : L, y ≠ 0 → ε ≤ ‖y‖ := by
    intro y hy
    obtain ⟨a, ha⟩ := (hmem y).1 y.2
    have ha0 : a ≠ 0 := by
      rintro rfl
      apply hy
      apply Subtype.ext
      apply Subtype.ext
      simpa using ha.symm
    have := hφ a ha0
    rw [ha] at this
    exact this
  haveI : DiscreteTopology L := by
    apply discreteTopology_of_isOpen_singleton_zero
    rw [Metric.isOpen_singleton_iff]
    refine ⟨ε, hε, fun y hy => ?_⟩
    by_contra hne
    rw [dist_zero_right] at hy
    linarith [hnorm y hne]
  haveI : IsZLattice ℝ L := by
    refine ⟨?_⟩
    have hs : (L : Set W) = ((↑) : W → V) ⁻¹' Set.range φ := rfl
    rw [hs]
    exact Submodule.span_span_coe_preimage
  have hinj : Function.Injective φ := by
    intro a b hab
    by_contra hne
    have h0 := hφ (a - b) (sub_ne_zero.mpr hne)
    rw [map_sub, hab, sub_self, norm_zero] at h0
    linarith
  let e : A ≃ L := Equiv.ofBijective
    (fun a => ⟨⟨φ a, Submodule.subset_span ⟨a, rfl⟩⟩, ⟨a, rfl⟩⟩)
    ⟨fun a b hab => hinj (congrArg (fun y : L => ((y : W) : V)) hab), fun y => by
      obtain ⟨a, ha⟩ := (hmem y).1 y.2
      exact ⟨a, Subtype.ext (Subtype.ext ha)⟩⟩
  have hL := UpperTheory.geometric_side_estimate W L
  have h1 := scale_equiv e hL
  exact scale_mono h1 (Submodule.finrank_le W)
