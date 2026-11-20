import Development.EtaleCohomology.CohomologicalPurity.LeafChartCut

noncomputable section
open TensorProduct

namespace LateralTheory.CohomologicalPurity.ChartCut

/- English proof (translation)
Rewrite using `[eq_top_iff, ← KaehlerDifferential.span_range_derivation, Submodule.span_le]`. Introduce and unpack `_ ⟨a', rfl⟩`. Take `⟨⟨a, s⟩, hs⟩` from `IsLocalization.surj (Submonoid.powers f) a'`. Simplify using `only at hs`. Establish `hu : IsUnit (algebraMap A A' (s : A))` using `IsLocalization.map_units A' s`.

Establish `h1 : algebraMap A A' (s : A) • KaehlerDifferential.D R A' a' ∈ N`. Establish `h` using `congrArg (KaehlerDifferential.D R A') hs`. Rewrite `h` using `[Derivation.leibniz]`. Establish `e : algebraMap A A' (s : A) • KaehlerDifferential.D R A' a' = KaehlerDifferential.D R A' (algebraMap A A' a) - a' • KaehlerDifferential.D R A' (algebraMap A A' s)`. Rewrite using `[← h]`.

Normalize the expressions using the abelian group laws. Rewrite using `[e]`. Conclude with `N.sub_mem (hN a) (N.smul_mem _ (hN s))`. Take `⟨u, hu'⟩` from `hu`. Establish `h2` using `N.smul_mem (↑u⁻¹ : A') h1`.

Rewrite `h2` using `[← hu', smul_smul, Units.inv_mul, one_smul]`. Then use the resulting hypothesis.
-/
lemma kd_span {R A A' : Type} [CommRing R] [CommRing A] [CommRing A'] [Algebra R A] [Algebra A A']
    [Algebra R A'] [IsScalarTower R A A'] (f : A) [IsLocalization.Away f A'] (N : Submodule A' Ω[A'⁄R])
    (hN : ∀ a : A, KaehlerDifferential.D R A' (algebraMap A A' a) ∈ N) : N = ⊤ := by
  rw [eq_top_iff, ← KaehlerDifferential.span_range_derivation, Submodule.span_le]
  rintro _ ⟨a', rfl⟩
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers f) a'
  simp only at hs
  have hu : IsUnit (algebraMap A A' (s : A)) := IsLocalization.map_units A' s
  have h1 : algebraMap A A' (s : A) • KaehlerDifferential.D R A' a' ∈ N := by
    have h := congrArg (KaehlerDifferential.D R A') hs
    rw [Derivation.leibniz] at h
    have e : algebraMap A A' (s : A) • KaehlerDifferential.D R A' a' =
        KaehlerDifferential.D R A' (algebraMap A A' a) - a' • KaehlerDifferential.D R A' (algebraMap A A' s) := by
      rw [← h]; abel
    rw [e]; exact N.sub_mem (hN a) (N.smul_mem _ (hN s))
  obtain ⟨u, hu'⟩ := hu
  have h2 := N.smul_mem (↑u⁻¹ : A') h1
  rwa [← hu', smul_smul, Units.inv_mul, one_smul] at h2

/- English proof (translation)
Introduce `e d R A _ _ φ I p hp hIp hstd`. Use `letI : Algebra R A := φ.toAlgebra`. Use `haveI h1 : Algebra.IsStandardSmoothOfRelativeDimension (e + d) R A := hstd.1`. Use `haveI h2 : Algebra.IsStandardSmoothOfRelativeDimension e R (A ⧸ I) := hstd.2`. Use `haveI : Algebra.IsStandardSmooth R A := h1.isStandardSmooth`.

Use `haveI : Algebra.IsStandardSmooth R (A ⧸ I) := h2.isStandardSmooth`. Establish `hfg : I.FG`. Use `Algebra.FinitePresentation.ker_fG_of_surjective (Ideal.Quotient.mkₐ R I) (Ideal.Quotient.mkₐ_surjective R I)` as an intermediate fact. Simplify `this` using `[Ideal.Quotient.mkₐ_ker]`. Use `haveI : Module.Finite A I := Module.Finite.iff_fg.mpr hfg`.

Use `haveI := hp`. Establish `hrank` using `hR e d R A I p hIp h1 h2`. Take `⟨x, f, hf, hx⟩` from `hP d A I p hrank`. Use `set x' : Fin d → A := fun j => (x j : A) with hx'`. Establish `hxI : ∀ j, x' j ∈ I` using `fun j => (x j).2`.

Establish `hfx : ∀ a ∈ I, f * a ∈ Ideal.span (Set.range x')`. Introduce `a ha`. Establish `h` using `Submodule.mem_map_of_mem (f := I.subtype) (hx ⟨a, ha⟩)`. Rewrite `h` using `[Submodule.map_span, ← Set.range_comp]`. Conclude with `h`.

Take `⟨y, g, hg, hy⟩` from `hS e d R A I p hp hIp h2 x' f hxI hf hfx`. Use `⟨f * g, fun h => (hp.mem_or_mem h).elim hf hg, ?_⟩` and prove the remaining obligations. Introduce `A' _ _ _`. Use `letI : Algebra R A' := ((algebraMap A A').comp φ).toAlgebra`. Use `haveI : IsScalarTower R A A' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)`.

Establish `hfgu : IsUnit (algebraMap A A' (f * g))` using `IsLocalization.Away.algebraMap_isUnit (f * g)`. Rewrite `hfgu` using `[map_mul]`. Establish `hfu : IsUnit (algebraMap A A' f)` using `isUnit_of_mul_isUnit_left hfgu`. Establish `hgu : IsUnit (algebraMap A A' g)` using `isUnit_of_mul_isUnit_right hfgu`. Use `⟨fun j => algebraMap A A' (x' j), fun k => algebraMap A A' (y k), ?_, ?_⟩` and prove the remaining obligations.

Use `haveI : Algebra.IsStandardSmoothOfRelativeDimension 0 A A' := Algebra.IsStandardSmoothOfRelativeDimension.localization_away (f * g)`. Establish `h3 : Algebra.IsStandardSmoothOfRelativeDimension (0 + (e + d)) R A'` using `Algebra.IsStandardSmoothOfRelativeDimension.trans (R := R) (S := A) (T := A') (n := e + d) (m := 0)`. Rewrite `h3` using `[zero_add]`. Use `hE (e + d) R A' (Fin d ⊕ Fin e) _ (by simp [add_comm]) h3 ?_` and prove the remaining obligations. Apply `kd_span (R := R) (A := A) (f * g)` to reduce the goal to its premises.

Introduce `a`. Establish `hm` using `Submodule.mem_map_of_mem (f := KaehlerDifferential.map R R A A') (hy (KaehlerDifferential.D R A a))`. Rewrite `hm` using `[Submodule.map_span, LinearMap.map_smul, KaehlerDifferential.map_D]`. Establish `hle : Submodule.span A (KaehlerDifferential.map R R A A' '' Set.range fun k => KaehlerDifferential.D R A (Sum.elim x' y k)) ≤ (Submodule.span A' (Set.range fun k => KaehlerDifferential.D R A' (Sum.elim (fun j => algebraMap A A' (x' j)) (fun k => algebraMap A A' (y k)) k))).restri …`. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `_ ⟨_, ⟨k, rfl⟩, rfl⟩`. Rewrite using `[KaehlerDifferential.map_D]`. Apply `Submodule.subset_span` to reduce the goal to its premises. Apply the tactic sequence `exact ⟨k, by cases k <;> rfl⟩`. Establish `h5` using `hle hm`.

Rewrite `h5` using `[Submodule.restrictScalars_mem, ← algebraMap_smul A']`. Take `⟨u, hu⟩` from `hgu`. Establish `h6` using `Submodule.smul_mem _ (↑u⁻¹ : A') h5`. Rewrite `h6` using `[← hu, smul_smul, Units.inv_mul, one_smul]`. Then use the resulting hypothesis. Apply `le_antisymm` to reduce the goal to its premises.

Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `a ha`. Rewrite using `[Ideal.mem_comap]`. Establish `h` using `Ideal.mem_map_of_mem (algebraMap A A') (hfx a ha)`. Rewrite `h` using `[Ideal.map_span, map_mul, ← Set.range_comp]`.

Take `⟨u, hu⟩` from `hfu`. Establish `h6` using `Ideal.mul_mem_left _ (↑u⁻¹ : A') h`. Rewrite `h6` using `[← mul_assoc, ← hu, Units.inv_mul, one_mul]`. Conclude with `h6`. Rewrite using `[Ideal.span_le]`.

Introduce and unpack `_ ⟨j, rfl⟩`. Conclude with `Ideal.mem_map_of_mem _ (hxI j)`.
-/
theorem LeafCoord_of (hR : LeafRank) (hP : LeafPick) (hS : LeafSpan) (hE : LeafEt) : LeafCoord := by
  intro e d R A _ _ φ I p hp hIp hstd
  letI : Algebra R A := φ.toAlgebra
  haveI h1 : Algebra.IsStandardSmoothOfRelativeDimension (e + d) R A := hstd.1
  haveI h2 : Algebra.IsStandardSmoothOfRelativeDimension e R (A ⧸ I) := hstd.2
  haveI : Algebra.IsStandardSmooth R A := h1.isStandardSmooth
  haveI : Algebra.IsStandardSmooth R (A ⧸ I) := h2.isStandardSmooth
  have hfg : I.FG := by
    have := Algebra.FinitePresentation.ker_fG_of_surjective (Ideal.Quotient.mkₐ R I)
      (Ideal.Quotient.mkₐ_surjective R I)
    simpa [Ideal.Quotient.mkₐ_ker] using this
  haveI : Module.Finite A I := Module.Finite.iff_fg.mpr hfg
  haveI := hp
  have hrank := hR e d R A I p hIp h1 h2
  obtain ⟨x, f, hf, hx⟩ := hP d A I p hrank
  set x' : Fin d → A := fun j => (x j : A) with hx'
  have hxI : ∀ j, x' j ∈ I := fun j => (x j).2
  have hfx : ∀ a ∈ I, f * a ∈ Ideal.span (Set.range x') := by
    intro a ha
    have h := Submodule.mem_map_of_mem (f := I.subtype) (hx ⟨a, ha⟩)
    rw [Submodule.map_span, ← Set.range_comp] at h
    exact h
  obtain ⟨y, g, hg, hy⟩ := hS e d R A I p hp hIp h2 x' f hxI hf hfx
  refine ⟨f * g, fun h => (hp.mem_or_mem h).elim hf hg, ?_⟩
  intro A' _ _ _
  letI : Algebra R A' := ((algebraMap A A').comp φ).toAlgebra
  haveI : IsScalarTower R A A' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hfgu : IsUnit (algebraMap A A' (f * g)) := IsLocalization.Away.algebraMap_isUnit (f * g)
  rw [map_mul] at hfgu
  have hfu : IsUnit (algebraMap A A' f) := isUnit_of_mul_isUnit_left hfgu
  have hgu : IsUnit (algebraMap A A' g) := isUnit_of_mul_isUnit_right hfgu
  refine ⟨fun j => algebraMap A A' (x' j), fun k => algebraMap A A' (y k), ?_, ?_⟩
  · haveI : Algebra.IsStandardSmoothOfRelativeDimension 0 A A' :=
      Algebra.IsStandardSmoothOfRelativeDimension.localization_away (f * g)
    have h3 : Algebra.IsStandardSmoothOfRelativeDimension (0 + (e + d)) R A' :=
      Algebra.IsStandardSmoothOfRelativeDimension.trans (R := R) (S := A) (T := A') (n := e + d) (m := 0)
    rw [zero_add] at h3
    refine hE (e + d) R A' (Fin d ⊕ Fin e) _ (by simp [add_comm]) h3 ?_
    apply kd_span (R := R) (A := A) (f * g)
    intro a
    have hm := Submodule.mem_map_of_mem (f := KaehlerDifferential.map R R A A')
      (hy (KaehlerDifferential.D R A a))
    rw [Submodule.map_span, LinearMap.map_smul, KaehlerDifferential.map_D] at hm
    have hle : Submodule.span A (KaehlerDifferential.map R R A A' ''
        Set.range fun k => KaehlerDifferential.D R A (Sum.elim x' y k)) ≤
        (Submodule.span A' (Set.range fun k => KaehlerDifferential.D R A'
          (Sum.elim (fun j => algebraMap A A' (x' j)) (fun k => algebraMap A A' (y k)) k))).restrictScalars A := by
      rw [Submodule.span_le]
      rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
      rw [KaehlerDifferential.map_D]
      apply Submodule.subset_span
      exact ⟨k, by cases k <;> rfl⟩
    have h5 := hle hm
    rw [Submodule.restrictScalars_mem, ← algebraMap_smul A'] at h5
    obtain ⟨u, hu⟩ := hgu
    have h6 := Submodule.smul_mem _ (↑u⁻¹ : A') h5
    rwa [← hu, smul_smul, Units.inv_mul, one_smul] at h6
  · apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      intro a ha
      rw [Ideal.mem_comap]
      have h := Ideal.mem_map_of_mem (algebraMap A A') (hfx a ha)
      rw [Ideal.map_span, map_mul, ← Set.range_comp] at h
      obtain ⟨u, hu⟩ := hfu
      have h6 := Ideal.mul_mem_left _ (↑u⁻¹ : A') h
      rw [← mul_assoc, ← hu, Units.inv_mul, one_mul] at h6
      exact h6
    · rw [Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      exact Ideal.mem_map_of_mem _ (hxI j)

end LateralTheory.CohomologicalPurity.ChartCut
