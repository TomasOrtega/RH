import Mathlib

/- English proof (translation)
Introduce `G Q _ _ _ _ Γ _ μ _ D π hπ hinv hcov p hp`. Rewrite `hp`, the goal using `[MeasureTheory.ae_iff]`. Take `⟨N, hsub, hNm, hN0⟩` from `MeasureTheory.exists_measurable_superset_of_null hp`. Rewrite `hN0` using `[MeasureTheory.Measure.map_apply hπ hNm, MeasureTheory.Measure.restrict_apply (hπ hNm)]`. Establish `hcover : {y | ¬ p (π y)} ⊆ ⋃ γ : Γ, (fun g : G => (γ : G) * g) ⁻¹' (π ⁻¹' N ∩ D)`.

Introduce `y hy`. Take `⟨γ, hγ⟩` from `hcov y`. Use `Set.mem_iUnion.2 ⟨γ, ?_, hγ⟩` and prove the remaining obligations. Use `show π ((γ : G) * y) ∈ N`. Rewrite using `[hinv]`.

Conclude with `hsub hy`. Use `MeasureTheory.measure_mono_null hcover (MeasureTheory.measure_iUnion_null fun γ => ?_)` and prove the remaining obligations. Rewrite using `[MeasureTheory.measure_preimage_mul]`. Conclude with `hN0`.
-/
theorem UpperTheory.ae_fundamental_domain :
    ∀ {G Q : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] [MeasurableSpace Q]
        (Γ : Subgroup G) [Countable Γ] (μ : MeasureTheory.Measure G) [μ.IsMulLeftInvariant] (D : Set G) (π : G → Q),
        Measurable π → (∀ (γ : Γ) (g : G), π ((γ : G) * g) = π g) → (∀ g : G, ∃ γ : Γ, (γ : G) * g ∈ D) →
        ∀ p : Q → Prop, (∀ᵐ q ∂(MeasureTheory.Measure.map π (μ.restrict D)), p q) → ∀ᵐ y ∂μ, p (π y) := by
  intro G Q _ _ _ _ Γ _ μ _ D π hπ hinv hcov p hp
  rw [MeasureTheory.ae_iff] at hp ⊢
  obtain ⟨N, hsub, hNm, hN0⟩ := MeasureTheory.exists_measurable_superset_of_null hp
  rw [MeasureTheory.Measure.map_apply hπ hNm,
    MeasureTheory.Measure.restrict_apply (hπ hNm)] at hN0
  have hcover : {y | ¬ p (π y)} ⊆
      ⋃ γ : Γ, (fun g : G => (γ : G) * g) ⁻¹' (π ⁻¹' N ∩ D) := by
    intro y hy
    obtain ⟨γ, hγ⟩ := hcov y
    refine Set.mem_iUnion.2 ⟨γ, ?_, hγ⟩
    show π ((γ : G) * y) ∈ N
    rw [hinv]
    exact hsub hy
  refine MeasureTheory.measure_mono_null hcover (MeasureTheory.measure_iUnion_null fun γ => ?_)
  rw [MeasureTheory.measure_preimage_mul]
  exact hN0
