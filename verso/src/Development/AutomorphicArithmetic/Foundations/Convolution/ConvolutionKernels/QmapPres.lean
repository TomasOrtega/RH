import GroundTheory.AutomorphicForms.QuotientMeasure

open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.RightCosetSpace

/- English proof (translation)
Introduce `G _ _ _ _ _ _ _ _ Γ _ μ _ e hΓ he`. Establish `h1 : ∀ x : G, mk Γ (e (Quotient.out (mk Γ x))) = mk Γ (e x)`. Introduce `x`. Establish `h0 : mk Γ (Quotient.out (mk Γ x)) = mk Γ x` using `Quotient.out_eq _`. Take `⟨γ, hγ⟩` from `mk_eq_mk_iff.1 h0`.

Rewrite using `[← hγ]`. Express the relevant statement in the definitionally equal form `mk Γ (e ((γ : G) * x)) = _`. Rewrite using `[map_mul]`. Conclude with `mk_mul_of_mem ((hΓ _).2 γ.2) _`. Establish `hcomm : (fun y : RightCosetSpace Γ => mk Γ (e (Quotient.out y))) ∘ mk Γ = mk Γ ∘ e`.

Use function extensionality and compare the values at `h1`. Establish `hm : Measurable (fun y : RightCosetSpace Γ => mk Γ (e (Quotient.out y)))`. Rewrite using `[measurable_from_quotient]`. Express the relevant statement in the definitionally equal form `Measurable ((fun y : RightCosetSpace Γ => mk Γ (e (Quotient.out y))) ∘ mk Γ)`. Rewrite using `[hcomm]`.

Conclude with `(measurable_mk Γ).comp he.measurable`. Use `⟨h1, hm, ?_⟩` and prove the remaining obligations. Set `ε : Γ → Γ` to `fun γ => ⟨e.symm γ, (hΓ _).1 (by simpa using γ.2)⟩`. Establish `hε : Function.Bijective ε`. Prove the components needed by the constructor for the conclusion.

Introduce `a b hab`. Conclude with `Subtype.ext (e.symm.injective (congrArg Subtype.val hab))`. Introduce `b`. Conclude with `⟨⟨e b, (hΓ _).2 b.2⟩, Subtype.ext (by simp [ε])⟩`. Establish `hF' : IsFundamentalDomain Γ (e ⁻¹' fundamentalDomain Γ) μ` using `(isFundamentalDomain_fundamentalDomain Γ μ).preimage_of_equiv he.quasiMeasurePreserving (e := ε) hε fun γ x => by`.

Express the relevant statement in the definitionally equal form `e (e.symm γ * x) = (γ : G) * e x`. Simplify using the standard rewrite rules. Establish `key` using `map_restrict_eq_quotientMeasure μ hF'`. Use `conv_lhs => rw [← key]`. Rewrite using `[Measure.map_map hm (measurable_mk Γ), hcomm, ← Measure.map_map (measurable_mk Γ) he.measurable, ← Measure.restrict_map he.measurable (measurableSet_fundamentalDomain Γ), he.map_eq]`.

Both sides reduce to the same expression.
-/
theorem UpperTheory.ConvolutionTheory.K.qmapPres :
    ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
      [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [DiscreteTopology Γ]
      (μ : Measure G) [μ.IsHaarMeasure] (e : G ≃ₜ* G), (∀ g, e g ∈ Γ ↔ g ∈ Γ) → MeasurePreserving e μ μ →
      (∀ x : G, mk Γ (e (Quotient.out (mk Γ x))) = mk Γ (e x)) ∧
      MeasurePreserving (fun y : RightCosetSpace Γ => mk Γ (e (Quotient.out y))) (quotientMeasure Γ μ) (quotientMeasure Γ μ) := by
  intro G _ _ _ _ _ _ _ _ Γ _ μ _ e hΓ he
  have h1 : ∀ x : G, mk Γ (e (Quotient.out (mk Γ x))) = mk Γ (e x) := by
    intro x
    have h0 : mk Γ (Quotient.out (mk Γ x)) = mk Γ x := Quotient.out_eq _
    obtain ⟨γ, hγ⟩ := mk_eq_mk_iff.1 h0
    rw [← hγ]
    change mk Γ (e ((γ : G) * x)) = _
    rw [map_mul]
    exact mk_mul_of_mem ((hΓ _).2 γ.2) _
  have hcomm : (fun y : RightCosetSpace Γ => mk Γ (e (Quotient.out y))) ∘ mk Γ = mk Γ ∘ e :=
    funext h1
  have hm : Measurable (fun y : RightCosetSpace Γ => mk Γ (e (Quotient.out y))) := by
    rw [measurable_from_quotient]
    change Measurable ((fun y : RightCosetSpace Γ => mk Γ (e (Quotient.out y))) ∘ mk Γ)
    rw [hcomm]
    exact (measurable_mk Γ).comp he.measurable
  refine ⟨h1, hm, ?_⟩
  let ε : Γ → Γ := fun γ => ⟨e.symm γ, (hΓ _).1 (by simpa using γ.2)⟩
  have hε : Function.Bijective ε := by
    constructor
    · intro a b hab
      exact Subtype.ext (e.symm.injective (congrArg Subtype.val hab))
    · intro b
      exact ⟨⟨e b, (hΓ _).2 b.2⟩, Subtype.ext (by simp [ε])⟩
  have hF' : IsFundamentalDomain Γ (e ⁻¹' fundamentalDomain Γ) μ :=
    (isFundamentalDomain_fundamentalDomain Γ μ).preimage_of_equiv
      he.quasiMeasurePreserving (e := ε) hε fun γ x => by
        change e (e.symm γ * x) = (γ : G) * e x
        simp
  have key := map_restrict_eq_quotientMeasure μ hF'
  conv_lhs => rw [← key]
  rw [Measure.map_map hm (measurable_mk Γ), hcomm, ← Measure.map_map (measurable_mk Γ) he.measurable,
    ← Measure.restrict_map he.measurable (measurableSet_fundamentalDomain Γ), he.map_eq]
  rfl
