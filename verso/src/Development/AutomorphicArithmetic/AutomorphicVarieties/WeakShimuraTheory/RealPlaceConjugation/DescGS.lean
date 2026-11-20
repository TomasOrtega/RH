import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RbUVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.FerreroWashington

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical

/- English proof (translation)
Use `continuous_iff_continuousAt.2 fun g => ?_` and prove the remaining obligations. Establish `ht : Filter.Tendsto (fun x => g⁻¹ * x) (nhds g) (nhds 1)`. Use `(continuous_mul_left g⁻¹).tendsto g` as an intermediate fact. Simplify using `using this`. Establish `hev : ∀ᶠ x in nhds g, f x = f g` using `by filter_upwards [ht (hH.mem_nhds H.one_mem)] with x hx`.

Use `hf g _ hx` as an intermediate fact. Simplify using `using this`. Conclude with `tendsto_const_nhds.congr' (hev.mono fun x hx => hx.symm)`.
-/
private theorem continuous_of_right_invariant_open_subgroup {Γ X : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [TopologicalSpace X] (H : Subgroup Γ) (hH : IsOpen (H : Set Γ)) (f : Γ → X)
    (hf : ∀ g, ∀ h ∈ H, f (g * h) = f g) : Continuous f := by
  refine continuous_iff_continuousAt.2 fun g => ?_
  have ht : Filter.Tendsto (fun x => g⁻¹ * x) (nhds g) (nhds 1) := by
    have := (continuous_mul_left g⁻¹).tendsto g
    simpa using this
  have hev : ∀ᶠ x in nhds g, f x = f g := by
    filter_upwards [ht (hH.mem_nhds H.one_mem)] with x hx
    have := hf g _ hx
    simpa using this
  exact tendsto_const_nhds.congr' (hev.mono fun x hx => hx.symm)

/- English proof (translation)
Introduce `F Ω _ _ _ _ _ R M _ _ _ _ _ _ S ρ K N hS hine hK hKρ`. Establish `hN : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ (S : Set (HeightOneSpectrum (𝓞 F))) → ∀ A : ValuationSubring Ω, IsPlaceOver A v → ∀ σ ∈ Inertia A, σ ∈ ineOff F Ω N`. Introduce `v hv A hA σ hσ`. Use `⟨A, ?_, hσ⟩` and prove the remaining obligations. Introduce `hlt`.

Apply `hv` to reduce the goal to its premises. Apply `hS` to reduce the goal to its premises. Establish `h1` using `(hA (N : 𝓞 F)).1`. Simplify using `only [plDvd, Set.mem_setOf_eq]`. Apply `h1` to reduce the goal to its premises.

Simplify using `using hlt`. Establish `hNS : NS Ω (S : Set (HeightOneSpectrum (𝓞 F))) ≤ ρ.ker`. Establish `hker : ∀ g, g ∈ ρ.ker ↔ ∀ m, ρ g m = m`. Introduce `g`. Rewrite using `[MonoidHom.mem_ker]`.

Prove the components needed by the constructor for the conclusion. Introduce `h m`. Rewrite using `[h]`. Both sides reduce to the same expression. Introduce `h`.

Conclude with `LinearMap.ext h`. Establish `hopen : IsOpen (ρ.ker : Set (G F Ω))`. Apply `Subgroup.isOpen_of_mem_nhds (g := 1)` to reduce the goal to its premises. Apply `Filter.mem_of_superset (hK.mem_nhds K.one_mem)` to reduce the goal to its premises. Introduce `σ hσ`.

Conclude with `(hker σ).2 (hKρ σ hσ)`. Apply `Subgroup.topologicalClosure_minimal _ _ (Subgroup.isClosed_of_isOpen _ hopen)` to reduce the goal to its premises. Apply `Subgroup.normalClosure_le_normal` to reduce the goal to its premises. Introduce `σ hσ`. Simplify using `only [Set.mem_iUnion] at hσ`.

Take `⟨v, hv, A, hA, hσ⟩` from `hσ`. Conclude with `(hker σ).2 (hine σ (hN v hv A hA σ hσ))`. Set `ρS : Representation R (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M` to `QuotientGroup.lift _ ρ hNS`. Establish `hρS : ∀ g m, ρS (toGS Ω _ g) m = ρ g m`. Introduce `g m`.

Both sides reduce to the same expression. Use `⟨ρS, hρS, ?_, ?_⟩` and prove the remaining obligations. Use `show Continuous fun p : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) × M => ρS p.1 p.2`. Rewrite using `[continuous_prod_of_discrete_right]`. Introduce `m`.

Rewrite using `[(QuotientGroup.isQuotientMap_mk _).continuous_iff]`. Apply `continuous_of_right_invariant_open_subgroup K hK` to reduce the goal to its premises. Introduce `g h hh`. Use `show ρ (g * h) m = ρ g m`. Rewrite using `[map_mul, Module.End.mul_apply, hKρ h hh]`.

Introduce `z hz`. Take `⟨hzlc, hzc, hz0⟩` from `hz`. Establish `hz1 : z 1 = 0`. Use `hzc 1 1` as an intermediate fact. Simplify using `only [mul_one, map_one, Module.End.one_apply] at this`.

Simplify using `using this`. Set `φ : G F Ω →* Function.End M` to `{ toFun := fun g m => ρ g m + z g map_one' := by`. Use function extensionality and compare the values at `m`. Use `show ρ 1 m + z 1 = m`. Rewrite using `[hz1, map_one]`.

Simplify using the standard rewrite rules. Use the proof step `map_mul' := by`. Introduce `g h`. Use function extensionality and compare the values at `m`. Use `show ρ (g * h) m + z (g * h) = ρ g (ρ h m + z h) + z g`.

Rewrite using `[hzc, map_mul, Module.End.mul_apply, map_add]`. Use `abel }`. Establish `hkerφ : ∀ g, g ∈ φ.ker ↔ z g = 0 ∧ ∀ m, ρ g m = m`. Introduce `g`. Rewrite using `[MonoidHom.mem_ker]`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h' : ∀ m, ρ g m + z g = m` using `fun m => congrFun h m`. Establish `h0 : z g = 0` using `by simpa using h' 0`. Use `⟨h0, fun m => ?_⟩` and prove the remaining obligations.

Simplify `h' m` using `[h0]`. Introduce and unpack `⟨h0, h1⟩`. Use function extensionality and compare the values at `m`. Use `show ρ g m + z g = m`. Rewrite using `[h0, h1, add_zero]`.

Establish `hopen : IsOpen (φ.ker : Set (G F Ω))`. Apply `Subgroup.isOpen_of_mem_nhds (g := 1)` to reduce the goal to its premises. Establish `hU : z ⁻¹' {0} ∈ nhds (1 : G F Ω)` using `(hzlc.isOpen_fiber 0).mem_nhds (by simpa using hz1)`. Apply `Filter.mem_of_superset (Filter.inter_mem (hK.mem_nhds K.one_mem) hU)` to reduce the goal to its premises. Introduce and unpack `σ ⟨hσK, hσz⟩`.

Conclude with `(hkerφ σ).2 ⟨hσz, hKρ σ hσK⟩`. Establish `hNSφ : NS Ω (S : Set (HeightOneSpectrum (𝓞 F))) ≤ φ.ker`. Apply `Subgroup.topologicalClosure_minimal _ _ (Subgroup.isClosed_of_isOpen _ hopen)` to reduce the goal to its premises. Apply `Subgroup.normalClosure_le_normal` to reduce the goal to its premises. Introduce `σ hσ`.

Simplify using `only [Set.mem_iUnion] at hσ`. Take `⟨v, hv, A, hA, hσ⟩` from `hσ`. Establish `hm` using `hN v hv A hA σ hσ`. Conclude with `(hkerφ σ).2 ⟨hz0 σ hm, hine σ hm⟩`. Set `φS` to `QuotientGroup.lift _ φ hNSφ`.

Set `y : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) → M` to `fun q => φS q 0`. Establish `hy : ∀ g, y (toGS Ω _ g) = z g`. Introduce `g`. Use `show ρ g 0 + z g = z g`. Simplify using the standard rewrite rules.

Use `⟨y, ⟨?_, ?_⟩, hy⟩` and prove the remaining obligations. Rewrite using `[(QuotientGroup.isQuotientMap_mk _).continuous_iff]`. Establish `: (y ∘ QuotientGroup.mk) = z` using `funext hy`. Rewrite using `[this]`. Conclude with `hzlc.continuous`.

Introduce `q₁ q₂`. Proceed by induction on `q₁ using QuotientGroup.induction_on with`. Consider the case `H g`. Proceed by induction on `q₂ using QuotientGroup.induction_on with`. Consider the case `H h`.

Establish `e` using `hy (g * h)`. Rewrite `e` using `[map_mul]`. Use `show y (toGS Ω _ g * toGS Ω _ h) = y (toGS Ω _ g) + ρS (toGS Ω _ g) (y (toGS Ω _ h))`. Rewrite using `[e, hy, hy, hρS, hzc]`.
-/
theorem UpperTheory.V.Ws.exists_descent_to_galoisGroupUnramifiedOutside :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (S : Finset (HeightOneSpectrum (𝓞 F))) (ρ : Representation R (G F Ω) M) (K : Subgroup (G F Ω)) (N : ℕ), (∀ v, v ∈ plDvd F N → v ∈ S) → (∀ σ ∈ ineOff F Ω N, ∀ m, ρ σ m = m) → IsOpen (K : Set (G F Ω)) → (∀ σ ∈ K, ∀ m, ρ σ m = m) → ∃ ρS : Representation R (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M, (∀ g m, ρS (toGS Ω _ g) m = ρ g m) ∧ ContAction ρS ∧ ∀ z ∈ cocOff ρ (ineOff F Ω N), ∃ y ∈ Z1 ρS, ∀ g, y (toGS Ω _ g) = z g := by
  intro F Ω _ _ _ _ _ R M _ _ _ _ _ _ S ρ K N hS hine hK hKρ
  have hN : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ (S : Set (HeightOneSpectrum (𝓞 F))) →
      ∀ A : ValuationSubring Ω, IsPlaceOver A v → ∀ σ ∈ Inertia A, σ ∈ ineOff F Ω N := by
    intro v hv A hA σ hσ
    refine ⟨A, ?_, hσ⟩
    intro hlt
    apply hv
    apply hS
    have h1 := (hA (N : 𝓞 F)).1
    simp only [plDvd, Set.mem_setOf_eq]
    apply h1
    simpa using hlt
  have hNS : NS Ω (S : Set (HeightOneSpectrum (𝓞 F))) ≤ ρ.ker := by
    have hker : ∀ g, g ∈ ρ.ker ↔ ∀ m, ρ g m = m := by
      intro g
      rw [MonoidHom.mem_ker]
      constructor
      · intro h m
        rw [h]
        rfl
      · intro h
        exact LinearMap.ext h
    have hopen : IsOpen (ρ.ker : Set (G F Ω)) := by
      apply Subgroup.isOpen_of_mem_nhds (g := 1)
      apply Filter.mem_of_superset (hK.mem_nhds K.one_mem)
      intro σ hσ
      exact (hker σ).2 (hKρ σ hσ)
    apply Subgroup.topologicalClosure_minimal _ _ (Subgroup.isClosed_of_isOpen _ hopen)
    apply Subgroup.normalClosure_le_normal
    intro σ hσ
    simp only [Set.mem_iUnion] at hσ
    obtain ⟨v, hv, A, hA, hσ⟩ := hσ
    exact (hker σ).2 (hine σ (hN v hv A hA σ hσ))
  let ρS : Representation R (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M :=
    QuotientGroup.lift _ ρ hNS
  have hρS : ∀ g m, ρS (toGS Ω _ g) m = ρ g m := by
    intro g m
    rfl
  refine ⟨ρS, hρS, ?_, ?_⟩
  · show Continuous fun p : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) × M => ρS p.1 p.2
    rw [continuous_prod_of_discrete_right]
    intro m
    rw [(QuotientGroup.isQuotientMap_mk _).continuous_iff]
    apply continuous_of_right_invariant_open_subgroup K hK
    intro g h hh
    show ρ (g * h) m = ρ g m
    rw [map_mul, Module.End.mul_apply, hKρ h hh]
  · intro z hz
    obtain ⟨hzlc, hzc, hz0⟩ := hz
    have hz1 : z 1 = 0 := by
      have := hzc 1 1
      simp only [mul_one, map_one, Module.End.one_apply] at this
      simpa using this
    let φ : G F Ω →* Function.End M :=
      { toFun := fun g m => ρ g m + z g
        map_one' := by
          funext m
          show ρ 1 m + z 1 = m
          rw [hz1, map_one]
          simp
        map_mul' := by
          intro g h
          funext m
          show ρ (g * h) m + z (g * h) = ρ g (ρ h m + z h) + z g
          rw [hzc, map_mul, Module.End.mul_apply, map_add]
          abel }
    have hkerφ : ∀ g, g ∈ φ.ker ↔ z g = 0 ∧ ∀ m, ρ g m = m := by
      intro g
      rw [MonoidHom.mem_ker]
      constructor
      · intro h
        have h' : ∀ m, ρ g m + z g = m := fun m => congrFun h m
        have h0 : z g = 0 := by simpa using h' 0
        refine ⟨h0, fun m => ?_⟩
        simpa [h0] using h' m
      · rintro ⟨h0, h1⟩
        funext m
        show ρ g m + z g = m
        rw [h0, h1, add_zero]
    have hopen : IsOpen (φ.ker : Set (G F Ω)) := by
      apply Subgroup.isOpen_of_mem_nhds (g := 1)
      have hU : z ⁻¹' {0} ∈ nhds (1 : G F Ω) :=
        (hzlc.isOpen_fiber 0).mem_nhds (by simpa using hz1)
      apply Filter.mem_of_superset (Filter.inter_mem (hK.mem_nhds K.one_mem) hU)
      rintro σ ⟨hσK, hσz⟩
      exact (hkerφ σ).2 ⟨hσz, hKρ σ hσK⟩
    have hNSφ : NS Ω (S : Set (HeightOneSpectrum (𝓞 F))) ≤ φ.ker := by
      apply Subgroup.topologicalClosure_minimal _ _ (Subgroup.isClosed_of_isOpen _ hopen)
      apply Subgroup.normalClosure_le_normal
      intro σ hσ
      simp only [Set.mem_iUnion] at hσ
      obtain ⟨v, hv, A, hA, hσ⟩ := hσ
      have hm := hN v hv A hA σ hσ
      exact (hkerφ σ).2 ⟨hz0 σ hm, hine σ hm⟩
    let φS := QuotientGroup.lift _ φ hNSφ
    let y : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) → M := fun q => φS q 0
    have hy : ∀ g, y (toGS Ω _ g) = z g := by
      intro g
      show ρ g 0 + z g = z g
      simp
    refine ⟨y, ⟨?_, ?_⟩, hy⟩
    · rw [(QuotientGroup.isQuotientMap_mk _).continuous_iff]
      have : (y ∘ QuotientGroup.mk) = z := funext hy
      rw [this]
      exact hzlc.continuous
    · intro q₁ q₂
      induction q₁ using QuotientGroup.induction_on with
      | H g =>
        induction q₂ using QuotientGroup.induction_on with
        | H h =>
          have e := hy (g * h)
          rw [map_mul] at e
          show y (toGS Ω _ g * toGS Ω _ h) = y (toGS Ω _ g) + ρS (toGS Ω _ g) (y (toGS Ω _ h))
          rw [e, hy, hy, hρS, hzc]
