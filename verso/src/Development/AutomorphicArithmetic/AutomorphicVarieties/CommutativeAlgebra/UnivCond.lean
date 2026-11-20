import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.FramedTwoCoboundaries
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoQuot

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

/- English proof (translation)
Apply `Lift.ext` to reduce the goal to its premises. Use extensionality with `x a b`. Both sides reduce to the same expression.
-/
private theorem lift_map_map' {O : Type} [CommRing O] [IsLocalRing O] {Γ ι : Type} [Group Γ]
    [TopologicalSpace Γ] [Fintype ι] [DecidableEq ι] {rbar : Γ →* Matrix ι ι (ResidueField O)}
    {R R' R'' : Type} [CommRing R] [Algebra O R] [IsCO O R] [CommRing R'] [Algebra O R'] [IsCO O R']
    [CommRing R''] [Algebra O R''] [IsCO O R''] (f : R →ₐ[O] R') (g : R' →ₐ[O] R'')
    (r : Lift O rbar R) : Lift.map g (Lift.map f r) = Lift.map (g.comp f) r := by
  apply Lift.ext
  ext x a b
  rfl

/- English proof (translation)
Introduce `O _ _ Γ ι _ _ _ _ rbar R _ _ _ r P₀ P hrep hcl hex`. Take `⟨I, hI⟩` from `hcl R r`. Take `⟨R₁, _, _, _, r₁, h0, h1⟩` from `hex`. Take `⟨f, hf, -⟩` from `(hrep R₁).2 r₁ h0`. Establish `hf1 : P R₁ (Lift.map f r)` using `hf ▸ h1`.

Establish `hfI : ∀ x ∈ I, f x = 0` using `(hI R₁ f).1 hf1`. Use `set J : Ideal R := Ideal.span I`. Establish `hJf : ∀ x ∈ J, f x = 0`. Introduce `x hx`. Establish `hle : J ≤ RingHom.ker f.toRingHom` using `Ideal.span_le.2 (fun y hy => hfI y hy)`.

Conclude with `hle hx`. Establish `hJ : J ≠ ⊤`. Introduce `htop`. Establish `h1mem : (1 : R) ∈ J` using `htop ▸ Submodule.mem_top`. Use `hJf 1 h1mem` as an intermediate fact.

Simplify using `at this`. Use `haveI : Nontrivial (R ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJ`. Use `haveI hco : IsCO O (R ⧸ J) := co_quot O R (R ⧸ J) (Ideal.Quotient.mkₐ O J) (Ideal.Quotient.mkₐ_surjective O J)`. Establish `hpI : ∀ x ∈ I, Ideal.Quotient.mkₐ O J x = 0`. Introduce `x hx`.

Rewrite using `[Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `Ideal.subset_span hx`. Use `⟨R ⧸ J, inferInstance, inferInstance, hco, Ideal.Quotient.mkₐ O J, Ideal.Quotient.mkₐ_surjective O J, ?_⟩` and prove the remaining obligations. Introduce `R'' _ _ _`. Use `⟨fun g => ?_, fun r' hr' => ?_⟩` and prove the remaining obligations.

Rewrite using `[lift_map_map']`. Use `⟨(hrep R'').1 _, (hI R'' _).2 ?_⟩` and prove the remaining obligations. Introduce `x hx`. Rewrite using `[AlgHom.comp_apply, hpI x hx, map_zero]`. Take `⟨f', hf', huniq⟩` from `(hrep R'').2 r' hr'.1`.

Establish `hf'I : ∀ x ∈ I, f' x = 0` using `(hI R'' f').1 (hf' ▸ hr'.2)`. Establish `hf'J : ∀ x ∈ J, f' x = 0`. Introduce `x hx`. Establish `hle : J ≤ RingHom.ker f'.toRingHom` using `Ideal.span_le.2 (fun y hy => hf'I y hy)`. Conclude with `hle hx`.

Use `⟨Ideal.Quotient.liftₐ J f' hf'J, ?_, ?_⟩` and prove the remaining obligations. Use `show Lift.map _ (Lift.map _ r) = r'`. Rewrite using `[lift_map_map', Ideal.Quotient.liftₐ_comp]`. Conclude with `hf'`. Introduce `g hg`.

Apply `Ideal.Quotient.algHom_ext O` to reduce the goal to its premises. Rewrite using `[Ideal.Quotient.liftₐ_comp]`. Apply `huniq` to reduce the goal to its premises. Use `show Lift.map _ r = r'`. Rewrite using `[← lift_map_map']`.

Conclude with `hg`.
-/
theorem UpperTheory.V.Alg.univ_cond :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] (Γ ι : Type) [Group Γ] [TopologicalSpace Γ] [Fintype ι] [DecidableEq ι] (rbar : Γ →* Matrix ι ι (ResidueField O)) (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (r : Lift O rbar R) (P₀ P : Cond O rbar), Represents P₀ r → P.IsClosed → (∃ (R₁ : Type) (_ : CommRing R₁) (_ : Algebra O R₁) (_ : IsCO O R₁) (r₁ : Lift O rbar R₁), P₀ R₁ r₁ ∧ P R₁ r₁) →
      ∃ (R' : Type) (_ : CommRing R') (_ : Algebra O R') (_ : IsCO O R') (p : R →ₐ[O] R'), Function.Surjective p ∧ Represents (fun C _ _ _ s => P₀ C s ∧ P C s) (r.map p) := by
  intro O _ _ Γ ι _ _ _ _ rbar R _ _ _ r P₀ P hrep hcl hex
  obtain ⟨I, hI⟩ := hcl R r
  obtain ⟨R₁, _, _, _, r₁, h0, h1⟩ := hex
  obtain ⟨f, hf, -⟩ := (hrep R₁).2 r₁ h0
  have hf1 : P R₁ (Lift.map f r) := hf ▸ h1
  have hfI : ∀ x ∈ I, f x = 0 := (hI R₁ f).1 hf1
  set J : Ideal R := Ideal.span I
  have hJf : ∀ x ∈ J, f x = 0 := by
    intro x hx
    have hle : J ≤ RingHom.ker f.toRingHom := Ideal.span_le.2 (fun y hy => hfI y hy)
    exact hle hx
  have hJ : J ≠ ⊤ := by
    intro htop
    have h1mem : (1 : R) ∈ J := htop ▸ Submodule.mem_top
    have := hJf 1 h1mem
    simp at this
  haveI : Nontrivial (R ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJ
  haveI hco : IsCO O (R ⧸ J) := co_quot O R (R ⧸ J) (Ideal.Quotient.mkₐ O J) (Ideal.Quotient.mkₐ_surjective O J)
  have hpI : ∀ x ∈ I, Ideal.Quotient.mkₐ O J x = 0 := by
    intro x hx
    rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span hx
  refine ⟨R ⧸ J, inferInstance, inferInstance, hco, Ideal.Quotient.mkₐ O J, Ideal.Quotient.mkₐ_surjective O J, ?_⟩
  intro R'' _ _ _
  refine ⟨fun g => ?_, fun r' hr' => ?_⟩
  · rw [lift_map_map']
    refine ⟨(hrep R'').1 _, (hI R'' _).2 ?_⟩
    intro x hx
    rw [AlgHom.comp_apply, hpI x hx, map_zero]
  · obtain ⟨f', hf', huniq⟩ := (hrep R'').2 r' hr'.1
    have hf'I : ∀ x ∈ I, f' x = 0 := (hI R'' f').1 (hf' ▸ hr'.2)
    have hf'J : ∀ x ∈ J, f' x = 0 := by
      intro x hx
      have hle : J ≤ RingHom.ker f'.toRingHom := Ideal.span_le.2 (fun y hy => hf'I y hy)
      exact hle hx
    refine ⟨Ideal.Quotient.liftₐ J f' hf'J, ?_, ?_⟩
    · show Lift.map _ (Lift.map _ r) = r'
      rw [lift_map_map', Ideal.Quotient.liftₐ_comp]
      exact hf'
    · intro g hg
      apply Ideal.Quotient.algHom_ext O
      rw [Ideal.Quotient.liftₐ_comp]
      apply huniq
      show Lift.map _ r = r'
      rw [← lift_map_map']
      exact hg
