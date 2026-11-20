import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ResidueFlagPoints.ResLeCont
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDecompositionGroupCyclotomicCharacterZpowN
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharInertiaSurjective

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.CuspRep GlobalTheory.GalOfCusp

/- English proof (translation)
Introduce `F Ω _ _ _ _ _ l _ A hA n hn`. Use `haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective`. Use `haveI : IsAlgClosure ℚ Ω := IsAlgClosure.ofAlgebraic ℚ F Ω`. Take `⟨u, hu⟩` from `GlobalTheory.CycDec.exists_unit_infinite_order l`. Take `⟨σ, hσI, hσu⟩` from `GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hA u`.

Set `ι : F →ₐ[ℚ] Ω` to `IsScalarTower.toAlgHom ℚ F Ω`. Set `f : ℕ → (F →ₐ[ℚ] Ω)` to `fun k => ((σ ^ k : Ω ≃ₐ[ℚ] Ω) : Ω →ₐ[ℚ] Ω).comp ι`. Use `haveI : Finite (F →ₐ[ℚ] Ω) := inferInstance`. Take `⟨a, b, hab, he⟩` from `Finite.exists_ne_map_eq_of_infinite f`. Establish `key : ∀ a b : ℕ, a < b → f a = f b → ∃ N : ℕ, 0 < N ∧ ∀ x : F, (σ ^ N) (algebraMap F Ω x) = algebraMap F Ω x`.

Introduce `a b hlt hfe`. Use `⟨b - a, Nat.sub_pos_of_lt hlt, fun x => ?_⟩` and prove the remaining obligations. Establish `h1 : (σ ^ a) (algebraMap F Ω x) = (σ ^ b) (algebraMap F Ω x)` using `congrArg (fun φ : F →ₐ[ℚ] Ω => φ x) hfe`. Establish `h2 : σ ^ b = σ ^ a * σ ^ (b - a)`. Rewrite using `[← pow_add, Nat.add_sub_cancel' hlt.le]`.

Rewrite `h1` using `[h2, AlgEquiv.mul_apply]`. Conclude with `((σ ^ a).injective h1).symm`. Choose the witnesses or unpack the hypotheses as in `⟨N, hN, hfix⟩ : ∃ N : ℕ, 0 < N ∧ ∀ x : F, (σ ^ N) (algebraMap F Ω x) = algebraMap F Ω x := by`. Break down `lt_or_gt_of_ne hab with h | h` into its components or cases. Conclude with `key a b h he`.

Conclude with `key b a h he.symm`. Set `g : G F Ω` to `AlgEquiv.ofRingEquiv (f := (σ ^ N).toRingEquiv) hfix`. Establish `hg : (g.restrictScalars ℚ : G ℚ Ω) = σ ^ N` using `AlgEquiv.ext fun y => rfl`. Establish `hφinj : Function.Injective (algebraMap ℤ_[l] (Qbar l)).toMonoidHom` using `by show Function.Injective (algebraMap ℤ_[l] (Qbar l))`. Rewrite using `[IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] (Qbar l), RingHom.coe_comp]`.

Conclude with `(algebraMap ℚ_[l] (Qbar l)).injective.comp (fun a b h => Subtype.ext h)`. Establish `hinj : Function.Injective (Units.map (algebraMap ℤ_[l] (Qbar l)).toMonoidHom)` using `Units.map_injective hφinj`. Use `⟨g, ?_, ?_⟩` and prove the remaining obligations. Use `show (g.restrictScalars ℚ : G ℚ Ω) ∈ Ine (F := ℚ) A`. Rewrite using `[hg]`.

Conclude with `Subgroup.pow_mem _ hσI N`. Establish `hc : cycBar F Ω l g = Units.map (algebraMap ℤ_[l] (Qbar l)).toMonoidHom (cycZ ℚ Ω l (g.restrictScalars ℚ))` using `rfl`. Rewrite using `[hc, hg, map_pow, hσu]`. Introduce `h`. Apply `hu ((N : ℤ) * n) (mul_ne_zero (by exact_mod_cast hN.ne') hn)` to reduce the goal to its premises.

Rewrite using `[zpow_mul, zpow_natCast]`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[map_zpow, map_one]`. Conclude with `h`.
-/
theorem UpperTheory.V.Ws.Pt.cycIne :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω), A.valuation (l : Ω) < 1 → ∀ n : ℤ, n ≠ 0 → ∃ g ∈ Ine (F := F) A, cycBar F Ω l g ^ n ≠ 1 := by
  intro F Ω _ _ _ _ _ l _ A hA n hn
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  haveI : IsAlgClosure ℚ Ω := IsAlgClosure.ofAlgebraic ℚ F Ω
  obtain ⟨u, hu⟩ := GlobalTheory.CycDec.exists_unit_infinite_order l
  obtain ⟨σ, hσI, hσu⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hA u
  let ι : F →ₐ[ℚ] Ω := IsScalarTower.toAlgHom ℚ F Ω
  let f : ℕ → (F →ₐ[ℚ] Ω) := fun k => ((σ ^ k : Ω ≃ₐ[ℚ] Ω) : Ω →ₐ[ℚ] Ω).comp ι
  haveI : Finite (F →ₐ[ℚ] Ω) := inferInstance
  obtain ⟨a, b, hab, he⟩ := Finite.exists_ne_map_eq_of_infinite f
  have key : ∀ a b : ℕ, a < b → f a = f b →
      ∃ N : ℕ, 0 < N ∧ ∀ x : F, (σ ^ N) (algebraMap F Ω x) = algebraMap F Ω x := by
    intro a b hlt hfe
    refine ⟨b - a, Nat.sub_pos_of_lt hlt, fun x => ?_⟩
    have h1 : (σ ^ a) (algebraMap F Ω x) = (σ ^ b) (algebraMap F Ω x) :=
      congrArg (fun φ : F →ₐ[ℚ] Ω => φ x) hfe
    have h2 : σ ^ b = σ ^ a * σ ^ (b - a) := by
      rw [← pow_add, Nat.add_sub_cancel' hlt.le]
    rw [h2, AlgEquiv.mul_apply] at h1
    exact ((σ ^ a).injective h1).symm
  obtain ⟨N, hN, hfix⟩ : ∃ N : ℕ, 0 < N ∧ ∀ x : F, (σ ^ N) (algebraMap F Ω x) = algebraMap F Ω x := by
    rcases lt_or_gt_of_ne hab with h | h
    · exact key a b h he
    · exact key b a h he.symm
  let g : G F Ω := AlgEquiv.ofRingEquiv (f := (σ ^ N).toRingEquiv) hfix
  have hg : (g.restrictScalars ℚ : G ℚ Ω) = σ ^ N := AlgEquiv.ext fun y => rfl
  have hφinj : Function.Injective (algebraMap ℤ_[l] (Qbar l)).toMonoidHom := by
    show Function.Injective (algebraMap ℤ_[l] (Qbar l))
    rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] (Qbar l), RingHom.coe_comp]
    exact (algebraMap ℚ_[l] (Qbar l)).injective.comp (fun a b h => Subtype.ext h)
  have hinj : Function.Injective (Units.map (algebraMap ℤ_[l] (Qbar l)).toMonoidHom) :=
    Units.map_injective hφinj
  refine ⟨g, ?_, ?_⟩
  · show (g.restrictScalars ℚ : G ℚ Ω) ∈ Ine (F := ℚ) A
    rw [hg]
    exact Subgroup.pow_mem _ hσI N
  · have hc : cycBar F Ω l g =
        Units.map (algebraMap ℤ_[l] (Qbar l)).toMonoidHom (cycZ ℚ Ω l (g.restrictScalars ℚ)) := rfl
    rw [hc, hg, map_pow, hσu]
    intro h
    apply hu ((N : ℤ) * n) (mul_ne_zero (by exact_mod_cast hN.ne') hn)
    rw [zpow_mul, zpow_natCast]
    apply hinj
    rw [map_zpow, map_one]
    exact h
