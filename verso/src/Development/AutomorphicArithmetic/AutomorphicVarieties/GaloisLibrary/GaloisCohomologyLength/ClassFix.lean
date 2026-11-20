import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.LevelInertiaLeLevelDec
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.GalAut

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology UpperTheory.V.LDataCardLeFinrank

/- English proof (translation)
Introduce `F Ω _ _ _ _ _ N _ K _ _ _ φ g h hg`. Use `haveI : CharZero Ω := (RingHom.charZero_iff (algebraMap F Ω).injective).mp inferInstance`. Use `letI : Algebra F K := φ.toRingHom.toAlgebra`. Use `haveI : IsScalarTower ℚ F K := inferInstance`. Use `haveI : Algebra.IsAlgebraic F K := Algebra.IsAlgebraic.tower_top (K := ℚ) F`.

Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F`. Set `ι : K →ₐ[F] Ω` to `IsAlgClosed.lift`. Establish `hι : ∀ x : F, ι (φ x) = algebraMap F Ω x` using `fun x => ι.commutes x`. Use `set σ : Gal(K/ℚ) := (IsCyclotomicExtension.Rat.galEquivZMod N K).symm h with hσ`. Establish `hσζ : ∀ y : K, y ^ N = 1 → σ y = y ^ (h : ZMod N).val`.

Introduce `y hy`. Use `IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq N K σ hy` as an intermediate fact. Rewrite using `[this, hσ, MulEquiv.apply_symm_apply]`. Establish `hcomm : ∀ y : K, g (ι y) = ι (σ y)`. Establish `key : (g.toRingHom.toRatAlgHom).comp (ι.toRingHom.toRatAlgHom) = (ι.toRingHom.toRatAlgHom).comp σ.toAlgHom`.

Use `AlgHom.ext_of_adjoin_eq_top (s := {b : K | ∃ n ∈ ({N} : Set ℕ), n ≠ 0 ∧ b ^ n = 1}) (Algebra.eq_top_iff.mpr IsCyclotomicExtension.adjoin_roots) ?_` and prove the remaining obligations. Introduce and unpack `b ⟨n, hn, -, hb⟩`. Rewrite `hn` using `[Set.mem_singleton_iff]`. Substitute `hn` using the available equality. Simplify using `only [AlgHom.coe_comp, Function.comp_apply, RingHom.toRatAlgHom_apply, AlgEquiv.coe_algHom]`.

Rewrite using `[hσζ b hb, map_pow]`. Apply `hg` to reduce the goal to its premises. Rewrite using `[← map_pow, hb, map_one]`. Introduce `y`. Conclude with `congrArg (fun f => f y) key`.

Unfold `KStar.TotallyRealRoots.fieldSubgroup`. Rewrite using `[Subgroup.mem_map_equiv, ← hσ, IntermediateField.mem_fixingSubgroup_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `H y hy`. Take `⟨x, rfl⟩` from `AlgHom.mem_fieldRange.mp hy`.

Apply `ι.toRingHom.injective` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `ι (σ (φ x)) = ι (φ x)`. Rewrite using `[← hcomm, hι, H]`. Introduce `H x`. Rewrite using `[← hι, hcomm, H _ (AlgHom.mem_fieldRange.mpr ⟨x, rfl⟩)]`.
-/
theorem UpperTheory.V.LDataCardLeFinrank.classFix :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (N : ℕ) [NeZero N] (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {N} ℚ K] (φ : F →ₐ[ℚ] K) (g : Ω ≃+* Ω) (h : (ZMod N)ˣ), (∀ ζ : Ω, ζ ^ N = 1 → g ζ = ζ ^ (h : ZMod N).val) → ((∀ x : F, g (algebraMap F Ω x) = algebraMap F Ω x) ↔ h ∈ KStar.TotallyRealRoots.fieldSubgroup N K φ.fieldRange) := by
  intro F Ω _ _ _ _ _ N _ K _ _ _ φ g h hg
  haveI : CharZero Ω := (RingHom.charZero_iff (algebraMap F Ω).injective).mp inferInstance
  letI : Algebra F K := φ.toRingHom.toAlgebra
  haveI : IsScalarTower ℚ F K := inferInstance
  haveI : Algebra.IsAlgebraic F K := Algebra.IsAlgebraic.tower_top (K := ℚ) F
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  let ι : K →ₐ[F] Ω := IsAlgClosed.lift
  have hι : ∀ x : F, ι (φ x) = algebraMap F Ω x := fun x => ι.commutes x
  set σ : Gal(K/ℚ) := (IsCyclotomicExtension.Rat.galEquivZMod N K).symm h with hσ
  have hσζ : ∀ y : K, y ^ N = 1 → σ y = y ^ (h : ZMod N).val := by
    intro y hy
    have := IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq N K σ hy
    rw [this, hσ, MulEquiv.apply_symm_apply]
  have hcomm : ∀ y : K, g (ι y) = ι (σ y) := by
    have key : (g.toRingHom.toRatAlgHom).comp (ι.toRingHom.toRatAlgHom) =
        (ι.toRingHom.toRatAlgHom).comp σ.toAlgHom := by
      refine AlgHom.ext_of_adjoin_eq_top (s := {b : K | ∃ n ∈ ({N} : Set ℕ), n ≠ 0 ∧ b ^ n = 1})
        (Algebra.eq_top_iff.mpr IsCyclotomicExtension.adjoin_roots) ?_
      rintro b ⟨n, hn, -, hb⟩
      rw [Set.mem_singleton_iff] at hn
      subst hn
      simp only [AlgHom.coe_comp, Function.comp_apply, RingHom.toRatAlgHom_apply,
        AlgEquiv.coe_algHom]
      rw [hσζ b hb, map_pow]
      apply hg
      rw [← map_pow, hb, map_one]
    intro y
    exact congrArg (fun f => f y) key
  unfold KStar.TotallyRealRoots.fieldSubgroup
  rw [Subgroup.mem_map_equiv, ← hσ, IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro H y hy
    obtain ⟨x, rfl⟩ := AlgHom.mem_fieldRange.mp hy
    apply ι.toRingHom.injective
    change ι (σ (φ x)) = ι (φ x)
    rw [← hcomm, hι, H]
  · intro H x
    rw [← hι, hcomm, H _ (AlgHom.mem_fieldRange.mpr ⟨x, rfl⟩)]
