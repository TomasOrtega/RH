import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

/- English proof (translation)
Introduce `k _ V hV χ₁ h₁`. Establish `key : ∀ (χ : Localization.Away (Polynomial.X : Polynomial k) →ₐ[k] k) (g : Localization.Away (Polynomial.X : Polynomial k)), g ∉ PrimeSpectrum.asIdeal (spMap χ.toRingHom (IsLocalRing.closedPoint k)) ↔ χ g ≠ 0`. Introduce `χ g`. Rewrite using `[Spec.map_base]`. Express the relevant statement in the definitionally equal form `g ∉ (PrimeSpectrum.comap χ.toRingHom (IsLocalRing.closedPoint k)).asIdeal ↔ _`.

Rewrite using `[PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]`. Establish `hb : (IsLocalRing.closedPoint k).asIdeal = ⊥` using `IsLocalRing.maximalIdeal_eq_bot`. Rewrite using `[hb, Ideal.mem_bot]`. Both sides reduce to the same expression. Establish `hV' : IsOpen (V : Set (PrimeSpectrum (Localization.Away (Polynomial.X : Polynomial k))))` using `hV`.

Take `⟨_, ⟨g, rfl⟩, hg, hgV⟩` from `(PrimeSpectrum.isTopologicalBasis_basic_opens).exists_subset_of_mem_open h₁ hV'`. Establish `hg₁ : χ₁ g ≠ 0` using `(key χ₁ g).1 hg`. Take `⟨n, p, hp⟩` from `IsLocalization.Away.surj (Polynomial.X : Polynomial k) g`. Establish `hXu : ∀ χ : Localization.Away (Polynomial.X : Polynomial k) →ₐ[k] k, χ (algebraMap (Polynomial k) _ Polynomial.X) ≠ 0` using `fun χ => ((IsLocalization.Away.algebraMap_isUnit (Polynomial.X : Polynomial k)).map χ).ne_zero`. Establish `hev : ∀ χ : Localization.Away (Polynomial.X : Polynomial k) →ₐ[k] k, ∀ q : Polynomial k, χ (algebraMap (Polynomial k) _ q) = q.eval (χ (algebraMap (Polynomial k) _ Polynomial.X))`.

Introduce `χ q`. Establish `: χ.comp (IsScalarTower.toAlgHom k (Polynomial k) (Localization.Away (Polynomial.X : Polynomial k))) = Polynomial.aeval (χ (algebraMap (Polynomial k) _ Polynomial.X))`. Apply `Polynomial.algHom_ext` to reduce the goal to its premises. Simplify using the standard rewrite rules. Establish `h2` using `congrArg (fun φ => φ q) this`.

Simplify `h2` using `[Polynomial.coe_aeval_eq_eval]`. Establish `hχp : ∀ χ : Localization.Away (Polynomial.X : Polynomial k) →ₐ[k] k, χ (algebraMap (Polynomial k) _ p) = χ g * (χ (algebraMap (Polynomial k) _ Polynomial.X)) ^ n`. Introduce `χ`. Rewrite using `[← hp, map_mul, map_pow]`. Establish `hp0 : p ≠ 0`.

Introduce and unpack `rfl`. Use `hχp χ₁` as an intermediate fact. Rewrite `this` using `[map_zero, map_zero]`. Conclude with `mul_ne_zero hg₁ (pow_ne_zero _ (hXu χ₁)) this.symm`. Use `(Polynomial.finite_setOf_isRoot hp0).subset ?_` and prove the remaining obligations.

Introduce and unpack `c ⟨hc0, hcall⟩`. Assume the negation of the conclusion as `hroot`. Establish `hunit : ∀ y : Submonoid.powers (Polynomial.X : Polynomial k), IsUnit (Polynomial.aeval c (y : Polynomial k))`. Introduce and unpack `⟨_, m, rfl⟩`. Simplify using `[hc0]`.

Set `χc : Localization.Away (Polynomial.X : Polynomial k) →ₐ[k] k` to `IsLocalization.liftAlgHom (M := Submonoid.powers (Polynomial.X : Polynomial k)) hunit`. Establish `hχc : χc (algebraMap (Polynomial k) _ Polynomial.X) = c`. Simplify using `[χc, IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]`. Apply `hcall χc hχc` to reduce the goal to its premises. Apply `hgV` to reduce the goal to its premises.

Use `(key χc g).2 ?_` and prove the remaining obligations. Introduce `h0`. Apply `hroot` to reduce the goal to its premises. Use `hχp χc` as an intermediate fact. Rewrite `this` using `[h0, zero_mul, hev, hχc]`.

Conclude with `this`.
-/
theorem punctured_line_open_cofinite : ∀ (k : Type) [Field k] (V : Set (Sp (Localization.Away (Polynomial.X : Polynomial k)))), IsOpen V → ∀ (χ₁ : Localization.Away (Polynomial.X : Polynomial k) →ₐ[k] k), spMap χ₁.toRingHom (IsLocalRing.closedPoint k) ∈ V → Set.Finite {c : k | c ≠ 0 ∧ ∀ χ : Localization.Away (Polynomial.X : Polynomial k) →ₐ[k] k, χ (algebraMap (Polynomial k) _ Polynomial.X) = c → spMap χ.toRingHom (IsLocalRing.closedPoint k) ∉ V} := by
  intro k _ V hV χ₁ h₁
  classical

  have key : ∀ (χ : Localization.Away (Polynomial.X : Polynomial k) →ₐ[k] k)
      (g : Localization.Away (Polynomial.X : Polynomial k)),
      g ∉ PrimeSpectrum.asIdeal (spMap χ.toRingHom (IsLocalRing.closedPoint k)) ↔ χ g ≠ 0 := by
    intro χ g
    rw [Spec.map_base]
    change g ∉ (PrimeSpectrum.comap χ.toRingHom (IsLocalRing.closedPoint k)).asIdeal ↔ _
    rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
    have hb : (IsLocalRing.closedPoint k).asIdeal = ⊥ := IsLocalRing.maximalIdeal_eq_bot
    rw [hb, Ideal.mem_bot]
    rfl
  have hV' : IsOpen (V : Set (PrimeSpectrum (Localization.Away (Polynomial.X : Polynomial k)))) := hV
  obtain ⟨_, ⟨g, rfl⟩, hg, hgV⟩ :=
    (PrimeSpectrum.isTopologicalBasis_basic_opens).exists_subset_of_mem_open h₁ hV'
  have hg₁ : χ₁ g ≠ 0 := (key χ₁ g).1 hg
  obtain ⟨n, p, hp⟩ := IsLocalization.Away.surj (Polynomial.X : Polynomial k) g
  have hXu : ∀ χ : Localization.Away (Polynomial.X : Polynomial k) →ₐ[k] k,
      χ (algebraMap (Polynomial k) _ Polynomial.X) ≠ 0 := fun χ =>
    ((IsLocalization.Away.algebraMap_isUnit (Polynomial.X : Polynomial k)).map χ).ne_zero
  have hev : ∀ χ : Localization.Away (Polynomial.X : Polynomial k) →ₐ[k] k, ∀ q : Polynomial k,
      χ (algebraMap (Polynomial k) _ q) = q.eval (χ (algebraMap (Polynomial k) _ Polynomial.X)) := by
    intro χ q
    have : χ.comp (IsScalarTower.toAlgHom k (Polynomial k) (Localization.Away (Polynomial.X : Polynomial k)))
        = Polynomial.aeval (χ (algebraMap (Polynomial k) _ Polynomial.X)) := by
      apply Polynomial.algHom_ext
      simp
    have h2 := congrArg (fun φ => φ q) this
    simpa [Polynomial.coe_aeval_eq_eval] using h2
  have hχp : ∀ χ : Localization.Away (Polynomial.X : Polynomial k) →ₐ[k] k,
      χ (algebraMap (Polynomial k) _ p) = χ g * (χ (algebraMap (Polynomial k) _ Polynomial.X)) ^ n := by
    intro χ
    rw [← hp, map_mul, map_pow]
  have hp0 : p ≠ 0 := by
    rintro rfl
    have := hχp χ₁
    rw [map_zero, map_zero] at this
    exact mul_ne_zero hg₁ (pow_ne_zero _ (hXu χ₁)) this.symm
  refine (Polynomial.finite_setOf_isRoot hp0).subset ?_
  rintro c ⟨hc0, hcall⟩
  by_contra hroot
  have hunit : ∀ y : Submonoid.powers (Polynomial.X : Polynomial k),
      IsUnit (Polynomial.aeval c (y : Polynomial k)) := by
    rintro ⟨_, m, rfl⟩
    simp [hc0]
  let χc : Localization.Away (Polynomial.X : Polynomial k) →ₐ[k] k :=
    IsLocalization.liftAlgHom (M := Submonoid.powers (Polynomial.X : Polynomial k)) hunit
  have hχc : χc (algebraMap (Polynomial k) _ Polynomial.X) = c := by
    simp [χc, IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]
  apply hcall χc hχc
  apply hgV
  refine (key χc g).2 ?_
  intro h0
  apply hroot
  have := hχp χc
  rw [h0, zero_mul, hev, hχc] at this
  exact this

end GlobalTheory
