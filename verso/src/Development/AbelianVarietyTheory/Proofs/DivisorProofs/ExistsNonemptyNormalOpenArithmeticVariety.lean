import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimEqSucc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteIntegralClosureOfEssFiniteTypeIntDomain
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpanFinrankMaximalIdealLeNcardOfLeSupSq

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB

namespace GlobalTheory.NormalOpen

/- English proof (translation)
Take `⟨s, hs⟩` from `Module.Finite.fg_top (R := A) (M := integralClosure A K)`. Take `⟨b, hb⟩` from `IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors A) (s.image fun z : integralClosure A K => (z : K))`. Use `⟨b, nonZeroDivisors.ne_zero b.2, fun y hy => ?_⟩` and prove the remaining obligations. Establish `key : ∀ z ∈ Submodule.span A (s : Set (integralClosure A K)), ∃ a : A, algebraMap A K a = (b : A) • (z : K)`. Introduce `z hz`.

Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem x hx => exact hb _ (Finset.mem_image_of_mem _ hx)`. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨a, ha⟩` from `hx`.

Take `⟨c, hc⟩` from `hy`. Conclude with `⟨a + c, by rw [map_add, ha, hc, Subalgebra.coe_add, smul_add]⟩`. Consider the case `smul r x _ hx`. Take `⟨a, ha⟩` from `hx`. Use `⟨r * a, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_mul, ha, Subalgebra.coe_smul, smul_comm, ← Algebra.smul_def]`. Conclude with `key ⟨y, hy⟩ (hs ▸ Submodule.mem_top)`.
-/
theorem exists_mul_isInteger (A K : Type*) [CommRing A] [IsDomain A] [Field K] [Algebra A K]
    [IsFractionRing A K] [Module.Finite A (integralClosure A K)] :
    ∃ f : A, f ≠ 0 ∧ ∀ y : K, IsIntegral A y → ∃ a : A, algebraMap A K a = f • y := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := A) (M := integralClosure A K)
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors A)
    (s.image fun z : integralClosure A K => (z : K))
  refine ⟨b, nonZeroDivisors.ne_zero b.2, fun y hy => ?_⟩
  have key : ∀ z ∈ Submodule.span A (s : Set (integralClosure A K)),
      ∃ a : A, algebraMap A K a = (b : A) • (z : K) := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem x hx => exact hb _ (Finset.mem_image_of_mem _ hx)
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨c, hc⟩ := hy
      exact ⟨a + c, by rw [map_add, ha, hc, Subalgebra.coe_add, smul_add]⟩
    | smul r x _ hx =>
      obtain ⟨a, ha⟩ := hx
      refine ⟨r * a, ?_⟩
      rw [map_mul, ha, Subalgebra.coe_smul, smul_comm, ← Algebra.smul_def]
  exact key ⟨y, hy⟩ (hs ▸ Submodule.mem_top)

/- English proof (translation)
Set `K` to `FractionRing A`. Take `⟨f, hf, h⟩` from `exists_mul_isInteger A K`. Use `⟨f, hf, ?_⟩` and prove the remaining obligations. Set `B` to `Localization.Away f`. Establish `hle` using `powers_le_nonZeroDivisors_of_noZeroDivisors hf`.

Establish `hg : ∀ y : Submonoid.powers f, IsUnit (algebraMap A K y)` using `fun y => IsLocalization.map_units K (⟨y, hle y.2⟩ : nonZeroDivisors A)`. Establish `: IsDomain B` using `IsLocalization.isDomain_of_le_nonZeroDivisors (M := Submonoid.powers f) _ hle`. Use `letI : Algebra B K := (IsLocalization.lift (S := B) hg).toAlgebra`. Establish `: IsScalarTower A B K` using `.of_algebraMap_eq fun a => (IsLocalization.lift_eq hg a).symm`. Establish `: IsFractionRing B K` using `IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers f) B K`.

Rewrite using `[isIntegrallyClosed_iff K]`. Introduce `x hx`. Take `⟨m, hm⟩` from `IsIntegral.exists_multiple_integral_of_isLocalization (Submonoid.powers f) (Rₘ := B) x hx`. Take `⟨a, ha⟩` from `h _ hm`. Set `t : Submonoid.powers f` to `⟨f, Submonoid.mem_powers f⟩ * m`.

Use `⟨IsLocalization.mk' B a t, ?_⟩` and prove the remaining obligations. Establish `e` using `congrArg (algebraMap B K) (IsLocalization.mk'_spec B a t)`. Rewrite `e` using `[map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, ha]`. Use `(hg t).mul_right_cancel ?_` and prove the remaining obligations. Rewrite using `[e, mul_comm, ← Algebra.smul_def, Submonoid.smul_def, smul_smul]`.

Both sides reduce to the same expression.
-/
theorem exists_isIntegrallyClosed_away (A : Type*) [CommRing A] [IsDomain A]
    [Module.Finite A (integralClosure A (FractionRing A))] :
    ∃ f : A, f ≠ 0 ∧ IsIntegrallyClosed (Localization.Away f) := by
  let K := FractionRing A
  obtain ⟨f, hf, h⟩ := exists_mul_isInteger A K
  refine ⟨f, hf, ?_⟩
  let B := Localization.Away f
  have hle := powers_le_nonZeroDivisors_of_noZeroDivisors hf
  have hg : ∀ y : Submonoid.powers f, IsUnit (algebraMap A K y) := fun y =>
    IsLocalization.map_units K (⟨y, hle y.2⟩ : nonZeroDivisors A)
  have : IsDomain B := IsLocalization.isDomain_of_le_nonZeroDivisors (M := Submonoid.powers f) _ hle
  letI : Algebra B K := (IsLocalization.lift (S := B) hg).toAlgebra
  have : IsScalarTower A B K := .of_algebraMap_eq fun a => (IsLocalization.lift_eq hg a).symm
  have : IsFractionRing B K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers f) B K
  rw [isIntegrallyClosed_iff K]
  intro x hx
  obtain ⟨m, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization (Submonoid.powers f)
    (Rₘ := B) x hx
  obtain ⟨a, ha⟩ := h _ hm
  let t : Submonoid.powers f := ⟨f, Submonoid.mem_powers f⟩ * m
  refine ⟨IsLocalization.mk' B a t, ?_⟩
  have e := congrArg (algebraMap B K) (IsLocalization.mk'_spec B a t)
  rw [map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, ha] at e
  refine (hg t).mul_right_cancel ?_
  rw [e, mul_comm, ← Algebra.smul_def, Submonoid.smul_def, smul_smul]
  rfl

/- English proof (translation)
Introduce `k _ X p D h`. Use `h.isIntegral` as an intermediate fact. Use `h.finite` as an intermediate fact. Take `⟨A, _, _, i, _, a, -, hi⟩` from `exists_affine_chart_over p (genericPoint X)`. Establish `: Nontrivial A` using `PrimeSpectrum.nonempty_iff_nontrivial.1 ⟨a⟩`.

Take `⟨_, hft, -⟩` from `RegGenSmooth.chart_props h i hi`. Establish `: Algebra.FiniteType ℤ A` using `Algebra.FiniteType.trans (S := k) inferInstance hft`. Use `finite_integralClosure_of_essFiniteType_int A` as an intermediate fact. Take `⟨f, hf, hc⟩` from `exists_isIntegrallyClosed_away A`. Set `B` to `Localization.Away f`.

Establish `: IsDomain B` using `IsLocalization.isDomain_of_le_nonZeroDivisors (M := Submonoid.powers f) _ (powers_le_nonZeroDivisors_of_noZeroDivisors hf)`. Establish `: IsOpenImmersion (spMap (algebraMap A B))` using `IsOpenImmersion.of_isLocalization f`. Set `j : Sp B ⟶ X` to `spMap (algebraMap A B) ≫ i`. Establish `hB : GlobalTheory.IsNormalScheme (Sp B)` using `GlobalTheory.IsNormalScheme.spec (.of B)`. Establish `: GlobalTheory.IsNormalScheme j.opensRange.toScheme` using `.of_isIso j.isoOpensRange.hom`.

Use `⟨j.opensRange, ?_, GlobalTheory.IsNormalScheme.pred _⟩` and prove the remaining obligations. Conclude with `⟨j (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum B), _, rfl⟩`.
-/
theorem exists_normal_opens : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∃ Ω : X.Opens, (Ω : Set X).Nonempty ∧
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Ω.toScheme := by
  intro k _ X p D h
  have := h.isIntegral
  have := h.finite
  obtain ⟨A, _, _, i, _, a, -, hi⟩ := exists_affine_chart_over p (genericPoint X)
  have : Nontrivial A := PrimeSpectrum.nonempty_iff_nontrivial.1 ⟨a⟩
  obtain ⟨_, hft, -⟩ := RegGenSmooth.chart_props h i hi
  have : Algebra.FiniteType ℤ A := Algebra.FiniteType.trans (S := k) inferInstance hft
  have := finite_integralClosure_of_essFiniteType_int A
  obtain ⟨f, hf, hc⟩ := exists_isIntegrallyClosed_away A
  let B := Localization.Away f
  have : IsDomain B := IsLocalization.isDomain_of_le_nonZeroDivisors (M := Submonoid.powers f) _
    (powers_le_nonZeroDivisors_of_noZeroDivisors hf)
  have : IsOpenImmersion (spMap (algebraMap A B)) := IsOpenImmersion.of_isLocalization f
  let j : Sp B ⟶ X := spMap (algebraMap A B) ≫ i
  have hB : GlobalTheory.IsNormalScheme (Sp B) := GlobalTheory.IsNormalScheme.spec (.of B)
  have : GlobalTheory.IsNormalScheme j.opensRange.toScheme := .of_isIso j.isoOpensRange.hom
  refine ⟨j.opensRange, ?_, GlobalTheory.IsNormalScheme.pred _⟩
  exact ⟨j (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum B), _, rfl⟩

end GlobalTheory.NormalOpen
