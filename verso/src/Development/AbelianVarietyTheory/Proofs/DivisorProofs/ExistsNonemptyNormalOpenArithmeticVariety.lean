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
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Proceed by induction. Treat this case separately. Treat this case separately. Treat this case separately. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Supply the required witnesses or components. Treat this case separately. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
Introduce a local definition for the expression. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Introduce a local definition for the expression. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Equip the data with the indicated structure. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Introduce a local definition for the expression.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

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
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result. Introduce a local definition for the expression.

Establish an intermediate fact. Establish an intermediate fact. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Supply the required witnesses or components.
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
