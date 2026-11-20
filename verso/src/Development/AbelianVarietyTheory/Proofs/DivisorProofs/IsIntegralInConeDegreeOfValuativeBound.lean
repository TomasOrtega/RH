import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralOfForallRealValuationLeOneStatement
open NumberField GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.DegCmp GlobalTheory.DegVal GlobalTheory.CovTop ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped ENNReal NNReal

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DegVal.ValInt

/- English proof (translation)
Take `⟨S, hS⟩` from `h`. Use `⟨insert RatFunc.X (S.image (algebraMap Ω (RatFunc Ω))), ?_⟩` and prove the remaining obligations. Use `set F := IntermediateField.adjoin K (↑(insert RatFunc.X (S.image (algebraMap Ω (RatFunc Ω)))) : Set (RatFunc Ω)) with hF`. Establish `hX : (RatFunc.X : RatFunc Ω) ∈ F` using `IntermediateField.subset_adjoin _ _ (by simp)`. Establish `hc : ∀ a : Ω, algebraMap Ω (RatFunc Ω) a ∈ F`.

Introduce `a`. Establish `ha : a ∈ IntermediateField.adjoin K (S : Set Ω)` using `hS ▸ IntermediateField.mem_top`. Establish `hm : algebraMap Ω (RatFunc Ω) a ∈ (IntermediateField.adjoin K (S : Set Ω)).map (IsScalarTower.toAlgHom K Ω (RatFunc Ω))` using `⟨a, ha, rfl⟩`. Rewrite `hm` using `[IntermediateField.adjoin_map]`. Use `IntermediateField.adjoin.mono K _ _ ?_ hm` and prove the remaining obligations.

Introduce and unpack `_ ⟨y, hy, rfl⟩`. Conclude with `Finset.mem_coe.2 (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hy))`. Establish `hp : ∀ p : Polynomial Ω, algebraMap (Polynomial Ω) (RatFunc Ω) p ∈ F`. Introduce `p`. Proceed by induction on `p using Polynomial.induction_on with`.

Consider the case `C a => rw [RatFunc.algebraMap_C, ← RatFunc.algebraMap_eq_C]`. Conclude with `hc a`. Consider the case `add p q hp hq => rw [map_add]`. Conclude with `add_mem hp hq`. Consider the case `monomial n a ih => rw [pow_succ, ← mul_assoc, map_mul, RatFunc.algebraMap_X]`.

Conclude with `mul_mem ih hX`. Use `eq_top_iff.2 fun x _ => ?_` and prove the remaining obligations. Rewrite using `[← RatFunc.num_div_denom x]`. Conclude with `div_mem (hp _) (hp _)`.
-/
theorem ratFunc_top_fg {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] (h : (⊤ : IntermediateField K Ω).FG) :
    (⊤ : IntermediateField K (RatFunc Ω)).FG := by
  classical
  obtain ⟨S, hS⟩ := h
  refine ⟨insert RatFunc.X (S.image (algebraMap Ω (RatFunc Ω))), ?_⟩
  set F := IntermediateField.adjoin K
    (↑(insert RatFunc.X (S.image (algebraMap Ω (RatFunc Ω)))) : Set (RatFunc Ω)) with hF
  have hX : (RatFunc.X : RatFunc Ω) ∈ F := IntermediateField.subset_adjoin _ _ (by simp)
  have hc : ∀ a : Ω, algebraMap Ω (RatFunc Ω) a ∈ F := by
    intro a
    have ha : a ∈ IntermediateField.adjoin K (S : Set Ω) := hS ▸ IntermediateField.mem_top
    have hm : algebraMap Ω (RatFunc Ω) a ∈
        (IntermediateField.adjoin K (S : Set Ω)).map (IsScalarTower.toAlgHom K Ω (RatFunc Ω)) := ⟨a, ha, rfl⟩
    rw [IntermediateField.adjoin_map] at hm
    refine IntermediateField.adjoin.mono K _ _ ?_ hm
    rintro _ ⟨y, hy, rfl⟩
    exact Finset.mem_coe.2 (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hy))
  have hp : ∀ p : Polynomial Ω, algebraMap (Polynomial Ω) (RatFunc Ω) p ∈ F := by
    intro p
    induction p using Polynomial.induction_on with
    | C a => rw [RatFunc.algebraMap_C, ← RatFunc.algebraMap_eq_C]; exact hc a
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | monomial n a ih => rw [pow_succ, ← mul_assoc, map_mul, RatFunc.algebraMap_X]; exact mul_mem ih hX
  refine eq_top_iff.2 fun x _ => ?_
  rw [← RatFunc.num_div_denom x]
  exact div_mem (hp _) (hp _)

/- English proof (translation)
Set `e` to `B.equivMapOfInjective φ hφ`. Take `⟨p, hm, hp⟩` from `h`. Use `⟨p.map e.symm.toRingHom, hm.map _, hφ ?_⟩` and prove the remaining obligations. Rewrite using `[map_zero, ← hp]`. Express the relevant statement in the definitionally equal form `φ.toRingHom _ = _`.

Rewrite using `[Polynomial.hom_eval₂, Polynomial.eval₂_map]`. Use `congr 1`. Use extensionality with `x`. Conclude with `congrArg Subtype.val (e.apply_symm_apply x)`.
-/
theorem isIntegral_of_map_subalgebra {K R L : Type} [Field K] [CommRing R] [Algebra K R] [CommRing L] [Algebra K L]
    (φ : R →ₐ[K] L) (hφ : Function.Injective φ) (B : Subalgebra K R) (y : R)
    (h : IsIntegral (B.map φ) (φ y)) : IsIntegral B y := by
  let e := B.equivMapOfInjective φ hφ
  obtain ⟨p, hm, hp⟩ := h
  refine ⟨p.map e.symm.toRingHom, hm.map _, hφ ?_⟩
  rw [map_zero, ← hp]
  change φ.toRingHom _ = _
  rw [Polynomial.hom_eval₂, Polynomial.eval₂_map]
  congr 1
  ext x
  exact congrArg Subtype.val (e.apply_symm_apply x)

/- English proof (translation)
Set `b` to `Module.finBasis K V`. Set `ψ : V →ₗ[K] Polynomial Ω` to `(LinearMap.mulLeft K (Polynomial.X : Polynomial Ω)) ∘ₗ (IsScalarTower.toAlgHom K Ω (Polynomial Ω)).toLinearMap ∘ₗ ev`. Establish `e : coneAlg ev = Algebra.adjoin K (ψ '' Set.range b)`. Rewrite using `[← Algebra.adjoin_span, ← Submodule.map_span, b.span_eq, Submodule.map_top]`. Both sides reduce to the same expression.

Conclude with `Subalgebra.fg_def.2 ⟨_, (Set.finite_range b).image ψ, e.symm⟩`.
-/
theorem coneAlg_fg {K V Ω : Type} [Field K] [AddCommGroup V] [Module K V] [Field Ω] [Algebra K Ω]
    [FiniteDimensional K V] (ev : V →ₗ[K] Ω) : (coneAlg ev).FG := by
  let b := Module.finBasis K V
  let ψ : V →ₗ[K] Polynomial Ω := (LinearMap.mulLeft K (Polynomial.X : Polynomial Ω)) ∘ₗ
    (IsScalarTower.toAlgHom K Ω (Polynomial Ω)).toLinearMap ∘ₗ ev
  have e : coneAlg ev = Algebra.adjoin K (ψ '' Set.range b) := by
    rw [← Algebra.adjoin_span, ← Submodule.map_span, b.span_eq, Submodule.map_top]
    rfl
  exact Subalgebra.fg_def.2 ⟨_, (Set.finite_range b).image ψ, e.symm⟩

/- English proof (translation)
Introduce `K V Ω _ _ _ _ _ ev hK hV hfg τ t hb`. Use `haveI := hK`. Use `haveI := hV`. Set `φ : Polynomial Ω →ₐ[K] RatFunc Ω` to `IsScalarTower.toAlgHom K (Polynomial Ω) (RatFunc Ω)`. Establish `hφ : Function.Injective φ` using `RatFunc.algebraMap_injective Ω`.

Establish `hφa : ∀ p, φ p = algebraMap (Polynomial Ω) (RatFunc Ω) p` using `fun _ => rfl`. Use `isIntegral_of_map_subalgebra φ hφ _ _ (GlobalTheory.T.isIntegral_of_forall_valuation_le_one_of_fg K (RatFunc Ω) (ratFunc_top_fg hfg) ((coneAlg ev).map φ) ((coneAlg_fg ev).map φ) _ fun μ hμ => ?_)` and prove the remaining obligations. Establish `hK1 : ∀ a : K, a ≠ 0 → μ (algebraMap K (RatFunc Ω) a) = 1`. Introduce `a ha`. Establish `h1 : μ (algebraMap K (RatFunc Ω) a) ≤ 1` using `hμ _ (Subalgebra.algebraMap_mem _ a)`.

Establish `h2 : μ (algebraMap K (RatFunc Ω) a⁻¹) ≤ 1` using `hμ _ (Subalgebra.algebraMap_mem _ a⁻¹)`. Establish `h3 : μ (algebraMap K (RatFunc Ω) a) * μ (algebraMap K (RatFunc Ω) a⁻¹) = 1`. Rewrite using `[← map_mul, ← map_mul, mul_inv_cancel₀ ha, map_one, map_one]`. Use `le_antisymm h1 ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

Take `⟨v, hv⟩` from `hb (μ.comap (algebraMap Ω (RatFunc Ω))) fun a ha => by`. Rewrite using `[Valuation.comap_apply, ← IsScalarTower.algebraMap_apply]`. Conclude with `hK1 a ha`. Rewrite `hv` using `[Valuation.comap_apply, Valuation.comap_apply]`. Establish `hXv : μ (RatFunc.X * algebraMap Ω (RatFunc Ω) (ev v)) ≤ 1`.

Use `hμ _ (Subalgebra.mem_map.2 ⟨_, Algebra.subset_adjoin ⟨v, rfl⟩, ?_⟩)` and prove the remaining obligations. Rewrite using `[hφa, map_mul, RatFunc.algebraMap_X, RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C]`. Rewrite using `[hφa, map_mul, map_pow, RatFunc.algebraMap_X, RatFunc.algebraMap_C, ← RatFunc.algebraMap_eq_C, map_mul, map_pow]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem isIntDeg_of_valBound : ∀ (K V Ω : Type) [Field K] [AddCommGroup V] [Module K V] [Field Ω] [Algebra K Ω]
    (ev : V →ₗ[K] Ω), CharZero K → FiniteDimensional K V → (⊤ : IntermediateField K Ω).FG →
    ∀ (τ : ℕ) (t : Ω), ValBound ev τ t → IsIntDeg ev τ t := by
  intro K V Ω _ _ _ _ _ ev hK hV hfg τ t hb
  haveI := hK
  haveI := hV
  let φ : Polynomial Ω →ₐ[K] RatFunc Ω := IsScalarTower.toAlgHom K (Polynomial Ω) (RatFunc Ω)
  have hφ : Function.Injective φ := RatFunc.algebraMap_injective Ω
  have hφa : ∀ p, φ p = algebraMap (Polynomial Ω) (RatFunc Ω) p := fun _ => rfl
  refine isIntegral_of_map_subalgebra φ hφ _ _ (GlobalTheory.T.isIntegral_of_forall_valuation_le_one_of_fg K (RatFunc Ω) (ratFunc_top_fg hfg)
    ((coneAlg ev).map φ) ((coneAlg_fg ev).map φ) _ fun μ hμ => ?_)
  have hK1 : ∀ a : K, a ≠ 0 → μ (algebraMap K (RatFunc Ω) a) = 1 := by
    intro a ha
    have h1 : μ (algebraMap K (RatFunc Ω) a) ≤ 1 := hμ _ (Subalgebra.algebraMap_mem _ a)
    have h2 : μ (algebraMap K (RatFunc Ω) a⁻¹) ≤ 1 := hμ _ (Subalgebra.algebraMap_mem _ a⁻¹)
    have h3 : μ (algebraMap K (RatFunc Ω) a) * μ (algebraMap K (RatFunc Ω) a⁻¹) = 1 := by
      rw [← map_mul, ← map_mul, mul_inv_cancel₀ ha, map_one, map_one]
    refine le_antisymm h1 ?_
    calc (1 : ℝ≥0) = _ := h3.symm
      _ ≤ μ (algebraMap K (RatFunc Ω) a) := mul_le_of_le_one_right zero_le' h2
  obtain ⟨v, hv⟩ := hb (μ.comap (algebraMap Ω (RatFunc Ω))) fun a ha => by
    rw [Valuation.comap_apply, ← IsScalarTower.algebraMap_apply]; exact hK1 a ha
  rw [Valuation.comap_apply, Valuation.comap_apply] at hv
  have hXv : μ (RatFunc.X * algebraMap Ω (RatFunc Ω) (ev v)) ≤ 1 := by
    refine hμ _ (Subalgebra.mem_map.2 ⟨_, Algebra.subset_adjoin ⟨v, rfl⟩, ?_⟩)
    rw [hφa, map_mul, RatFunc.algebraMap_X, RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C]
  rw [hφa, map_mul, map_pow, RatFunc.algebraMap_X, RatFunc.algebraMap_C, ← RatFunc.algebraMap_eq_C, map_mul, map_pow]
  calc μ RatFunc.X ^ τ * μ (algebraMap Ω (RatFunc Ω) t)
      ≤ μ RatFunc.X ^ τ * μ (algebraMap Ω (RatFunc Ω) (ev v)) ^ τ := mul_le_mul_of_nonneg_left hv zero_le'
    _ = μ (RatFunc.X * algebraMap Ω (RatFunc Ω) (ev v)) ^ τ := by rw [map_mul, mul_pow]
    _ ≤ 1 := pow_le_one₀ zero_le' hXv

end GlobalTheory.DegVal.ValInt
