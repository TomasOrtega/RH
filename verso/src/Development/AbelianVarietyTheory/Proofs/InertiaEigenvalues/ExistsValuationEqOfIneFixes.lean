import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsLocExtFinrankEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteGaloisInertiaLiftsAbsoluteInertiaRat

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.DelEps
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open Pointwise
noncomputable section
namespace GlobalTheory.InertFixVal

/- English proof (translation)
Use `haveI : NumberField M := NumberField.of_module_finite F M`. Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F`. Use `haveI : IsAlgClosure M Ω := ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := F) M⟩`. Set `σ₁ : Ω ≃ₐ[F] Ω` to `τ.liftNormal Ω`. Establish `h₁ : ∀ x : M, σ₁ (algebraMap M Ω x) = algebraMap M Ω (τ x)` using `fun x => τ.liftNormal_commutes Ω x`.

Take `⟨g, hg⟩` from `GlobalTheory.InertiaLift.exists_smul_eq (F := M) (A := A) (A' := σ₁⁻¹ • A) (by`. Introduce `x`. Rewrite using `[smul_valuation_lt_one_iff, inv_inv]`. Express the relevant statement in the definitionally equal form `A.valuation (algebraMap M Ω (x : M)) < 1 ↔ A.valuation (σ₁ (algebraMap M Ω (x : M))) < 1`. Rewrite using `[h₁]`.

Establish `hx` using `h x`. Prove the components needed by the constructor for the conclusion. Introduce `hl`. Simplify using `using Valuation.map_add_lt _ hx hl`. Introduce `hl`.

Simplify using `using Valuation.map_sub_lt _ hl hx)`. Set `σ₂ : Ω ≃ₐ[F] Ω` to `σ₁ * g.restrictScalars F`. Establish `h₂ : ∀ x : M, σ₂ (algebraMap M Ω x) = algebraMap M Ω (τ x)` using `fun x => by`. Rewrite using `[← h₁]`. Conclude with `congrArg σ₁ (g.commutes x)`.

Establish `h₂' : ∀ y, A.valuation (σ₂ y) < 1 ↔ A.valuation y < 1` using `fun y => by`. Rewrite using `[← hg y, smul_valuation_lt_one_iff, inv_inv]`. Both sides reduce to the same expression. Take `⟨k, hk, hk'⟩` from `GlobalTheory.InertiaLift.exists_congr (F := M) (A := A) σ₂.toRingEquiv h₂' (by`. Introduce `x`.

Express the relevant statement in the definitionally equal form `A.valuation (σ₂ (algebraMap M Ω (x : M)) - algebraMap M Ω (x : M)) < 1`. Rewrite using `[h₂]`. Conclude with `h x)`. Establish `hkinv : ∀ y, A.valuation (k.symm y) < 1 ↔ A.valuation y < 1` using `fun y => by`. Rewrite using `[← valuation_apply_lt_one_iff hk, k.apply_symm_apply]`.

Use `⟨k.symm.restrictScalars F * σ₂, GlobalTheory.InertiaLift.mem_Ine_of_integral (GlobalTheory.InertiaLift.mem_Dec_of_lt fun y => ?_) fun b hb => ?_, fun x => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `A.valuation (k.symm (σ₂ y)) < 1 ↔ _`. Rewrite using `[hkinv, h₂']`. Express the relevant statement in the definitionally equal form `A.valuation (k.symm (σ₂ b) - b) < 1`. Rewrite using `[← valuation_apply_lt_one_iff hk, map_sub, k.apply_symm_apply, Valuation.map_sub_swap]`.

Conclude with `hk' b hb`. Express the relevant statement in the definitionally equal form `k.symm (σ₂ (algebraMap M Ω x)) = _`. Rewrite using `[h₂]`. Conclude with `k.symm.commutes (τ x)`.
-/
theorem exists_mem_Ine_lift_int {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (A : ValuationSubring Ω) (M : Type*) [Field M] [Algebra F M]
    [Algebra M Ω] [IsScalarTower F M Ω] [FiniteDimensional F M] [IsGalois F M] (τ : M ≃ₐ[F] M)
    (h : ∀ x : 𝓞 M, A.valuation (algebraMap M Ω (τ (x : M)) - algebraMap M Ω (x : M)) < 1) :
    ∃ σ ∈ Ine (F := F) A, ∀ x : M, σ (algebraMap M Ω x) = algebraMap M Ω (τ x) := by
  haveI : NumberField M := NumberField.of_module_finite F M
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : IsAlgClosure M Ω := ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := F) M⟩
  let σ₁ : Ω ≃ₐ[F] Ω := τ.liftNormal Ω
  have h₁ : ∀ x : M, σ₁ (algebraMap M Ω x) = algebraMap M Ω (τ x) := fun x => τ.liftNormal_commutes Ω x
  obtain ⟨g, hg⟩ := GlobalTheory.InertiaLift.exists_smul_eq (F := M) (A := A) (A' := σ₁⁻¹ • A) (by
    intro x
    rw [smul_valuation_lt_one_iff, inv_inv]
    change A.valuation (algebraMap M Ω (x : M)) < 1 ↔ A.valuation (σ₁ (algebraMap M Ω (x : M))) < 1
    rw [h₁]
    have hx := h x
    constructor
    · intro hl
      simpa using Valuation.map_add_lt _ hx hl
    · intro hl
      simpa using Valuation.map_sub_lt _ hl hx)
  let σ₂ : Ω ≃ₐ[F] Ω := σ₁ * g.restrictScalars F
  have h₂ : ∀ x : M, σ₂ (algebraMap M Ω x) = algebraMap M Ω (τ x) := fun x => by
    rw [← h₁]
    exact congrArg σ₁ (g.commutes x)
  have h₂' : ∀ y, A.valuation (σ₂ y) < 1 ↔ A.valuation y < 1 := fun y => by
    rw [← hg y, smul_valuation_lt_one_iff, inv_inv]
    rfl
  obtain ⟨k, hk, hk'⟩ := GlobalTheory.InertiaLift.exists_congr (F := M) (A := A) σ₂.toRingEquiv h₂' (by
    intro x
    change A.valuation (σ₂ (algebraMap M Ω (x : M)) - algebraMap M Ω (x : M)) < 1
    rw [h₂]
    exact h x)
  have hkinv : ∀ y, A.valuation (k.symm y) < 1 ↔ A.valuation y < 1 := fun y => by
    rw [← valuation_apply_lt_one_iff hk, k.apply_symm_apply]
  refine ⟨k.symm.restrictScalars F * σ₂, GlobalTheory.InertiaLift.mem_Ine_of_integral
    (GlobalTheory.InertiaLift.mem_Dec_of_lt fun y => ?_) fun b hb => ?_, fun x => ?_⟩
  · change A.valuation (k.symm (σ₂ y)) < 1 ↔ _
    rw [hkinv, h₂']
  · change A.valuation (k.symm (σ₂ b) - b) < 1
    rw [← valuation_apply_lt_one_iff hk, map_sub, k.apply_symm_apply, Valuation.map_sub_swap]
    exact hk' b hb
  · change k.symm (σ₂ (algebraMap M Ω x)) = _
    rw [h₂]
    exact k.symm.commutes (τ x)

def primeUnder {Ω : Type*} [Field Ω] (A : ValuationSubring Ω) (M : Type*) [Field M] [NumberField M] [Algebra M Ω] :
    Ideal (𝓞 M) :=
  Ideal.comap (((algebraMap M Ω).comp (algebraMap (𝓞 M) M)).codRestrict A.toSubring fun x =>
    mem_of_isIntegral_int A (x.isIntegral_coe.map (algebraMap M Ω).toIntAlgHom)) (IsLocalRing.maximalIdeal A)

/- English proof (translation)
Rewrite using `[primeUnder, Ideal.mem_comap, ValuationSubring.valuation_lt_one_iff]`. Both sides reduce to the same expression.
-/
theorem mem_primeUnder {Ω : Type*} [Field Ω] (A : ValuationSubring Ω) (M : Type*) [Field M] [NumberField M]
    [Algebra M Ω] (x : 𝓞 M) : x ∈ primeUnder A M ↔ A.valuation (algebraMap M Ω (x : M)) < 1 := by
  rw [primeUnder, Ideal.mem_comap, ValuationSubring.valuation_lt_one_iff]
  rfl

/- English proof (translation)
Set `N : IntermediateField K Ω` to `IntermediateField.normalClosure K L Ω`. Set `M : Type` to `N`. Use `haveI : FiniteDimensional K M := inferInstance`. Use `haveI : NumberField M := NumberField.of_module_finite K M`. Use `haveI : IsGalois K M := IsGalois.normalClosure K L Ω`.

Use `haveI : IsGalois L M := IsGalois.tower_top_of_isGalois K L M`. Set `P : Ideal (𝓞 M)` to `primeUnder A M`. Use `haveI : P.IsPrime := Ideal.comap_isPrime _ _`. Establish `hPv : P.under (𝓞 K) = v.asIdeal`. Use extensionality with `x`.

Rewrite using `[Ideal.mem_comap, mem_primeUnder, ← hv x]`. Use `congr! 2`. Establish `hPw : P.under (𝓞 L) = w.asIdeal`. Use extensionality with `x`. Rewrite using `[Ideal.mem_comap, mem_primeUnder, ← hw x]`.

Use `congr! 2`. Use `haveI hPv' : P.LiesOver v.asIdeal := ⟨hPv.symm⟩`. Use `haveI hPw' : P.LiesOver w.asIdeal := ⟨hPw.symm⟩`. Use `haveI hwv : w.asIdeal.LiesOver v.asIdeal := ⟨by rw [← hPw, Ideal.under_under, hPv]⟩`. Use `⟨hwv, ?_⟩` and prove the remaining obligations.

Establish `hv0` using `v.ne_bot`. Establish `hw0` using `w.ne_bot`. Establish `hP0 : P ≠ ⊥` using `Ideal.ne_bot_of_liesOver_of_ne_bot hv0 P`. Use `v.isMaximal` as an intermediate fact. Use `w.isMaximal` as an intermediate fact.

Establish `: Finite (𝓞 K ⧸ v.asIdeal)` using `Ideal.finiteQuotientOfFreeOfNeBot _ hv0`. Establish `: Finite (𝓞 L ⧸ w.asIdeal)` using `Ideal.finiteQuotientOfFreeOfNeBot _ hw0`. Establish `h1` using `Ideal.card_inertia_eq_ramificationIdxIn (G := M ≃ₐ[K] M) v.asIdeal P`. Establish `h2` using `Ideal.card_inertia_eq_ramificationIdxIn (G := M ≃ₐ[L] M) w.asIdeal P`. Rewrite `h1` using `[Ideal.ramificationIdxIn_eq_ramificationIdx _ P (M ≃ₐ[K] M)]`.

Rewrite `h2` using `[Ideal.ramificationIdxIn_eq_ramificationIdx _ P (M ≃ₐ[L] M)]`. Establish `h3` using `Ideal.ramificationIdx_tower (R := 𝓞 K) w.asIdeal P`. Establish `hfix : ∀ τ ∈ P.toAddSubgroup.inertia (M ≃ₐ[K] M), ∀ x : L, τ (algebraMap L M x) = algebraMap L M x`. Introduce `τ hτ x`. Take `⟨σ, hσ, hστ⟩` from `exists_mem_Ine_lift_int A M τ fun y => by`.

Use `(mem_primeUnder A M _).1 (hτ y)` as an intermediate fact. Establish `e : ((τ • y - y : 𝓞 M) : M) = τ (y : M) - (y : M)` using `rfl`. Rewrite using `[← map_sub, ← e]`. Conclude with `this`. Apply `(algebraMap M Ω).injective` to reduce the goal to its premises.

Rewrite using `[← hστ, ← IsScalarTower.algebraMap_apply, hI σ hσ x]`. Set `f : P.toAddSubgroup.inertia (M ≃ₐ[K] M) → P.toAddSubgroup.inertia (M ≃ₐ[L] M)` to `fun τ => ⟨{ (τ : M ≃ₐ[K] M).toRingEquiv with commutes' := hfix τ τ.2 }, fun y => τ.2 y⟩`. Establish `hf : Function.Injective f`. Introduce `a b hab`. Apply `Subtype.ext` to reduce the goal to its premises.

Apply `AlgEquiv.ext` to reduce the goal to its premises. Introduce `y`. Conclude with `DFunLike.congr_fun (congrArg Subtype.val hab) y`. Establish `h4` using `Nat.card_le_card_of_injective f hf`. Rewrite `h4` using `[h1, h2, h3]`.

Establish `hpos : 0 < P.ramificationIdx (𝓞 K)` using `h1 ▸ Nat.card_pos`. Rewrite `hpos` using `[h3]`. Establish `ha : w.asIdeal.ramificationIdx (𝓞 K) ≠ 0`. Introduce `h0`. Rewrite `hpos` using `[h0]`.

Simplify using `at hpos`. Establish `hb : P.ramificationIdx (𝓞 L) ≠ 0`. Introduce `h0`. Rewrite `hpos` using `[h0]`. Simplify using `at hpos`.

Establish `hle : w.asIdeal.ramificationIdx (𝓞 K) ≤ 1`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Establish `: 2 * P.ramificationIdx (𝓞 L) ≤ w.asIdeal.ramificationIdx (𝓞 K) * P.ramificationIdx (𝓞 L)` using `Nat.mul_le_mul_right _ hc`. Use linear arithmetic over natural numbers and integers.

Use linear arithmetic over natural numbers and integers.
-/
theorem ramificationIdx_eq_one {K Ω L : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    [Field L] [NumberField L] [Algebra K L] [Algebra L Ω] [IsScalarTower K L Ω] (A : ValuationSubring Ω)
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) (hv : IsPlaceOver A v) (hw : IsPlaceOver A w)
    (hI : ∀ σ ∈ Ine (F := K) A, ∀ x : L, σ (algebraMap L Ω x) = algebraMap L Ω x) :
    w.asIdeal.LiesOver v.asIdeal ∧ w.asIdeal.ramificationIdx (𝓞 K) = 1 := by
  let N : IntermediateField K Ω := IntermediateField.normalClosure K L Ω
  let M : Type := N
  haveI : FiniteDimensional K M := inferInstance
  haveI : NumberField M := NumberField.of_module_finite K M
  haveI : IsGalois K M := IsGalois.normalClosure K L Ω
  haveI : IsGalois L M := IsGalois.tower_top_of_isGalois K L M
  let P : Ideal (𝓞 M) := primeUnder A M
  haveI : P.IsPrime := Ideal.comap_isPrime _ _
  have hPv : P.under (𝓞 K) = v.asIdeal := by
    ext x
    rw [Ideal.mem_comap, mem_primeUnder, ← hv x]
    congr! 2
  have hPw : P.under (𝓞 L) = w.asIdeal := by
    ext x
    rw [Ideal.mem_comap, mem_primeUnder, ← hw x]
    congr! 2
  haveI hPv' : P.LiesOver v.asIdeal := ⟨hPv.symm⟩
  haveI hPw' : P.LiesOver w.asIdeal := ⟨hPw.symm⟩
  haveI hwv : w.asIdeal.LiesOver v.asIdeal := ⟨by rw [← hPw, Ideal.under_under, hPv]⟩
  refine ⟨hwv, ?_⟩
  have hv0 := v.ne_bot
  have hw0 := w.ne_bot
  have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hv0 P
  have := v.isMaximal
  have := w.isMaximal
  have : Finite (𝓞 K ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ hv0
  have : Finite (𝓞 L ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ hw0
  have h1 := Ideal.card_inertia_eq_ramificationIdxIn (G := M ≃ₐ[K] M) v.asIdeal P
  have h2 := Ideal.card_inertia_eq_ramificationIdxIn (G := M ≃ₐ[L] M) w.asIdeal P
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx _ P (M ≃ₐ[K] M)] at h1
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx _ P (M ≃ₐ[L] M)] at h2
  have h3 := Ideal.ramificationIdx_tower (R := 𝓞 K) w.asIdeal P

  have hfix : ∀ τ ∈ P.toAddSubgroup.inertia (M ≃ₐ[K] M), ∀ x : L, τ (algebraMap L M x) = algebraMap L M x := by
    intro τ hτ x
    obtain ⟨σ, hσ, hστ⟩ := exists_mem_Ine_lift_int A M τ fun y => by
      have := (mem_primeUnder A M _).1 (hτ y)
      have e : ((τ • y - y : 𝓞 M) : M) = τ (y : M) - (y : M) := rfl
      rw [← map_sub, ← e]
      exact this
    apply (algebraMap M Ω).injective
    rw [← hστ, ← IsScalarTower.algebraMap_apply, hI σ hσ x]
  let f : P.toAddSubgroup.inertia (M ≃ₐ[K] M) → P.toAddSubgroup.inertia (M ≃ₐ[L] M) := fun τ =>
    ⟨{ (τ : M ≃ₐ[K] M).toRingEquiv with commutes' := hfix τ τ.2 }, fun y => τ.2 y⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply AlgEquiv.ext
    intro y
    exact DFunLike.congr_fun (congrArg Subtype.val hab) y
  have h4 := Nat.card_le_card_of_injective f hf
  rw [h1, h2, h3] at h4
  have hpos : 0 < P.ramificationIdx (𝓞 K) := h1 ▸ Nat.card_pos
  rw [h3] at hpos
  have ha : w.asIdeal.ramificationIdx (𝓞 K) ≠ 0 := by
    intro h0
    rw [h0] at hpos
    simp at hpos
  have hb : P.ramificationIdx (𝓞 L) ≠ 0 := by
    intro h0
    rw [h0] at hpos
    simp at hpos
  have hle : w.asIdeal.ramificationIdx (𝓞 K) ≤ 1 := by
    by_contra hc
    push_neg at hc
    have : 2 * P.ramificationIdx (𝓞 L) ≤ w.asIdeal.ramificationIdx (𝓞 K) * P.ramificationIdx (𝓞 L) :=
      Nat.mul_le_mul_right _ hc
    omega
  omega

end GlobalTheory.InertFixVal
end
