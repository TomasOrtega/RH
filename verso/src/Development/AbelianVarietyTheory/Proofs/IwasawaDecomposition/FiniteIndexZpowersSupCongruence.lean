import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChevalleyUnits
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL

noncomputable section

open ValuativeRel

namespace GlobalTheory.CongruenceSubgroupIndex

section Defs

variable {K : Type} [Field K] [ValuativeRel K]

/- English proof (translation)
Establish `h : valuation K (y - 1) < 1` using `hy.trans_le hγ`. Simplify using `using (valuation K).map_one_add_of_lt h`.
-/
theorem valuation_eq_one_of_sub_one_lt {γ : ValueGroupWithZero K} (hγ : γ ≤ 1) {y : K}
    (hy : valuation K (y - 1) < γ) : valuation K y = 1 := by
  have h : valuation K (y - 1) < 1 := hy.trans_le hγ
  simpa using (valuation K).map_one_add_of_lt h

def f0 {K : Type} [Field K] [ValuativeRel K] (γ : ValueGroupWithZero K) (hγ : γ ≤ 1) (h0 : γ ≠ 0) :
    Subgroup Kˣ where
  carrier := {x | valuation K ((x : K) - 1) < γ}
  one_mem' := by simpa using zero_lt_iff.2 h0
  mul_mem' := by
    intro a b ha hb
    have ha' : valuation K ((a : K) - 1) < γ := ha
    have hb' : valuation K ((b : K) - 1) < γ := hb
    have h1 := valuation_eq_one_of_sub_one_lt hγ ha'
    show valuation K (((a * b : Kˣ) : K) - 1) < γ
    have e : ((a * b : Kˣ) : K) - 1 = (a : K) * ((b : K) - 1) + ((a : K) - 1) := by
      rw [Units.val_mul]; ring
    rw [e]
    refine (valuation K).map_add_lt ?_ ha'
    rw [map_mul, h1, one_mul]
    exact hb'
  inv_mem' := by
    intro a ha
    have ha' : valuation K ((a : K) - 1) < γ := ha
    have h1 := valuation_eq_one_of_sub_one_lt hγ ha'
    show valuation K (((a⁻¹ : Kˣ) : K) - 1) < γ
    have e : ((a⁻¹ : Kˣ) : K) - 1 = -((a : K)⁻¹ * ((a : K) - 1)) := by
      rw [Units.val_inv_eq_inv_val, mul_sub, inv_mul_cancel₀ a.ne_zero]; ring
    rw [e, Valuation.map_neg, map_mul, map_inv₀, h1, inv_one, one_mul]
    exact ha'

end Defs

section Local

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/- English proof (translation)
Rewrite using `[isOpen_iff_mem_nhds]`. Introduce `y hy`. Rewrite using `[IsValuativeTopology.mem_nhds_iff']`. Use `⟨Units.mk0 γ h0, fun z hz => ?_⟩` and prove the remaining obligations. Establish `hz' : valuation K (z - y) < γ` using `hz`.

Establish `: valuation K ((z - y) + y) < γ` using `(valuation K).map_add_lt hz' hy`. Simplify using `using this`.
-/
theorem isOpen_ball {γ : ValueGroupWithZero K} (h0 : γ ≠ 0) :
    IsOpen {y : K | valuation K y < γ} := by
  rw [isOpen_iff_mem_nhds]
  intro y hy
  rw [IsValuativeTopology.mem_nhds_iff']
  refine ⟨Units.mk0 γ h0, fun z hz => ?_⟩
  have hz' : valuation K (z - y) < γ := hz
  have : valuation K ((z - y) + y) < γ := (valuation K).map_add_lt hz' hy
  simpa using this

/- English proof (translation)
The claim follows from `(isOpen_ball h0).preimage (f := fun x : Kˣ => (x : K) - 1) (Units.continuous_val.sub continuous_const)`.
-/
theorem isOpen_congruence_subgroup (γ : ValueGroupWithZero K) (hγ : γ ≤ 1) (h0 : γ ≠ 0) :
    IsOpen (f0 γ hγ h0 : Set Kˣ) :=
  (isOpen_ball h0).preimage (f := fun x : Kˣ => (x : K) - 1)
    (Units.continuous_val.sub continuous_const)

/- English proof (translation)
Rewrite using `[Units.isEmbedding_val₀.isCompact_iff]`. Establish `e : ((↑) : Kˣ → K) '' {x : Kˣ | valuation K (x : K) = 1} = {y : K | valuation K y ≤ 1} \ {y : K | valuation K y < 1}`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, rfl⟩`.

Establish `hx' : valuation K (x : K) = 1` using `hx`. Simplify using `[hx']`. Introduce and unpack `⟨h1, h2⟩`. Establish `h : valuation K y = 1` using `le_antisymm h1 (not_lt.1 h2)`. Establish `hy : y ≠ 0`.

Introduce and unpack `rfl`. Simplify using `at h`. Conclude with `⟨Units.mk0 y hy, h, rfl⟩`. Rewrite using `[e]`. Conclude with `(IsNonarchimedeanLocalField.isCompact_closedBall K 1).diff (isOpen_ball one_ne_zero)`.
-/
theorem isCompact_units : IsCompact {x : Kˣ | valuation K (x : K) = 1} := by
  rw [Units.isEmbedding_val₀.isCompact_iff]
  have e : ((↑) : Kˣ → K) '' {x : Kˣ | valuation K (x : K) = 1} =
      {y : K | valuation K y ≤ 1} \ {y : K | valuation K y < 1} := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : valuation K (x : K) = 1 := hx
      simp [hx']
    · rintro ⟨h1, h2⟩
      have h : valuation K y = 1 := le_antisymm h1 (not_lt.1 h2)
      have hy : y ≠ 0 := by
        rintro rfl
        simp at h
      exact ⟨Units.mk0 y hy, h, rfl⟩
  rw [e]
  exact (IsNonarchimedeanLocalField.isCompact_closedBall K 1).diff (isOpen_ball one_ne_zero)

/- English proof (translation)
Set `o : Kˣ →* Multiplicative ℤ` to `MonoidHom.mk' (fun z => .ofAdd (GlobalTheory.SmGL.ord K z)) fun a b => by`. Rewrite using `[GlobalTheory.SmGL.ord_mul, ofAdd_add]`. Establish `h1 : o (y / x ^ GlobalTheory.SmGL.ord K y) = 1`. Rewrite using `[map_div, map_zpow, show o x = .ofAdd 1 from congrArg Multiplicative.ofAdd hx, ← ofAdd_zsmul, smul_eq_mul, mul_one]`. Conclude with `div_self' _`.

Conclude with `GlobalTheory.SmGL.ord_eq_zero_iff.1 (ofAdd_eq_one.1 h1)`.
-/
theorem valuation_div_zpow {x : Kˣ} (hx : GlobalTheory.SmGL.ord K x = 1) (y : Kˣ) :
    valuation K ((y / x ^ GlobalTheory.SmGL.ord K y : Kˣ) : K) = 1 := by
  let o : Kˣ →* Multiplicative ℤ := MonoidHom.mk' (fun z => .ofAdd (GlobalTheory.SmGL.ord K z)) fun a b => by
    rw [GlobalTheory.SmGL.ord_mul, ofAdd_add]
  have h1 : o (y / x ^ GlobalTheory.SmGL.ord K y) = 1 := by
    rw [map_div, map_zpow, show o x = .ofAdd 1 from congrArg Multiplicative.ofAdd hx, ← ofAdd_zsmul,
      smul_eq_mul, mul_one]
    exact div_self' _
  exact GlobalTheory.SmGL.ord_eq_zero_iff.1 (ofAdd_eq_one.1 h1)

/- English proof (translation)
Use `haveI : DiscreteTopology (Kˣ ⧸ H) := QuotientGroup.discreteTopology hH`. Establish `hc` using `(isCompact_units (K := K)).image (QuotientGroup.continuous_mk (N := H))`. Establish `hu : ((↑) : Kˣ → Kˣ ⧸ H) '' {x : Kˣ | valuation K (x : K) = 1} = Set.univ`. Use `Set.eq_univ_of_forall fun q => ?_` and prove the remaining obligations. Take `⟨y, rfl⟩` from `QuotientGroup.mk_surjective q`.

Use `⟨y / x ^ GlobalTheory.SmGL.ord K y, valuation_div_zpow hx y, ?_⟩` and prove the remaining obligations. Rewrite using `[QuotientGroup.eq]`. Establish `: (y / x ^ GlobalTheory.SmGL.ord K y)⁻¹ * y = x ^ GlobalTheory.SmGL.ord K y`. Rewrite using `[inv_div, div_mul_cancel]`. Rewrite using `[this]`.

Conclude with `H.zpow_mem hxH _`. Rewrite `hc` using `[hu]`. Use `haveI : Finite (Kˣ ⧸ H) := Set.finite_univ_iff.1 hc.finite_of_discrete`. Conclude with `Subgroup.finiteIndex_of_finite_quotient`.
-/
theorem finiteIndex_of_isOpen {H : Subgroup Kˣ} (hH : IsOpen (H : Set Kˣ)) {x : Kˣ}
    (hx : GlobalTheory.SmGL.ord K x = 1) (hxH : x ∈ H) : H.FiniteIndex := by
  haveI : DiscreteTopology (Kˣ ⧸ H) := QuotientGroup.discreteTopology hH
  have hc := (isCompact_units (K := K)).image (QuotientGroup.continuous_mk (N := H))
  have hu : ((↑) : Kˣ → Kˣ ⧸ H) '' {x : Kˣ | valuation K (x : K) = 1} = Set.univ := by
    refine Set.eq_univ_of_forall fun q => ?_
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    refine ⟨y / x ^ GlobalTheory.SmGL.ord K y, valuation_div_zpow hx y, ?_⟩
    rw [QuotientGroup.eq]
    have : (y / x ^ GlobalTheory.SmGL.ord K y)⁻¹ * y = x ^ GlobalTheory.SmGL.ord K y := by
      rw [inv_div, div_mul_cancel]
    rw [this]
    exact H.zpow_mem hxH _
  rw [hu] at hc
  haveI : Finite (Kˣ ⧸ H) := Set.finite_univ_iff.1 hc.finite_of_discrete
  exact Subgroup.finiteIndex_of_finite_quotient

/- English proof (translation)
The claim follows from `finiteIndex_of_isOpen (Subgroup.isOpen_mono le_sup_right (isOpen_congruence_subgroup γ hγ h0)) hx (Subgroup.mem_sup_left (Subgroup.mem_zpowers x))`.
-/
theorem finiteIndex_zpowers_sup_congruence (γ : ValueGroupWithZero K) (hγ : γ ≤ 1) (h0 : γ ≠ 0) {x : Kˣ}
    (hx : GlobalTheory.SmGL.ord K x = 1) : (Subgroup.zpowers x ⊔ f0 γ hγ h0).FiniteIndex :=
  finiteIndex_of_isOpen (Subgroup.isOpen_mono le_sup_right (isOpen_congruence_subgroup γ hγ h0)) hx
    (Subgroup.mem_sup_left (Subgroup.mem_zpowers x))

end Local

/- English proof (translation)
Assemble the required witnesses or components as `⟨@f0, fun γ hγ h0 => isOpen_congruence_subgroup γ hγ h0, fun γ hγ h0 _ hx => finiteIndex_zpowers_sup_congruence γ hγ h0 hx⟩`.
-/
theorem main : ∃ f0 : {K : Type} → [inst : Field K] → [inst_1 : ValuativeRel K] →
      (γ : ValuativeRel.ValueGroupWithZero K) → γ ≤ (1 : ValuativeRel.ValueGroupWithZero K) →
      γ ≠ (0 : ValuativeRel.ValueGroupWithZero K) → Subgroup Kˣ,
    (∀ {K : Type} [inst : Field K] [inst_1 : ValuativeRel K] [inst_2 : TopologicalSpace K]
      [IsNonarchimedeanLocalField K] (γ : ValuativeRel.ValueGroupWithZero K)
      (hγ : γ ≤ (1 : ValuativeRel.ValueGroupWithZero K))
      (h0 : γ ≠ (0 : ValuativeRel.ValueGroupWithZero K)), IsOpen (↑(f0 γ hγ h0) : Set Kˣ)) ∧
    (∀ {K : Type} [inst : Field K] [inst_1 : ValuativeRel K] [inst_2 : TopologicalSpace K]
      [inst_3 : IsNonarchimedeanLocalField K] (γ : ValuativeRel.ValueGroupWithZero K)
      (hγ : γ ≤ (1 : ValuativeRel.ValueGroupWithZero K))
      (h0 : γ ≠ (0 : ValuativeRel.ValueGroupWithZero K)) {x : Kˣ}, GlobalTheory.SmGL.ord K x = (1 : ℤ) →
      Subgroup.FiniteIndex (Subgroup.zpowers x ⊔ f0 γ hγ h0)) :=
  ⟨@f0, fun γ hγ h0 => isOpen_congruence_subgroup γ hγ h0,
    fun γ hγ h0 _ hx => finiteIndex_zpowers_sup_congruence γ hγ h0 hx⟩

end GlobalTheory.CongruenceSubgroupIndex

end
