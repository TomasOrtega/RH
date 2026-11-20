import Mathlib
import GroundTheory.LocalFields.LocalFourier

noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel Topology Filter
open scoped WithZero Pointwise

section RatCircle

def ratAddCircleToReal : AddCircle (1 : ℚ) →+ AddCircle (1 : ℝ) :=
  QuotientAddGroup.map _ _ (Rat.castHom ℝ : ℚ →+* ℝ).toAddMonoidHom
    (AddSubgroup.zmultiples_le_of_mem (by
      rw [AddSubgroup.mem_comap]
      simp))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem ratAddCircleToReal_coe (q : ℚ) :
    ratAddCircleToReal (q : AddCircle (1 : ℚ)) = ((q : ℝ) : AddCircle (1 : ℝ)) := rfl

/- English proof (translation)
Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Proceed by induction on `x using QuotientAddGroup.induction_on with`. Consider the case `H q`. Rewrite `hx` using `[ratAddCircleToReal_coe, AddCircle.coe_eq_zero_iff]`.

Take `⟨n, hn⟩` from `hx`. Rewrite using `[QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_zmultiples_iff]`. Use `⟨n, ?_⟩` and prove the remaining obligations. Establish `: ((n : ℚ) : ℝ) = (q : ℝ)` using `by simpa using hn`. Simplify using `using (Rat.cast_injective this)`.
-/
theorem ratAddCircleToReal_injective : Function.Injective ratAddCircleToReal := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  induction x using QuotientAddGroup.induction_on with
  | H q =>
    rw [ratAddCircleToReal_coe, AddCircle.coe_eq_zero_iff] at hx
    obtain ⟨n, hn⟩ := hx
    rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_zmultiples_iff]
    refine ⟨n, ?_⟩
    have : ((n : ℚ) : ℝ) = (q : ℝ) := by simpa using hn
    simpa using (Rat.cast_injective this)

def ratCircleChar : AddChar (AddCircle (1 : ℚ)) Circle :=
  (AddCircle.toCircle_addChar (T := 1)).compAddMonoidHom ratAddCircleToReal

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem ratCircleChar_apply (x : AddCircle (1 : ℚ)) :
    ratCircleChar x = AddCircle.toCircle (ratAddCircleToReal x) := rfl

/- English proof (translation)
The claim follows from `(AddCircle.injective_toCircle one_ne_zero).comp ratAddCircleToReal_injective`.
-/
theorem ratCircleChar_injective : Function.Injective ratCircleChar :=
  (AddCircle.injective_toCircle one_ne_zero).comp ratAddCircleToReal_injective

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Apply `ratCircleChar_injective` to reduce the goal to its premises. Rewrite using `[h, AddChar.map_zero_eq_one]`. Introduce and unpack `rfl`.

Conclude with `AddChar.map_zero_eq_one _`.
-/
theorem ratCircleChar_eq_one_iff {x : AddCircle (1 : ℚ)} : ratCircleChar x = 1 ↔ x = 0 := by
  constructor
  · intro h
    apply ratCircleChar_injective
    rw [h, AddChar.map_zero_eq_one]
  · rintro rfl
    exact AddChar.map_zero_eq_one _

end RatCircle

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

section Existence

/- English proof (translation)
Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible 𝒪[K]`. Establish `h0 : (ϖ : K) ≠ 0` using `fun h => hϖ.ne_zero (Subtype.ext h)`. Establish `hi : (ϖ : K)⁻¹ ≠ 0` using `inv_ne_zero h0`. Use `⟨(ϖ : K)⁻¹, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[mem_valBall_iff_le_ord hi, ord_inv h0, ord_uniformizer hϖ]`.

Rewrite using `[mem_valBall_iff_le_ord hi, ord_inv h0, ord_uniformizer hϖ]`. Use linear arithmetic over natural numbers and integers.
-/
theorem exists_mem_valBall_neg_one_notMem_valBall_zero :
    ∃ x : K, x ∈ valBall K (-1) ∧ x ∉ valBall K 0 := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have h0 : (ϖ : K) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  have hi : (ϖ : K)⁻¹ ≠ 0 := inv_ne_zero h0
  refine ⟨(ϖ : K)⁻¹, ?_, ?_⟩
  · rw [mem_valBall_iff_le_ord hi, ord_inv h0, ord_uniformizer hϖ]
  · rw [mem_valBall_iff_le_ord hi, ord_inv h0, ord_uniformizer hϖ]
    omega

/- English proof (translation)
Establish `hlc : IsLocallyConstant χ`. Rewrite using `[IsLocallyConstant.iff_exists_open]`. Introduce `x`. Use `⟨{z | z - x ∈ valBall K n}, (isOpen_valBall n).preimage (continuous_id.sub continuous_const), by simp, fun z hz => ?_⟩` and prove the remaining obligations. Establish `e : x + (z - x) = z` using `by abel`.

Rewrite using `[← e, AddChar.map_add_eq_mul, h _ hz, mul_one]`. Conclude with `hlc.continuous`.
-/
theorem continuous_of_isTrivialOn {χ : AddChar K Circle} {n : ℤ} (h : IsTrivialOn χ n) :
    Continuous χ := by
  have hlc : IsLocallyConstant χ := by
    rw [IsLocallyConstant.iff_exists_open]
    intro x
    refine ⟨{z | z - x ∈ valBall K n},
      (isOpen_valBall n).preimage (continuous_id.sub continuous_const), by simp, fun z hz => ?_⟩
    have e : x + (z - x) = z := by abel
    rw [← e, AddChar.map_add_eq_mul, h _ hz, mul_one]
  exact hlc.continuous

/- English proof (translation)
Assemble the required witnesses or components as `⟨exists_isTrivialOn χ, fun ⟨_, h⟩ => continuous_of_isTrivialOn h⟩`.
-/
theorem continuous_iff_exists_isTrivialOn (χ : AddChar K Circle) :
    Continuous χ ↔ ∃ n, IsTrivialOn χ n :=
  ⟨exists_isTrivialOn χ, fun ⟨_, h⟩ => continuous_of_isTrivialOn h⟩

/- English proof (translation)
Take `⟨x, hx1, hx0⟩` from `exists_mem_valBall_neg_one_notMem_valBall_zero (K := K)`. Set `π : K →+ K ⧸ valBall K 0` to `QuotientAddGroup.mk' (valBall K 0)`. Establish `hπx : π x ≠ 0`. Rewrite using `[Ne, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]` and apply the resulting hypothesis. Take `⟨c, hc⟩` from `CharacterModule.exists_character_apply_ne_zero_of_ne_zero hπx`.

Set `ψ : AddChar K Circle` to `ratCircleChar.compAddMonoidHom ((c : K ⧸ valBall K 0 →+ AddCircle (1 : ℚ)).comp π)`. Establish `hψ : ∀ y, ψ y = ratCircleChar (c (π y))` using `fun _ => rfl`. Use `⟨ψ, fun y hy => ?_, fun h => ?_⟩` and prove the remaining obligations. Establish `: π y = 0`. Rewrite using `[QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]` and apply the resulting hypothesis.

Rewrite using `[hψ, this, map_zero, AddChar.map_zero_eq_one]`. Conclude with `hc (ratCircleChar_eq_one_iff.mp ((hψ x).symm.trans (h x hx1)))`.
-/
theorem exists_addChar_isTrivialOn_zero_not_isTrivialOn_neg_one :
    ∃ ψ : AddChar K Circle, IsTrivialOn ψ 0 ∧ ¬ IsTrivialOn ψ (-1) := by
  obtain ⟨x, hx1, hx0⟩ := exists_mem_valBall_neg_one_notMem_valBall_zero (K := K)
  let π : K →+ K ⧸ valBall K 0 := QuotientAddGroup.mk' (valBall K 0)
  have hπx : π x ≠ 0 := by
    rwa [Ne, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
  obtain ⟨c, hc⟩ := CharacterModule.exists_character_apply_ne_zero_of_ne_zero hπx
  let ψ : AddChar K Circle :=
    ratCircleChar.compAddMonoidHom ((c : K ⧸ valBall K 0 →+ AddCircle (1 : ℚ)).comp π)
  have hψ : ∀ y, ψ y = ratCircleChar (c (π y)) := fun _ => rfl
  refine ⟨ψ, fun y hy => ?_, fun h => ?_⟩
  · have : π y = 0 := by
      rwa [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
    rw [hψ, this, map_zero, AddChar.map_zero_eq_one]
  · exact hc (ratCircleChar_eq_one_iff.mp ((hψ x).symm.trans (h x hx1)))

/- English proof (translation)
Take `⟨ψ, h0, h1⟩` from `exists_addChar_isTrivialOn_zero_not_isTrivialOn_neg_one (K := K)`. Establish `hc : Continuous ψ` using `continuous_of_isTrivialOn h0`. Establish `hne : ψ ≠ 1`. Introduce and unpack `rfl`. Conclude with `h1 fun _ _ => AddChar.one_apply _`.

Use `⟨ψ, hc, hne, le_antisymm ((isTrivialOn_iff hc hne 0).mp h0) ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hlt`. Conclude with `h1 ((isTrivialOn_iff hc hne (-1)).mpr (by omega))`.
-/
theorem exists_addChar_addCharConductor_eq_zero :
    ∃ ψ : AddChar K Circle, Continuous ψ ∧ ψ ≠ 1 ∧ addCharConductor ψ = 0 := by
  obtain ⟨ψ, h0, h1⟩ := exists_addChar_isTrivialOn_zero_not_isTrivialOn_neg_one (K := K)
  have hc : Continuous ψ := continuous_of_isTrivialOn h0
  have hne : ψ ≠ 1 := by
    rintro rfl
    exact h1 fun _ _ => AddChar.one_apply _
  refine ⟨ψ, hc, hne, le_antisymm ((isTrivialOn_iff hc hne 0).mp h0) ?_⟩
  by_contra hlt
  exact h1 ((isTrivialOn_iff hc hne (-1)).mpr (by omega))

/- English proof (translation)
Take `⟨ψ, hc, hne, h0⟩` from `exists_addChar_addCharConductor_eq_zero (K := K)`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible 𝒪[K]`. Establish `h0ϖ : (ϖ : K) ≠ 0` using `fun h => hϖ.ne_zero (Subtype.ext h)`. Establish `ha : (ϖ : K) ^ (-n) ≠ 0` using `zpow_ne_zero _ h0ϖ`. Use `⟨ψ.mulShift ((ϖ : K) ^ (-n)), continuous_mulShift hc _, mulShift_ne_one hne ha, ?_⟩` and prove the remaining obligations.

Establish `hord : ord ((ϖ : K) ^ (-n)) = -n`. Simplify using `[ord, map_zpow₀, normalizedValuation_uniformizer hϖ]`. Rewrite using `[addCharConductor_mulShift hc hne ha, h0, hord]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_addChar_addCharConductor_eq (n : ℤ) :
    ∃ ψ : AddChar K Circle, Continuous ψ ∧ ψ ≠ 1 ∧ addCharConductor ψ = n := by
  obtain ⟨ψ, hc, hne, h0⟩ := exists_addChar_addCharConductor_eq_zero (K := K)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have h0ϖ : (ϖ : K) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  have ha : (ϖ : K) ^ (-n) ≠ 0 := zpow_ne_zero _ h0ϖ
  refine ⟨ψ.mulShift ((ϖ : K) ^ (-n)), continuous_mulShift hc _, mulShift_ne_one hne ha, ?_⟩
  have hord : ord ((ϖ : K) ^ (-n)) = -n := by
    simp [ord, map_zpow₀, normalizedValuation_uniformizer hϖ]
  rw [addCharConductor_mulShift hc hne ha, h0, hord]
  ring

/- English proof (translation)
Take `⟨ψ, hc, hne, -⟩` from `exists_addChar_addCharConductor_eq_zero (K := K)`. Conclude with `⟨ψ, hc, hne⟩`.
-/
theorem exists_addChar_continuous_ne_one :
    ∃ ψ : AddChar K Circle, Continuous ψ ∧ ψ ≠ 1 := by
  obtain ⟨ψ, hc, hne, -⟩ := exists_addChar_addCharConductor_eq_zero (K := K)
  exact ⟨ψ, hc, hne⟩

/- English proof (translation)
Take `⟨ψ, hc, hne⟩` from `exists_addChar_continuous_ne_one (K := K)`. Conclude with `⟨selfDual hc hne⟩`.
-/
theorem nonempty_selfDual :
    Nonempty (Multiplicative K ≃ₜ* PontryaginDual (Multiplicative K)) := by
  obtain ⟨ψ, hc, hne⟩ := exists_addChar_continuous_ne_one (K := K)
  exact ⟨selfDual hc hne⟩

end Existence

end GroundTheory.LocalField
