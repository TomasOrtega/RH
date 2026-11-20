import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpOrderLe
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PTorsionFreeQuotientLength
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u

open Module Submodule
open scoped Pointwise

namespace IntermediateRingQuotLength

/- English proof (translation)
Rewrite using `[← Submodule.ideal_span_singleton_smul, smul_eq_mul, Ideal.mul_top]`.
-/
theorem smul_top_eq_span {A : Type*} [CommRing A] (a : A) :
    (a • ⊤ : Submodule A A) = Ideal.span {a} := by
  rw [← Submodule.ideal_span_singleton_smul, smul_eq_mul, Ideal.mul_top]

/- English proof (translation)
Rewrite using `[← smul_top_eq_span]`. Establish `hLtop : Module.length A (A ⧸ (a • ⊤ : Submodule A A)) ≠ ⊤`. Rewrite using `[smul_top_eq_span]`. Conclude with `Module.length_ne_top_iff.mpr (isFiniteLength_quotient_span_singleton A (mem_nonZeroDivisors_of_ne_zero ha))`. Set `T : Submodule A M` to `a • ⊤`.

Establish `hfg : ∀ N : Submodule A M, N.FG → LinearMap.range φ ≤ N → Module.length A (N.map T.mkQ) ≤ Module.length A (A ⧸ (a • ⊤ : Submodule A A))`. Introduce `N hN hφN`. Establish `: Module.Finite A N` using `Module.Finite.iff_fg.mpr hN`. Set `φN : A →ₗ[A] N` to `φ.codRestrict N fun y => hφN (LinearMap.mem_range_self φ y)`. Establish `hφN' : Function.Injective φN` using `fun y z h => hφ (congrArg Subtype.val h)`.

Establish `hregN : Function.Injective fun x : N => a • x` using `fun x y h => Subtype.ext (hreg (congrArg Subtype.val h))`. Establish `hfin : IsFiniteLength A (N ⧸ LinearMap.range φN)`. Use `GroundTheory.Heights₂.Heights.Model.TorsionFreeQuotientLength.isFiniteLength_of_torsion _ fun q => ?_` and prove the remaining obligations. Take `⟨x, rfl⟩` from `Submodule.Quotient.mk_surjective _ q`. Take `⟨c, hc, y, hy⟩` from `htor x`.

Use `⟨c, hc, ?_⟩` and prove the remaining obligations. Rewrite using `[← Quotient.mk_smul, Quotient.mk_eq_zero]`. Conclude with `⟨y, Subtype.ext hy⟩`. Establish `hle : (a • ⊤ : Submodule A N) ≤ LinearMap.ker (T.mkQ ∘ₗ N.subtype)` using `fun x hx => by`. Take `⟨b, -, rfl⟩` from `(mem_smul_pointwise_iff_exists _ _ _).mp hx`.

Simplify using `only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply, mkQ_apply, Quotient.mk_eq_zero, Submodule.coe_smul, Submodule.subtype_apply]`. Conclude with `smul_mem_pointwise_smul _ a ⊤ mem_top`. Establish `hmap : N.map T.mkQ = LinearMap.range ((a • ⊤ : Submodule A N).liftQ _ hle)`. Rewrite using `[range_liftQ, LinearMap.range_comp, range_subtype]`. Rewrite using `[hmap, ← GroundTheory.Heights₂.Heights.Model.TorsionFreeQuotientLength.length_quot_smul_eq φN hφN' hregN hfin]`.

Conclude with `Module.length_le_of_surjective _ (LinearMap.surjective_rangeRestrict _)`. Set `S : Set ℕ` to `{n | ∃ N : Submodule A M, N.FG ∧ LinearMap.range φ ≤ N ∧ Module.length A (N.map T.mkQ) = n}`. Establish `hSb : BddAbove S` using `⟨(Module.length A (A ⧸ (a • ⊤ : Submodule A A))).toNat, by`. Introduce and unpack `n ⟨N, hN, hφN, hn⟩`. Use `hfg N hN hφN` as an intermediate fact.

Rewrite `this` using `[hn]`. Simplify using `using ENat.toNat_le_toNat this hLtop⟩`. Establish `hφfg : (LinearMap.range φ).FG`. Rewrite using `[LinearMap.range_eq_map]`. Conclude with `Module.Finite.fg_top.map φ`.

Establish `hne0 : Module.length A ((LinearMap.range φ).map T.mkQ) ≠ ⊤` using `ne_top_of_le_ne_top hLtop (hfg _ hφfg le_rfl)`. Establish `hSne : S.Nonempty` using `⟨_, LinearMap.range φ, hφfg, le_rfl, (ENat.natCast_toNat hne0).symm⟩`. Take `⟨N₀, hN₀, hφN₀, hm⟩` from `Nat.sSup_mem hSne hSb`. Establish `htop : N₀.map T.mkQ = ⊤`. Use `eq_top_iff.mpr fun q _ => ?_` and prove the remaining obligations.

Take `⟨x, rfl⟩` from `Submodule.Quotient.mk_surjective _ q`. Assume the negation of the conclusion as `hx`. Establish `hN₁ : (N₀ ⊔ span A {x}).FG` using `hN₀.sup (fg_span_singleton x)`. Establish `hx1 : Submodule.Quotient.mk x ∈ (N₀ ⊔ span A {x}).map T.mkQ` using `mem_map_of_mem (mem_sup_right (mem_span_singleton_self x))`. Establish `hlt : N₀.map T.mkQ < (N₀ ⊔ span A {x}).map T.mkQ` using `lt_of_le_of_ne (map_mono le_sup_left) fun h => hx (by rw [h]; exact hx1)`.

Establish `hne : Module.length A ((N₀ ⊔ span A {x}).map T.mkQ) ≠ ⊤` using `ne_top_of_le_ne_top hLtop (hfg _ hN₁ (hφN₀.trans le_sup_left))`. Establish `h1` using `le_csSup hSb ⟨_, hN₁, hφN₀.trans le_sup_left, (ENat.natCast_toNat hne).symm⟩`. Establish `h2 : Module.length A (N₀.map T.mkQ) < Module.length A ((N₀ ⊔ span A {x}).map T.mkQ)`. Rewrite using `[Module.length_submodule, Module.length_submodule]`. Use `Order.height_strictMono hlt ?_` and prove the remaining obligations.

Rewrite using `[← Module.length_submodule, hm]`. Conclude with `ENat.natCast_lt_top _`. Rewrite `h2` using `[hm, ← ENat.natCast_toNat hne]`. Conclude with `absurd (ENat.natCast_lt_natCast.mp h2) (not_lt.mpr h1)`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[htop, Module.length_top]`. Use `_ ≤ Module.length A (A ⧸ (a • ⊤ : Submodule A A)) := hfg N₀ hN₀ hφN₀`.
-/
theorem length_quot_smul_le {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [Ring.KrullDimLE 1 A] {M : Type*} [AddCommGroup M] [Module A M] (φ : A →ₗ[A] M)
    (hφ : Function.Injective φ) (htor : ∀ x : M, ∃ c : A, c ≠ 0 ∧ c • x ∈ LinearMap.range φ)
    {a : A} (ha : a ≠ 0) (hreg : Function.Injective fun x : M => a • x) :
    Module.length A (M ⧸ (a • ⊤ : Submodule A M)) ≤ Module.length A (A ⧸ Ideal.span {a}) := by
  rw [← smul_top_eq_span]
  have hLtop : Module.length A (A ⧸ (a • ⊤ : Submodule A A)) ≠ ⊤ := by
    rw [smul_top_eq_span]
    exact Module.length_ne_top_iff.mpr
      (isFiniteLength_quotient_span_singleton A (mem_nonZeroDivisors_of_ne_zero ha))
  let T : Submodule A M := a • ⊤
  have hfg : ∀ N : Submodule A M, N.FG → LinearMap.range φ ≤ N →
      Module.length A (N.map T.mkQ) ≤ Module.length A (A ⧸ (a • ⊤ : Submodule A A)) := by
    intro N hN hφN
    have : Module.Finite A N := Module.Finite.iff_fg.mpr hN
    let φN : A →ₗ[A] N := φ.codRestrict N fun y => hφN (LinearMap.mem_range_self φ y)
    have hφN' : Function.Injective φN := fun y z h => hφ (congrArg Subtype.val h)
    have hregN : Function.Injective fun x : N => a • x := fun x y h =>
      Subtype.ext (hreg (congrArg Subtype.val h))
    have hfin : IsFiniteLength A (N ⧸ LinearMap.range φN) := by
      refine GroundTheory.Heights₂.Heights.Model.TorsionFreeQuotientLength.isFiniteLength_of_torsion _
        fun q => ?_
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      obtain ⟨c, hc, y, hy⟩ := htor x
      refine ⟨c, hc, ?_⟩
      rw [← Quotient.mk_smul, Quotient.mk_eq_zero]
      exact ⟨y, Subtype.ext hy⟩
    have hle : (a • ⊤ : Submodule A N) ≤ LinearMap.ker (T.mkQ ∘ₗ N.subtype) := fun x hx => by
      obtain ⟨b, -, rfl⟩ := (mem_smul_pointwise_iff_exists _ _ _).mp hx
      simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply, mkQ_apply,
        Quotient.mk_eq_zero, Submodule.coe_smul, Submodule.subtype_apply]
      exact smul_mem_pointwise_smul _ a ⊤ mem_top
    have hmap : N.map T.mkQ = LinearMap.range ((a • ⊤ : Submodule A N).liftQ _ hle) := by
      rw [range_liftQ, LinearMap.range_comp, range_subtype]
    rw [hmap, ← GroundTheory.Heights₂.Heights.Model.TorsionFreeQuotientLength.length_quot_smul_eq φN hφN'
      hregN hfin]
    exact Module.length_le_of_surjective _ (LinearMap.surjective_rangeRestrict _)
  let S : Set ℕ := {n | ∃ N : Submodule A M, N.FG ∧ LinearMap.range φ ≤ N ∧
    Module.length A (N.map T.mkQ) = n}
  have hSb : BddAbove S := ⟨(Module.length A (A ⧸ (a • ⊤ : Submodule A A))).toNat, by
    rintro n ⟨N, hN, hφN, hn⟩
    have := hfg N hN hφN
    rw [hn] at this
    simpa using ENat.toNat_le_toNat this hLtop⟩
  have hφfg : (LinearMap.range φ).FG := by
    rw [LinearMap.range_eq_map]
    exact Module.Finite.fg_top.map φ
  have hne0 : Module.length A ((LinearMap.range φ).map T.mkQ) ≠ ⊤ :=
    ne_top_of_le_ne_top hLtop (hfg _ hφfg le_rfl)
  have hSne : S.Nonempty := ⟨_, LinearMap.range φ, hφfg, le_rfl, (ENat.natCast_toNat hne0).symm⟩
  obtain ⟨N₀, hN₀, hφN₀, hm⟩ := Nat.sSup_mem hSne hSb
  have htop : N₀.map T.mkQ = ⊤ := by
    refine eq_top_iff.mpr fun q _ => ?_
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    by_contra hx
    have hN₁ : (N₀ ⊔ span A {x}).FG := hN₀.sup (fg_span_singleton x)
    have hx1 : Submodule.Quotient.mk x ∈ (N₀ ⊔ span A {x}).map T.mkQ :=
      mem_map_of_mem (mem_sup_right (mem_span_singleton_self x))
    have hlt : N₀.map T.mkQ < (N₀ ⊔ span A {x}).map T.mkQ :=
      lt_of_le_of_ne (map_mono le_sup_left) fun h => hx (by rw [h]; exact hx1)
    have hne : Module.length A ((N₀ ⊔ span A {x}).map T.mkQ) ≠ ⊤ :=
      ne_top_of_le_ne_top hLtop (hfg _ hN₁ (hφN₀.trans le_sup_left))
    have h1 := le_csSup hSb ⟨_, hN₁, hφN₀.trans le_sup_left, (ENat.natCast_toNat hne).symm⟩
    have h2 : Module.length A (N₀.map T.mkQ) < Module.length A ((N₀ ⊔ span A {x}).map T.mkQ) := by
      rw [Module.length_submodule, Module.length_submodule]
      refine Order.height_strictMono hlt ?_
      rw [← Module.length_submodule, hm]
      exact ENat.natCast_lt_top _
    rw [hm, ← ENat.natCast_toNat hne] at h2
    exact absurd (ENat.natCast_lt_natCast.mp h2) (not_lt.mpr h1)
  calc Module.length A (M ⧸ T) = Module.length A (N₀.map T.mkQ) := by
        rw [htop, Module.length_top]
    _ ≤ Module.length A (A ⧸ (a • ⊤ : Submodule A A)) := hfg N₀ hN₀ hφN₀

end IntermediateRingQuotLength

/- English proof (translation)
Introduce `A C _ _ _ _ _ _ hdim hinj hfrac a ha`. Establish `: Ring.KrullDimLE 1 A` using `Ring.krullDimLE_iff.mpr (by rw [hdim]; rfl)`. Establish `hI : (Ideal.span {algebraMap A C a}).restrictScalars A = (a • ⊤ : Submodule A C)`. Use extensionality with `x`. Simplify using `only [Submodule.restrictScalars_mem, Ideal.mem_span_singleton', mem_smul_pointwise_iff_exists, mem_top, true_and, Algebra.smul_def, mul_comm]`.

Establish `hreg : Function.Injective fun x : C => a • x` using `fun x y h => by`. Simplify using `only [Algebra.smul_def] at h`. Conclude with `mul_left_cancel₀ (by simpa using (map_ne_zero_iff _ hinj).mpr ha) h`. Establish `htor : ∀ x : C, ∃ c : A, c ≠ 0 ∧ c • x ∈ LinearMap.range (Algebra.linearMap A C)`. Introduce `x`.

Take `⟨c, hc, y, hy⟩` from `hfrac x`. Conclude with `⟨c, hc, y, by simpa using hy⟩`. Rewrite using `[← (Submodule.Quotient.restrictScalarsEquiv A (Ideal.span {algebraMap A C a})).length_eq, hI]`. Conclude with `IntermediateRingQuotLength.length_quot_smul_le (Algebra.linearMap A C) hinj htor ha hreg`.
-/
theorem IntermediateRingQuotLength.proof : IntermediateRingQuotLength.Statement.{u} := by
  intro A C _ _ _ _ _ _ hdim hinj hfrac a ha
  have : Ring.KrullDimLE 1 A := Ring.krullDimLE_iff.mpr (by rw [hdim]; rfl)
  have hI : (Ideal.span {algebraMap A C a}).restrictScalars A = (a • ⊤ : Submodule A C) := by
    ext x
    simp only [Submodule.restrictScalars_mem, Ideal.mem_span_singleton',
      mem_smul_pointwise_iff_exists, mem_top, true_and, Algebra.smul_def, mul_comm]
  have hreg : Function.Injective fun x : C => a • x := fun x y h => by
    simp only [Algebra.smul_def] at h
    exact mul_left_cancel₀ (by simpa using (map_ne_zero_iff _ hinj).mpr ha) h
  have htor : ∀ x : C, ∃ c : A, c ≠ 0 ∧ c • x ∈ LinearMap.range (Algebra.linearMap A C) := by
    intro x
    obtain ⟨c, hc, y, hy⟩ := hfrac x
    exact ⟨c, hc, y, by simpa using hy⟩
  rw [← (Submodule.Quotient.restrictScalarsEquiv A (Ideal.span {algebraMap A C a})).length_eq, hI]
  exact IntermediateRingQuotLength.length_quot_smul_le (Algebra.linearMap A C) hinj htor ha hreg

end GroundTheory.Heights₂.Heights.NumbersDVR
