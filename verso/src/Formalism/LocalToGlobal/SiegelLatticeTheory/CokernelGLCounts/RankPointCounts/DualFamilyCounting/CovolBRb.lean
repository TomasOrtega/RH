import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.CovolBRa
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.CovolIdxK
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.BaseLatticeLe
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.EmbVHomInjective
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LeadingMinorIntegrality
import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.TermTiesEmptyOfLargeIndex
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.FinrankSpanLb

noncomputable section

open NumberField Formalism.BasicNotions
open scoped nonZeroDivisors

namespace Formalism.L2.SG.Pf.NcReal.JX.CovB.TrD

open Formalism.L2.SG.HidaSetting Formalism.MainNotions.S Formalism.L2.SG.Pf.NcReal.JX Formalism.L2.SG.Pf.NcReal.JX.CovB.CovolumeSpans

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev Dv (D : D7) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E :=
  FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)

/- English proof (translation)
Establish `h10 : (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0` using `fun h => by`. Use `congrArg (fun I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E => (1 : D.host.E) ∈ I) h` as an intermediate fact. Simplify using `[FractionalIdeal.one_mem_one, FractionalIdeal.mem_zero_iff] at this`. Rewrite using `[FractionalIdeal.mem_dual h10]`. Simplify using `only [FractionalIdeal.mem_one_iff, forall_exists_index, forall_apply_eq_imp_iff, Algebra.traceForm_apply, RingHom.mem_range, eq_intCast]`.

Prove the components needed by the constructor for the conclusion. Introduce `h o`. Take `⟨z, hz⟩` from `h o`. Conclude with `⟨z, hz.symm⟩`. Introduce `h o`.

Take `⟨z, hz⟩` from `h o`. Conclude with `⟨z, hz.symm⟩`.
-/
theorem memDv (t : D.host.E) :
    t ∈ Dv D ↔ ∀ o : 𝓞 D.host.E, ∃ z : ℤ, Algebra.trace ℚ D.host.E (t * o) = z := by
  have h10 : (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 := fun h => by
    have := congrArg (fun I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E => (1 : D.host.E) ∈ I) h
    simp [FractionalIdeal.one_mem_one, FractionalIdeal.mem_zero_iff] at this
  rw [FractionalIdeal.mem_dual h10]
  simp only [FractionalIdeal.mem_one_iff, forall_exists_index, forall_apply_eq_imp_iff,
    Algebra.traceForm_apply, RingHom.mem_range, eq_intCast]
  constructor
  · intro h o
    obtain ⟨z, hz⟩ := h o
    exact ⟨z, hz.symm⟩
  · intro h o
    obtain ⟨z, hz⟩ := h o
    exact ⟨z, hz.symm⟩

/- English proof (translation)
Establish `e : ∀ x : ℚ, (starRingAut : RingAut D.host.E) (algebraMap ℚ D.host.E x) = algebraMap ℚ D.host.E x` using `fun x => by simp`. Conclude with `Algebra.trace_eq_of_algEquiv (AlgEquiv.ofRingEquiv (f := (starRingAut : RingAut D.host.E)) e) t`.
-/
theorem trace_conj (t : D.host.E) : Algebra.trace ℚ D.host.E (star t) = Algebra.trace ℚ D.host.E t := by
  have e : ∀ x : ℚ, (starRingAut : RingAut D.host.E) (algebraMap ℚ D.host.E x) = algebraMap ℚ D.host.E x :=
    fun x => by simp
  exact Algebra.trace_eq_of_algEquiv (AlgEquiv.ofRingEquiv (f := (starRingAut : RingAut D.host.E)) e) t

/- English proof (translation)
Rewrite `ht`, the goal using `[memDv]`. Introduce `o`. Take `⟨o', ho'⟩` from `Formalism.L2.SG.NGCut.LeadingMinorIntegrality.star_int (D := D) o`. Take `⟨z, hz⟩` from `ht o'`. Use `⟨z, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hz, ho', ← trace_conj (t * star (o : D.host.E)), star_mul', star_star]`.
-/
theorem star_memDv {t : D.host.E} (ht : t ∈ Dv D) : star t ∈ Dv D := by
  rw [memDv] at ht ⊢
  intro o
  obtain ⟨o', ho'⟩ := Formalism.L2.SG.NGCut.LeadingMinorIntegrality.star_int (D := D) o
  obtain ⟨z, hz⟩ := ht o'
  refine ⟨z, ?_⟩
  rw [← hz, ho', ← trace_conj (t * star (o : D.host.E)), star_mul', star_star]

/- English proof (translation)
Establish `hi : IsIntegral ℤ (Algebra.trace ℚ D.host.E (o : D.host.E))` using `Algebra.isIntegral_trace (RingOfIntegers.isIntegral_coe o)`. Take `⟨z, hz⟩` from `(IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).mp hi`. Conclude with `⟨z, by rw [← hz, eq_intCast]⟩`.
-/
theorem trace_int (o : 𝓞 D.host.E) : ∃ z : ℤ, Algebra.trace ℚ D.host.E (o : D.host.E) = z := by
  have hi : IsIntegral ℤ (Algebra.trace ℚ D.host.E (o : D.host.E)) :=
    Algebra.isIntegral_trace (RingOfIntegers.isIntegral_coe o)
  obtain ⟨z, hz⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).mp hi
  exact ⟨z, by rw [← hz, eq_intCast]⟩

variable (X : HidaSetting D)

/- English proof (translation)
Establish `hL0 : X.Lb ≤ (VS D).L0`. Rewrite using `[X.Lam_split]`. Conclude with `le_sup_of_le_left le_sup_right`. Establish `hU` using `(VS D).baseLattice_isUnimodular`. Unfold `Formalism.HermitianLatticesTheory.IsUnimodular Formalism.HermitianLatticesTheory.dual at hU`.

Establish `hy' : y ∈ Formalism.E.hdual (VS D).hT (VS D).L0`. Rewrite using `[hU]`. Conclude with `hL0 hy`. Simplify using `only [Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply] at hy'`. Take `⟨o, ho⟩` from `Submodule.mem_one.mp (hy' x (hL0 hx))`.

Conclude with `⟨o, ho⟩`.
-/
theorem hint {x y : (VS D).V} (hx : x ∈ X.Lb) (hy : y ∈ X.Lb) : ∃ o : 𝓞 D.host.E, (o : D.host.E) = (VS D).hT x y := by
  have hL0 : X.Lb ≤ (VS D).L0 := by
    rw [X.Lam_split]
    exact le_sup_of_le_left le_sup_right
  have hU := (VS D).baseLattice_isUnimodular
  unfold Formalism.HermitianLatticesTheory.IsUnimodular Formalism.HermitianLatticesTheory.dual at hU
  have hy' : y ∈ Formalism.E.hdual (VS D).hT (VS D).L0 := by
    rw [hU]
    exact hL0 hy
  simp only [Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply] at hy'
  obtain ⟨o, ho⟩ := Submodule.mem_one.mp (hy' x (hL0 hx))
  exact ⟨o, ho⟩

def Ldual : Submodule (𝓞 D.host.E) (VS D).V where
  carrier := {x | x ∈ Wb X ∧ ∀ y ∈ X.Lb, ∃ z : ℤ, Algebra.trace ℚ D.host.E ((VS D).hT x y) = z}
  add_mem' {a b} ha hb := by
    refine ⟨(Wb X).add_mem ha.1 hb.1, fun y hy => ?_⟩
    obtain ⟨za, hza⟩ := ha.2 y hy
    obtain ⟨zb, hzb⟩ := hb.2 y hy
    exact ⟨za + zb, by rw [map_add, LinearMap.add_apply, map_add, hza, hzb]; push_cast; ring⟩
  zero_mem' := ⟨(Wb X).zero_mem, fun y _ => ⟨0, by simp⟩⟩
  smul_mem' c x hx := by
    refine ⟨?_, fun y hy => ?_⟩
    · have : c • x = (c : D.host.E) • x := (algebraMap_smul D.host.E c x).symm
      rw [this]; exact (Wb X).smul_mem _ hx.1
    · obtain ⟨c', hc'⟩ := Formalism.L2.SG.NGCut.LeadingMinorIntegrality.star_int c
      have e : (VS D).hT (c • x) y = (VS D).hT x (c' • y) := by
        rw [← algebraMap_smul D.host.E c x, ← algebraMap_smul D.host.E c' y, LinearMap.map_smulₛₗ₂,
          LinearMap.map_smul]
        show starRingEnd D.host.E (c : D.host.E) * _ = (c' : D.host.E) * _
        rw [hc']; rfl
      rw [e]
      exact hx.2 _ (X.Lb.smul_mem c' hy)

/- English proof (translation)
Conclude with `fun x hx => span_Lb_le X (Submodule.subset_span hx)`.
-/
theorem Lb_le_alt : X.Lb ≤ (Wb X).restrictScalars (𝓞 D.host.E) := by
  exact fun x hx => span_Lb_le X (Submodule.subset_span hx)

/- English proof (translation)
Conclude with `fun y hy => ⟨Lb_le_alt X hy, fun y' hy' => by`. Take `⟨o, ho⟩` from `hint X hy hy'`. Rewrite using `[← ho]`. Conclude with `trace_int o⟩`.
-/
theorem Lb_le_Ldual : X.Lb ≤ Ldual X := by
  exact fun y hy => ⟨Lb_le_alt X hy, fun y' hy' => by
    obtain ⟨o, ho⟩ := hint X hy hy'
    rw [← ho]
    exact trace_int o⟩

/- English proof (translation)
Apply `Submodule.span_le.mpr` to reduce the goal to its premises. Introduce and unpack `y ⟨a, x, -, rfl⟩`. Conclude with `Submodule.smul_mem _ x (Submodule.subset_span ⟨a, rfl⟩)`.
-/
theorem latSpanS_le {r : ℕ} (aa : Fin r → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (v : Fin r → (VS D).V) :
    latSpanS aa v ≤ (Submodule.span D.host.E (Set.range v)).restrictScalars (𝓞 D.host.E) := by
  apply Submodule.span_le.mpr
  rintro y ⟨a, x, -, rfl⟩
  exact Submodule.smul_mem _ x (Submodule.subset_span ⟨a, rfl⟩)

/- English proof (translation)
Rewrite `hy` using `[X.Lam_split]`. Take `⟨y12, hy12, y3, hy3, rfl⟩` from `Submodule.mem_sup.1 hy`. Take `⟨y1, hy1, l, hl, rfl⟩` from `Submodule.mem_sup.1 hy12`. Take `⟨α, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun D.host.E).1 (latSpanS_le _ _ hy1)`. Take `⟨β, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun D.host.E).1 (latSpanS_le _ _ hy3)`.

Conclude with `⟨α, β, l, hl, rfl⟩`.
-/
theorem decomp {y : (VS D).V} (hy : y ∈ (VS D).L0) :
    ∃ (α β : Fin D.R.rS → D.host.E) (l : (VS D).V), l ∈ X.Lb ∧ y = ∑ c, α c • X.eX c + l + ∑ c, β c • X.fY c := by
  rw [X.Lam_split] at hy
  obtain ⟨y12, hy12, y3, hy3, rfl⟩ := Submodule.mem_sup.1 hy
  obtain ⟨y1, hy1, l, hl, rfl⟩ := Submodule.mem_sup.1 hy12
  obtain ⟨α, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun D.host.E).1 (latSpanS_le _ _ hy1)
  obtain ⟨β, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun D.host.E).1 (latSpanS_le _ _ hy3)
  exact ⟨α, β, l, hl, rfl⟩

/- English proof (translation)
Establish `hzW` using `(mem_Wb X).1 hz`. Establish `hzL : z ∈ (VS D).L0`. Establish `hun` using `(VS D).baseLattice_isUnimodular`. Rewrite using `[← hun]`. Simplify using `only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.coe_restrictScalars]`.

Introduce `y hy`. Take `⟨α, β, l, hl, rfl⟩` from `decomp X hy`. Take `⟨o, ho⟩` from `hd l hl`. Establish `e : (VS D).hT (∑ c, α c • X.eX c + l + ∑ c, β c • X.fY c) z = (VS D).hT l z`. Simplify using `[map_add, map_sum, LinearMap.map_smulₛₗ₂, (hzW _).1, (hzW _).2]`.

Rewrite using `[Submodule.mem_one]`. Conclude with `⟨o, by rw [e]; exact ho⟩`. Take `⟨α, β, l, hl, hzeq⟩` from `decomp X hzL`. Establish `hlW : ∀ c, (VS D).hT (X.eX c) l = 0 ∧ (VS D).hT (X.fY c) l = 0` using `fun c => X.Lb_perp l hl c`. Establish `hα : ∀ c, α c = 0`.

Introduce `c`. Use `(hzW c).2` as an intermediate fact. Rewrite `this` using `[hzeq]`. Simplify using `[map_add, map_sum, map_smul, Formalism.L2.SG.Pf.NcReal.JX.NOf.Ex.h_fe, X.ff, (hlW c).2, Finset.sum_ite_eq] at this`. Conclude with `this`.

Establish `hβ : ∀ c, β c = 0`. Introduce `c`. Use `(hzW c).1` as an intermediate fact. Rewrite `this` using `[hzeq]`. Simplify using `[map_add, map_sum, map_smul, X.ef, X.ee, (hlW c).1, Finset.sum_ite_eq] at this`.

Conclude with `this`. Rewrite using `[hzeq]`. Simplify using `only [hα, hβ, zero_smul, Finset.sum_const_zero, zero_add, add_zero]`. Conclude with `hl`.
-/
theorem Lsharp {z : (VS D).V} (hz : z ∈ Wb X) (hd : ∀ y ∈ X.Lb, ∃ o : 𝓞 D.host.E, (o : D.host.E) = (VS D).hT y z) :
    z ∈ X.Lb := by
  have hzW := (mem_Wb X).1 hz

  have hzL : z ∈ (VS D).L0 := by
    have hun := (VS D).baseLattice_isUnimodular
    rw [← hun]
    simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.coe_restrictScalars]
    intro y hy
    obtain ⟨α, β, l, hl, rfl⟩ := decomp X hy
    obtain ⟨o, ho⟩ := hd l hl
    have e : (VS D).hT (∑ c, α c • X.eX c + l + ∑ c, β c • X.fY c) z = (VS D).hT l z := by
      simp [map_add, map_sum, LinearMap.map_smulₛₗ₂, (hzW _).1, (hzW _).2]
    rw [Submodule.mem_one]
    exact ⟨o, by rw [e]; exact ho⟩
  obtain ⟨α, β, l, hl, hzeq⟩ := decomp X hzL
  have hlW : ∀ c, (VS D).hT (X.eX c) l = 0 ∧ (VS D).hT (X.fY c) l = 0 := fun c => X.Lb_perp l hl c
  have hα : ∀ c, α c = 0 := by
    intro c
    have := (hzW c).2
    rw [hzeq] at this
    simp [map_add, map_sum, map_smul, Formalism.L2.SG.Pf.NcReal.JX.NOf.Ex.h_fe, X.ff, (hlW c).2, Finset.sum_ite_eq] at this
    exact this
  have hβ : ∀ c, β c = 0 := by
    intro c
    have := (hzW c).1
    rw [hzeq] at this
    simp [map_add, map_sum, map_smul, X.ef, X.ee, (hlW c).1, Finset.sum_ite_eq] at this
    exact this
  rw [hzeq]
  simp only [hα, hβ, zero_smul, Finset.sum_const_zero, zero_add, add_zero]
  exact hl

/- English proof (translation)
Use `first`. Consider the case `exact ((VS D).herm x y).symm`. Consider the case `exact ((VS D).herm.eq x y).symm`.
-/
theorem herm_swap (x y : (VS D).V) : (VS D).hT y x = star ((VS D).hT x y) := by
  first
    | exact ((VS D).herm x y).symm
    | exact ((VS D).herm.eq x y).symm

/- English proof (translation)
Rewrite using `[memDv]`. Introduce `o`. Take `⟨z, hz⟩` from `hx.2 (o • y) (X.Lb.smul_mem o hy)`. Use `⟨z, ?_⟩` and prove the remaining obligations. Rewrite using `[← hz, ← algebraMap_smul D.host.E o y, LinearMap.map_smul, smul_eq_mul, mul_comm]`.

Apply the tactic sequence `try rfl`.
-/
theorem F4 {x y : (VS D).V} (hx : x ∈ Ldual X) (hy : y ∈ X.Lb) : (VS D).hT x y ∈ Dv D := by
  rw [memDv]
  intro o
  obtain ⟨z, hz⟩ := hx.2 (o • y) (X.Lb.smul_mem o hy)
  refine ⟨z, ?_⟩
  rw [← hz, ← algebraMap_smul D.host.E o y, LinearMap.map_smul, smul_eq_mul, mul_comm]
  try rfl

/- English proof (translation)
Conclude with `coeIdeal_differentIdeal ℤ ℚ D.host.E (𝓞 D.host.E)`.
-/
theorem coe_different :
    ((differentIdeal ℤ (𝓞 D.host.E) : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) = (Dv D)⁻¹ := by
  exact coeIdeal_differentIdeal ℤ ℚ D.host.E (𝓞 D.host.E)

/- English proof (translation)
Introduce `h`. Establish `e` using `coe_different (D := D)`. Rewrite `e` using `[h, inv_zero]`. Conclude with `differentIdeal_ne_bot (FractionalIdeal.coeIdeal_eq_zero.mp e)`.
-/
theorem Dv_ne : Dv D ≠ 0 := by
  intro h
  have e := coe_different (D := D)
  rw [h, inv_zero] at e
  exact differentIdeal_ne_bot (FractionalIdeal.coeIdeal_eq_zero.mp e)

/- English proof (translation)
Rewrite using `[Submodule.smul_le]`. Introduce `δ hδ x hx`. Use `Lsharp X ?_ fun y hy => ?_` and prove the remaining obligations. Establish `: δ • x = (δ : D.host.E) • x` using `(algebraMap_smul D.host.E δ x).symm`. Rewrite using `[this]`.

Conclude with `(Wb X).smul_mem _ hx.1`. Establish `h1 : star ((VS D).hT x y) ∈ Dv D` using `star_memDv (F4 X hx hy)`. Establish `h2 : (δ : D.host.E) ∈ (Dv D)⁻¹`. Rewrite using `[← coe_different]`. Conclude with `(FractionalIdeal.mem_coeIdeal _).2 ⟨δ, hδ, rfl⟩`.

Establish `h3` using `FractionalIdeal.mul_mem_mul h2 h1`. Rewrite `h3` using `[inv_mul_cancel₀ (Dv_ne (D := D))]`. Take `⟨o, ho⟩` from `(FractionalIdeal.mem_one_iff _).1 h3`. Use `⟨o, ?_⟩` and prove the remaining obligations. Rewrite using `[← algebraMap_smul D.host.E δ x, LinearMap.map_smul, herm_swap]`.

Conclude with `ho`.
-/
theorem F5 : (differentIdeal ℤ (𝓞 D.host.E)) • Ldual X ≤ X.Lb := by
  rw [Submodule.smul_le]
  intro δ hδ x hx
  refine Lsharp X ?_ fun y hy => ?_
  · have : δ • x = (δ : D.host.E) • x := (algebraMap_smul D.host.E δ x).symm
    rw [this]; exact (Wb X).smul_mem _ hx.1
  · have h1 : star ((VS D).hT x y) ∈ Dv D := star_memDv (F4 X hx hy)
    have h2 : (δ : D.host.E) ∈ (Dv D)⁻¹ := by
      rw [← coe_different]; exact (FractionalIdeal.mem_coeIdeal _).2 ⟨δ, hδ, rfl⟩
    have h3 := FractionalIdeal.mul_mem_mul h2 h1
    rw [inv_mul_cancel₀ (Dv_ne (D := D))] at h3
    obtain ⟨o, ho⟩ := (FractionalIdeal.mem_one_iff _).1 h3
    refine ⟨o, ?_⟩
    rw [← algebraMap_smul D.host.E δ x, LinearMap.map_smul, herm_swap]
    exact ho

/- English proof (translation)
Introduce `l hl`. Establish `h1 : (1 : D.host.E) ∈ (Dv D)⁻¹ * Dv D`. Rewrite using `[inv_mul_cancel₀ (Dv_ne (D := D))]`. Conclude with `FractionalIdeal.one_mem_one _`. Establish `key : ∀ a ∈ (Dv D)⁻¹ * Dv D, a • l ∈ (differentIdeal ℤ (𝓞 D.host.E)) • Ldual X`.

Introduce `a ha`. Use `FractionalIdeal.mul_induction_on ha ?_ ?_` and prove the remaining obligations. Introduce `i hi j hj`. Rewrite `hi` using `[← coe_different]`. Take `⟨δ, hδ, rfl⟩` from `(FractionalIdeal.mem_coeIdeal _).1 hi`.

Establish `hjl : j • l ∈ Ldual X`. Use `⟨(Wb X).smul_mem _ (Lb_le_alt X hl), fun y hy => ?_⟩` and prove the remaining obligations. Take `⟨o, ho⟩` from `hint X hl hy`. Take `⟨z, hz⟩` from `(memDv _).1 (star_memDv hj) o`. Use `⟨z, ?_⟩` and prove the remaining obligations.

Rewrite using `[LinearMap.map_smulₛₗ₂]`. Use `show Algebra.trace ℚ D.host.E (star j * (VS D).hT l y) = z`. Rewrite using `[← ho]`. Conclude with `hz`. Establish `: (algebraMap (𝓞 D.host.E) D.host.E δ * j) • l = δ • (j • l)`.

Rewrite using `[mul_smul, algebraMap_smul]`. Rewrite using `[this]`. Conclude with `Submodule.smul_mem_smul hδ hjl`. Introduce `x y hx hy`. Rewrite using `[add_smul]`.

Conclude with `Submodule.add_mem _ hx hy`. Simplify using `using key 1 h1`.
-/
theorem F6 : X.Lb ≤ (differentIdeal ℤ (𝓞 D.host.E)) • Ldual X := by
  intro l hl
  have h1 : (1 : D.host.E) ∈ (Dv D)⁻¹ * Dv D := by
    rw [inv_mul_cancel₀ (Dv_ne (D := D))]; exact FractionalIdeal.one_mem_one _
  have key : ∀ a ∈ (Dv D)⁻¹ * Dv D, a • l ∈ (differentIdeal ℤ (𝓞 D.host.E)) • Ldual X := by
    intro a ha
    refine FractionalIdeal.mul_induction_on ha ?_ ?_
    · intro i hi j hj
      rw [← coe_different] at hi
      obtain ⟨δ, hδ, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hi
      have hjl : j • l ∈ Ldual X := by
        refine ⟨(Wb X).smul_mem _ (Lb_le_alt X hl), fun y hy => ?_⟩
        obtain ⟨o, ho⟩ := hint X hl hy
        obtain ⟨z, hz⟩ := (memDv _).1 (star_memDv hj) o
        refine ⟨z, ?_⟩
        rw [LinearMap.map_smulₛₗ₂]
        show Algebra.trace ℚ D.host.E (star j * (VS D).hT l y) = z
        rw [← ho]; exact hz
      have : (algebraMap (𝓞 D.host.E) D.host.E δ * j) • l = δ • (j • l) := by
        rw [mul_smul, algebraMap_smul]
      rw [this]
      exact Submodule.smul_mem_smul hδ hjl
    · intro x y hx hy
      rw [add_smul]; exact Submodule.add_mem _ hx hy
  simpa using key 1 h1

open Formalism.L2.SG.Pf.NcReal.JX.CovB.IdxK

/- English proof (translation)
Introduce `y hy`. Set `y' : Fin (D.R.k + 1 + 1) → Wb X` to `fun i => ⟨y i, hN (hy i)⟩`. Establish `hnot : ¬ LinearIndependent D.host.E y'`. Introduce `hli`. Use `hli.fintype_card_le_finrank` as an intermediate fact.

Rewrite `this` using `[Fintype.card_fin, finrank_Wb]`. Use linear arithmetic over natural numbers and integers. Take `⟨g, hg, i0, hi0⟩` from `Fintype.not_linearIndependent_iff.1 hnot`. Take `⟨⟨b, hb⟩, hbint⟩` from `IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 D.host.E)) (Finset.univ.image g)`. Use `choose c hc using fun i => hbint (g i) (Finset.mem_image_of_mem g (Finset.mem_univ i))`.

Use `⟨c, fun h0 => ?_, ?_⟩` and prove the remaining obligations. Use `hc i0` as an intermediate fact. Rewrite `this` using `[congrFun h0 i0, Pi.zero_apply, map_zero, Algebra.smul_def]`. Establish `hb0 : (algebraMap (𝓞 D.host.E) D.host.E b) ≠ 0`. Rewrite using `[Ne, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)]`.

Conclude with `nonZeroDivisors.ne_zero hb`. Conclude with `hi0 ((mul_eq_zero.1 this.symm).resolve_left hb0)`. Establish `e : ∀ i, c i • y i = b • (g i • y i)`. Introduce `i`. Rewrite using `[← algebraMap_smul D.host.E (c i), hc i, smul_assoc]`.

Repeatedly rewrite using `[e, ← Finset.smul_sum]`. Establish `: ∑ i, g i • y i = 0`. Use `congrArg Subtype.val hg` as an intermediate fact. Simplify `this` using `[y']`. Rewrite using `[this, smul_zero]`.
-/
theorem hdepW (N : Submodule (𝓞 D.host.E) (VS D).V) (hN : N ≤ (Wb X).restrictScalars (𝓞 D.host.E)) :
    HDep (D.R.k + 1) N := by
  intro y hy
  classical
  let y' : Fin (D.R.k + 1 + 1) → Wb X := fun i => ⟨y i, hN (hy i)⟩
  have hnot : ¬ LinearIndependent D.host.E y' := by
    intro hli
    have := hli.fintype_card_le_finrank
    rw [Fintype.card_fin, finrank_Wb] at this
    omega
  obtain ⟨g, hg, i0, hi0⟩ := Fintype.not_linearIndependent_iff.1 hnot
  obtain ⟨⟨b, hb⟩, hbint⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 D.host.E))
    (Finset.univ.image g)
  choose c hc using fun i => hbint (g i) (Finset.mem_image_of_mem g (Finset.mem_univ i))
  refine ⟨c, fun h0 => ?_, ?_⟩
  · have := hc i0
    rw [congrFun h0 i0, Pi.zero_apply, map_zero, Algebra.smul_def] at this
    have hb0 : (algebraMap (𝓞 D.host.E) D.host.E b) ≠ 0 := by
      rw [Ne, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)]; exact nonZeroDivisors.ne_zero hb
    exact hi0 ((mul_eq_zero.1 this.symm).resolve_left hb0)
  · have e : ∀ i, c i • y i = b • (g i • y i) := by
      intro i
      rw [← algebraMap_smul D.host.E (c i), hc i, smul_assoc]
    simp_rw [e, ← Finset.smul_sum]
    have : ∑ i, g i • y i = 0 := by
      have := congrArg Subtype.val hg
      simpa [y'] using this
    rw [this, smul_zero]

/- English proof (translation)
Establish `h` using `(VS D).standardTuple_isLattice.fg`. Establish `: Module.Finite (𝓞 D.host.E) (VS D).L0` using `Module.Finite.iff_fg.2 h`. Establish `: IsNoetherian (𝓞 D.host.E) (VS D).L0` using `isNoetherian_of_isNoetherianRing_of_finite (𝓞 D.host.E) _`. Establish `h2` using `IsNoetherian.noetherian (X.Lb.comap (VS D).L0.subtype)`. Establish `e : (X.Lb.comap (VS D).L0.subtype).map (VS D).L0.subtype = X.Lb` using `Submodule.map_comap_eq_of_le (by rw [Submodule.range_subtype]; exact base_lattice_le X)`.

Rewrite using `[← e]`. Conclude with `h2.map _`.
-/
theorem fg_Lb : X.Lb.FG := by
  have h := (VS D).standardTuple_isLattice.fg
  have : Module.Finite (𝓞 D.host.E) (VS D).L0 := Module.Finite.iff_fg.2 h
  have : IsNoetherian (𝓞 D.host.E) (VS D).L0 := isNoetherian_of_isNoetherianRing_of_finite (𝓞 D.host.E) _
  have h2 := IsNoetherian.noetherian (X.Lb.comap (VS D).L0.subtype)
  have e : (X.Lb.comap (VS D).L0.subtype).map (VS D).L0.subtype = X.Lb :=
    Submodule.map_comap_eq_of_le (by rw [Submodule.range_subtype]; exact base_lattice_le X)
  rw [← e]; exact h2.map _

/- English proof (translation)
Set `w : Module.Basis (Fin (D.R.k + 1)) D.host.E (Wb X)` to `Module.finBasisOfFinrankEq D.host.E (Wb X) (finrank_Wb X)`. Establish `hwL : ∀ i, ((w i : Wb X) : (VS D).V) ∈ Submodule.span D.host.E (X.Lb : Set (VS D).V)`. Introduce `i`. Rewrite using `[span_Lb]`. Conclude with `(w i).2`.

Use `choose n hn hnL using fun i => Formalism.MainNotions.LatticeGluingRadicals.j_exists_nat_smul_mem X.Lb (hwL i)`. Set `l : Fin (D.R.k + 1) → (VS D).V` to `fun i => n i • ((w i : Wb X) : (VS D).V)`. Set `ι : (Fin (D.R.k + 1) → 𝓞 D.host.E) →ₗ[𝓞 D.host.E] (VS D).V` to `Fintype.linearCombination (𝓞 D.host.E) l`. Establish `hιap : ∀ a, ι a = ∑ i, a i • l i` using `fun a => by simp [ι, Fintype.linearCombination_apply]`. Establish `hli : LinearIndependent D.host.E l`.

Establish `h1 : LinearIndependent D.host.E (fun i => ((w i : Wb X) : (VS D).V))` using `(LinearIndependent.map' w.linearIndependent (Wb X).subtype (Submodule.ker_subtype _))`. Establish `h2` using `h1.units_smul (fun i => Units.mk0 ((n i : ℕ) : D.host.E) (by exact_mod_cast (hn i).ne'))`. Use `h2 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`. Simplify using `only [l, Pi.smul_apply', Units.smul_def, Units.val_mk0]`.

Rewrite using `[Nat.cast_smul_eq_nsmul]`. Establish `hinj : Function.Injective ι`. Rewrite using `[← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]`. Introduce `a ha`. Rewrite `ha` using `[LinearMap.mem_ker, hιap]`.

Establish `ha' : ∑ i, ((a i : 𝓞 D.host.E) : D.host.E) • l i = 0`. Rewrite using `[← ha]`. Conclude with `Finset.sum_congr rfl fun i _ => algebraMap_smul D.host.E (a i) (l i)`. Use function extensionality and compare the values at `i`. Use `Fintype.linearIndependent_iff.1 hli _ ha' i` as an intermediate fact.

Conclude with `(FaithfulSMul.algebraMap_injective (𝓞 D.host.E) D.host.E) (by rw [Pi.zero_apply, map_zero]; exact this)`. Establish `hrange : LinearMap.range ι ≤ X.Lb`. Introduce and unpack `_ ⟨a, rfl⟩`. Rewrite using `[hιap]`. Conclude with `Submodule.sum_mem _ fun i _ => X.Lb.smul_mem _ (hnL i)`.

Use `⟨ι, hinj, hrange, ?_⟩` and prove the remaining obligations. Establish `hspan : ∀ x ∈ X.Lb, x ∈ Submodule.span D.host.E (LinearMap.range ι : Set (VS D).V)`. Introduce `x hx`. Establish `hxW : x ∈ Wb X` using `Lb_le_alt X hx`. Establish `hx' : (⟨x, hxW⟩ : Wb X) ∈ Submodule.span D.host.E (Set.range w)` using `by rw [w.span_eq]; trivial`.

Establish `: ∀ z ∈ Submodule.span D.host.E (Set.range w), (z : (VS D).V) ∈ Submodule.span D.host.E (LinearMap.range ι : Set (VS D).V)`. Introduce `z hz`. Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem z hz`. Take `⟨i, rfl⟩` from `hz`.

Establish `hl : l i ∈ LinearMap.range ι` using `⟨Pi.single i 1, by rw [hιap]; simp [Pi.single_apply]⟩`. Establish `: ((w i : Wb X) : (VS D).V) = ((n i : D.host.E))⁻¹ • l i`. Simplify using `only [l]`. Rewrite using `[← Nat.cast_smul_eq_nsmul D.host.E, smul_smul, inv_mul_cancel₀ (by exact_mod_cast (hn i).ne'), one_smul]`. Rewrite using `[this]`.

Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span hl)`. Consider the case `zero => simp`. Consider the case `add a b _ _ ha hb => simpa using Submodule.add_mem _ ha hb`. Consider the case `smul c a _ ha => simpa using Submodule.smul_mem _ c ha`. Conclude with `this _ hx'`.

Take `⟨s, hs⟩` from `fg_Lb X`. Use `choose! m hm hmι using fun g (hg : g ∈ X.Lb) => Formalism.MainNotions.LatticeGluingRadicals.j_exists_nat_smul_mem (LinearMap.range ι) (hspan g hg)`. Use `set dN : ℕ := ∏ g ∈ s, m g with hdN`. Establish `hgs : ∀ g ∈ s, g ∈ X.Lb` using `fun g hg => hs ▸ Submodule.subset_span hg`. Establish `hdN0 : dN ≠ 0` using `Finset.prod_ne_zero_iff.2 fun g hg => (hm g (hgs g hg)).ne'`.

Use `⟨(dN : 𝓞 D.host.E), by exact_mod_cast hdN0, ?_⟩` and prove the remaining obligations. Rewrite using `[Submodule.ideal_span_singleton_smul]`. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Rewrite `hx` using `[← hs]`. Proceed by induction on `hx using Submodule.span_induction with`.

Consider the case `mem g hg`. Establish `e : (dN : 𝓞 D.host.E) • g = ((∏ g' ∈ s.erase g, m g' : ℕ) : 𝓞 D.host.E) • (m g • g)`. Rewrite using `[Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, hdN, ← Finset.mul_prod_erase s m hg, mul_comm, mul_smul]`. Use `show (dN : 𝓞 D.host.E) • g ∈ LinearMap.range ι`. Rewrite using `[e]`.

Conclude with `Submodule.smul_mem _ _ (hmι g (hgs g hg))`. Consider the case `zero => simp`. Consider the case `add a b _ _ ha hb => simpa [smul_add] using Submodule.add_mem _ ha hb`. Consider the case `smul c a _ ha => show (dN : 𝓞 D.host.E) • (c • a) ∈ LinearMap.range ι`. Rewrite using `[smul_comm]`.

Conclude with `Submodule.smul_mem _ c ha`.
-/
theorem free_sub : ∃ (ι : (Fin (D.R.k + 1) → 𝓞 D.host.E) →ₗ[𝓞 D.host.E] (VS D).V), Function.Injective ι ∧
    LinearMap.range ι ≤ X.Lb ∧ ∃ d : 𝓞 D.host.E, d ≠ 0 ∧ Ideal.span {d} • X.Lb ≤ LinearMap.range ι := by
  classical
  let w : Module.Basis (Fin (D.R.k + 1)) D.host.E (Wb X) := Module.finBasisOfFinrankEq D.host.E (Wb X) (finrank_Wb X)
  have hwL : ∀ i, ((w i : Wb X) : (VS D).V) ∈ Submodule.span D.host.E (X.Lb : Set (VS D).V) := by
    intro i; rw [span_Lb]; exact (w i).2
  choose n hn hnL using fun i => Formalism.MainNotions.LatticeGluingRadicals.j_exists_nat_smul_mem X.Lb (hwL i)
  let l : Fin (D.R.k + 1) → (VS D).V := fun i => n i • ((w i : Wb X) : (VS D).V)
  let ι : (Fin (D.R.k + 1) → 𝓞 D.host.E) →ₗ[𝓞 D.host.E] (VS D).V := Fintype.linearCombination (𝓞 D.host.E) l
  have hιap : ∀ a, ι a = ∑ i, a i • l i := fun a => by simp [ι, Fintype.linearCombination_apply]
  have hli : LinearIndependent D.host.E l := by
    have h1 : LinearIndependent D.host.E (fun i => ((w i : Wb X) : (VS D).V)) :=
      (LinearIndependent.map' w.linearIndependent (Wb X).subtype (Submodule.ker_subtype _))
    have h2 := h1.units_smul (fun i => Units.mk0 ((n i : ℕ) : D.host.E) (by exact_mod_cast (hn i).ne'))
    convert h2 using 1
    funext i
    simp only [l, Pi.smul_apply', Units.smul_def, Units.val_mk0]
    rw [Nat.cast_smul_eq_nsmul]
  have hinj : Function.Injective ι := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro a ha
    rw [LinearMap.mem_ker, hιap] at ha
    have ha' : ∑ i, ((a i : 𝓞 D.host.E) : D.host.E) • l i = 0 := by
      rw [← ha]; exact Finset.sum_congr rfl fun i _ => algebraMap_smul D.host.E (a i) (l i)
    funext i
    have := Fintype.linearIndependent_iff.1 hli _ ha' i
    exact (FaithfulSMul.algebraMap_injective (𝓞 D.host.E) D.host.E) (by rw [Pi.zero_apply, map_zero]; exact this)
  have hrange : LinearMap.range ι ≤ X.Lb := by
    rintro _ ⟨a, rfl⟩
    rw [hιap]
    exact Submodule.sum_mem _ fun i _ => X.Lb.smul_mem _ (hnL i)
  refine ⟨ι, hinj, hrange, ?_⟩

  have hspan : ∀ x ∈ X.Lb, x ∈ Submodule.span D.host.E (LinearMap.range ι : Set (VS D).V) := by
    intro x hx
    have hxW : x ∈ Wb X := Lb_le_alt X hx
    have hx' : (⟨x, hxW⟩ : Wb X) ∈ Submodule.span D.host.E (Set.range w) := by rw [w.span_eq]; trivial
    have : ∀ z ∈ Submodule.span D.host.E (Set.range w), (z : (VS D).V) ∈
        Submodule.span D.host.E (LinearMap.range ι : Set (VS D).V) := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨i, rfl⟩ := hz
        have hl : l i ∈ LinearMap.range ι := ⟨Pi.single i 1, by rw [hιap]; simp [Pi.single_apply]⟩
        have : ((w i : Wb X) : (VS D).V) = ((n i : D.host.E))⁻¹ • l i := by
          simp only [l]
          rw [← Nat.cast_smul_eq_nsmul D.host.E, smul_smul, inv_mul_cancel₀ (by exact_mod_cast (hn i).ne'), one_smul]
        rw [this]
        exact Submodule.smul_mem _ _ (Submodule.subset_span hl)
      | zero => simp
      | add a b _ _ ha hb => simpa using Submodule.add_mem _ ha hb
      | smul c a _ ha => simpa using Submodule.smul_mem _ c ha
    exact this _ hx'
  obtain ⟨s, hs⟩ := fg_Lb X
  choose! m hm hmι using fun g (hg : g ∈ X.Lb) => Formalism.MainNotions.LatticeGluingRadicals.j_exists_nat_smul_mem (LinearMap.range ι) (hspan g hg)
  set dN : ℕ := ∏ g ∈ s, m g with hdN
  have hgs : ∀ g ∈ s, g ∈ X.Lb := fun g hg => hs ▸ Submodule.subset_span hg
  have hdN0 : dN ≠ 0 := Finset.prod_ne_zero_iff.2 fun g hg => (hm g (hgs g hg)).ne'
  refine ⟨(dN : 𝓞 D.host.E), by exact_mod_cast hdN0, ?_⟩
  rw [Submodule.ideal_span_singleton_smul]
  rintro _ ⟨x, hx, rfl⟩
  rw [← hs] at hx
  induction hx using Submodule.span_induction with
  | mem g hg =>
    have e : (dN : 𝓞 D.host.E) • g = ((∏ g' ∈ s.erase g, m g' : ℕ) : 𝓞 D.host.E) • (m g • g) := by
      rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, hdN, ← Finset.mul_prod_erase s m hg, mul_comm, mul_smul]
    show (dN : 𝓞 D.host.E) • g ∈ LinearMap.range ι
    rw [e]; exact Submodule.smul_mem _ _ (hmι g (hgs g hg))
  | zero => simp
  | add a b _ _ ha hb => simpa [smul_add] using Submodule.add_mem _ ha hb
  | smul c a _ ha =>
    show (dN : 𝓞 D.host.E) • (c • a) ∈ LinearMap.range ι
    rw [smul_comm]; exact Submodule.smul_mem _ c ha

instance nzsd : NoZeroSMulDivisors (𝓞 D.host.E) (VS D).V :=
  ⟨fun {c x} h => by
    rw [← algebraMap_smul D.host.E c x] at h
    rcases smul_eq_zero.1 h with h | h
    · left; exact (map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).1 h
    · right; exact h⟩

/- English proof (translation)
Use `haveI := isNoetherian_of_fg_of_noetherian L hL`. Establish `h1 : (N.comap L.subtype).FG` using `IsNoetherian.noetherian _`. Establish `h2 : (N.comap L.subtype).map L.subtype = N`. Rewrite using `[Submodule.map_comap_subtype, inf_eq_right.mpr h]`. Rewrite using `[← h2]`.

Conclude with `h1.map _`.
-/
theorem fg_of_le {N L : Submodule (𝓞 D.host.E) (VS D).V} (h : N ≤ L) (hL : L.FG) : N.FG := by
  haveI := isNoetherian_of_fg_of_noetherian L hL
  have h1 : (N.comap L.subtype).FG := IsNoetherian.noetherian _
  have h2 : (N.comap L.subtype).map L.subtype = N := by
    rw [Submodule.map_comap_subtype, inf_eq_right.mpr h]
  rw [← h2]
  exact h1.map _

/- English proof (translation)
Establish `h1 : (N.map (a • LinearMap.id)).FG`. Apply `fg_of_le _ hL` to reduce the goal to its premises. Introduce `x hx`. Take `⟨y, hy, rfl⟩` from `Submodule.mem_map.mp hx`. Apply `h` to reduce the goal to its premises.

Rewrite using `[LinearMap.smul_apply, LinearMap.id_apply]`. Conclude with `Submodule.smul_mem_smul (Ideal.mem_span_singleton_self a) hy`. Conclude with `Submodule.fg_of_fg_map_injective _ (fun x y hxy => smul_right_injective (VS D).V ha (by simpa using hxy)) h1`.
-/
theorem fg_of_smul_le {N L : Submodule (𝓞 D.host.E) (VS D).V} (a : 𝓞 D.host.E) (ha : a ≠ 0)
    (h : Ideal.span {a} • N ≤ L) (hL : L.FG) : N.FG := by
  have h1 : (N.map (a • LinearMap.id)).FG := by
    apply fg_of_le _ hL
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
    apply h
    rw [LinearMap.smul_apply, LinearMap.id_apply]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self a) hy
  exact Submodule.fg_of_fg_map_injective _ (fun x y hxy => smul_right_injective (VS D).V ha (by simpa using hxy)) h1

/- English proof (translation)
Conclude with `le_antisymm (F5 X) (F6 X)`.
-/
theorem dDual_eq : (differentIdeal ℤ (𝓞 D.host.E)) • Ldual X = X.Lb := by
  exact le_antisymm (F5 X) (F6 X)

/- English proof (translation)
Conclude with `Submodule.smul_mono_left ((Ideal.span_singleton_le_iff_mem I).mpr (Ideal.absNorm_mem I))`.
-/
theorem absNorm_mem_smul (I : Ideal (𝓞 D.host.E)) (N : Submodule (𝓞 D.host.E) (VS D).V) :
    Ideal.span {((Ideal.absNorm I : ℕ) : 𝓞 D.host.E)} • N ≤ I • N := by
  exact Submodule.smul_mono_left ((Ideal.span_singleton_le_iff_mem I).mpr (Ideal.absNorm_mem I))

/- English proof (translation)
Conclude with `fun x hx => hx.1`.
-/
theorem dual_lattice_le_w : Ldual X ≤ (Wb X).restrictScalars (𝓞 D.host.E) := by
  exact fun x hx => hx.1

/- English proof (translation)
Take `⟨ι, hι, hιL, d, hd, hdL⟩` from `free_sub X`. Establish `h𝔇 : differentIdeal ℤ (𝓞 D.host.E) ≠ ⊥` using `differentIdeal_ne_bot`. Use `set a : 𝓞 D.host.E := ((Ideal.absNorm (differentIdeal ℤ (𝓞 D.host.E)) : ℕ) : 𝓞 D.host.E)`. Establish `ha : a ≠ 0`. Simplify using `only [a]`.

Conclude with `(Ideal.absNorm_eq_zero_iff.not.2 h𝔇)` after adjusting the coercions. Establish `haL : Ideal.span {a} • Ldual X ≤ X.Lb` using `(absNorm_mem_smul _ _).trans (dDual_eq X).le`. Establish `hfg : (Ldual X).FG` using `fg_of_smul_le a ha haL (fg_Lb X)`. Establish `hdd : Ideal.span {d * a} • Ldual X ≤ LinearMap.range ι`. Rewrite using `[← Ideal.span_singleton_mul_span_singleton, Submodule.mul_smul]`.

Conclude with `(Submodule.smul_mono le_rfl haL).trans hdL`. Establish `h` using `relIndex_eq (D.R.k + 1) _ h𝔇 (Ldual X) hfg (hdepW X _ (dual_lattice_le_w X)) ι hι (hιL.trans (Lb_le_Ldual X)) (d * a) (mul_ne_zero hd ha) hdd`. Rewrite `h` using `[dDual_eq X, NumberField.absNorm_differentIdeal D.host.E (𝓞 D.host.E)]`. Conclude with `h`.
-/
theorem idx_dual : (X.Lb.toAddSubgroup).relIndex (Ldual X).toAddSubgroup = (discr D.host.E).natAbs ^ (D.R.k + 1) := by
  obtain ⟨ι, hι, hιL, d, hd, hdL⟩ := free_sub X
  have h𝔇 : differentIdeal ℤ (𝓞 D.host.E) ≠ ⊥ := differentIdeal_ne_bot
  set a : 𝓞 D.host.E := ((Ideal.absNorm (differentIdeal ℤ (𝓞 D.host.E)) : ℕ) : 𝓞 D.host.E)
  have ha : a ≠ 0 := by
    simp only [a]; exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.2 h𝔇)
  have haL : Ideal.span {a} • Ldual X ≤ X.Lb := (absNorm_mem_smul _ _).trans (dDual_eq X).le
  have hfg : (Ldual X).FG := fg_of_smul_le a ha haL (fg_Lb X)
  have hdd : Ideal.span {d * a} • Ldual X ≤ LinearMap.range ι := by
    rw [← Ideal.span_singleton_mul_span_singleton, Submodule.mul_smul]
    exact (Submodule.smul_mono le_rfl haL).trans hdL
  have h := relIndex_eq (D.R.k + 1) _ h𝔇 (Ldual X) hfg (hdepW X _ (dual_lattice_le_w X)) ι hι
    (hιL.trans (Lb_le_Ldual X)) (d * a) (mul_ne_zero hd ha) hdd
  rw [dDual_eq X, NumberField.absNorm_differentIdeal D.host.E (𝓞 D.host.E)] at h
  exact h

/- English proof (translation)
Unfold `aaD`. Rewrite using `[FractionalIdeal.coeIdeal_pow, ← zpow_natCast, ← zpow_neg]`. Use `congr 1`. Move the coercions through the operations in `[Nat.cast_sub b.2.le]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem aaD_inv (b : Fin D.R.rS) :
    aaD D b = (((Formalism.L2.SG.NGCut.LeadingMinorIntegrality.dI D ^ (D.R.rS - (b : ℕ)) : Ideal (𝓞 D.host.E)) :
      FractionalIdeal (𝓞 D.host.E)⁰ D.host.E))⁻¹ := by
  unfold aaD
  rw [FractionalIdeal.coeIdeal_pow, ← zpow_natCast, ← zpow_neg]
  congr 1
  push_cast [Nat.cast_sub b.2.le]; ring

/- English proof (translation)
Use `set I := Formalism.L2.SG.NGCut.LeadingMinorIntegrality.dI D ^ (D.R.rS - (b : ℕ)) with hI`. Establish `hI0 : (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0`. Rewrite using `[Ne, FractionalIdeal.coeIdeal_eq_zero]`. Conclude with `Formalism.L2.SG.NGCut.LeadingMinorIntegrality.dI_ne_bot _`. Establish `hinv` using `aaD_inv b`.

Rewrite `hinv` using `[← hI]`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.smul_le]`. Introduce `r hr x hx`. Unfold `aaLbS at hx`.

Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨c, hc, l, hl, rfl⟩` from `hy`. Establish `h1 : (r : D.host.E) * c ∈ (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)`. Establish `hc' : c ∈ (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)⁻¹` using `by rw [← hinv]; exact hc`.

Use `FractionalIdeal.mul_mem_mul ((FractionalIdeal.mem_coeIdeal _).2 ⟨r, hr, rfl⟩) hc'` as an intermediate fact. Rewrite `this` using `[mul_inv_cancel₀ hI0]`. Then use the resulting hypothesis. Take `⟨o, ho⟩` from `(FractionalIdeal.mem_one_iff _).1 h1`. Establish `: r • (c • l) = o • l` using `by rw [← algebraMap_smul D.host.E r, smul_smul, ← ho, algebraMap_smul]`. Rewrite using `[this]`.

Conclude with `X.Lb.smul_mem o hl`. Consider the case `zero => simp`. Consider the case `add a b' _ _ ha hb => rw [smul_add]`. Conclude with `X.Lb.add_mem ha hb`. Consider the case `smul c a _ ha => rw [smul_comm]`.

Conclude with `X.Lb.smul_mem c ha`. Introduce `l hl`. Establish `h1 : (1 : D.host.E) ∈ (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) * (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)⁻¹`. Rewrite using `[mul_inv_cancel₀ hI0]`. Conclude with `FractionalIdeal.one_mem_one _`.

Establish `key : ∀ a ∈ (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) * (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)⁻¹, a • l ∈ I • aaLbS X b`. Introduce `a ha`. Use `FractionalIdeal.mul_induction_on ha ?_ ?_` and prove the remaining obligations. Introduce `i hi c hc`. Take `⟨r, hr, rfl⟩` from `(FractionalIdeal.mem_coeIdeal _).1 hi`.

Establish `hcl : c • l ∈ aaLbS X b` using `Submodule.subset_span ⟨c, by rw [hinv]; exact hc, l, hl, rfl⟩`. Establish `: (algebraMap (𝓞 D.host.E) D.host.E r * c) • l = r • (c • l)` using `by rw [mul_smul, algebraMap_smul]`. Rewrite using `[this]`. Conclude with `Submodule.smul_mem_smul hr hcl`. Introduce `x y hx hy`.

Rewrite using `[add_smul]`. Conclude with `Submodule.add_mem _ hx hy`. Simplify using `using key 1 h1`.
-/
theorem smul_aaLbS (b : Fin D.R.rS) :
    (Formalism.L2.SG.NGCut.LeadingMinorIntegrality.dI D ^ (D.R.rS - (b : ℕ))) • aaLbS X b = X.Lb := by
  set I := Formalism.L2.SG.NGCut.LeadingMinorIntegrality.dI D ^ (D.R.rS - (b : ℕ)) with hI
  have hI0 : (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 := by
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero]; exact Formalism.L2.SG.NGCut.LeadingMinorIntegrality.dI_ne_bot _
  have hinv := aaD_inv b
  rw [← hI] at hinv
  apply le_antisymm
  · rw [Submodule.smul_le]
    intro r hr x hx
    unfold aaLbS at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨c, hc, l, hl, rfl⟩ := hy
      have h1 : (r : D.host.E) * c ∈ (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := by
        have hc' : c ∈ (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)⁻¹ := by rw [← hinv]; exact hc
        have := FractionalIdeal.mul_mem_mul ((FractionalIdeal.mem_coeIdeal _).2 ⟨r, hr, rfl⟩) hc'
        rwa [mul_inv_cancel₀ hI0] at this
      obtain ⟨o, ho⟩ := (FractionalIdeal.mem_one_iff _).1 h1
      have : r • (c • l) = o • l := by rw [← algebraMap_smul D.host.E r, smul_smul, ← ho, algebraMap_smul]
      rw [this]; exact X.Lb.smul_mem o hl
    | zero => simp
    | add a b' _ _ ha hb => rw [smul_add]; exact X.Lb.add_mem ha hb
    | smul c a _ ha => rw [smul_comm]; exact X.Lb.smul_mem c ha
  · intro l hl
    have h1 : (1 : D.host.E) ∈ (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) * (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)⁻¹ := by
      rw [mul_inv_cancel₀ hI0]; exact FractionalIdeal.one_mem_one _
    have key : ∀ a ∈ (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) * (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)⁻¹,
        a • l ∈ I • aaLbS X b := by
      intro a ha
      refine FractionalIdeal.mul_induction_on ha ?_ ?_
      · intro i hi c hc
        obtain ⟨r, hr, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hi
        have hcl : c • l ∈ aaLbS X b := Submodule.subset_span ⟨c, by rw [hinv]; exact hc, l, hl, rfl⟩
        have : (algebraMap (𝓞 D.host.E) D.host.E r * c) • l = r • (c • l) := by rw [mul_smul, algebraMap_smul]
        rw [this]; exact Submodule.smul_mem_smul hr hcl
      · intro x y hx hy; rw [add_smul]; exact Submodule.add_mem _ hx hy
    simpa using key 1 h1

/- English proof (translation)
Apply `Submodule.span_le.mpr` to reduce the goal to its premises. Introduce and unpack `y ⟨c, -, l, hl, rfl⟩`. Conclude with `(Wb X).smul_mem c (Lb_le_alt X hl)`.
-/
theorem lattice_b_le_w (b : Fin D.R.rS) : aaLbS X b ≤ (Wb X).restrictScalars (𝓞 D.host.E) := by
  apply Submodule.span_le.mpr
  rintro y ⟨c, -, l, hl, rfl⟩
  exact (Wb X).smul_mem c (Lb_le_alt X hl)

/- English proof (translation)
Take `⟨ι, hι, hιL, d, hd, hdL⟩` from `free_sub X`. Use `set I := Formalism.L2.SG.NGCut.LeadingMinorIntegrality.dI D ^ (D.R.rS - (b : ℕ)) with hI`. Establish `hIb : I ≠ ⊥` using `Formalism.L2.SG.NGCut.LeadingMinorIntegrality.dI_ne_bot _`. Use `set a : 𝓞 D.host.E := ((Ideal.absNorm I : ℕ) : 𝓞 D.host.E)`. Establish `ha : a ≠ 0` using `by simp only [a]; exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.2 hIb)`.

Establish `haL : Ideal.span {a} • aaLbS X b ≤ X.Lb` using `(absNorm_mem_smul _ _).trans (smul_aaLbS X b).le`. Establish `hdd : Ideal.span {d * a} • aaLbS X b ≤ LinearMap.range ι`. Rewrite using `[← Ideal.span_singleton_mul_span_singleton, Submodule.mul_smul]`. Conclude with `(Submodule.smul_mono le_rfl haL).trans hdL`. Establish `h` using `relIndex_eq (D.R.k + 1) I hIb (aaLbS X b) (fg_aaLbS X b) (hdepW X _ (lattice_b_le_w X b)) ι hι (hιL.trans (Lb_le_aaLbS X b)) (d * a) (mul_ne_zero hd ha) hdd`.

Rewrite `h` using `[smul_aaLbS X b]`. Rewrite using `[h, hI, map_pow, Formalism.L2.SG.NGCut.LeadingMinorIntegrality.dI, Formalism.L2.SG.Pf.NcReal.JX.CovB.absNorm_ddS_ideal]`.
-/
theorem idx_M (b : Fin D.R.rS) : (X.Lb.toAddSubgroup).relIndex (aaLbS X b).toAddSubgroup =
    (((discr D.host.F).natAbs ^ 2) ^ (D.R.rS - (b : ℕ))) ^ (D.R.k + 1) := by
  obtain ⟨ι, hι, hιL, d, hd, hdL⟩ := free_sub X
  set I := Formalism.L2.SG.NGCut.LeadingMinorIntegrality.dI D ^ (D.R.rS - (b : ℕ)) with hI
  have hIb : I ≠ ⊥ := Formalism.L2.SG.NGCut.LeadingMinorIntegrality.dI_ne_bot _
  set a : 𝓞 D.host.E := ((Ideal.absNorm I : ℕ) : 𝓞 D.host.E)
  have ha : a ≠ 0 := by simp only [a]; exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.2 hIb)
  have haL : Ideal.span {a} • aaLbS X b ≤ X.Lb := (absNorm_mem_smul _ _).trans (smul_aaLbS X b).le
  have hdd : Ideal.span {d * a} • aaLbS X b ≤ LinearMap.range ι := by
    rw [← Ideal.span_singleton_mul_span_singleton, Submodule.mul_smul]
    exact (Submodule.smul_mono le_rfl haL).trans hdL
  have h := relIndex_eq (D.R.k + 1) I hIb (aaLbS X b) (fg_aaLbS X b) (hdepW X _ (lattice_b_le_w X b)) ι hι
    (hιL.trans (Lb_le_aaLbS X b)) (d * a) (mul_ne_zero hd ha) hdd
  rw [smul_aaLbS X b] at h
  rw [h, hI, map_pow, Formalism.L2.SG.NGCut.LeadingMinorIntegrality.dI, Formalism.L2.SG.Pf.NcReal.JX.CovB.absNorm_ddS_ideal]

instance nzsdZ : NoZeroSMulDivisors ℤ (VS D).V :=
  ⟨fun {z x} h => by
    rw [← Int.cast_smul_eq_zsmul D.host.E z x] at h
    rcases smul_eq_zero.1 h with h | h
    · left; exact_mod_cast h
    · right; exact h⟩

def Gr {N : ℕ} (w : Fin N → (VS D).V) : Matrix (Fin N) (Fin N) ℚ :=
  Matrix.of fun i j => Algebra.trace ℚ D.host.E ((VS D).hT (w i) (w j))

/- English proof (translation)
Rewrite using `[map_zsmul, LinearMap.smul_apply, map_zsmul, zsmul_eq_mul]`.
-/
theorem trB_zsmul_left (z : ℤ) (x y : (VS D).V) :
    Algebra.trace ℚ D.host.E ((VS D).hT (z • x) y) = z * Algebra.trace ℚ D.host.E ((VS D).hT x y) := by
  rw [map_zsmul, LinearMap.smul_apply, map_zsmul, zsmul_eq_mul]

/- English proof (translation)
Rewrite using `[map_zsmul, map_zsmul, zsmul_eq_mul]`.
-/
theorem trB_zsmul_right (z : ℤ) (x y : (VS D).V) :
    Algebra.trace ℚ D.host.E ((VS D).hT x (z • y)) = z * Algebra.trace ℚ D.host.E ((VS D).hT x y) := by
  rw [map_zsmul, map_zsmul, zsmul_eq_mul]

/- English proof (translation)
Rewrite using `[map_sum, LinearMap.sum_apply, map_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => trB_zsmul_left (c i) (w i) y`.
-/
theorem trB_sum_left {N : ℕ} (c : Fin N → ℤ) (w : Fin N → (VS D).V) (y : (VS D).V) :
    Algebra.trace ℚ D.host.E ((VS D).hT (∑ i, c i • w i) y) =
      ∑ i, (c i : ℚ) * Algebra.trace ℚ D.host.E ((VS D).hT (w i) y) := by
  rw [map_sum, LinearMap.sum_apply, map_sum]
  exact Finset.sum_congr rfl fun i _ => trB_zsmul_left (c i) (w i) y

/- English proof (translation)
Rewrite using `[map_sum, map_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => trB_zsmul_right (c i) x (w i)`.
-/
theorem trB_sum_right {N : ℕ} (c : Fin N → ℤ) (w : Fin N → (VS D).V) (x : (VS D).V) :
    Algebra.trace ℚ D.host.E ((VS D).hT x (∑ i, c i • w i)) =
      ∑ i, (c i : ℚ) * Algebra.trace ℚ D.host.E ((VS D).hT x (w i)) := by
  rw [map_sum, map_sum]
  exact Finset.sum_congr rfl fun i _ => trB_zsmul_right (c i) x (w i)

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [Gr, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, hw, trB_sum_left, trB_sum_right, Finset.mul_sum, Finset.sum_mul]`. Use `first`. Consider the case `exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring`. Consider the case `(rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)`.

Consider the case `(conv_rhs => rw [Finset.sum_comm])`. Conclude with `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring`.
-/
theorem gr_change {N : ℕ} (w w' : Fin N → (VS D).V) (A : Matrix (Fin N) (Fin N) ℤ)
    (hw : ∀ j, w' j = ∑ i, A i j • w i) :
    Gr w' = (A.map (Int.cast : ℤ → ℚ)).transpose * Gr w * A.map (Int.cast : ℤ → ℚ) := by
  ext i j
  simp only [Gr, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, hw,
    trB_sum_left, trB_sum_right, Finset.mul_sum, Finset.sum_mul]
  first
    | exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    | (rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)
    | (conv_rhs => rw [Finset.sum_comm])
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/- English proof (translation)
Establish `h : (A.map (Int.cast : ℤ → ℚ)).det = ((A.det : ℤ) : ℚ)` using `((Int.castRingHom ℚ).map_det A).symm`. Rewrite using `[gr_change w w' A hw, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem det_gr_change {N : ℕ} (w w' : Fin N → (VS D).V) (A : Matrix (Fin N) (Fin N) ℤ)
    (hw : ∀ j, w' j = ∑ i, A i j • w i) :
    (Gr w').det = ((A.det : ℤ) : ℚ) ^ 2 * (Gr w).det := by
  have h : (A.map (Int.cast : ℤ → ℚ)).det = ((A.det : ℤ) : ℚ) := ((Int.castRingHom ℚ).map_det A).symm
  rw [gr_change w w' A hw, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h]
  ring

/- English proof (translation)
Simplify using `only [Module.Basis.toMatrix_apply]`. Use `conv_lhs => rw [← b.sum_repr (v j)]`. Rewrite using `[Submodule.coe_sum]`. Simplify using `only [Submodule.coe_smul]`.
-/
theorem basis_expand {M : Submodule ℤ (VS D).V} {N : ℕ} (b : Module.Basis (Fin N) ℤ M) (v : Fin N → M) (j : Fin N) :
    ((v j : M) : (VS D).V) = ∑ i, (b.toMatrix v i j) • ((b i : M) : (VS D).V) := by
  simp only [Module.Basis.toMatrix_apply]
  conv_lhs => rw [← b.sum_repr (v j)]
  rw [Submodule.coe_sum]
  simp only [Submodule.coe_smul]

def DetHOne : Prop :=
  ∀ {D : D7} (X : HidaSetting D) {N : ℕ} (ℓ : Module.Basis (Fin N) ℤ (X.Lb.restrictScalars ℤ))
    (ℓs : Module.Basis (Fin N) ℤ ((Ldual X).restrictScalars ℤ)),
    |(Matrix.of fun k j => Algebra.trace ℚ D.host.E ((VS D).hT (ℓs k : (VS D).V) (ℓ j : (VS D).V))).det| = 1

/- English proof (translation)
Establish `h1 : Module.Finite (𝓞 D.host.E) L` using `Module.Finite.iff_fg.2 hL`. Establish `h2 : Module.Finite ℤ L` using `Module.Finite.trans (𝓞 D.host.E) _`. Conclude with `Module.Finite.equiv ((Submodule.restrictScalarsEquiv ℤ (𝓞 D.host.E) (VS D).V L).restrictScalars ℤ).symm`.
-/
theorem fin_Z (L : Submodule (𝓞 D.host.E) (VS D).V) (hL : L.FG) : Module.Finite ℤ (L.restrictScalars ℤ) := by
  have h1 : Module.Finite (𝓞 D.host.E) L := Module.Finite.iff_fg.2 hL
  have h2 : Module.Finite ℤ L := Module.Finite.trans (𝓞 D.host.E) _
  exact Module.Finite.equiv ((Submodule.restrictScalarsEquiv ℤ (𝓞 D.host.E) (VS D).V L).restrictScalars ℤ).symm

/- English proof (translation)
Use `fin_Z A hA` as an intermediate fact. Use `fin_Z B hB` as an intermediate fact. Apply `le_antisymm` to reduce the goal to its premises. Conclude with `LinearMap.finrank_le_finrank_of_injective (f := Submodule.inclusion (show A.restrictScalars ℤ ≤ B.restrictScalars ℤ from hAB)) (Submodule.inclusion_injective _)`. Establish `hmem : ∀ x ∈ B, (c : ℤ) • x ∈ A`.

Introduce `x hx`. Apply `hcB` to reduce the goal to its premises. Rewrite using `[Submodule.ideal_span_singleton_smul]`. Use `⟨x, hx, ?_⟩` and prove the remaining obligations. Use `show (c : 𝓞 D.host.E) • x = (c : ℤ) • x`.

Rewrite using `[natCast_zsmul, Nat.cast_smul_eq_nsmul]`. Set `f : (B.restrictScalars ℤ) →ₗ[ℤ] (A.restrictScalars ℤ)` to `LinearMap.codRestrict (A.restrictScalars ℤ) ((c : ℤ) • (B.restrictScalars ℤ).subtype) (fun x => hmem x x.2)`. Use `LinearMap.finrank_le_finrank_of_injective (f := f) fun x y hxy => ?_` and prove the remaining obligations. Establish `h` using `congrArg Subtype.val hxy`. Simplify using `only [f, LinearMap.codRestrict_apply, LinearMap.smul_apply, Submodule.coe_subtype] at h`.

Establish `: (c : ℤ) • ((x : (VS D).V) - y) = 0` using `by rw [smul_sub]; exact sub_eq_zero.2 h`. Conclude with `Subtype.ext (sub_eq_zero.1 ((smul_eq_zero.1 this).resolve_left (by exact_mod_cast hc)))`.
-/
theorem finrank_eq_of_sandwich (A B : Submodule (𝓞 D.host.E) (VS D).V) (hA : A.FG) (hB : B.FG) (hAB : A ≤ B)
    (c : ℕ) (hc : c ≠ 0) (hcB : Ideal.span {(c : 𝓞 D.host.E)} • B ≤ A) :
    Module.finrank ℤ (A.restrictScalars ℤ) = Module.finrank ℤ (B.restrictScalars ℤ) := by
  have := fin_Z A hA
  have := fin_Z B hB
  apply le_antisymm
  · exact LinearMap.finrank_le_finrank_of_injective (f := Submodule.inclusion (show A.restrictScalars ℤ ≤ B.restrictScalars ℤ from hAB))
      (Submodule.inclusion_injective _)
  · have hmem : ∀ x ∈ B, (c : ℤ) • x ∈ A := by
      intro x hx
      apply hcB
      rw [Submodule.ideal_span_singleton_smul]
      refine ⟨x, hx, ?_⟩
      show (c : 𝓞 D.host.E) • x = (c : ℤ) • x
      rw [natCast_zsmul, Nat.cast_smul_eq_nsmul]
    let f : (B.restrictScalars ℤ) →ₗ[ℤ] (A.restrictScalars ℤ) :=
      LinearMap.codRestrict (A.restrictScalars ℤ) ((c : ℤ) • (B.restrictScalars ℤ).subtype) (fun x => hmem x x.2)
    refine LinearMap.finrank_le_finrank_of_injective (f := f) fun x y hxy => ?_
    have h := congrArg Subtype.val hxy
    simp only [f, LinearMap.codRestrict_apply, LinearMap.smul_apply, Submodule.coe_subtype] at h
    have : (c : ℤ) • ((x : (VS D).V) - y) = 0 := by rw [smul_sub]; exact sub_eq_zero.2 h
    exact Subtype.ext (sub_eq_zero.1 ((smul_eq_zero.1 this).resolve_left (by exact_mod_cast hc)))

/- English proof (translation)
Introduce `D X b N m hN`. Establish `hMfg : (aaLbS X b).FG` using `fg_aaLbS X b`. Establish `hLfg : X.Lb.FG` using `fg_Lb X`. Use `set I := Formalism.L2.SG.NGCut.LeadingMinorIntegrality.dI D ^ (D.R.rS - (b : ℕ))`. Establish `hIb : I ≠ ⊥` using `Formalism.L2.SG.NGCut.LeadingMinorIntegrality.dI_ne_bot _`.

Establish `haM : Ideal.span {((Ideal.absNorm I : ℕ) : 𝓞 D.host.E)} • aaLbS X b ≤ X.Lb` using `(absNorm_mem_smul _ _).trans (smul_aaLbS X b).le`. Establish `ha0 : Ideal.absNorm I ≠ 0` using `Ideal.absNorm_eq_zero_iff.not.2 hIb`. Establish `h𝔇 : differentIdeal ℤ (𝓞 D.host.E) ≠ ⊥` using `differentIdeal_ne_bot`. Establish `haD : Ideal.span {((Ideal.absNorm (differentIdeal ℤ (𝓞 D.host.E)) : ℕ) : 𝓞 D.host.E)} • Ldual X ≤ X.Lb` using `(absNorm_mem_smul _ _).trans (dDual_eq X).le`. Establish `ha0' : Ideal.absNorm (differentIdeal ℤ (𝓞 D.host.E)) ≠ 0` using `Ideal.absNorm_eq_zero_iff.not.2 h𝔇`.

Establish `hLdfg : (Ldual X).FG` using `fg_of_smul_le _ (by exact_mod_cast ha0') haD hLfg`. Establish `hMfin : Module.Finite ℤ ((aaLbS X b).restrictScalars ℤ)` using `Module.Finite.of_basis m`. Establish `hrM : Module.finrank ℤ ((aaLbS X b).restrictScalars ℤ) = N` using `by rw [Module.finrank_eq_card_basis m, Fintype.card_fin]`. Establish `hrL : Module.finrank ℤ (X.Lb.restrictScalars ℤ) = N`. Rewrite using `[finrank_eq_of_sandwich X.Lb (aaLbS X b) hLfg hMfg (Lb_le_aaLbS X b) _ ha0 haM, hrM]`.

Establish `hrLd : Module.finrank ℤ ((Ldual X).restrictScalars ℤ) = N`. Rewrite using `[← finrank_eq_of_sandwich X.Lb (Ldual X) hLfg hLdfg (Lb_le_Ldual X) _ ha0' haD, hrL]`. Use `fin_Z X.Lb hLfg` as an intermediate fact. Use `fin_Z (Ldual X) hLdfg` as an intermediate fact. Establish `: Module.Free ℤ (X.Lb.restrictScalars ℤ)` using `Module.free_of_finite_type_torsion_free'`.

Establish `: Module.Free ℤ ((Ldual X).restrictScalars ℤ)` using `Module.free_of_finite_type_torsion_free'`. Set `ℓ : Module.Basis (Fin N) ℤ (X.Lb.restrictScalars ℤ)` to `Module.finBasisOfFinrankEq ℤ _ hrL`. Set `ℓs : Module.Basis (Fin N) ℤ ((Ldual X).restrictScalars ℤ)` to `Module.finBasisOfFinrankEq ℤ _ hrLd`. Establish `hLM : X.Lb.toAddSubgroup ≤ (aaLbS X b).toAddSubgroup` using `Lb_le_aaLbS X b`. Establish `e1` using `AddSubgroup.relIndex_eq_natAbs_det X.Lb.toAddSubgroup (aaLbS X b).toAddSubgroup hLM ℓ m`.

Rewrite `e1` using `[idx_M X b]`. Set `vA : Fin N → (aaLbS X b).restrictScalars ℤ` to `fun i => ⟨ℓ i, hLM (SetLike.coe_mem _)⟩`. Set `A` to `m.toMatrix vA`. Establish `e1' : (m.det vA).natAbs = (((discr D.host.F).natAbs ^ 2) ^ (D.R.rS - (b : ℕ))) ^ (D.R.k + 1)` using `e1.symm`. Rewrite `e1'` using `[Module.Basis.det_apply]`.

Establish `hA : ∀ j, ((ℓ j : X.Lb.restrictScalars ℤ) : (VS D).V) = ∑ i, A i j • ((m i : (aaLbS X b).restrictScalars ℤ) : (VS D).V)` using `fun j => basis_expand m vA j`. Establish `hGA` using `det_gr_change (fun i => ((m i : (aaLbS X b).restrictScalars ℤ) : (VS D).V)) (fun j => ((ℓ j : X.Lb.restrictScalars ℤ) : (VS D).V)) A hA`. Establish `hLLd : X.Lb.toAddSubgroup ≤ (Ldual X).toAddSubgroup` using `Lb_le_Ldual X`. Establish `e2` using `AddSubgroup.relIndex_eq_natAbs_det X.Lb.toAddSubgroup (Ldual X).toAddSubgroup hLLd ℓ ℓs`. Rewrite `e2` using `[idx_dual X]`.

Set `vC : Fin N → (Ldual X).restrictScalars ℤ` to `fun i => ⟨ℓ i, hLLd (SetLike.coe_mem _)⟩`. Set `C` to `ℓs.toMatrix vC`. Establish `e2' : (ℓs.det vC).natAbs = (discr D.host.E).natAbs ^ (D.R.k + 1)` using `e2.symm`. Rewrite `e2'` using `[Module.Basis.det_apply]`. Establish `hC : ∀ j, ((ℓ j : X.Lb.restrictScalars ℤ) : (VS D).V) = ∑ k, C k j • ((ℓs k : (Ldual X).restrictScalars ℤ) : (VS D).V)` using `fun j => basis_expand ℓs vC j`.

Set `H` to `Matrix.of fun k j => Algebra.trace ℚ D.host.E ((VS D).hT (ℓs k : (VS D).V) (ℓ j : (VS D).V))`. Establish `hGC : Gr (fun j => ((ℓ j : X.Lb.restrictScalars ℤ) : (VS D).V)) = (C.map (Int.cast : ℤ → ℚ)).transpose * H`. Use extensionality with `i j`. Simplify using `only [Gr, H, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]`. Rewrite using `[hC i, trB_sum_left]`.

Establish `hdetC : (C.map (Int.cast : ℤ → ℚ)).det = ((C.det : ℤ) : ℚ)`. Use `(RingHom.map_det (Int.castRingHom ℚ) C).symm` as an intermediate fact. Simplify using `using this`. Establish `hHdet` using `hH X ℓ ℓs`. Establish `hGm : (Gr (fun i => ((m i : (aaLbS X b).restrictScalars ℤ) : (VS D).V))) = Matrix.of fun i j => Algebra.trace ℚ D.host.E ((VS D).hT (m i : (VS D).V) (m j : (VS D).V))` using `rfl`.

Rewrite using `[← hGm]`. Establish `hAz : ((A.det : ℤ) : ℚ) ^ 2 = (((((discr D.host.F).natAbs ^ 2) ^ (D.R.rS - (b : ℕ))) ^ (D.R.k + 1) : ℕ) : ℚ) ^ 2`. Rewrite using `[← e1', Nat.cast_natAbs, Int.cast_abs, sq_abs]`. Establish `hLdet : |(Gr (fun j => ((ℓ j : X.Lb.restrictScalars ℤ) : (VS D).V))).det| = (((discr D.host.E).natAbs ^ (D.R.k + 1) : ℕ) : ℚ)`. Rewrite using `[hGC, Matrix.det_mul, Matrix.det_transpose, hdetC, abs_mul, hHdet, mul_one, ← e2', Nat.cast_natAbs, Int.cast_abs]`.

Establish `hA0 : ((A.det : ℤ) : ℚ) ≠ 0`. Introduce `h0`. Establish `: (((((discr D.host.F).natAbs ^ 2) ^ (D.R.rS - (b : ℕ))) ^ (D.R.k + 1) : ℕ) : ℚ) = 0`. Use `hAz; rw [h0] at this; exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this.symm` as an intermediate fact. Establish `hne : (discr D.host.F).natAbs ≠ 0` using `Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero _)`.

Conclude with `(pow_ne_zero _ (pow_ne_zero _ (pow_ne_zero _ hne))) (by exact_mod_cast this)` after adjusting the coercions. Establish `key : |(Gr (fun i => ((m i : (aaLbS X b).restrictScalars ℤ) : (VS D).V))).det| = (((discr D.host.E).natAbs ^ (D.R.k + 1) : ℕ) : ℚ) / (((((discr D.host.F).natAbs ^ 2) ^ (D.R.rS - (b : ℕ))) ^ (D.R.k + 1) : ℕ) : ℚ) ^ 2`. Establish `hP : (((((discr D.host.F).natAbs ^ 2) ^ (D.R.rS - (b : ℕ))) ^ (D.R.k + 1) : ℕ) : ℚ) ≠ 0`. Establish `hne : (discr D.host.F).natAbs ≠ 0` using `Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero _)`. Conclude with `pow_ne_zero _ (pow_ne_zero _ (pow_ne_zero _ hne))` after adjusting the coercions.

Rewrite using `[← hLdet, hGA, abs_mul, abs_pow, sq_abs, hAz]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[key]`. Establish `hN2 : (FractionalIdeal.absNorm (aaD D b) : ℚ) = ((((discr D.host.F).natAbs ^ 2) ^ (D.R.rS - (b : ℕ)) : ℕ) : ℚ)⁻¹`. Rewrite using `[aaD_inv b, map_inv₀, FractionalIdeal.coeIdeal_absNorm, map_pow, Formalism.L2.SG.NGCut.LeadingMinorIntegrality.dI, Formalism.L2.SG.Pf.NcReal.JX.CovB.absNorm_ddS_ideal]`.

Rewrite using `[hN2]`. Establish `hF : ((discr D.host.F : ℤ) : ℚ) ≠ 0` using `by exact_mod_cast NumberField.discr_ne_zero _`. Establish `hF' : |((discr D.host.F : ℤ) : ℚ)| ≠ 0` using `abs_ne_zero.2 hF`. Move the coercions through the operations in `[Nat.cast_natAbs, Int.cast_abs]`. Rewrite using `[inv_pow]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem trDetUnimod_of (hH : DetHOne) : TrDetUnimod := by
  intro D X b N m hN
  classical
  have hMfg : (aaLbS X b).FG := fg_aaLbS X b
  have hLfg : X.Lb.FG := fg_Lb X

  set I := Formalism.L2.SG.NGCut.LeadingMinorIntegrality.dI D ^ (D.R.rS - (b : ℕ))
  have hIb : I ≠ ⊥ := Formalism.L2.SG.NGCut.LeadingMinorIntegrality.dI_ne_bot _
  have haM : Ideal.span {((Ideal.absNorm I : ℕ) : 𝓞 D.host.E)} • aaLbS X b ≤ X.Lb :=
    (absNorm_mem_smul _ _).trans (smul_aaLbS X b).le
  have ha0 : Ideal.absNorm I ≠ 0 := Ideal.absNorm_eq_zero_iff.not.2 hIb
  have h𝔇 : differentIdeal ℤ (𝓞 D.host.E) ≠ ⊥ := differentIdeal_ne_bot
  have haD : Ideal.span {((Ideal.absNorm (differentIdeal ℤ (𝓞 D.host.E)) : ℕ) : 𝓞 D.host.E)} • Ldual X ≤ X.Lb :=
    (absNorm_mem_smul _ _).trans (dDual_eq X).le
  have ha0' : Ideal.absNorm (differentIdeal ℤ (𝓞 D.host.E)) ≠ 0 := Ideal.absNorm_eq_zero_iff.not.2 h𝔇
  have hLdfg : (Ldual X).FG := fg_of_smul_le _ (by exact_mod_cast ha0') haD hLfg

  have hMfin : Module.Finite ℤ ((aaLbS X b).restrictScalars ℤ) := Module.Finite.of_basis m
  have hrM : Module.finrank ℤ ((aaLbS X b).restrictScalars ℤ) = N := by rw [Module.finrank_eq_card_basis m, Fintype.card_fin]
  have hrL : Module.finrank ℤ (X.Lb.restrictScalars ℤ) = N := by
    rw [finrank_eq_of_sandwich X.Lb (aaLbS X b) hLfg hMfg (Lb_le_aaLbS X b) _ ha0 haM, hrM]
  have hrLd : Module.finrank ℤ ((Ldual X).restrictScalars ℤ) = N := by
    rw [← finrank_eq_of_sandwich X.Lb (Ldual X) hLfg hLdfg (Lb_le_Ldual X) _ ha0' haD, hrL]
  have := fin_Z X.Lb hLfg
  have := fin_Z (Ldual X) hLdfg
  have : Module.Free ℤ (X.Lb.restrictScalars ℤ) := Module.free_of_finite_type_torsion_free'
  have : Module.Free ℤ ((Ldual X).restrictScalars ℤ) := Module.free_of_finite_type_torsion_free'
  let ℓ : Module.Basis (Fin N) ℤ (X.Lb.restrictScalars ℤ) := Module.finBasisOfFinrankEq ℤ _ hrL
  let ℓs : Module.Basis (Fin N) ℤ ((Ldual X).restrictScalars ℤ) := Module.finBasisOfFinrankEq ℤ _ hrLd

  have hLM : X.Lb.toAddSubgroup ≤ (aaLbS X b).toAddSubgroup := Lb_le_aaLbS X b
  have e1 := AddSubgroup.relIndex_eq_natAbs_det X.Lb.toAddSubgroup (aaLbS X b).toAddSubgroup hLM ℓ m
  rw [idx_M X b] at e1
  let vA : Fin N → (aaLbS X b).restrictScalars ℤ := fun i => ⟨ℓ i, hLM (SetLike.coe_mem _)⟩
  let A := m.toMatrix vA
  have e1' : (m.det vA).natAbs = (((discr D.host.F).natAbs ^ 2) ^ (D.R.rS - (b : ℕ))) ^ (D.R.k + 1) := e1.symm
  rw [Module.Basis.det_apply] at e1'
  have hA : ∀ j, ((ℓ j : X.Lb.restrictScalars ℤ) : (VS D).V) = ∑ i, A i j • ((m i : (aaLbS X b).restrictScalars ℤ) : (VS D).V) :=
    fun j => basis_expand m vA j
  have hGA := det_gr_change (fun i => ((m i : (aaLbS X b).restrictScalars ℤ) : (VS D).V))
    (fun j => ((ℓ j : X.Lb.restrictScalars ℤ) : (VS D).V)) A hA

  have hLLd : X.Lb.toAddSubgroup ≤ (Ldual X).toAddSubgroup := Lb_le_Ldual X
  have e2 := AddSubgroup.relIndex_eq_natAbs_det X.Lb.toAddSubgroup (Ldual X).toAddSubgroup hLLd ℓ ℓs
  rw [idx_dual X] at e2
  let vC : Fin N → (Ldual X).restrictScalars ℤ := fun i => ⟨ℓ i, hLLd (SetLike.coe_mem _)⟩
  let C := ℓs.toMatrix vC
  have e2' : (ℓs.det vC).natAbs = (discr D.host.E).natAbs ^ (D.R.k + 1) := e2.symm
  rw [Module.Basis.det_apply] at e2'
  have hC : ∀ j, ((ℓ j : X.Lb.restrictScalars ℤ) : (VS D).V) = ∑ k, C k j • ((ℓs k : (Ldual X).restrictScalars ℤ) : (VS D).V) :=
    fun j => basis_expand ℓs vC j
  let H := Matrix.of fun k j => Algebra.trace ℚ D.host.E ((VS D).hT (ℓs k : (VS D).V) (ℓ j : (VS D).V))
  have hGC : Gr (fun j => ((ℓ j : X.Lb.restrictScalars ℤ) : (VS D).V)) = (C.map (Int.cast : ℤ → ℚ)).transpose * H := by
    ext i j
    simp only [Gr, H, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
    rw [hC i, trB_sum_left]
  have hdetC : (C.map (Int.cast : ℤ → ℚ)).det = ((C.det : ℤ) : ℚ) := by
    have := (RingHom.map_det (Int.castRingHom ℚ) C).symm
    simpa using this
  have hHdet := hH X ℓ ℓs

  have hGm : (Gr (fun i => ((m i : (aaLbS X b).restrictScalars ℤ) : (VS D).V))) =
      Matrix.of fun i j => Algebra.trace ℚ D.host.E ((VS D).hT (m i : (VS D).V) (m j : (VS D).V)) := rfl
  rw [← hGm]
  have hAz : ((A.det : ℤ) : ℚ) ^ 2 = (((((discr D.host.F).natAbs ^ 2) ^ (D.R.rS - (b : ℕ))) ^ (D.R.k + 1) : ℕ) : ℚ) ^ 2 := by
    rw [← e1', Nat.cast_natAbs, Int.cast_abs, sq_abs]
  have hLdet : |(Gr (fun j => ((ℓ j : X.Lb.restrictScalars ℤ) : (VS D).V))).det| =
      (((discr D.host.E).natAbs ^ (D.R.k + 1) : ℕ) : ℚ) := by
    rw [hGC, Matrix.det_mul, Matrix.det_transpose, hdetC, abs_mul, hHdet, mul_one, ← e2', Nat.cast_natAbs, Int.cast_abs]
  have hA0 : ((A.det : ℤ) : ℚ) ≠ 0 := by
    intro h0
    have : (((((discr D.host.F).natAbs ^ 2) ^ (D.R.rS - (b : ℕ))) ^ (D.R.k + 1) : ℕ) : ℚ) = 0 := by
      have := hAz; rw [h0] at this; exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this.symm
    have hne : (discr D.host.F).natAbs ≠ 0 := Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero _)
    exact_mod_cast (pow_ne_zero _ (pow_ne_zero _ (pow_ne_zero _ hne))) (by exact_mod_cast this)
  have key : |(Gr (fun i => ((m i : (aaLbS X b).restrictScalars ℤ) : (VS D).V))).det| =
      (((discr D.host.E).natAbs ^ (D.R.k + 1) : ℕ) : ℚ) /
        (((((discr D.host.F).natAbs ^ 2) ^ (D.R.rS - (b : ℕ))) ^ (D.R.k + 1) : ℕ) : ℚ) ^ 2 := by
    have hP : (((((discr D.host.F).natAbs ^ 2) ^ (D.R.rS - (b : ℕ))) ^ (D.R.k + 1) : ℕ) : ℚ) ≠ 0 := by
      have hne : (discr D.host.F).natAbs ≠ 0 := Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero _)
      exact_mod_cast pow_ne_zero _ (pow_ne_zero _ (pow_ne_zero _ hne))
    rw [← hLdet, hGA, abs_mul, abs_pow, sq_abs, hAz]
    field_simp
  rw [key]

  have hN2 : (FractionalIdeal.absNorm (aaD D b) : ℚ) =
      ((((discr D.host.F).natAbs ^ 2) ^ (D.R.rS - (b : ℕ)) : ℕ) : ℚ)⁻¹ := by
    rw [aaD_inv b, map_inv₀, FractionalIdeal.coeIdeal_absNorm, map_pow, Formalism.L2.SG.NGCut.LeadingMinorIntegrality.dI,
      Formalism.L2.SG.Pf.NcReal.JX.CovB.absNorm_ddS_ideal]
  rw [hN2]
  have hF : ((discr D.host.F : ℤ) : ℚ) ≠ 0 := by exact_mod_cast NumberField.discr_ne_zero _
  have hF' : |((discr D.host.F : ℤ) : ℚ)| ≠ 0 := abs_ne_zero.2 hF
  push_cast [Nat.cast_natAbs, Int.cast_abs]
  rw [inv_pow]
  field_simp
  ring

end Formalism.L2.SG.Pf.NcReal.JX.CovB.TrD
