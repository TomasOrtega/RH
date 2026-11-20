import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HalfData
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn

open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff in
open MeasureTheory IsDedekindDomain NumberField in
attribute [local instance] _root_.Formalism.BasicNotions.Host.cmStar in
/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Simplify to obtain the desired conclusion from the available facts. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components.

Simplify to obtain the desired conclusion from the available facts. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Replace the relevant objects with their definitions.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify to obtain the desired conclusion from the available facts. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
private theorem bijective_quot_mk_map_out {G₁ G₂ : Type} [Group G₁] [Group G₂] (κ : G₁ ≃* G₂)
    (P₁ Γ₁ : Subgroup G₁) (P₂ Γ₂ : Subgroup G₂) (hP : ∀ g, g ∈ P₁ ↔ κ g ∈ P₂)
    (hΓ : ∀ g, g ∈ Γ₁ ↔ κ g ∈ Γ₂) :
    Function.Bijective fun q : _root_.GlobalTheory.AutomorphicL2Unitary.Quot (P₁.subgroupOf Γ₁) =>
      _root_.GlobalTheory.AutomorphicL2Unitary.mk (P₂.subgroupOf Γ₂)
        (⟨κ (Quotient.out q : Γ₁), (hΓ _).1 (Quotient.out q : Γ₁).2⟩ : Γ₂) := by
  have hout : ∀ q : _root_.GlobalTheory.AutomorphicL2Unitary.Quot (P₁.subgroupOf Γ₁),
      _root_.GlobalTheory.AutomorphicL2Unitary.mk (P₁.subgroupOf Γ₁) (Quotient.out q) = q := by
    intro q
    unfold _root_.GlobalTheory.AutomorphicL2Unitary.mk
    exact Quotient.out_eq q
  constructor
  · intro q q' h
    simp only at h
    obtain ⟨p, hp⟩ := _root_.GlobalTheory.AutomorphicL2Unitary.mk_eq_iff.1 h
    have hp' : κ.symm ((p : Γ₂) : G₂) * (Quotient.out q : Γ₁) = (Quotient.out q' : Γ₁) := by
      apply κ.injective
      have := congrArg Subtype.val hp
      simpa using this
    have hmemΓ : κ.symm ((p : Γ₂) : G₂) ∈ Γ₁ := by
      rw [hΓ]; simpa using ((p : Γ₂)).2
    have hmemP : (⟨κ.symm ((p : Γ₂) : G₂), hmemΓ⟩ : Γ₁) ∈ P₁.subgroupOf Γ₁ := by
      rw [Subgroup.mem_subgroupOf, hP]
      simpa using Subgroup.mem_subgroupOf.1 p.2
    rw [← hout q, ← hout q']
    refine _root_.GlobalTheory.AutomorphicL2Unitary.mk_eq_iff.2 ⟨⟨_, hmemP⟩, ?_⟩
    ext
    simpa using hp'
  · intro q₂
    obtain ⟨y, rfl⟩ : ∃ y : Γ₂, _root_.GlobalTheory.AutomorphicL2Unitary.mk (P₂.subgroupOf Γ₂) y = q₂ := by
      refine ⟨Quotient.out q₂, ?_⟩
      unfold _root_.GlobalTheory.AutomorphicL2Unitary.mk
      exact Quotient.out_eq q₂
    have hx : κ.symm (y : G₂) ∈ Γ₁ := by
      rw [hΓ]; simpa using y.2
    refine ⟨_root_.GlobalTheory.AutomorphicL2Unitary.mk (P₁.subgroupOf Γ₁) ⟨_, hx⟩, ?_⟩
    obtain ⟨p, hp⟩ := _root_.GlobalTheory.AutomorphicL2Unitary.mk_eq_iff.1
      (hout (_root_.GlobalTheory.AutomorphicL2Unitary.mk (P₁.subgroupOf Γ₁) ⟨_, hx⟩)).symm
    simp only
    rw [← hp]
    have hmemΓ : κ ((p : Γ₁) : G₁) ∈ Γ₂ := (hΓ _).1 (p : Γ₁).2
    have hmemP : (⟨κ ((p : Γ₁) : G₁), hmemΓ⟩ : Γ₂) ∈ P₂.subgroupOf Γ₂ := by
      rw [Subgroup.mem_subgroupOf]
      exact (hP _).1 (Subgroup.mem_subgroupOf.1 p.2)
    refine (_root_.GlobalTheory.AutomorphicL2Unitary.mk_eq_iff.2 ⟨⟨_, hmemP⟩, ?_⟩).symm
    ext
    simp

open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff in
open MeasureTheory IsDedekindDomain NumberField in
attribute [local instance] _root_.Formalism.BasicNotions.Host.cmStar in

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Replace the relevant objects with their definitions. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument.

Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion repeatedly using the stated equalities. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion repeatedly using the stated equalities. A detailed English derivation is pending.
-/
theorem _root_.GlobalTheory.StdUnn.cosetSum_along_mulEquiv : ∀ (G₁ G₂ : Type) [Group G₁] [Group G₂] (κ : G₁ ≃* G₂) (P₁ Γ₁ : Subgroup G₁) (P₂ Γ₂ : Subgroup G₂), (∀ g, g ∈ P₁ ↔ κ g ∈ P₂) → (∀ g, g ∈ Γ₁ ↔ κ g ∈ Γ₂) → ∀ (Φ₂ : G₂ → ℂ) (x : G₁) (c : ℂ) (Φ₁ : G₁ → ℂ), (∀ g, Φ₁ g = c * Φ₂ (κ (g * x))) → _root_.GlobalTheory.AutomorphicL2Unitary.LeftInv (P₂ ⊓ Γ₂) Φ₂ → _root_.GlobalTheory.AutomorphicL2Unitary.LeftInv (P₁ ⊓ Γ₁) Φ₁ ∧ ∀ g, (_root_.GlobalTheory.Eis.CosetConv P₂ Γ₂ Φ₂ (κ (g * x)) → _root_.GlobalTheory.Eis.CosetConv P₁ Γ₁ Φ₁ g) ∧ _root_.GlobalTheory.Eis.cosetSum P₁ Γ₁ Φ₁ g = c * _root_.GlobalTheory.Eis.cosetSum P₂ Γ₂ Φ₂ (κ (g * x)) := by
  intro G₁ G₂ _ _ κ P₁ Γ₁ P₂ Γ₂ hP hΓ Φ₂ x c Φ₁ hΦ hinv₂
  have hinv₁ : _root_.GlobalTheory.AutomorphicL2Unitary.LeftInv (P₁ ⊓ Γ₁) Φ₁ := by
    unfold _root_.GlobalTheory.AutomorphicL2Unitary.LeftInv at hinv₂ ⊢
    intro γ hγ g
    have hγ₂ : κ γ ∈ P₂ ⊓ Γ₂ :=
      Subgroup.mem_inf.2 ⟨(hP γ).1 (Subgroup.mem_inf.1 hγ).1, (hΓ γ).1 (Subgroup.mem_inf.1 hγ).2⟩
    rw [hΦ, hΦ, mul_assoc, map_mul, hinv₂ _ hγ₂]
  have hbij := bijective_quot_mk_map_out κ P₁ Γ₁ P₂ Γ₂ hP hΓ
  have hbij₁ : Function.Bijective fun q : _root_.GlobalTheory.AutomorphicL2Unitary.Quot (P₁.subgroupOf Γ₁) =>
      _root_.GlobalTheory.AutomorphicL2Unitary.mk (P₁.subgroupOf Γ₁) (Quotient.out q) := by
    have : (fun q : _root_.GlobalTheory.AutomorphicL2Unitary.Quot (P₁.subgroupOf Γ₁) =>
        _root_.GlobalTheory.AutomorphicL2Unitary.mk (P₁.subgroupOf Γ₁) (Quotient.out q)) = id := by
      funext q
      unfold _root_.GlobalTheory.AutomorphicL2Unitary.mk
      exact Quotient.out_eq q
    rw [this]
    exact Function.bijective_id
  have hterm : ∀ (g : G₁) (q : _root_.GlobalTheory.AutomorphicL2Unitary.Quot (P₁.subgroupOf Γ₁)),
      Φ₁ (((Quotient.out q : Γ₁) : G₁) * g) =
        c * Φ₂ (((⟨κ (Quotient.out q : Γ₁), (hΓ _).1 (Quotient.out q : Γ₁).2⟩ : Γ₂) : G₂) *
          κ (g * x)) := by
    intro g q
    rw [hΦ, mul_assoc, map_mul]
  refine ⟨hinv₁, fun g => ⟨fun hconv => ?_, ?_⟩⟩
  · rw [_root_.GlobalTheory.Eis.cosetConv_iff hinv₁ hbij₁]
    rw [_root_.GlobalTheory.Eis.cosetConv_iff hinv₂ hbij] at hconv
    simp_rw [hterm g, norm_mul]
    exact hconv.mul_left _
  · rw [_root_.GlobalTheory.Eis.cosetSum_eq_tsum hinv₁ hbij₁,
      _root_.GlobalTheory.Eis.cosetSum_eq_tsum hinv₂ hbij]
    simp_rw [hterm g]
    exact tsum_mul_left

end GlobalTheory.StdUnn
