import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.AlgebraMapIntMemIntAd
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.ParabolicDecomposition
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.NatSmulMulEq

noncomputable section

namespace PI.IwaMeasEx.Nrm

open Matrix NumberField Topology Filter MeasureTheory Formalism.MainNotions.S Formalism.MainNotions.LeviCoordinates Formalism.L2.S.S7.DensDefs
  Formalism.L2.S.S7.WittLeviSubgroups Formalism.L2.S.S7.PositiveOrthantChangeOfVariables Formalism.L2.S.S7.GLOne
open scoped TensorProduct nonZeroDivisors

section Top

variable (I : AutInst)

attribute [local instance] AfT.tAf

/- English proof (translation)
The claim follows from `AfT.isTopologicalRing_tAf I`.
-/
theorem topRing : IsTopologicalRing (AEf I) := AfT.isTopologicalRing_tAf I

/- English proof (translation)
The claim follows from `AfT.t2Space_finite_adeles_ext I`.
-/
theorem t2 : T2Space (AEf I) := AfT.t2Space_finite_adeles_ext I

attribute [local instance] topRing t2

def mAf : MeasurableSpace (AEf I) := borel (AEf I)

attribute [local instance] mAf

/- English proof (translation)
Assemble the required witnesses or components as `⟨rfl⟩`.
-/
theorem borel_mAf : BorelSpace (AEf I) := ⟨rfl⟩

attribute [local instance] borel_mAf

/- English proof (translation)
Rewrite using `[isOpen_iff_mem_nhds]`. Introduce `x hx`. Rewrite using `[(AfT.hasBasis_nhds_tAf I x).mem_iff]`. Use `⟨0, trivial, fun y hy => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `y - x ∈ AfT.bsub I (0 + 1) at hy`.

Take `⟨z, hz, he⟩` from `(AfT.mem_bsub I).1 hy`. Establish `e : y = x + (y - x)` using `by ring`. Use `show y ∈ IntAf I.F I.E`. Rewrite using `[e, ← he]`. Conclude with `add_mem hx (mul_mem (natCast_mem _ _) hz)`.
-/
theorem isOpen_IntAf : IsOpen ((IntAf I.F I.E : Subring (AEf I)) : Set (AEf I)) := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rw [(AfT.hasBasis_nhds_tAf I x).mem_iff]
  refine ⟨0, trivial, fun y hy => ?_⟩
  change y - x ∈ AfT.bsub I (0 + 1) at hy
  obtain ⟨z, hz, he⟩ := (AfT.mem_bsub I).1 hy
  have e : y = x + (y - x) := by ring
  show y ∈ IntAf I.F I.E
  rw [e, ← he]
  exact add_mem hx (mul_mem (natCast_mem _ _) hz)

/- English proof (translation)
Apply `continuous_of_continuousAt_zero` to reduce the goal to its premises. Rewrite using `[ContinuousAt, map_zero]`. Use `(AfT.hasBasis_nhds_zero_tAf I).tendsto_right_iff.2 fun k _ => ?_` and prove the remaining obligations. Establish `hk : ((k + 1 : ℕ) : I.F) ≠ 0` using `Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)`. Establish `hU : IsOpen {a : Af I.F | algebraMap I.F (Af I.F) (((k + 1 : ℕ) : I.F)⁻¹) * a ∈ Wau.Ohat I.F}` using `Wau.isOpen_Ohat.preimage (continuous_const.mul continuous_id)`.

Establish `h0 : (0 : Af I.F) ∈ {a : Af I.F | algebraMap I.F (Af I.F) (((k + 1 : ℕ) : I.F)⁻¹) * a ∈ Wau.Ohat I.F}` using `by show _ * 0 ∈ Wau.Ohat I.F`. Rewrite using `[mul_zero]`. Conclude with `Wau.ohat_zero`. Use `filter_upwards [hU.mem_nhds h0] with a ha`. Use `show Algebra.TensorProduct.includeRight a ∈ AfT.bsub I (k + 1)`.

Use `(AfT.mem_bsub I).2 ⟨Algebra.TensorProduct.includeRight (algebraMap I.F (Af I.F) (((k + 1 : ℕ) : I.F)⁻¹) * a), AfT.includeRight_mem_IntAf I ha, ?_⟩` and prove the remaining obligations. Rewrite using `[← map_natCast (Algebra.TensorProduct.includeRight (R := I.F) (A := I.E) (B := Af I.F)), ← map_mul, ← mul_assoc, ← map_natCast (algebraMap I.F (Af I.F)), ← map_mul, mul_inv_cancel₀ hk, map_one, one_mul]`.
-/
theorem continuous_inclR :
    Continuous (Algebra.TensorProduct.includeRight (R := I.F) (A := I.E) (B := Af I.F) : Af I.F → AEf I) := by
  apply continuous_of_continuousAt_zero
  rw [ContinuousAt, map_zero]
  refine (AfT.hasBasis_nhds_zero_tAf I).tendsto_right_iff.2 fun k _ => ?_
  have hk : ((k + 1 : ℕ) : I.F) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)
  have hU : IsOpen {a : Af I.F | algebraMap I.F (Af I.F) (((k + 1 : ℕ) : I.F)⁻¹) * a ∈ Wau.Ohat I.F} :=
    Wau.isOpen_Ohat.preimage (continuous_const.mul continuous_id)
  have h0 : (0 : Af I.F) ∈ {a : Af I.F | algebraMap I.F (Af I.F) (((k + 1 : ℕ) : I.F)⁻¹) * a ∈ Wau.Ohat I.F} := by
    show _ * 0 ∈ Wau.Ohat I.F
    rw [mul_zero]
    exact Wau.ohat_zero
  filter_upwards [hU.mem_nhds h0] with a ha
  show Algebra.TensorProduct.includeRight a ∈ AfT.bsub I (k + 1)
  refine (AfT.mem_bsub I).2 ⟨Algebra.TensorProduct.includeRight
    (algebraMap I.F (Af I.F) (((k + 1 : ℕ) : I.F)⁻¹) * a), AfT.includeRight_mem_IntAf I ha, ?_⟩
  rw [← map_natCast (Algebra.TensorProduct.includeRight (R := I.F) (A := I.E) (B := Af I.F)), ← map_mul, ← mul_assoc,
    ← map_natCast (algebraMap I.F (Af I.F)), ← map_mul, mul_inv_cancel₀ hk, map_one, one_mul]

/- English proof (translation)
Use `continuous_finset_sum _ fun j _ => ?_` and prove the remaining obligations. Establish `e : (fun c : ι → Af I.F => (b j ⊗ₜ[I.F] c j : AEf I)) = fun c => iE I (b j) * Algebra.TensorProduct.includeRight (c j)`. Use function extensionality and compare the values at `c`. Use `show b j ⊗ₜ[I.F] c j = (b j ⊗ₜ[I.F] (1 : Af I.F)) * ((1 : I.E) ⊗ₜ[I.F] c j)`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]`.

Rewrite using `[e]`. Conclude with `continuous_const.mul ((continuous_inclR I).comp (continuous_apply j))`.
-/
theorem continuous_embC {ι : Type} [Fintype ι] (b : Module.Basis ι I.F I.E) :
    Continuous (fun c : ι → Af I.F => (∑ j, b j ⊗ₜ[I.F] c j : AEf I)) := by
  refine continuous_finset_sum _ fun j _ => ?_
  have e : (fun c : ι → Af I.F => (b j ⊗ₜ[I.F] c j : AEf I)) =
      fun c => iE I (b j) * Algebra.TensorProduct.includeRight (c j) := by
    funext c
    show b j ⊗ₜ[I.F] c j = (b j ⊗ₜ[I.F] (1 : Af I.F)) * ((1 : I.E) ⊗ₜ[I.F] c j)
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [e]
  exact continuous_const.mul ((continuous_inclR I).comp (continuous_apply j))

/- English proof (translation)
Set `b` to `Module.finBasis I.F I.E`. Take `⟨D, hD, hDb⟩` from `AfT.exists_denom I b`. Establish `hK : IsCompact ((fun c => (∑ j, b j ⊗ₜ[I.F] c j : AEf I)) '' Set.univ.pi fun _ => Wau.Cpt.Bx I D)` using `(isCompact_univ_pi fun _ => Wau.Cpt.isCompact_Bx I D).image (continuous_embC I b)`. Establish `hcl : IsClosed ((IntAf I.F I.E : Subring (AEf I)) : Set (AEf I))` using `AddSubgroup.isClosed_of_isOpen (IntAf I.F I.E).toAddSubgroup (isOpen_IntAf I)`. Use `hK.of_isClosed_subset hcl fun x hx => ?_` and prove the remaining obligations.

Use `⟨fun j => AfT.crd I b j x, fun j _ => Wau.Cpt.mem_Bx I (by omega) ?_, (AfT.sum_crd I b x).symm⟩` and prove the remaining obligations. Rewrite using `[nsmul_eq_mul]`. Conclude with `AfT.crd_mem I b hDb (AfT.IntAf_le_sumsInt I hx) j`.
-/
theorem isCompact_IntAf : IsCompact ((IntAf I.F I.E : Subring (AEf I)) : Set (AEf I)) := by
  let b := Module.finBasis I.F I.E
  obtain ⟨D, hD, hDb⟩ := AfT.exists_denom I b
  have hK : IsCompact ((fun c => (∑ j, b j ⊗ₜ[I.F] c j : AEf I)) '' Set.univ.pi fun _ => Wau.Cpt.Bx I D) :=
    (isCompact_univ_pi fun _ => Wau.Cpt.isCompact_Bx I D).image (continuous_embC I b)
  have hcl : IsClosed ((IntAf I.F I.E : Subring (AEf I)) : Set (AEf I)) :=
    AddSubgroup.isClosed_of_isOpen (IntAf I.F I.E).toAddSubgroup (isOpen_IntAf I)
  refine hK.of_isClosed_subset hcl fun x hx => ?_
  refine ⟨fun j => AfT.crd I b j x, fun j _ => Wau.Cpt.mem_Bx I (by omega) ?_, (AfT.sum_crd I b x).symm⟩
  rw [nsmul_eq_mul]
  exact AfT.crd_mem I b hDb (AfT.IntAf_le_sumsInt I hx) j

def Bs (𝔞 : FractionalIdeal (𝓞 I.E)⁰ I.E) : Set (AEf I) :=
  {x | ∃ b ∈ (𝔞 : Submodule (𝓞 I.E) I.E), ∃ N : ℕ, 1 ≤ N ∧ (N : I.E) ∈ (𝔞 : Submodule (𝓞 I.E) I.E) ∧
    ∃ z ∈ IntAf I.F I.E, x = iE I b + iE I N * z}

def Sa (𝔞 : FractionalIdeal (𝓞 I.E)⁰ I.E) : Set (AEf I) :=
  Bs I 𝔞 ∩ ⋂ 𝔟 : {𝔟 : FractionalIdeal (𝓞 I.E)⁰ I.E // 𝔟 ≠ 0 ∧ 𝔟 < 𝔞}, (Bs I 𝔟.1)ᶜ

open Classical in

def hq (u : AEf I) : ℚ := if h : IsUnit u then (FractionalIdeal.absNorm (FI I h.unit))⁻¹ else 0

end Top

attribute [local instance] AfT.tAf topRing t2 mAf borel_mAf

end PI.IwaMeasEx.Nrm

end
