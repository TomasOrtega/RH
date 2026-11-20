import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PinColL
import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdelicUnitaryTopCong
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.HaarIdx
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevVol

variable {D : D7}

/- English proof (translation)
Use extensionality with `g`. Simplify using `only [Set.mem_setOf_eq, SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_subgroupOf]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨k, hk, κ, hκ, rfl⟩`. Establish `e : GlobalTheory.AutMult.toFin V (k * κ) = ⟨κ, hU hκ⟩`.

Rewrite using `[map_mul, GlobalTheory.AutMult.toFin_coe_inf (⟨k, hk⟩ : GinfC V), one_mul]`. Conclude with `GlobalTheory.AutMult.toFin_coe (⟨κ, hU hκ⟩ : GfC V)`. Rewrite using `[e]`. Conclude with `hκ`. Introduce `h`.

Conclude with `⟨_, (GlobalTheory.AutMult.toInf V g).2, _, h, (GlobalTheory.AutMult.toInf_mul_toFin g).symm⟩`.
-/
theorem mul_set_eq_comap (V : HSp D) (U : Subgroup (GA D V)) (hU : U ≤ GfC V) :
    {g : GA D V | ∃ k ∈ GinfC V, ∃ κ ∈ U, g = k * κ} =
      (((U.subgroupOf (GfC V)).comap (GlobalTheory.AutMult.toFin V) : Subgroup (GA D V)) : Set (GA D V)) := by
  ext g
  simp only [Set.mem_setOf_eq, SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨k, hk, κ, hκ, rfl⟩
    have e : GlobalTheory.AutMult.toFin V (k * κ) = ⟨κ, hU hκ⟩ := by
      rw [map_mul, GlobalTheory.AutMult.toFin_coe_inf (⟨k, hk⟩ : GinfC V), one_mul]
      exact GlobalTheory.AutMult.toFin_coe (⟨κ, hU hκ⟩ : GfC V)
    rw [e]
    exact hκ
  · intro h
    exact ⟨_, (GlobalTheory.AutMult.toInf V g).2, _, h, (GlobalTheory.AutMult.toInf_mul_toFin g).symm⟩

/- English proof (translation)
Introduce `D V v U U' hle hU' _ hopn`. Take `⟨i1, -, -, -, i5, -⟩` from `GlobalTheory.Ker.CongTop.adelicUnitary_top_cong D V`. Use `haveI := i1`. Use `haveI := i5`. Use `haveI := v.haar`.

Establish `hU : U ≤ GfC V` using `hle.trans hU'`. Use `set A := (U.subgroupOf (GfC V)).comap (GlobalTheory.AutMult.toFin V) with hA`. Use `set A' := (U'.subgroupOf (GfC V)).comap (GlobalTheory.AutMult.toFin V) with hA'`. Establish `hAA : A ≤ A'` using `Subgroup.comap_mono (fun x hx => Subgroup.mem_subgroupOf.2 (hle (Subgroup.mem_subgroupOf.1 hx)))`. Establish `hAo : IsOpen (A : Set (GA D V))` using `hopn.preimage (GlobalTheory.AutMult.continuous_toFin V)`.

Establish `key` using `MassDataLevelSSteps.toReal_eq_relIndex_mul_of_open v.μ A A' hAA hAo`. Establish `hsurj : Function.Surjective (GlobalTheory.AutMult.toFin V)` using `fun y => ⟨y, GlobalTheory.AutMult.toFin_coe y⟩`. Establish `hidx : A.relIndex A' = U.relIndex U'`. Rewrite using `[hA, Subgroup.relIndex_comap, hA', Subgroup.map_comap_eq_self_of_surjective hsurj, Subgroup.relIndex_subgroupOf hU']`. Unfold `GlobalTheory.SeeSaw.volLev`.

Rewrite using `[mul_set_eq_comap V U hU, mul_set_eq_comap V U' hU', ← hA, ← hA', key, hidx, mul_comm]`.
-/
theorem volLev_mul_relIndex : ∀ (D : D7) (V : HSp D) (v : GlobalTheory.Unf.Vol V) (U U' : Subgroup (GA D V)), U ≤ U' → U' ≤ GfC V →
    IsCompact (U' : Set (GA D V)) → IsOpen ((U.subgroupOf (GfC V) : Subgroup (GfC V)) : Set (GfC V)) →
    volLev v U * (U.relIndex U' : ℝ) = volLev v U' := by
  intro D V v U U' hle hU' _ hopn
  obtain ⟨i1, -, -, -, i5, -⟩ := GlobalTheory.Ker.CongTop.adelicUnitary_top_cong D V
  haveI := i1
  haveI := i5
  haveI := v.haar
  have hU : U ≤ GfC V := hle.trans hU'
  set A := (U.subgroupOf (GfC V)).comap (GlobalTheory.AutMult.toFin V) with hA
  set A' := (U'.subgroupOf (GfC V)).comap (GlobalTheory.AutMult.toFin V) with hA'
  have hAA : A ≤ A' := Subgroup.comap_mono (fun x hx => Subgroup.mem_subgroupOf.2 (hle (Subgroup.mem_subgroupOf.1 hx)))
  have hAo : IsOpen (A : Set (GA D V)) := hopn.preimage (GlobalTheory.AutMult.continuous_toFin V)
  have key := MassDataLevelSSteps.toReal_eq_relIndex_mul_of_open v.μ A A' hAA hAo
  have hsurj : Function.Surjective (GlobalTheory.AutMult.toFin V) := fun y => ⟨y, GlobalTheory.AutMult.toFin_coe y⟩
  have hidx : A.relIndex A' = U.relIndex U' := by
    rw [hA, Subgroup.relIndex_comap, hA', Subgroup.map_comap_eq_self_of_surjective hsurj,
      Subgroup.relIndex_subgroupOf hU']
  unfold GlobalTheory.SeeSaw.volLev
  rw [mul_set_eq_comap V U hU, mul_set_eq_comap V U' hU', ← hA, ← hA', key, hidx, mul_comm]

end GlobalTheory.LevVol
