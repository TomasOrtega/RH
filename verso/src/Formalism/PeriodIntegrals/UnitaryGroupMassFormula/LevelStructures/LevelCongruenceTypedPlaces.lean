import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataInst
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.GlobProdOfK2Loc

noncomputable section

namespace MassDataLevelSSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
open scoped TensorProduct

def KgLoc : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (κ : X.B.I.Gf), κ ∈ X.B.I.Kset →
    (∀ p : TypX X, haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F p.1) (finHA X hb κ) = 1) → κ ∈ X.B.I.Kg X.B.g

def LevelCongruenceTypedPlaces : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I), X.LevelSubgroupCharacter → X.LevelSubgroupNormalized → ∀ κ : X.B.I.Gf,
    κ ∈ X.B.I.Kset →
    (∀ v, v ∉ typSet X.B.I.F (D.host.g 0) (D.host.g 1) →
      haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F v) (finHA X hb κ) = 1) →
    (∀ p : TypX X, ∃ κ' ∈ X.K2,
      haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F p.1) (finHA X hb κ) =
        haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F p.1) (finHA X hb κ')) → κ ∈ X.K2

/- English proof (translation)
Introduce `D X hb hK hL κ hκ hloc`. Take `⟨h, hT, hO⟩` from `glueHA_holds X (fun p => haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F p.1) (finHA X hb κ))`. Take `⟨κt, hκt⟩` from `PI.MassDataKppVolLemmas.Bridge_tf_surjective X.B.I hb h`. Establish `hκtf : finHA X hb κt = h` using `hκt`. Establish `hκf : finHA X hb κ ∈ Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))` using `finHA_mem_Kf X hb κ hκ`.

Establish `hhK : h ∈ Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))`. Use `Subgroup.mem_iInf.2 fun v => ?_` and prove the remaining obligations. Establish `hv' : haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F v) h ∈ Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) v`. Distinguish the cases in `hv : v ∈ typSet X.B.I.F (D.host.g 0) (D.host.g 1)`. Establish `e` using `hT ⟨v, hv⟩`.

Simplify using `only at e`. Rewrite using `[e]`. Conclude with `compK_holds X v _ hκf`. Rewrite using `[hO v hv]`. Conclude with `Subgroup.one_mem (Kloc (E := X.B.I.E) v (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)))`.

Conclude with `hv'`. Establish `hκtK : κt ∈ X.B.I.Kset`. Use `(PI.MassDataKppVolLemmas.Bridge_mem_Kf_iff X.B.I hb κt).1 ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `finHA X hb κt ∈ _`. Rewrite using `[hκtf]`.

Conclude with `hhK`. Establish `hrK : κt⁻¹ * κ ∈ X.B.I.Kset`. Use `(PI.MassDataKppVolLemmas.Bridge_mem_Kf_iff X.B.I hb _).1 ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `finHA X hb (κt⁻¹ * κ) ∈ _`. Rewrite using `[finHA_mul, finHA_inv, hκtf]`.

Conclude with `Subgroup.mul_mem _ (Subgroup.inv_mem _ hhK) hκf`. Establish `hrest : κt⁻¹ * κ ∈ X.B.I.Kg X.B.g` using `hg X hb _ hrK (fun p => by`. Rewrite using `[finHA_mul, finHA_inv, map_mul, map_inv, hκtf, hT p]`. Conclude with `inv_mul_cancel _)`. Establish `hκt2 : κt ∈ X.K2` using `ht X hb hK hL κt hκtK (fun v hv => by rw [hκtf]; exact hO v hv) (fun p => by`.

Take `⟨κ', hκ', e⟩` from `hloc p`. Conclude with `⟨κ', hκ', by rw [hκtf, hT p]; exact e⟩)`. Establish `hr2 : κt⁻¹ * κ ∈ X.K2` using `(hL.1 _ hrest).1`. Establish `hprod` using `hK.2.1 _ hκt2 _ hr2`. Rewrite `hprod` using `[mul_inv_cancel_left]`. Then use the resulting hypothesis.
-/
theorem level_local_of_typed (hg : KgLoc) (ht : LevelCongruenceTypedPlaces) : LevelCongruenceLocal := by
  intro D X hb hK hL κ hκ hloc
  classical
  obtain ⟨h, hT, hO⟩ := glueHA_holds X
    (fun p => haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F p.1) (finHA X hb κ))
  obtain ⟨κt, hκt⟩ := PI.MassDataKppVolLemmas.Bridge_tf_surjective X.B.I hb h
  have hκtf : finHA X hb κt = h := hκt
  have hκf : finHA X hb κ ∈ Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) :=
    finHA_mem_Kf X hb κ hκ
  have hhK : h ∈ Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) := by
    refine Subgroup.mem_iInf.2 fun v => ?_
    have hv' : haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F v) h ∈
        Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) v := by
      by_cases hv : v ∈ typSet X.B.I.F (D.host.g 0) (D.host.g 1)
      · have e := hT ⟨v, hv⟩
        simp only at e
        rw [e]
        exact compK_holds X v _ hκf
      · rw [hO v hv]
        exact Subgroup.one_mem (Kloc (E := X.B.I.E) v (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)))
    exact hv'
  have hκtK : κt ∈ X.B.I.Kset := by
    refine (PI.MassDataKppVolLemmas.Bridge_mem_Kf_iff X.B.I hb κt).1 ?_
    change finHA X hb κt ∈ _
    rw [hκtf]
    exact hhK
  have hrK : κt⁻¹ * κ ∈ X.B.I.Kset := by
    refine (PI.MassDataKppVolLemmas.Bridge_mem_Kf_iff X.B.I hb _).1 ?_
    change finHA X hb (κt⁻¹ * κ) ∈ _
    rw [finHA_mul, finHA_inv, hκtf]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hhK) hκf
  have hrest : κt⁻¹ * κ ∈ X.B.I.Kg X.B.g := hg X hb _ hrK (fun p => by
    rw [finHA_mul, finHA_inv, map_mul, map_inv, hκtf, hT p]
    exact inv_mul_cancel _)
  have hκt2 : κt ∈ X.K2 := ht X hb hK hL κt hκtK (fun v hv => by rw [hκtf]; exact hO v hv)
    (fun p => by
      obtain ⟨κ', hκ', e⟩ := hloc p
      exact ⟨κ', hκ', by rw [hκtf, hT p]; exact e⟩)
  have hr2 : κt⁻¹ * κ ∈ X.K2 := (hL.1 _ hrest).1
  have hprod := hK.2.1 _ hκt2 _ hr2
  rwa [mul_inv_cancel_left] at hprod

/- English proof (translation)
The claim follows from `globProd_of_k2Loc (level_local_of_typed hg ht)`.
-/
theorem globProd_of_loc (hg : KgLoc) (ht : LevelCongruenceTypedPlaces) : GlobProd := globProd_of_k2Loc (level_local_of_typed hg ht)

end MassDataLevelSSteps
