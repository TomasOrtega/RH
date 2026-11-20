import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.InfPartOfSplitIdem
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeCompletionSelfAnnihilatorAtPlaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
set_option synthInstance.maxHeartbeats 400000
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HatLatV

variable {D : D7}

def cut (P : Pl D → Prop) (u : Af D.host.F ⊗[D.host.F] D.host.E) : AE D :=
  Formalism.IndefR.Fin.LevelGroupLemmas.Lat.lift ((GlobalTheory.SelfDualAt.indP P ⊗ₜ[D.host.F] (1 : D.host.E)) * u)

def cutHom (P : Pl D → Prop) : (Af D.host.F ⊗[D.host.F] D.host.E) →+ AE D where
  toFun := cut P
  map_zero' := by
    show Formalism.IndefR.Fin.LevelGroupLemmas.Lat.lift _ = 0
    rw [mul_zero]; exact Formalism.IndefR.Fin.LevelGroupLemmas.Lat.lift_zero
  map_add' a b := by
    show Formalism.IndefR.Fin.LevelGroupLemmas.Lat.lift _ = Formalism.IndefR.Fin.LevelGroupLemmas.Lat.lift _ + Formalism.IndefR.Fin.LevelGroupLemmas.Lat.lift _
    rw [mul_add]; exact Formalism.IndefR.Fin.LevelGroupLemmas.Lat.lift_add _ _

/- English proof (translation)
Unfold `cut`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, one_mul]`. Both sides reduce to the same expression.
-/
theorem cut_tmul (P : Pl D → Prop) (a : Af D.host.F) (x : D.host.E) :
    cut P (a ⊗ₜ[D.host.F] x) = pairA D.host.F 0 (GlobalTheory.SelfDualAt.indP P * a) ⊗ₜ[D.host.F] x := by
  unfold cut
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rfl

set_option maxHeartbeats 800000 in

/- English proof (translation)
Unfold `idAt at hu`. Rewrite `hu` using `[Ideal.mem_inf]`. Take `⟨hinf, hfin⟩` from `hu`. Rewrite `hinf` using `[RingHom.mem_ker]`. Establish `hoff : ∀ w : Pl D, ¬ P w → GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w (finPart D u) = 0`.

Introduce `w hw`. Use `(Submodule.mem_iInf _).1 hfin ⟨w, hw⟩` as an intermediate fact. Conclude with `(RingHom.mem_ker).1 this`. Establish `hcut : (GlobalTheory.SelfDualAt.indP P ⊗ₜ[D.host.F] (1 : D.host.E)) * finPart D u = finPart D u`. Use `(sub_eq_zero.mp (GlobalTheory.SelfDualAt.eq_zero_of_compFin _ fun w => ?_)).symm` and prove the remaining obligations.

Rewrite using `[map_sub, map_mul]`. Establish `hc : GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w (GlobalTheory.SelfDualAt.indP P ⊗ₜ[D.host.F] (1 : D.host.E)) = evalV D.host.F w (GlobalTheory.SelfDualAt.indP P) ⊗ₜ[D.host.F] (1 : D.host.E)` using `rfl`. Rewrite using `[hc, GlobalTheory.SelfDualAt.evalV_indP]`. Distinguish the cases in `hw : P w`. Rewrite using `[if_pos hw, ← Algebra.TensorProduct.one_def, one_mul, sub_self]`.

Rewrite using `[if_neg hw, TensorProduct.zero_tmul, zero_mul, sub_zero, hoff w hw]`. Unfold `cut`. Rewrite using `[hcut]`. Conclude with `(Formalism.IndefR.Fin.LevelGroupLemmas.Lat.eq_lift_of_infPart u hinf).symm`.
-/
theorem cut_finPart (P : Pl D → Prop) (u : AE D) (hu : u ∈ idAt D P) : cut P (finPart D u) = u := by
  unfold idAt at hu
  rw [Ideal.mem_inf] at hu
  obtain ⟨hinf, hfin⟩ := hu
  rw [RingHom.mem_ker] at hinf
  have hoff : ∀ w : Pl D, ¬ P w → GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w (finPart D u) = 0 := by
    intro w hw
    have := (Submodule.mem_iInf _).1 hfin ⟨w, hw⟩
    exact (RingHom.mem_ker).1 this
  have hcut : (GlobalTheory.SelfDualAt.indP P ⊗ₜ[D.host.F] (1 : D.host.E)) * finPart D u = finPart D u := by
    refine (sub_eq_zero.mp (GlobalTheory.SelfDualAt.eq_zero_of_compFin _ fun w => ?_)).symm
    rw [map_sub, map_mul]
    have hc : GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w (GlobalTheory.SelfDualAt.indP P ⊗ₜ[D.host.F] (1 : D.host.E)) =
        evalV D.host.F w (GlobalTheory.SelfDualAt.indP P) ⊗ₜ[D.host.F] (1 : D.host.E) := rfl
    rw [hc, GlobalTheory.SelfDualAt.evalV_indP]
    by_cases hw : P w
    · rw [if_pos hw, ← Algebra.TensorProduct.one_def, one_mul, sub_self]
    · rw [if_neg hw, TensorProduct.zero_tmul, zero_mul, sub_zero, hoff w hw]
  unfold cut
  rw [hcut]
  exact (Formalism.IndefR.Fin.LevelGroupLemmas.Lat.eq_lift_of_infPart u hinf).symm

/- English proof (translation)
Introduce `D S L P y hy hz`. Establish `hlat : (fun i => finPart D (y i)) ∈ latHat D.host.F D.host.E (L : Set (Fin S.rank → D.host.E))` using `(GlobalTheory.LevSplit.latHat_iff L _).2 hz`. Establish `key : y = AddMonoidHom.compLeft (cutHom P) (Fin S.rank) (fun i => finPart D (y i))`. Use function extensionality and compare the values at `fun i => (cut_finPart P (y i) (hy i)).symm`. Rewrite using `[key]`.

Use `AddSubgroup.closure_induction (p := fun u _ => AddMonoidHom.compLeft (cutHom P) (Fin S.rank) u ∈ latV S L P) ?_ ?_ ?_ ?_ hlat` and prove the remaining obligations. Introduce and unpack `_ ⟨a, ha, x, hx, rfl⟩`. Apply `AddSubgroup.subset_closure` to reduce the goal to its premises. Use `⟨GlobalTheory.SelfDualAt.indP P * a, ?_, ?_, 1, rfl, x, hx, ?_⟩` and prove the remaining obligations. Introduce `v`.

Rewrite using `[map_mul, GlobalTheory.SelfDualAt.evalV_indP]`. Use `split_ifs`. Rewrite using `[one_mul]`. Conclude with `ha v`. Rewrite using `[zero_mul]`.

Conclude with `zero_mem _`. Introduce `v hv`. Rewrite using `[map_mul, GlobalTheory.SelfDualAt.evalV_indP, if_neg hv, zero_mul]`. Use function extensionality and compare the values at `i show cut P (a ⊗ₜ[D.host.F] x i) = _`. Rewrite using `[cut_tmul, one_mul]`.

Rewrite using `[map_zero]`. Conclude with `zero_mem _`. Introduce `a b _ _ ha hb`. Rewrite using `[map_add]`. Conclude with `add_mem ha hb`.

Introduce `a _ ha`. Rewrite using `[map_neg]`. Conclude with `neg_mem ha`.
-/
theorem mem_latV_of_hatL : ∀ (D : D7) (S : HSp D) (L : Lat S) (P : Pl D → Prop) (y : Fin S.rank → AE D),
    (∀ i, y i ∈ idAt D P) →
    (fun i => Formalism.IndefR.Lev.swapAE D (finPart D (y i))) ∈ Formalism.L2.Herm.hatL (F := D.host.F) L → y ∈ latV S L P := by
  intro D S L P y hy hz
  have hlat : (fun i => finPart D (y i)) ∈ latHat D.host.F D.host.E (L : Set (Fin S.rank → D.host.E)) :=
    (GlobalTheory.LevSplit.latHat_iff L _).2 hz
  have key : y = AddMonoidHom.compLeft (cutHom P) (Fin S.rank) (fun i => finPart D (y i)) :=
    funext fun i => (cut_finPart P (y i) (hy i)).symm
  rw [key]
  refine AddSubgroup.closure_induction
    (p := fun u _ => AddMonoidHom.compLeft (cutHom P) (Fin S.rank) u ∈ latV S L P) ?_ ?_ ?_ ?_ hlat
  · rintro _ ⟨a, ha, x, hx, rfl⟩
    apply AddSubgroup.subset_closure
    refine ⟨GlobalTheory.SelfDualAt.indP P * a, ?_, ?_, 1, rfl, x, hx, ?_⟩
    · intro v
      rw [map_mul, GlobalTheory.SelfDualAt.evalV_indP]
      split_ifs
      · rw [one_mul]; exact ha v
      · rw [zero_mul]; exact zero_mem _
    · intro v hv
      rw [map_mul, GlobalTheory.SelfDualAt.evalV_indP, if_neg hv, zero_mul]
    · funext i
      show cut P (a ⊗ₜ[D.host.F] x i) = _
      rw [cut_tmul, one_mul]
  · rw [map_zero]; exact zero_mem _
  · intro a b _ _ ha hb
    rw [map_add]; exact add_mem ha hb
  · intro a _ ha
    rw [map_neg]; exact neg_mem ha

end GlobalTheory.HatLatV

end
