import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValueDoubleExact
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeStabilizersFixWeilVacuumOnPlaceSeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
open GlobalTheory.FinPl

noncomputable section

namespace GlobalTheory.VacFixP

/- English proof (translation)
Rewrite using `[eq_bot_iff]`. Introduce `x hx`. Rewrite using `[Ideal.mem_bot]`. Use `GlobalTheory.FinPlLoc.eq_zero_of_comp x hx.1 fun w => ?_` and prove the remaining obligations. Conclude with `(Submodule.mem_iInf _).1 hx.2 ⟨w, hP w⟩`.
-/
theorem idAt_eq_bot {D : D7} {P : Pl D → Prop} (hP : ∀ v, ¬ P v) : idAt D P = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Ideal.mem_bot]
  refine GlobalTheory.FinPlLoc.eq_zero_of_comp x hx.1 fun w => ?_
  exact (Submodule.mem_iInf _).1 hx.2 ⟨w, hP w⟩

/- English proof (translation)
Unfold `grpAt congGrp at h`. Rewrite `h` using `[idAt_eq_bot hP, MonoidHom.mem_ker, MonoidHom.comp_apply]`. Establish `h2 : matHom S κ = 1`. Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`.

Use `congrArg (fun g : GL (Fin S.rank) (AE D ⧸ (⊥ : Ideal (AE D))) => g.val i j) h` as an intermediate fact. Simplify using `only [Matrix.GeneralLinearGroup.map_apply, Units.val_one] at this`. Rewrite using `[Units.val_one]`. Rewrite `this`, the goal using `[Matrix.one_apply]`. Apply the tactic sequence `have h1 : ((if i = j then 1 else 0 : AE D ⧸ (⊥ : Ideal (AE D)))) = Ideal.Quotient.mk ⊥ (if i = j then 1 else 0) := by split_ifs <;> simp`.

Rewrite `this` using `[h1, Ideal.Quotient.eq, Ideal.mem_bot, sub_eq_zero]`. Conclude with `this`. Unfold `matHom at h2`. Conclude with `Subgroup.subtype_injective _ (h2.trans (map_one _).symm)`.
-/
theorem eq_one_of_grpAt {D : D7} {S : HSp D} {P : Pl D → Prop} (hP : ∀ v, ¬ P v) {κ : GA D S}
    (h : κ ∈ grpAt S P) : κ = 1 := by
  unfold grpAt congGrp at h
  rw [idAt_eq_bot hP, MonoidHom.mem_ker, MonoidHom.comp_apply] at h
  have h2 : matHom S κ = 1 := by
    apply Units.ext
    ext i j
    have := congrArg (fun g : GL (Fin S.rank) (AE D ⧸ (⊥ : Ideal (AE D))) => g.val i j) h
    simp only [Matrix.GeneralLinearGroup.map_apply, Units.val_one] at this
    rw [Units.val_one]
    rw [Matrix.one_apply] at this ⊢
    have h1 : ((if i = j then 1 else 0 : AE D ⧸ (⊥ : Ideal (AE D)))) = Ideal.Quotient.mk ⊥ (if i = j then 1 else 0) := by
      split_ifs <;> simp
    rw [h1, Ideal.Quotient.eq, Ideal.mem_bot, sub_eq_zero] at this
    exact this
  unfold matHom at h2
  exact Subgroup.subtype_injective _ (h2.trans (map_one _).symm)

/- English proof (translation)
Introduce `D ψ S T χS χT om hW LS LT P hP f hf κ κ' hκ hκ'`. Distinguish the cases in `hex : ∃ v, P v`. Take `⟨v, hv⟩` from `hex`. Take `⟨hS, hT, -⟩` from `hP v hv`. Conclude with `GlobalTheory.T.selfDualLatticeStabilizers_fix_weilVacuum_on_placeSet D ψ S T χS χT om hW LS LT hS hT P (fun w hw => (hP w hw).2.2) f hf κ κ' hκ hκ'`.

Use `push_neg at hex`. Rewrite using `[eq_one_of_grpAt hex hκ.1, eq_one_of_grpAt hex hκ'.1, Prod.mk_one_one, map_one]`. Both sides reduce to the same expression.
-/
theorem vac_fix_on : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ (LS : Lat S) (LT : Lat T) (P : Pl D → Prop), (∀ v, P v → IsSelfDualC S LS ∧ IsSelfDualC T LT ∧ Tame D v ∧ CharUnramAt D χS v ∧ CharUnramAt D χT v) → ∀ f, Vac ψ S T LS LT P f → ∀ κ κ', InK S LS P κ → InK T LT P κ' → om (κ, κ') f = f := by
  intro D ψ S T χS χT om hW LS LT P hP f hf κ κ' hκ hκ'
  by_cases hex : ∃ v, P v
  · obtain ⟨v, hv⟩ := hex
    obtain ⟨hS, hT, -⟩ := hP v hv
    exact GlobalTheory.T.selfDualLatticeStabilizers_fix_weilVacuum_on_placeSet D ψ S T χS χT om hW LS LT hS hT P (fun w hw => (hP w hw).2.2) f hf κ κ' hκ hκ'
  · push_neg at hex
    rw [eq_one_of_grpAt hex hκ.1, eq_one_of_grpAt hex hκ'.1, Prod.mk_one_one, map_one]
    rfl

end GlobalTheory.VacFixP
