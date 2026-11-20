import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
import Formalism.LocalToGlobal.IndefiniteReal.RationalEmbedding
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiagGLConjApply
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CrdLatEqLatFrame
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EvalTIota
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

noncomputable section

namespace GlobalTheory.SeeConjReadIota

variable {D : D7}

/- English proof (translation)
Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Fix the arbitrary inputs or assume the hypotheses. Prove the components needed by the constructor for the conclusion.

Fix the arbitrary inputs or assume the hypotheses. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem mem_Kset_iff_mem_St (β : GL (Fin (Yc D 0).rank) (EAf D))
    (hβ : IsFrame β (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0)) (x : (Formalism.L2.SG.InstExistsPf.instOf D).Gf) :
    x ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Kset ↔ (x.1 : GL (Fin (Yc D 0).rank) (EAf D)) ∈ St β := by
  rw [GlobalTheory.ConjPlaceRed.crdLat_eq_latFrame] at hβ
  refine ⟨GlobalTheory.ConjPlaceRed.mem_St_of_Kset D β x hβ, fun hx => ?_⟩
  obtain ⟨h1, h2⟩ := (GlobalTheory.LevSplit.mem_St_iff β _ hβ (x.1 : GL (Fin (Yc D 0).rank) (EAf D))).1 hx
  intro v
  constructor
  · intro hv
    exact (GlobalTheory.ConjPlaceRed.mem_Lf D _).1 (h1 v ((GlobalTheory.ConjPlaceRed.mem_Lf D v).2 hv))
  · intro hv
    have h3 := h2 _ ((GlobalTheory.ConjPlaceRed.mem_Lf D _).2 hv)
    have e : Matrix.mulVec ((x.1 : GL (Fin (Yc D 0).rank) (EAf D))⁻¹).val
        (Matrix.mulVec (x.1 : GL (Fin (Yc D 0).rank) (EAf D)).val v) = v := by
      rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    have h4 : v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (GlobalTheory.PlaceModel.latFrame (Yc D 0)) := e ▸ h3
    exact (GlobalTheory.ConjPlaceRed.mem_Lf D v).1 h4

/- English proof (translation)
Substitute using the available equality. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Express the relevant assertion in an equivalent form by its definition. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem instanceIota_real_finite_stabilizer_unitary_characterization {I : Formalism.MainNotions.S.AutInst} (h : I = Formalism.L2.SG.InstExistsPf.instOf D) (β : GL (Fin (Yc D 0).rank) (EAf D))
    (hβ : IsFrame β (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0)) (κ : GA D (Yc D 0)) :
    ((((Formalism.IndefR.RationalEmbedding.iota D).trans (castGA h.symm)) κ).1 = 1 ↔ κ ∈ GfC (Yc D 0)) ∧
    ((((Formalism.IndefR.RationalEmbedding.iota D).trans (castGA h.symm)) κ).2 ∈ I.Kset ↔ finE (Yc D 0) κ ∈ St β) ∧
    finE (Yc D 0) κ ∈ UA D.sp.cm (Yc D 0).gram := by
  subst h
  have e : (Formalism.IndefR.RationalEmbedding.iota D).symm (Formalism.IndefR.RationalEmbedding.iota D κ) = κ := (Formalism.IndefR.RationalEmbedding.iota D).symm_apply_apply κ
  have h1 := Formalism.L2.SG.EvalTIota.brg_mem_GfC_i (Formalism.IndefR.RationalEmbedding.iota D κ)
  have hf := Formalism.L2.SG.EvalTIota.finE_brg_i (Formalism.IndefR.RationalEmbedding.iota D κ)
  rw [e] at h1 hf
  change ((Formalism.IndefR.RationalEmbedding.iota D κ).1 = 1 ↔ κ ∈ GfC (Yc D 0)) ∧
    ((Formalism.IndefR.RationalEmbedding.iota D κ).2 ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Kset ↔ finE (Yc D 0) κ ∈ St β) ∧
    finE (Yc D 0) κ ∈ UA D.sp.cm (Yc D 0).gram
  refine ⟨h1.symm, ?_, ?_⟩
  · rw [mem_Kset_iff_mem_St β hβ]
    exact iff_of_eq (congrArg (· ∈ St β) hf.symm)
  · have := ((Formalism.IndefR.RationalEmbedding.iota D κ).2).2
    exact hf ▸ this

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem read_iota : ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (β : GL (Fin (Yc D 0).rank) (EAf D)), IsFrame β (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → ∀ κ : GA D (Yc D 0), (((iotaX X h).toMulEquiv κ).1 = 1 ↔ κ ∈ GfC (Yc D 0)) ∧ (((iotaX X h).toMulEquiv κ).2 ∈ X.B.I.Kset ↔ finE (Yc D 0) κ ∈ St β) ∧ finE (Yc D 0) κ ∈ UA D.sp.cm (Yc D 0).gram := by
  intro D X h β hβ κ
  exact instanceIota_real_finite_stabilizer_unitary_characterization h β hβ κ

end GlobalTheory.SeeConjReadIota
