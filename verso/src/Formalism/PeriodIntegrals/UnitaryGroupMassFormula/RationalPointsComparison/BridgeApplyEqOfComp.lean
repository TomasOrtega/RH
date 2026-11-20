import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FundamentalEquivalence.AdBridge

noncomputable section

namespace Formalism.L2.SG.AdBridge

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open Formalism.MainNotions.S (AutInst uMat)

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
private theorem thetaV_inclR' (I : AutInst) (v : InfinitePlace I.F) (y : I.E) :
    thetaV I v (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) y) = I.φ v y := by
  simp [thetaV, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
private theorem tauF_inclR' (I : AutInst) (y : I.E) :
    tauF I (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) y) = Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) y := by
  simp [tauF, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR, Formalism.UG.inclE]

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
private theorem map_inclR_map_thetaV (I : AutInst) (v : InfinitePlace I.F) (M : Matrix (Fin I.n) (Fin I.n) I.E) :
    (M.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F))).map (thetaV I v) = M.map (I.φ v) := by
  ext i j
  simp only [Matrix.map_apply, thetaV_inclR']

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
private theorem map_inclR_map_tauF (I : AutInst) (M : Matrix (Fin I.n) (Fin I.n) I.E) :
    (M.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F))).map (tauF I) = M.map (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)) := by
  ext i j
  simp only [Matrix.map_apply, tauF_inclR']

/- English proof (translation)
Establish an intermediate fact. Treat this case separately. Treat this case separately. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem bridge_apply_eq_of_comp (I : AutInst) (e : I.GA ≃ₜ* HAd I) (he : IsBridge I e)
    (x : I.GA) (h : HAd I) (h1 : ∀ v, uMat (x.1 v) = ofHAInf I h v)
    (h2 : I.fmat x.2 = ofHAFin I h) : e x = h := by
  have hs : e (e.symm h) = h := by
    first
    | exact e.apply_symm_apply h
    | simp
  have hB := he (e.symm h)
  rw [hs] at hB
  obtain ⟨h1', h2'⟩ := hB
  have hx : x = e.symm h := by
    refine Prod.ext (funext fun v => ?_) ?_
    · exact Subtype.ext (Units.ext ((h1 v).trans (h1' v).symm))
    · exact Subtype.ext (Units.ext (h2.trans h2'.symm))
  rw [hx, hs]

/- English proof (translation)
Treat this case separately. Treat this case separately. A detailed English derivation is pending.
-/
theorem sigR_inclR_star (I : AutInst) (y : I.E) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig
              (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) y) =
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) (starRingEnd I.E y) := by
  first
  | (simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR, Formalism.BasicNotions.CMData.sig]; done)
  | rfl

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem bc_inclR_mem_HR (I : AutInst) (γ : GL (Fin I.n) I.E)
    (hγ : γ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J) :
    Formalism.UG.bc (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F)) γ ∈
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J := by
  have hγ' : Formalism.UG.cT (starRingEnd I.E) (γ : Matrix (Fin I.n) (Fin I.n) I.E) * I.J * (γ : Matrix (Fin I.n) (Fin I.n) I.E) = I.J := hγ
  have key : Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig) ((γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F))) =
      (Formalism.UG.cT (starRingEnd I.E) (γ : Matrix (Fin I.n) (Fin I.n) I.E)).map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F)) := by
    ext i j
    simp only [Formalism.UG.cT, Matrix.map_apply, Matrix.transpose_apply, sigR_inclR_star]
  show Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig) ((γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F))) *
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.J * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F)) =
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.J
  rw [key, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR, ← Matrix.map_mul, ← Matrix.map_mul, hγ']

/- English proof (translation)
Replace the relevant objects with their definitions. Fix the arbitrary inputs or assume the hypotheses. By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact.

Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Establish an intermediate fact. Treat this case separately. Treat this case separately. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem adBridgeGF_main (I : AutInst) : AdBridgeGF I := by
  unfold AdBridgeGF
  intro e he
  ext h
  constructor
  · rintro ⟨x, hxG, rfl⟩
    obtain ⟨γ, hγ, hinf, hfin⟩ := hxG
    have hmem := bc_inclR_mem_HR I γ hγ
    let h0 : HAd I := (⟨Formalism.UG.bc (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F)) γ, hmem⟩ :
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J)
    have hm0 : hmat I h0 = (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F)) := rfl
    have hx : e x = h0 := by
      apply bridge_apply_eq_of_comp I e he x h0
      · intro v
        rw [hinf v]
        unfold ofHAInf
        rw [hm0, map_inclR_map_thetaV]
      · rw [hfin]
        unfold ofHAFin
        rw [hm0, map_inclR_map_tauF]
    rw [hx]
    show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J h0 ∈
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HFin (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J
    exact Subgroup.mem_map.mpr ⟨γ, hγ, rfl⟩
  · intro hh
    have hh' : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J h ∈
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HFin (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J := hh
    obtain ⟨γ, hγ, hγh⟩ := Subgroup.mem_map.mp hh'
    have hm : hmat I h = (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F)) := by
      show ((Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J h :
        GL (Fin I.n) ((Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) ⊗[I.F] I.E)) :
        Matrix (Fin I.n) (Fin I.n) ((Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) ⊗[I.F] I.E)) = _
      rw [← hγh]
      rfl
    have hs : e (e.symm h) = h := by
      first
      | exact e.apply_symm_apply h
      | simp
    refine ⟨e.symm h, ?_, hs⟩
    simp only [Formalism.MainNotions.S.AutInst.GFset, Set.mem_setOf_eq]
    refine ⟨γ, hγ, fun v => ?_, ?_⟩
    · rw [(he (e.symm h)).1 v, hs]
      unfold ofHAInf
      rw [hm, map_inclR_map_thetaV]
    · rw [(he (e.symm h)).2, hs]
      unfold ofHAFin
      rw [hm, map_inclR_map_tauF]

end Formalism.L2.SG.AdBridge
