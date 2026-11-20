import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EvalTPh
import Formalism.LocalToGlobal.IndefiniteReal.EqZeroOfVec
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.DensLow
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.ContinuousSplitInv
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GEqBase
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.InfFam

noncomputable section

open MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.ProjRows Formalism.MainNotions.S
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice
open scoped InnerProductSpace TensorProduct

namespace Formalism.L2.SG.EvalTEquiv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S)

/- English proof (translation)
Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem sm_stable_uh (τ : D.what₂.Tau) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) {w : M.H τ} (hw : w ∈ M.sm τ) : M.rep τ g w ∈ M.sm τ := by
  obtain ⟨gg, rfl⟩ := Formalism.IndefR.Eqv.KerDiag.gt_of_uh τ M hg
  exact Formalism.IndefR.SchurOrthogonalityAlt.sm_stable M τ gg hw

abbrev comp (a : GA D V) (τ : D.what₂.Tau) : Matrix (Fin V.rank) (Fin V.rank) ℂ :=
  infMat D.sp.cm.sig V.gram (Formalism.IndefR.Eqv.thetaC D τ) a

open Classical in

def translS (a : GA D V) (s : Finset D.what₂.Tau) (v : M.Vec) : M.Vec := fun τ =>
  if τ ∈ s then ⟨M.rep τ (comp a τ) (v τ), sm_stable_uh M τ (Formalism.IndefR.Eqv.infMat_unitary' D V a τ) (v τ).2⟩
  else v τ

def transl (a : GA D V) (v : M.Vec) : M.Vec := translS M a Finset.univ v

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem transl_apply (a : GA D V) (v : M.Vec) (τ : D.what₂.Tau) :
    (transl M a v τ : M.H τ) = M.rep τ (comp a τ) (v τ) := by
  simp [transl, translS]

variable {M}

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Proceed by induction. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. Apply an available result and prove the equalities needed to match it to the conclusion. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Establish an intermediate fact.

Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Apply function extensionality and compare values at an arbitrary argument.

Consider separately whether the proposition holds or fails. Substitute using the available equality. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem equiv_ginf {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} (hθ : IsInfFam θ) {T : MMap M}
    (hT : Formalism.IndefR.AutomorphicEvaluation.EqCont θ M T) {a : GA D V} (ha : a ∈ GinfC V) (v : M.Vec) (y : GA D V) :
    T v (y * a) = T (transl M a v) y := by
  classical
  obtain rfl := Formalism.IndefR.Eqv.eq_thetaC D hθ
  set gs : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ := fun τ => comp a τ with hgsd
  have hgs : Formalism.IndefR.Eqv.IsUnitFam D V gs := Formalism.IndefR.Eqv.infMat_unitary' D V a
  have hu : ∀ s : Finset D.what₂.Tau, Formalism.IndefR.Eqv.IsUnitFam D V (fun τ => if τ ∈ s then gs τ else 1) := by
    intro s τ
    by_cases hτ : τ ∈ s
    · simp only [hτ, if_true]; exact hgs τ
    · simp only [hτ, if_false]; simp
  have key : ∀ s : Finset D.what₂.Tau, ∀ y, T v (y * Formalism.IndefR.Eqv.famH D V _ (hu s)) = T (translS M a s v) y := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro y
      have e : Formalism.IndefR.Eqv.famH D V _ (hu ∅) = 1 := by
        apply Formalism.IndefR.Eqv.matA_inj D V
        rw [Formalism.IndefR.Eqv.matA_famH, Formalism.IndefR.Eqv.matA_one]
        convert Formalism.IndefR.Eqv.famM_one D V using 2
        funext τ
        simp
      have e2 : translS M a ∅ v = v := by
        funext τ; simp [translS]
      rw [e, mul_one, e2]
    | insert τ0 s hτ0 ih =>
      intro y
      have e : Formalism.IndefR.Eqv.famH D V _ (hu (insert τ0 s)) =
          Formalism.IndefR.Eqv.atH D V τ0 (gs τ0) (hgs τ0) * Formalism.IndefR.Eqv.famH D V _ (hu s) := by
        apply Formalism.IndefR.Eqv.matA_inj D V
        rw [Formalism.IndefR.Eqv.matA_famH, Formalism.IndefR.Eqv.matA_mul, Formalism.IndefR.Eqv.matA_atH, Formalism.IndefR.Eqv.matA_famH]
        apply Formalism.IndefR.Eqv.mat_ext D
        · intro τ
          rw [Matrix.map_mul, Formalism.IndefR.Eqv.psi_famM, Formalism.IndefR.Eqv.psi_atM, Formalism.IndefR.Eqv.psi_famM]
          by_cases h : τ = τ0
          · subst h; simp [hτ0]
          · simp [h]
        · rw [Matrix.map_mul, Formalism.IndefR.Eqv.fin_famM, Formalism.IndefR.Eqv.fin_atM, Formalism.IndefR.Eqv.fin_famM,
            Matrix.one_mul]
      rw [e, ← mul_assoc, ih]
      have hw : M.rep τ0 (gs τ0) ((translS M a s v τ0 : M.H τ0)) ∈ M.sm τ0 :=
        sm_stable_uh M τ0 (hgs τ0) (translS M a s v τ0).2
      have hq := hT.equiv τ0 (gs τ0) (hgs τ0) (translS M a s v) ⟨_, hw⟩ rfl
      have hq' := congrFun hq y
      simp only [rTr] at hq'
      rw [Formalism.IndefR.Eqv.atTau_eq D V τ0 (gs τ0) (hgs τ0)] at hq'
      rw [← hq']
      refine congrFun (congrArg T ?_) y
      funext τ
      by_cases h : τ = τ0
      · subst h
        rw [Function.update_self]
        apply Subtype.ext
        simp [translS, hτ0, hgsd]
      · rw [Function.update_of_ne h]
        simp [translS, h]
  have e : a = Formalism.IndefR.Eqv.famH D V _ (hu Finset.univ) :=
    Formalism.IndefR.Eqv.famH_unique D V _ (hu Finset.univ) a ha (fun τ => by simp [gs])
  conv_lhs => rw [e]
  exact key Finset.univ y

section Read

variable {M : DSModel (D.sp.Y 0) S} {E : Submodule ℂ (MMap M)} {X : Formalism.L2.SG.HidaSetting.HidaSetting D}
  {ι : GA D (D.sp.Y 0) ≃* X.B.I.GA} {t : GA D (D.sp.Y 0)} {v₀ : M.Vec}

end Read

end Formalism.L2.SG.EvalTEquiv

end
