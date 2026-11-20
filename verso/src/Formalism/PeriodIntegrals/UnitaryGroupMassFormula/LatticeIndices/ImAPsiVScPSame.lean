import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ImAVecVMulVec

noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge MassDataIdxStIm PI.MassDataKppVolLemmas
open scoped TensorProduct Matrix

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I)

def scP (p : TypX X) (c : Fv X.B.I.F p.1) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F :=
  eOf X.B.I (singleV X.B.I.F p.1 c)

/- English proof (translation)
Simplify using the standard rewrite rules. Both sides reduce to the same expression.
-/
theorem imA_psiV_eOf (v : HeightOneSpectrum (𝓞 X.B.I.F)) (a : Formalism.MainNotions.S.Af X.B.I.F) :
    PI.FinKW.psiV X.B.I v (eOf X.B.I a) = algebraMap (Fv X.B.I.F v) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) (a v) := by
  simp [PI.FinKW.psiV, eOf]
  rfl

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem component_scalarAt_same (p : TypX X) (c : Fv X.B.I.F p.1) :
    PI.FinKW.psiV X.B.I p.1 (scP X p c) = algebraMap (Fv X.B.I.F p.1) (Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E) c := by
  rw [scP, imA_psiV_eOf, Comp_single_same]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem component_scalarAt_of_ne (p : TypX X) (v : HeightOneSpectrum (𝓞 X.B.I.F)) (h : v ≠ p.1)
    (c : Fv X.B.I.F p.1) : PI.FinKW.psiV X.B.I v (scP X p c) = 0 := by
  rw [scP, imA_psiV_eOf, Comp_single_ne X.B.I p.1 v h, map_zero]

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Substitute using the available equality. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem scalarAt_mem_integralAdeles (p : TypX X) (c : p.1.adicCompletionIntegers X.B.I.F) :
    scP X p (c : Fv X.B.I.F p.1) ∈ Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E := by
  apply LocB_eOf_mem
  intro v
  by_cases h : v = p.1
  · subst h; show singleV X.B.I.F _ _ _ ∈ _; rw [Comp_single_same]; exact c.2
  · show singleV X.B.I.F p.1 _ v ∈ _; rw [Comp_single_ne X.B.I p.1 v h]; exact zero_mem _

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem imA_smul_alg (p : TypX X) (c : p.1.adicCompletionIntegers X.B.I.F)
    (u : Fin X.B.I.n → Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E) :
    c • u = algebraMap (Fv X.B.I.F p.1) (Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E) (c : Fv X.B.I.F p.1) • u := by
  funext i
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← Algebra.smul_def]
  rfl

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.
-/
theorem imA_vecV_sub (v : HeightOneSpectrum (𝓞 X.B.I.F)) (a b : Fin X.B.I.n → X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) :
    PI.FinKW.vecV X.B.I v (a - b) = PI.FinKW.vecV X.B.I v a - PI.FinKW.vecV X.B.I v b := by
  funext i; simp [PI.FinKW.vecV]

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.
-/
theorem imA_vecV_smul' (v : HeightOneSpectrum (𝓞 X.B.I.F)) (t : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F)
    (w : Fin X.B.I.n → X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) :
    PI.FinKW.vecV X.B.I v (t • w) = PI.FinKW.psiV X.B.I v t • PI.FinKW.vecV X.B.I v w := by
  funext i; simp [PI.FinKW.vecV, map_mul]

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. A detailed English derivation is pending.
-/
theorem imA_vec_ext (w : Fin X.B.I.n → X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F)
    (h : ∀ v, PI.FinKW.vecV X.B.I v w = 0) : w = 0 := by
  funext i
  exact PI.FinKW.local_vector_injective X.B.I (w i) fun v => congrFun (h v) i

end MassDataIdxSteps
