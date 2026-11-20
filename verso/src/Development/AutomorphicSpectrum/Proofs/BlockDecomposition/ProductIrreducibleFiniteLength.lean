import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContragredientProductIrreducibleStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityPos
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ParabolicInductionFiniteLengthStatement

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

namespace GlobalTheory.CompanionTheory.ProdFL

/- English proof (translation)
The claim follows from `GlobalTheory.T.parabolic_induction_finite_length k _ _ _ _ _ _ (isSmooth_piTensor fun a => (x a).2.rep.smooth) (hasFiniteLength_of_isIrreducible (GlobalTheory.CompanionTheory.FrobJm.piTensor_rep_isIrreducible hA x))`.
-/
theorem hasFiniteLength_prodIrr {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {h N : ℕ} (x : Fin h → IrrGL k)
    (hd : ∑ a, (x a).1 = N) : HasFiniteLength (prodIrr x hd) :=
  GlobalTheory.T.parabolic_induction_finite_length k _ _ _ _ _ _ (isSmooth_piTensor fun a => (x a).2.rep.smooth)
    (hasFiniteLength_of_isIrreducible (GlobalTheory.CompanionTheory.FrobJm.piTensor_rep_isIrreducible hA x))

/- English proof (translation)
Introduce `hA _ _ x hd` and use `hasFiniteLength_prodIrr hA x hd`.
-/
theorem main : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    GlobalTheory.Published.IrreducibleAdmissibleGL → ∀ {h N : ℕ} (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N),
      HasFiniteLength (prodIrr x hd) :=
  fun hA _ _ x hd => hasFiniteLength_prodIrr hA x hd

end GlobalTheory.CompanionTheory.ProdFL

end
