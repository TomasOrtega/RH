import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.CosetCount
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstEqOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JordanHolderMultiplicityNormalizedBorelJacquetUn

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel

namespace GlobalTheory.CompanionTheory.TorusExpU

/- English proof (translation)
Unfold `PositivityTheory.Rg.BcB.F.Tail.PExp.TorusExp`. Introduce `k _ _ _ _ n V _ _ π ϖ hϖ ξ c y hy hfix hx t`. Establish `hord : ord k ϖ = 1`. Conclude with `ord_eq_one hϖ`. Use `GlobalTheory.CompanionTheory.ExtCharU.extChar k n _ (jacB π) y ϖ ξ c hy hord ?_ ?_ t` and prove the remaining obligations.

Introduce `s hs`. Establish `h1 : ((deltaHalf k fun _ : Fin n => Unit).comp (leviTorus k (Fin n)).toMonoidHom) s = 1`. Simplify using `using GlobalTheory.SmGL.UnramFixed.deltaHalf_torusO k hs`. Establish `h2 : jacBU π s y = y` using `by simpa using hfix ⟨s, hs⟩`. Rewrite using `[GlobalTheory.SmGL.UnramFixed.jacB_apply, h1, h2]`.

Simplify using the standard rewrite rules. Introduce `x hxa`. Establish `hD : ((deltaHalf k fun _ : Fin n => Unit).comp (leviTorus k (Fin n)).toMonoidHom) (fun i => ϖ ^ x i) = deltaHalf k (fun _ : Fin n => Unit) (leviTorus k (Fin n) fun i => ϖ ^ x i)` using `rfl`. Establish `hne : ((deltaHalf k (fun _ : Fin n => Unit) (leviTorus k (Fin n) fun i => ϖ ^ x i) : ℂˣ) : ℂ) ≠ 0` using `Units.ne_zero _`. Rewrite using `[GlobalTheory.SmGL.UnramFixed.jacB_apply, hD, hx x hxa, smul_smul]`.

Use `congr 1`. Rewrite using `[Units.val_inv_eq_inv_val, mul_comm, mul_assoc, mul_inv_cancel₀ hne, mul_one]`. Both sides reduce to the same expression.
-/
theorem torusExp : PositivityTheory.Rg.BcB.F.Tail.PExp.TorusExp := by
  unfold PositivityTheory.Rg.BcB.F.Tail.PExp.TorusExp
  intro k _ _ _ _ n V _ _ π ϖ hϖ ξ c y hy hfix hx t
  have hord : ord k ϖ = 1 := by
    exact ord_eq_one hϖ
  refine GlobalTheory.CompanionTheory.ExtCharU.extChar k n _ (jacB π) y ϖ ξ c hy hord ?_ ?_ t
  · intro s hs
    have h1 : ((deltaHalf k fun _ : Fin n => Unit).comp (leviTorus k (Fin n)).toMonoidHom) s = 1 := by
      simpa using GlobalTheory.SmGL.UnramFixed.deltaHalf_torusO k hs
    have h2 : jacBU π s y = y := by simpa using hfix ⟨s, hs⟩
    rw [GlobalTheory.SmGL.UnramFixed.jacB_apply, h1, h2]
    simp
  · intro x hxa
    have hD : ((deltaHalf k fun _ : Fin n => Unit).comp (leviTorus k (Fin n)).toMonoidHom)
        (fun i => ϖ ^ x i) = deltaHalf k (fun _ : Fin n => Unit) (leviTorus k (Fin n) fun i => ϖ ^ x i) := rfl
    have hne : ((deltaHalf k (fun _ : Fin n => Unit) (leviTorus k (Fin n) fun i => ϖ ^ x i) : ℂˣ) : ℂ) ≠ 0 :=
      Units.ne_zero _
    rw [GlobalTheory.SmGL.UnramFixed.jacB_apply, hD, hx x hxa, smul_smul]
    congr 1
    rw [Units.val_inv_eq_inv_val, mul_comm, mul_assoc, mul_inv_cancel₀ hne, mul_one]
    rfl

end GlobalTheory.CompanionTheory.TorusExpU

end
