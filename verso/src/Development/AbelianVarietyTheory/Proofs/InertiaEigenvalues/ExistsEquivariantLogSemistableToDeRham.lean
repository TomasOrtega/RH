import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLogTiltKummerCoboundaryBdRStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BstLog

/- English proof (translation)
Introduce `l _ P AI T`. Take `⟨u, hu⟩` from `GlobalTheory.T.exists_log_tilt_kummerCoboundary_BdR l P AI T`. Establish `hcomm : ∀ (g : GQ l) (z : P.R.B), P.ιB (P.actQ g z) = P.actQdR g (P.ιB z)`. Introduce `g z`. Use `(P.PD (botExt l)).ι_comm ⟨g, mem_GK_botExt g⟩ z` as an intermediate fact.

Rewrite `this` using `[P.PD_ι, P.PD_actB, P.PD_ι, P.PD_actdR]`. Then use the resulting hypothesis. Set `ι : Bst P →ₐ[ℚ_[l]] P.R.BdR` to `Polynomial.eval₂AlgHom P.ιB u (fun _ => Commute.all _ _)`. Use `⟨ι, fun b => Polynomial.eval₂_C _ _, fun g x => ?_⟩` and prove the remaining obligations. Establish `h : ι.comp (actSt P g) = ((P.actQdR g : P.R.BdR ≃ₐ[ℚ_[l]] P.R.BdR) : P.R.BdR →ₐ[ℚ_[l]] P.R.BdR).comp ι`. Apply `Polynomial.algHom_ext'` to reduce the goal to its premises.

Use extensionality with `b show Polynomial.eval₂ (P.ιB : P.R.B →+* P.R.BdR) u (actSt P g (Polynomial.C b)) = P.actQdR g (Polynomial.eval₂ (P.ιB : P.R.B →+* P.R.BdR) u (Polynomial.C b))`. Rewrite using `[actSt_C, Polynomial.eval₂_C, Polynomial.eval₂_C]`. Conclude with `hcomm g b`. Use `show Polynomial.eval₂ (P.ιB : P.R.B →+* P.R.BdR) u (actSt P g Polynomial.X) = P.actQdR g (Polynomial.eval₂ (P.ιB : P.R.B →+* P.R.BdR) u Polynomial.X)`. Rewrite using `[actSt_X, Polynomial.eval₂_add, Polynomial.eval₂_X, Polynomial.eval₂_C, hu]`.

Both sides reduce to the same expression. Conclude with `congrArg (fun F : Bst P →ₐ[ℚ_[l]] P.R.BdR => F x) h`.
-/
theorem iota_exists : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI),
    ∃ ι : Bst P →ₐ[ℚ_[l]] P.R.BdR, (∀ b, ι (Polynomial.C b) = P.ιB b) ∧
      (∀ (g : GQ l) (x : Bst P), ι (actSt P g x) = P.actQdR g (ι x)) := by
  intro l _ P AI T
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_log_tilt_kummerCoboundary_BdR l P AI T
  have hcomm : ∀ (g : GQ l) (z : P.R.B), P.ιB (P.actQ g z) = P.actQdR g (P.ιB z) := by
    intro g z
    have := (P.PD (botExt l)).ι_comm ⟨g, mem_GK_botExt g⟩ z
    rwa [P.PD_ι, P.PD_actB, P.PD_ι, P.PD_actdR] at this
  let ι : Bst P →ₐ[ℚ_[l]] P.R.BdR := Polynomial.eval₂AlgHom P.ιB u (fun _ => Commute.all _ _)
  refine ⟨ι, fun b => Polynomial.eval₂_C _ _, fun g x => ?_⟩
  have h : ι.comp (actSt P g) = ((P.actQdR g : P.R.BdR ≃ₐ[ℚ_[l]] P.R.BdR) : P.R.BdR →ₐ[ℚ_[l]] P.R.BdR).comp ι := by
    apply Polynomial.algHom_ext'
    · ext b
      show Polynomial.eval₂ (P.ιB : P.R.B →+* P.R.BdR) u (actSt P g (Polynomial.C b)) =
        P.actQdR g (Polynomial.eval₂ (P.ιB : P.R.B →+* P.R.BdR) u (Polynomial.C b))
      rw [actSt_C, Polynomial.eval₂_C, Polynomial.eval₂_C]
      exact hcomm g b
    · show Polynomial.eval₂ (P.ιB : P.R.B →+* P.R.BdR) u (actSt P g Polynomial.X) =
        P.actQdR g (Polynomial.eval₂ (P.ιB : P.R.B →+* P.R.BdR) u Polynomial.X)
      rw [actSt_X, Polynomial.eval₂_add, Polynomial.eval₂_X, Polynomial.eval₂_C, hu]
      rfl
  exact congrArg (fun F : Bst P →ₐ[ℚ_[l]] P.R.BdR => F x) h

end GlobalTheory.BstLog
