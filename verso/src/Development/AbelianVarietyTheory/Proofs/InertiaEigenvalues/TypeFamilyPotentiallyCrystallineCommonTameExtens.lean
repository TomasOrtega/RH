import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixOfStabilizerTrivial
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MonodromyZeroOfDeRhamCharacter
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MaxUnramifiedSubfieldStableOfNormal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AevalEqOfMemDpcris
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedFamilyPotentiallyCrystallineFrobStableStatement
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
open Formalism.MainNotions.PairedCharacterCondition Polynomial
open Classical

namespace GlobalTheory.PotDirect

/- English proof (translation)
Introduce `D P hT hFo h0 hBr hPH hChi hIE h12 hTen hTP i k hl r ρ hr π hπ hdec Xs hπX hTL w hw`. Take `⟨Y, u, hu, hY, hYc, hX, hχ, hχσ⟩` from `GlobalTheory.TypeInertia.inertial_chars D P hT h0 hPH hChi i k hl r hr Xs hTL w hw`. Establish `hχc : Continuous fun g => ((chiGL i g : GL (Fin 1) (D.nd.O i)) : Matrix (Fin 1) (Fin 1) (D.nd.O i))`. Use `continuous_pi fun a => continuous_pi fun b => ?_` and prove the remaining obligations. Establish `hab : a = b` using `Subsingleton.elim a b`.

Substitute `hab` using the available equality. Simplify `D.nd.chi_cont i 1` using `[chiGL, Matrix.scalar]`. Take `⟨K', h, hN, hF', hS, hpc, hpc0, hker⟩` from `GlobalTheory.PotExt.main D P h12 i k w hw Y (fun y hy => (hY y hy).1) (↥Xs) D.R.nV (fun x => r x) 1 (chiGL i) (fun x => (hr x).1) hχc (fun x => (hX x x.2).1) hχ`. Take `⟨ch, hch⟩` from `GlobalTheory.InertiaChars.main D P hTP hIE i k hl w hw Y hY K' h hN hF' hS hker`. Establish `hdeg` using `(GlobalTheory.TypeDegOne.degree_one D i k hl).2 w hw`.

Use `GlobalTheory.T.twistedFamily_potentiallyCrystalline_frobStable D hTen i w hw hdeg r Xs K' h hN hF' hS (Y.image ch) (ch u) (D.R.nV + 1) (Finset.mem_image_of_mem _ hu) (Finset.card_image_le.trans hYc) (fun x _ => (hr x).1) ?_ hpc0 ?_` and prove the remaining obligations. Introduce `x hx`. Take `⟨M, hM, hσ⟩` from `(hX x hx).2`. Conclude with `⟨hpc ⟨x, hx⟩, hch Y subset_rfl _ (r x) (hr x).1 (hpc ⟨x, hx⟩) M hM hσ⟩`. Use `hch {u} (by simpa using hu) 1 (chiGL i) hχc hpc0 {u} (by simp) (fun σ hσ => by simpa using hχσ σ hσ)` as an intermediate fact.

Simplify using `using this`.
-/
theorem main : StepPotDirect := by
  intro D P hT hFo h0 hBr hPH hChi hIE h12 hTen hTP i k hl r ρ hr π hπ hdec Xs hπX hTL w hw
  obtain ⟨Y, u, hu, hY, hYc, hX, hχ, hχσ⟩ := GlobalTheory.TypeInertia.inertial_chars D P hT h0 hPH hChi i k hl r hr Xs hTL w hw
  have hχc : Continuous fun g => ((chiGL i g : GL (Fin 1) (D.nd.O i)) : Matrix (Fin 1) (Fin 1) (D.nd.O i)) := by
    refine continuous_pi fun a => continuous_pi fun b => ?_
    have hab : a = b := Subsingleton.elim a b
    subst hab
    simpa [chiGL, Matrix.scalar] using D.nd.chi_cont i 1
  obtain ⟨K', h, hN, hF', hS, hpc, hpc0, hker⟩ := GlobalTheory.PotExt.main D P h12 i k w hw Y (fun y hy => (hY y hy).1) (↥Xs) D.R.nV
    (fun x => r x) 1 (chiGL i) (fun x => (hr x).1) hχc (fun x => (hX x x.2).1) hχ
  obtain ⟨ch, hch⟩ := GlobalTheory.InertiaChars.main D P hTP hIE i k hl w hw Y hY K' h hN hF' hS hker
  have hdeg := (GlobalTheory.TypeDegOne.degree_one D i k hl).2 w hw
  refine GlobalTheory.T.twistedFamily_potentiallyCrystalline_frobStable D hTen i w hw hdeg r Xs K' h hN hF' hS (Y.image ch) (ch u) (D.R.nV + 1)
    (Finset.mem_image_of_mem _ hu) (Finset.card_image_le.trans hYc) (fun x _ => (hr x).1) ?_ hpc0 ?_
  · intro x hx
    obtain ⟨M, hM, hσ⟩ := (hX x hx).2
    exact ⟨hpc ⟨x, hx⟩, hch Y subset_rfl _ (r x) (hr x).1 (hpc ⟨x, hx⟩) M hM hσ⟩
  · have := hch {u} (by simpa using hu) 1 (chiGL i) hχc hpc0 {u} (by simp) (fun σ hσ => by simpa using hχσ σ hσ)
    simpa using this

end GlobalTheory.PotDirect
