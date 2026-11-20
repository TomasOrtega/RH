import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRCoreCut

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
open scoped Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP

noncomputable section

/- English proof (translation)
Establish `key : ∀ t : ℝ, F (g * NormedSpace.exp ((t : ℂ) • X)) = (F g).comp (π' (NormedSpace.exp ((t : ℂ) • X)))` using `fun t => hF _ (Formalism.FourierDecayAlt.P.QrD.exp_uw hX t) g hg`. Unfold `Formalism.REAL.RdV`. Simplify using `only [key]`. Set `L : (Wq →L[ℂ] Wq) →L[ℝ] (Wq →L[ℂ] Wp)` to `(ContinuousLinearMap.compL ℂ Wq Wq Wp (F g)).restrictScalars ℝ`. Establish `hL : ∀ A, L A = (F g).comp A` using `fun A => rfl`.

Establish `hd : HasDerivAt (fun t : ℝ => L (π' (NormedSpace.exp ((t : ℂ) • X)))) (L (P.QrD.dOp π' X)) 0` using `L.hasFDerivAt.comp_hasDerivAt 0 (Formalism.FourierDecayAlt.P.QrD.dOp_hasDeriv hπ hc hX)`. Simplify using `only [hL] at hd`. Conclude with `hd.deriv`.
-/
theorem rdV_rightCov {k r : ℕ} {z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp]
    [NormedAddCommGroup Wq] [NormedSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    {π' : Q.Mx k r → (Wq →L[ℂ] Wq)} (hπ : IsCRepOn (UWset k r z') π') (hc : ContinuousOn π' (UWset k r z'))
    {D : Set (Q.Mx k r)} {F : Q.Mx k r → (Wq →L[ℂ] Wp)}
    (hF : ∀ h ∈ UWset k r z', ∀ g ∈ Q.Glev k r (Fin.last r) ∩ D, F (g * h) = (F g).comp (π' h))
    {g : Q.Mx k r} (hg : g ∈ Q.Glev k r (Fin.last r) ∩ D) {X : Q.Mx k r} (hX : P.QrD.InLieW k r z' X) :
    RdV X F g = (F g).comp (P.QrD.dOp π' X) := by
  have key : ∀ t : ℝ, F (g * NormedSpace.exp ((t : ℂ) • X)) = (F g).comp (π' (NormedSpace.exp ((t : ℂ) • X))) :=
    fun t => hF _ (Formalism.FourierDecayAlt.P.QrD.exp_uw hX t) g hg
  unfold Formalism.REAL.RdV
  simp only [key]
  let L : (Wq →L[ℂ] Wq) →L[ℝ] (Wq →L[ℂ] Wp) :=
    (ContinuousLinearMap.compL ℂ Wq Wq Wp (F g)).restrictScalars ℝ
  have hL : ∀ A, L A = (F g).comp A := fun A => rfl
  have hd : HasDerivAt (fun t : ℝ => L (π' (NormedSpace.exp ((t : ℂ) • X)))) (L (P.QrD.dOp π' X)) 0 :=
    L.hasFDerivAt.comp_hasDerivAt 0 (Formalism.FourierDecayAlt.P.QrD.dOp_hasDeriv hπ hc hX)
  simp only [hL] at hd
  exact hd.deriv

/- English proof (translation)
Introduce `k r z' Wp Wq _ _ _ _ _ _ π' hπ hc _ D F _ _ _ hF g hg A hA`. Use `⟨⟨hA.1.1, hA.2.1⟩, ?_⟩` and prove the remaining obligations. Unfold `Rc P.QrD.ecOp`. Rewrite using `[rdV_rightCov hπ hc hF hg hA.1, rdV_rightCov hπ hc hF hg hA.2]`. Use extensionality with `v`.

Simplify using the standard rewrite rules.
-/
theorem right_covariance_holds : RightCov := by
  intro k r z' Wp Wq _ _ _ _ _ _ π' hπ hc _ D F _ _ _ hF g hg A hA
  refine ⟨⟨hA.1.1, hA.2.1⟩, ?_⟩
  unfold Rc P.QrD.ecOp
  rw [rdV_rightCov hπ hc hF hg hA.1, rdV_rightCov hπ hc hF hg hA.2]
  ext v
  simp

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP
