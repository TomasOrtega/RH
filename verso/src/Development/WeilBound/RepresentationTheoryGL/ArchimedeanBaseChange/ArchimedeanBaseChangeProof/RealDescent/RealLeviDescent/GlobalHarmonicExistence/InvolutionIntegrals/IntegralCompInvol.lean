import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsThetaInvolution
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContinuousMapGL

noncomputable section

open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.Desc GlobalTheory.CompanionTheory.TwY

namespace PositivityTheory.Rg.BcB.Desc.Tw

section Haar

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]

end Haar

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

/- English proof (translation)
Use `Units.ext ?_` and prove the remaining obligations. Use extensionality with `i j`. Rewrite using `[thetaR_val, ← map_inv]`. Express the relevant statement in the definitionally equal form `f (σ (((g⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) j i)) = τ (f (((g⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) j i))`. Conclude with `h _`.
-/
theorem map_thetaR' {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (σ : A →+* A) (τ : B →+* B)
    (h : ∀ x, f (σ x) = τ (f x)) (g : GL (Fin n) A) :
    GeneralLinearGroup.map f (thetaR σ n g) = thetaR τ n (GeneralLinearGroup.map f g) := by
  refine Units.ext ?_
  ext i j
  rw [thetaR_val, ← map_inv]
  change f (σ (((g⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) j i)) =
    τ (f (((g⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) j i))
  exact h _

variable (E n) in

def tF : GL (Fin n) (Af E) →* GL (Fin n) (Af E) := thetaR (GlobalTheory.ThetaPull.cFin E) n

/- English proof (translation)
Unfold `thetaF finOf tF`. Rewrite using `[map_thetaR' (pFin E) (conjAd E) (GlobalTheory.ThetaPull.cFin E) GlobalTheory.ThetaPull.pFin_conjAd, pFin_finGL]`. Both sides reduce to the same expression.
-/
theorem thetaF_eq (g : GL (Fin n) (Af E)) : thetaF E n g = tF E n g := by
  unfold thetaF finOf tF
  rw [map_thetaR' (pFin E) (conjAd E) (GlobalTheory.ThetaPull.cFin E) GlobalTheory.ThetaPull.pFin_conjAd, pFin_finGL]
  rfl

end PositivityTheory.Rg.BcB.Desc.Tw

end
