import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PositionOneOfUnique
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SplitWeil GlobalTheory.LocFrame
open GlobalTheory.EmbChart (idem)
open GlobalTheory.StepData (LatFrame)
open GlobalTheory.RootEx (colE rowE)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (schT schM)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.SrcHalfOne
open GlobalTheory.EmbChart (tensAt atPlace)
open GlobalTheory.AdelicU (splitProj compFin isCMExt_host)
variable {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)}

/- English proof (translation)
The claim follows from `Formalism.L2.Theta.cA_cA z`.
-/
theorem cA_cA' (z : AE D) : cA D (cA D z) = z := Formalism.L2.Theta.cA_cA z
/- English proof (translation)
Express the relevant statement in the definitionally equal form `a ⊗ₜ[D.host.F] D.sp.cm.sig 1 = _`. Rewrite using `[map_one]`. Both sides reduce to the same expression.
-/
theorem cA_alg (a : AF D.host.F) : cA D (algebraMap (AF D.host.F) (AE D) a) = algebraMap (AF D.host.F) (AE D) a := by
  change a ⊗ₜ[D.host.F] D.sp.cm.sig 1 = _
  rw [map_one]; rfl

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Consider the case `tmul a x => rfl`.
-/
theorem compFin_cA (z : AE D) : compFin D.host.F D.host.E v (cA D z) = sigR _ D.sp.cm.sig (compFin D.host.F D.host.E v z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a x => rfl

variable (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v)

/- English proof (translation)
The claim follows from `((chart_piW τ).2.1 _).2 (GlobalTheory.EmbChart.isSplitIdem_idem τ).2.1`.
-/
theorem piW_cA_idem : piW τ (cA D (idem τ)) = 0 :=
  ((chart_piW τ).2.1 _).2 (GlobalTheory.EmbChart.isSplitIdem_idem τ).2.1

/- English proof (translation)
Express the relevant statement in the definitionally equal form `splitProj τ (compFin _ _ v (idem τ)) = 1`. Rewrite using `[GlobalTheory.EmbChart.compFin_idem, GlobalTheory.AdelicU.splitProj_splitIdem]`.
-/
theorem piW_idem : piW τ (idem τ) = 1 := by
  change splitProj τ (compFin _ _ v (idem τ)) = 1
  rw [GlobalTheory.EmbChart.compFin_idem, GlobalTheory.AdelicU.splitProj_splitIdem]

/- English proof (translation)
Rewrite using `[(chart_piW τ).2.2.1]`. Conclude with `GlobalTheory.AdelicU.evalV_singleFin_self v a`.
-/
theorem piW_alg (a : Fv D.host.F v) : piW τ (algebraMap (AF D.host.F) (AE D) (atPlace v a)) = a := by
  rw [(chart_piW τ).2.2.1]
  exact GlobalTheory.AdelicU.evalV_singleFin_self v a

/- English proof (translation)
Express the relevant statement in the definitionally equal form `splitProj τ (compFin _ _ v (cA D z)) = _`. Rewrite using `[compFin_cA, GlobalTheory.AdelicU.splitProj_comp]`.
-/
theorem piW_cA (z : AE D) : piW τ (cA D z) = splitProj (τ.comp D.sp.cm.sig) (compFin D.host.F D.host.E v z) := by
  change splitProj τ (compFin _ _ v (cA D z)) = _
  rw [compFin_cA, GlobalTheory.AdelicU.splitProj_comp]

def plcC (y : Fv D.host.F v) : AE D := cA D (idem τ) * algebraMap (AF D.host.F) (AE D) (atPlace v y)

def plcW (y : Fv D.host.F v) : AE D := idem τ * algebraMap (AF D.host.F) (AE D) (atPlace v y)

/- English proof (translation)
Rewrite using `[plcC, map_mul, piW_cA_idem, zero_mul]`.
-/
theorem piW_plcC (y) : piW τ (plcC τ y) = 0 := by rw [plcC, map_mul, piW_cA_idem, zero_mul]
/- English proof (translation)
Rewrite using `[plcC, map_mul, cA_cA', cA_alg, map_mul, piW_idem, piW_alg, one_mul]`.
-/
theorem piW_cA_plcC (y) : piW τ (cA D (plcC τ y)) = y := by
  rw [plcC, map_mul, cA_cA', cA_alg, map_mul, piW_idem, piW_alg, one_mul]

/- English proof (translation)
Rewrite using `[plcC, plcC, plcC, map_add, map_add, mul_add]`.
-/
theorem plcC_add (y y') : plcC τ (y + y') = plcC τ y + plcC τ y' := by
  rw [plcC, plcC, plcC, map_add, map_add, mul_add]

/- English proof (translation)
Establish `hev : Continuous (GlobalTheory.AdelicU.evFin D.host.F v)` using `(RestrictedProduct.continuous_eval v).comp continuous_snd`. Establish `h` using `GlobalTheory.AutFunCompare.continuous_tensNU (E := D.host.E) (GlobalTheory.AdelicU.evFin D.host.F v).toLinearMap (fun a b => map_mul (GlobalTheory.AdelicU.evFin D.host.F v) a b) hev`. Conclude with `(GlobalTheory.AdelicU.continuous_splitProj τ).comp h`.
-/
theorem continuous_piW : Continuous (piW τ) := by
  have hev : Continuous (GlobalTheory.AdelicU.evFin D.host.F v) :=
    (RestrictedProduct.continuous_eval v).comp continuous_snd
  have h := GlobalTheory.AutFunCompare.continuous_tensNU (E := D.host.E) (GlobalTheory.AdelicU.evFin D.host.F v).toLinearMap
    (fun a b => map_mul (GlobalTheory.AdelicU.evFin D.host.F v) a b) hev
  exact (GlobalTheory.AdelicU.continuous_splitProj τ).comp h

/- English proof (translation)
The claim follows from `(GlobalTheory.EmbChart.isSplitIdem_idem τ).1`.
-/
theorem idem_mul_self : idem τ * idem τ = idem τ := (GlobalTheory.EmbChart.isSplitIdem_idem τ).1

def plcCH : Fv D.host.F v →+ AE D := AddMonoidHom.mk' (plcC τ) (plcC_add τ)

section Frame

variable (V : HSp D) {ι : Type} [Fintype ι] [DecidableEq ι] (β : LatFrame (Fv D.host.F v) ι (Fin V.rank))

def rowL (y : Fin V.rank → D.host.E) : ι → Fv D.host.F v := (τ ∘ (star y ᵥ* V.gram)) ᵥ* cols β

def crd (x : Fin V.rank → D.host.E) : ι → Fv D.host.F v := what₂ β *ᵥ (τ ∘ x)

end Frame

section FJ

variable {V V₀ : HSp D} {σ : ℕ} (d : HypDec V V₀ (σ + 1)) {n : Type} [Fintype n] [DecidableEq n]
  {γ : LatFrame (Fv D.host.F v) n (Fin V₀.rank)} {β : LatFrame (Fv D.host.F v) (n ⊕ Fin (2 * (σ + 1))) (Fin V.rank)}
  {t : ℕ → Fv D.host.F v}

variable {τ}

open GlobalTheory.RootEx (colE rowE)

variable (hβ : IsScaled V V₀ τ d.i₀ (fourierJacobiVectors d) γ β t)
include hβ

end FJ

section Jac

variable {V V₀ L : HSp D} {σ : ℕ} (d : HypDec V V₀ (σ + 1)) (ζ : Fin L.rank → D.host.E)

end Jac
end GlobalTheory.SrcHalfOne
