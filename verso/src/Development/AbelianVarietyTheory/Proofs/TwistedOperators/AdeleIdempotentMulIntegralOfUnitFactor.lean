import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option synthInstance.maxHeartbeats 160000
set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.UnitAtPl

open GlobalTheory.FinPlLoc (idem ePl evalV_ePl ePl_int idem_mem_idAt idem_mul_self finPart_pair)

variable {D : D7}

/- English proof (translation)
Rewrite using `[AlgHom.commutes, HeightOneSpectrum.mem_adicCompletionIntegers]`. Establish `h1 : x.intValuation c = 1` using `HeightOneSpectrum.intValuation_eq_one_iff.2 hc`. Establish `h2` using `HeightOneSpectrum.valuation_of_algebraMap (K := D.host.F) x c`. Rewrite `h2` using `[h1]`. Use `show Valued.v ((((c : D.host.F))⁻¹ : D.host.F) : x.adicCompletion D.host.F) ≤ 1`.

Rewrite using `[HeightOneSpectrum.valuedAdicCompletion_eq_valuation', map_inv₀]`. Establish `: HeightOneSpectrum.valuation D.host.F x (c : D.host.F) = 1` using `h2`. Rewrite using `[this, inv_one]`.
-/
theorem evalV_inv_mem (x : GlobalTheory.FinPl.Pl D) (c : 𝓞 D.host.F) (hc : c ∉ x.asIdeal) :
    evalV D.host.F x (algebraMap D.host.F (Af D.host.F) ((c : D.host.F))⁻¹) ∈ x.adicCompletionIntegers D.host.F := by
  rw [AlgHom.commutes, HeightOneSpectrum.mem_adicCompletionIntegers]
  have h1 : x.intValuation c = 1 := HeightOneSpectrum.intValuation_eq_one_iff.2 hc
  have h2 := HeightOneSpectrum.valuation_of_algebraMap (K := D.host.F) x c
  rw [h1] at h2
  show Valued.v ((((c : D.host.F))⁻¹ : D.host.F) : x.adicCompletion D.host.F) ≤ 1
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', map_inv₀]
  have : HeightOneSpectrum.valuation D.host.F x (c : D.host.F) = 1 := h2
  rw [this, inv_one]

/- English proof (translation)
Introduce `w`. Rewrite using `[Algebra.smul_def, map_mul, evalV_ePl]`. Use `split_ifs with h`. Substitute `h` using the available equality. Rewrite using `[mul_one]`.

Conclude with `evalV_inv_mem w c hc`. Rewrite using `[mul_zero]`. Conclude with `zero_mem _`.
-/
theorem inv_ePl_int (x : GlobalTheory.FinPl.Pl D) (c : 𝓞 D.host.F) (hc : c ∉ x.asIdeal) :
    ((c : D.host.F))⁻¹ • ePl D (· = x) ∈ intAf D.host.F := by
  intro w
  rw [Algebra.smul_def, map_mul, evalV_ePl]
  split_ifs with h
  · subst h; rw [mul_one]; exact evalV_inv_mem w c hc
  · rw [mul_zero]; exact zero_mem _

/- English proof (translation)
Proceed by induction on `hw using AddSubgroup.closure_induction with`. Consider the case `mem w hw`. Take `⟨α, hα, o, rfl⟩` from `hw`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, one_mul]`. Use `AddSubgroup.subset_closure ⟨γ * α, fun v => ?_, o, rfl⟩` and prove the remaining obligations.

Rewrite using `[map_mul]`. Conclude with `mul_mem (hγ v) (hα v)`. Consider the case `zero => rw [mul_zero]`. Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy => rw [mul_add]`.

Conclude with `add_mem hx hy`. Consider the case `neg x _ hx => rw [mul_neg]`. Conclude with `neg_mem hx`.
-/
theorem tmul_one_mul_mem {γ : Af D.host.F} (hγ : γ ∈ intAf D.host.F) {w : Af D.host.F ⊗[D.host.F] D.host.E}
    (hw : w ∈ intAE D) : (γ ⊗ₜ[D.host.F] (1 : D.host.E)) * w ∈ intAE D := by
  induction hw using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, o, rfl⟩ := hw
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    refine AddSubgroup.subset_closure ⟨γ * α, fun v => ?_, o, rfl⟩
    rw [map_mul]
    exact mul_mem (hγ v) (hα v)
  | zero => rw [mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | neg x _ hx => rw [mul_neg]; exact neg_mem hx

/- English proof (translation)
Establish `h0 : idem D (· = x) * incA D ((c : D.host.F) : D.host.E)⁻¹ = pairA D.host.F 0 (ePl D (· = x)) ⊗ₜ[D.host.F] ((c : D.host.F) : D.host.E)⁻¹`. Express the relevant statement in the definitionally equal form `(pairA D.host.F 0 (ePl D (· = x)) ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] ((c : D.host.F) : D.host.E)⁻¹) = _`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]`. Establish `h1 : ((c : D.host.F) : D.host.E)⁻¹ = ((c : D.host.F))⁻¹ • (1 : D.host.E)`. Rewrite using `[Algebra.smul_def, map_inv₀, mul_one]`.

Both sides reduce to the same expression. Rewrite using `[h0, finPart_pair, h1, TensorProduct.tmul_smul, TensorProduct.smul_tmul']`.
-/
theorem finPart_idem_inv (x : GlobalTheory.FinPl.Pl D) (c : 𝓞 D.host.F) :
    finPart D (idem D (· = x) * incA D ((c : D.host.F) : D.host.E)⁻¹) =
      (((c : D.host.F))⁻¹ • ePl D (· = x)) ⊗ₜ[D.host.F] (1 : D.host.E) := by
  have h0 : idem D (· = x) * incA D ((c : D.host.F) : D.host.E)⁻¹ =
      pairA D.host.F 0 (ePl D (· = x)) ⊗ₜ[D.host.F] ((c : D.host.F) : D.host.E)⁻¹ := by
    change (pairA D.host.F 0 (ePl D (· = x)) ⊗ₜ[D.host.F] (1 : D.host.E)) *
      ((1 : AF D.host.F) ⊗ₜ[D.host.F] ((c : D.host.F) : D.host.E)⁻¹) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have h1 : ((c : D.host.F) : D.host.E)⁻¹ = ((c : D.host.F))⁻¹ • (1 : D.host.E) := by
    rw [Algebra.smul_def, map_inv₀, mul_one]; rfl
  rw [h0, finPart_pair, h1, TensorProduct.tmul_smul, TensorProduct.smul_tmul']

/- English proof (translation)
Introduce `D v u hu z hz`. Establish `hu0 : ((u : D.host.F) : D.host.E) ≠ 0`. Introduce `h`. Apply `hu` to reduce the goal to its premises. Establish `h' : (u : D.host.F) = 0` using `by exact_mod_cast h`.

Establish `h'' : u = 0` using `by exact_mod_cast h'`. Rewrite using `[h'']`. Conclude with `zero_mem _`. Establish `hinc : incA D ((u : D.host.F) : D.host.E)⁻¹ * incA D ((u : D.host.F) : D.host.E) = 1`. Rewrite using `[← map_mul, inv_mul_cancel₀ hu0, map_one]`.

Establish `key : idem D (· = v) * z = (idem D (· = v) * incA D ((u : D.host.F) : D.host.E)⁻¹) * (idem D (· = v) * incA D ((u : D.host.F) : D.host.E) * z)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[idem_mul_self, hinc, mul_one]`. Use `_ = _ := by ring`. Use `⟨Ideal.mul_mem_right _ _ (idem_mem_idAt _), ?_⟩` and prove the remaining obligations.

Rewrite using `[key, (finPart D).map_mul, finPart_idem_inv]`. Conclude with `tmul_one_mul_mem (inv_ePl_int v u hu) hz.2`.
-/
theorem idem_mul_mem_of_unit : ∀ (D : D7) (v : GlobalTheory.FinPl.Pl D) (u : 𝓞 D.host.F), u ∉ v.asIdeal → ∀ z : AE D, GlobalTheory.FinPlLoc.idem D (· = v) * incA D ((u : D.host.F) : D.host.E) * z ∈ intAt D (· = v) → GlobalTheory.FinPlLoc.idem D (· = v) * z ∈ intAt D (· = v) := by
  intro D v u hu z hz
  have hu0 : ((u : D.host.F) : D.host.E) ≠ 0 := by
    intro h
    apply hu
    have h' : (u : D.host.F) = 0 := by exact_mod_cast h
    have h'' : u = 0 := by exact_mod_cast h'
    rw [h'']; exact zero_mem _
  have hinc : incA D ((u : D.host.F) : D.host.E)⁻¹ * incA D ((u : D.host.F) : D.host.E) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hu0, map_one]
  have key : idem D (· = v) * z = (idem D (· = v) * incA D ((u : D.host.F) : D.host.E)⁻¹) *
      (idem D (· = v) * incA D ((u : D.host.F) : D.host.E) * z) := by
    calc idem D (· = v) * z = (idem D (· = v) * idem D (· = v)) *
        (incA D ((u : D.host.F) : D.host.E)⁻¹ * incA D ((u : D.host.F) : D.host.E)) * z := by
          rw [idem_mul_self, hinc, mul_one]
      _ = _ := by ring
  refine ⟨Ideal.mul_mem_right _ _ (idem_mem_idAt _), ?_⟩
  rw [key, (finPart D).map_mul, finPart_idem_inv]
  exact tmul_one_mul_mem (inv_ePl_int v u hu) hz.2

end GlobalTheory.UnitAtPl

end
