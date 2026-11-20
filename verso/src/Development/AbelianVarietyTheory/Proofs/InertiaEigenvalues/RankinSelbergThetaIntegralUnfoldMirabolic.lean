import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WtOfLastRowOfDetPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEqColGenMulBlkU
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOfMemSmoothSpan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPsiLocNeOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralThetaSeriesUnfoldMirabolic
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NegOneNotMemNatLat
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecaysOfMemSmoothSpan
import GroundTheory.GlobalFields.Adele.Compact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermAutomorphicFormIntegral

noncomputable section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.RSJ GlobalTheory.MirTower GlobalTheory.CuspGeneric Formalism.L2.Host
open scoped ENNReal NNReal ComplexConjugate Matrix

namespace GlobalTheory.ZUnfTheta

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

/- English proof (translation)
Use `continuous_matrix fun i j => ?_` and prove the remaining obligations. Simplify using `only [secRow, Matrix.of_apply]`. Use `split_ifs`. Conclude with `continuous_apply j`. Conclude with `continuous_const`.
-/
theorem continuous_secRow {n : ℕ} :
    Continuous (fun y : Fin n → Cinf E => secRow y) := by
  refine continuous_matrix fun i j => ?_
  simp only [secRow, Matrix.of_apply]
  split_ifs
  · exact continuous_apply j
  · exact continuous_const

/- English proof (translation)
Rewrite using `[continuousOn_iff_continuous_restrict]`. Use `Units.continuous_iff.2 ⟨?_, ?_⟩` and prove the remaining obligations. Establish `h1 : ∀ y : ↥{y : Fin n → Cinf E | IsUnit (secRow y).det}, ((secInv y.1 : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) = (secRow y.1)⁻¹` using `fun y => by`. Rewrite using `[secInv, dif_pos (show IsUnit (secRow y.1).det from y.2), Matrix.coe_units_inv]`. Both sides reduce to the same expression.

Establish `hc : Continuous fun y : ↥{y : Fin n → Cinf E | IsUnit (secRow y).det} => secRow y.1` using `continuous_secRow.comp continuous_subtype_val`. Use `continuous_iff_continuousAt.2 fun y => ?_` and prove the remaining obligations. Establish `hinv : ContinuousAt Ring.inverse (secRow y.1).det`. Use `NormedRing.inverse_continuousAt y.2.unit` as an intermediate fact. Simplify using `using this`.

Establish `h2 : ContinuousAt (fun z : ↥{y : Fin n → Cinf E | IsUnit (secRow y).det} => (secRow z.1)⁻¹) y` using `(continuousAt_matrix_inv _ hinv).comp (f := fun z : ↥{y : Fin n → Cinf E | IsUnit (secRow y).det} => secRow z.1) hc.continuousAt`. Use `h2 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `z`. Conclude with `h1 z`. Establish `h1 : ∀ y : ↥{y : Fin n → Cinf E | IsUnit (secRow y).det}, (((secInv y.1)⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) = secRow y.1` using `fun y => by`.

Rewrite using `[secInv, dif_pos (show IsUnit (secRow y.1).det from y.2), inv_inv]`. Both sides reduce to the same expression. Use `(continuous_secRow.comp continuous_subtype_val : Continuous fun z : ↥{y : Fin n → Cinf E | IsUnit (secRow y).det} => secRow z.1) using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `z`. Conclude with `h1 z`.
-/
theorem continuousOn_secInv {n : ℕ} :
    ContinuousOn (fun y : Fin n → Cinf E => secInv y) {y | IsUnit (secRow y).det} := by
  rw [continuousOn_iff_continuous_restrict]
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · have h1 : ∀ y : ↥{y : Fin n → Cinf E | IsUnit (secRow y).det},
        ((secInv y.1 : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) = (secRow y.1)⁻¹ := fun y => by
      rw [secInv, dif_pos (show IsUnit (secRow y.1).det from y.2), Matrix.coe_units_inv]
      rfl
    have hc : Continuous fun y : ↥{y : Fin n → Cinf E | IsUnit (secRow y).det} => secRow y.1 :=
      continuous_secRow.comp continuous_subtype_val
    refine continuous_iff_continuousAt.2 fun y => ?_
    have hinv : ContinuousAt Ring.inverse (secRow y.1).det := by
      have := NormedRing.inverse_continuousAt y.2.unit
      simpa using this
    have h2 : ContinuousAt (fun z : ↥{y : Fin n → Cinf E | IsUnit (secRow y).det} => (secRow z.1)⁻¹) y :=
      (continuousAt_matrix_inv _ hinv).comp (f := fun z : ↥{y : Fin n → Cinf E | IsUnit (secRow y).det} => secRow z.1)
        hc.continuousAt
    convert h2 using 1
    funext z
    exact h1 z
  · have h1 : ∀ y : ↥{y : Fin n → Cinf E | IsUnit (secRow y).det},
        (((secInv y.1)⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) = secRow y.1 := fun y => by
      rw [secInv, dif_pos (show IsUnit (secRow y.1).det from y.2), inv_inv]
      rfl
    convert (continuous_secRow.comp continuous_subtype_val :
      Continuous fun z : ↥{y : Fin n → Cinf E | IsUnit (secRow y).det} => secRow z.1) using 1
    funext z
    exact h1 z

variable {m : ℕ}

/- English proof (translation)
Establish `h : natLat E N = (fun u : Af E => (N : Af E) * u) '' (GroundTheory.Global.integralFiniteAdeles (𝓞 E) E : Set (Af E))`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, hz, rfl⟩`. Conclude with `⟨z, hz, rfl⟩`.

Introduce and unpack `⟨z, hz, rfl⟩`. Conclude with `⟨z, hz, rfl⟩`. Rewrite using `[h]`. Conclude with `((GroundTheory.Global.isCompact_integralFiniteAdeles E).image (continuous_const.mul continuous_id)).isClosed`.
-/
theorem isClosed_natLat (N : ℕ) : IsClosed (natLat E N) := by
  have h : natLat E N =
      (fun u : Af E => (N : Af E) * u) '' (GroundTheory.Global.integralFiniteAdeles (𝓞 E) E : Set (Af E)) := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z, hz, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z, hz, rfl⟩
  rw [h]
  exact ((GroundTheory.Global.isCompact_integralFiniteAdeles E).image (continuous_const.mul continuous_id)).isClosed

/- English proof (translation)
The claim follows from `continuous_pi fun j => (Units.continuous_val (M := Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E))).matrix_elem (Fin.last m) j`.
-/
theorem continuous_lastRow : Continuous fun g : GA E (m + 1) => GlobalTheory.ZEul.lastRow g :=
  continuous_pi fun j => (Units.continuous_val (M := Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E))).matrix_elem (Fin.last m) j

/- English proof (translation)
The claim follows from `continuous_pi fun i => GlobalTheory.ShortVecDecay.continuous_pInf.comp ((continuous_apply i).comp continuous_lastRow)`.
-/
theorem continuous_yInfRow : Continuous fun g : GA E (m + 1) => fun i => pInf E (GlobalTheory.ZEul.lastRow g i) :=
  continuous_pi fun i => GlobalTheory.ShortVecDecay.continuous_pInf.comp ((continuous_apply i).comp continuous_lastRow)

/- English proof (translation)
Establish `hy` using `continuous_yInfRow (E := E) (m := m)`. Use `set s := {g : GA E (m + 1) | IsUnit (secRow fun i => pInf E (GlobalTheory.ZEul.lastRow g i)).det} with hsdef`. Establish `hs : IsOpen s` using `Units.isOpen.preimage ((continuous_secRow.comp hy).matrix_det)`. Use `measurable_of_restrict_of_restrict_compl hs.measurableSet ?_ ?_` and prove the remaining obligations. Establish `hc : ContinuousOn (fun g : GA E (m + 1) => g * infGL E (m + 1) (secInv fun i => pInf E (GlobalTheory.ZEul.lastRow g i))) s` using `continuousOn_id.mul (GlobalTheory.ConstTermSmooth.continuous_infGL.comp_continuousOn (continuousOn_secInv.comp hy.continuousOn fun g hg => hg))`.

Conclude with `hc.restrict.measurable`. Use `(measurable_subtype_coe : Measurable (Subtype.val : (sᶜ : Set (GA E (m + 1))) → GA E (m + 1))) using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `g`. Establish `hg : ¬ IsUnit (secRow fun i => pInf E (GlobalTheory.ZEul.lastRow g.1 i)).det` using `g.2`. Use `show g.1 * infGL E (m + 1) (secInv fun i => pInf E (GlobalTheory.ZEul.lastRow g.1 i)) = g.1`.

Rewrite using `[secInv, dif_neg hg, map_one, mul_one]`.
-/
theorem measurable_mulSec :
    Measurable fun g : GA E (m + 1) => g * infGL E (m + 1) (secInv fun i => pInf E (GlobalTheory.ZEul.lastRow g i)) := by
  have hy := continuous_yInfRow (E := E) (m := m)
  set s := {g : GA E (m + 1) | IsUnit (secRow fun i => pInf E (GlobalTheory.ZEul.lastRow g i)).det} with hsdef
  have hs : IsOpen s := Units.isOpen.preimage ((continuous_secRow.comp hy).matrix_det)
  refine measurable_of_restrict_of_restrict_compl hs.measurableSet ?_ ?_
  · have hc : ContinuousOn (fun g : GA E (m + 1) =>
        g * infGL E (m + 1) (secInv fun i => pInf E (GlobalTheory.ZEul.lastRow g i))) s :=
      continuousOn_id.mul (GlobalTheory.ConstTermSmooth.continuous_infGL.comp_continuousOn
        (continuousOn_secInv.comp hy.continuousOn fun g hg => hg))
    exact hc.restrict.measurable
  · convert (measurable_subtype_coe : Measurable (Subtype.val : (sᶜ : Set (GA E (m + 1))) → GA E (m + 1))) using 1
    funext g
    have hg : ¬ IsUnit (secRow fun i => pInf E (GlobalTheory.ZEul.lastRow g.1 i)).det := g.2
    show g.1 * infGL E (m + 1) (secInv fun i => pInf E (GlobalTheory.ZEul.lastRow g.1 i)) = g.1
    rw [secInv, dif_neg hg, map_one, mul_one]

/- English proof (translation)
Establish `hh` using `measurable_mulSec (E := E) (m := m)`. Establish `hy` using `continuous_yInfRow (E := E) (m := m)`. Establish `hI : Measurable fun g : GA E (m + 1) => indN N (fun i => GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow g i))`. Establish `hS : IsClosed {g : GA E (m + 1) | ∀ i : Fin (m + 1), GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow g i) - (if (i : ℕ) + 1 = m + 1 then 1 else 0) ∈ natLat E N}`. Simplify using `only [Set.setOf_forall]`.

Conclude with `isClosed_iInter fun i => (isClosed_natLat N).preimage (((continuous_snd : Continuous (GlobalTheory.RSJ.pFin E)).comp ((continuous_apply i).comp continuous_lastRow)).sub continuous_const)`. Unfold `indN`. Conclude with `Measurable.ite hS.measurableSet measurable_const measurable_const`. Establish `hD : Continuous fun g : GA E (m + 1) => (detPow E (m + 1) x g : ℂ)`. Unfold `detPow chiDet`.

Conclude with `Complex.continuous_ofReal.comp (continuous_norm.comp (Units.continuous_val.comp ((GlobalTheory.HeckeGal.Model.absPow E x).2.1.comp Matrix.GeneralLinearGroup.continuous_det)))`. Unfold `Psi`. Conclude with `((((hφ.comp hh).mul (Complex.continuous_conj.measurable.comp (hφ'.comp hh))).mul (hΦ.measurable.comp hy.measurable)).mul hI).mul hD.measurable`.
-/
theorem measurable_integrand {φ φ' : GA E (m + 1) → ℂ} (hφ : Measurable φ) (hφ' : Measurable φ')
    {Φ : (Fin (m + 1) → Cinf E) → ℂ} (hΦ : Continuous Φ) (N : ℕ) (x : ℝ) :
    Measurable fun g : GA E (m + 1) => Psi φ φ' Φ N g (GlobalTheory.ZEul.lastRow g) * (detPow E (m + 1) x g : ℂ) := by
  have hh := measurable_mulSec (E := E) (m := m)
  have hy := continuous_yInfRow (E := E) (m := m)
  have hI : Measurable fun g : GA E (m + 1) => indN N (fun i => GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow g i)) := by
    have hS : IsClosed {g : GA E (m + 1) | ∀ i : Fin (m + 1),
        GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow g i) - (if (i : ℕ) + 1 = m + 1 then 1 else 0) ∈ natLat E N} := by
      simp only [Set.setOf_forall]
      exact isClosed_iInter fun i => (isClosed_natLat N).preimage
        (((continuous_snd : Continuous (GlobalTheory.RSJ.pFin E)).comp ((continuous_apply i).comp continuous_lastRow)).sub
          continuous_const)
    unfold indN
    exact Measurable.ite hS.measurableSet measurable_const measurable_const
  have hD : Continuous fun g : GA E (m + 1) => (detPow E (m + 1) x g : ℂ) := by
    unfold detPow chiDet
    exact Complex.continuous_ofReal.comp (continuous_norm.comp (Units.continuous_val.comp
      ((GlobalTheory.HeckeGal.Model.absPow E x).2.1.comp Matrix.GeneralLinearGroup.continuous_det)))
  unfold Psi
  exact ((((hφ.comp hh).mul (Complex.continuous_conj.measurable.comp (hφ'.comp hh))).mul
    (hΦ.measurable.comp hy.measurable)).mul hI).mul hD.measurable

end GlobalTheory.ZUnfTheta

/- English proof (translation)
Introduce `E _ _ _ m μ _ 𝓕 𝓕P h𝓕 h𝓕P φ φ' hφm hφ'm hφ hφ' N Φ hΦ x hfin`. Use `set l : Fin (m + 1) := Fin.last m with hl`. Set `F : GA E (m + 1) → (Fin (m + 1) → Ad E) → ℂ` to `fun g y => Psi φ φ' Φ N g y * (detPow E (m + 1) x g : ℂ)`. Establish `hv : (Pi.single l 1 : Fin (m + 1) → E) ≠ 0` using `fun h0 => by simpa using congrFun h0 l`. Establish `hP' : ∀ γ : GL (Fin (m + 1)) E, γ ∈ mirU E (m + 1) m ↔ (Pi.single l 1 : Fin (m + 1) → E) ᵥ* γ.val = Pi.single l 1` using `fun γ => by`.

Rewrite using `[mem_mirU_last, Matrix.single_one_vecMul, funext_iff]`. Simplify using `only [Pi.single_apply, Matrix.row]`. Conclude with `Iff.rfl`. Establish `he : ∀ g : GA E (m + 1), (algebraMap E (Ad E) ∘ (Pi.single l 1 : Fin (m + 1) → E)) ᵥ* g.val = GlobalTheory.ZEul.lastRow g` using `fun g => by`. Establish `h1 : algebraMap E (Ad E) ∘ (Pi.single l 1 : Fin (m + 1) → E) = Pi.single l 1`.

Use function extensionality and compare the values at `j`. Simplify using `only [Function.comp_apply, Pi.single_apply]`. Apply the tactic sequence `split_ifs <;> simp`. Rewrite using `[h1, Matrix.single_one_vecMul]`. Both sides reduce to the same expression.

Establish `hF : ∀ γ g y, F (ratGL E (m + 1) γ * g) y = F g y` using `fun γ g y => by`. Simplify using `only [F, Psi, mul_assoc (ratGL E (m + 1) γ) g, hφ, hφ', GlobalTheory.RSJ.Model.detPow_mul, GlobalTheory.RSJ.Model.detPow_ratGL, one_mul]`. Establish `hm : Measurable fun g => F g (GlobalTheory.ZEul.lastRow g)` using `GlobalTheory.ZUnfTheta.measurable_integrand hφm hφ'm hΦ N x`. Establish `h𝓕P' : IsFundamentalDomain ((mirU E (m + 1) m).map (ratGL E (m + 1))) 𝓕P μ` using `h𝓕P`. Establish `hlin` using `GlobalTheory.ThetaUnfold.lintegral_tsum_vecMul μ hv hP' h𝓕 h𝓕P' (fun g y => ‖F g y‖ₑ) (fun γ g y => by simp only [hF]) (by simp only [he]; exact hm.enorm.aemeasurable)`.

Establish `hfin' : ∫⁻ g in 𝓕, ∑' ξ : {ξ : Fin (m + 1) → E // ξ ≠ 0}, ‖F g ((algebraMap E (Ad E) ∘ ξ.1) ᵥ* g.val)‖ₑ ∂μ ≠ ⊤`. Rewrite using `[hlin]`. Simplify `hfin` using `only [he]`. Take `⟨-, -, -, hint⟩` from `GlobalTheory.ThetaUnfold.integral_tsum_vecMul μ hv hP' h𝓕 h𝓕P' F hF (by simp only [he]; exact hm.aestronglyMeasurable) hfin'`. Simplify using `only [he] at hint`.

Unfold `Zint thetaSum`. Rewrite using `[← hint]`. Use `congr 1`. Use function extensionality and compare the values at `g`. Rewrite using `[← tsum_mul_right]`.

Both sides reduce to the same expression.
-/
theorem GlobalTheory.ZUnfTheta.zint_eq_mirabolic : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ)
    (μ : Measure (GA E (m + 1))) [μ.IsHaarMeasure] (𝓕 𝓕P : Set (GA E (m + 1))),
    IsFundamentalDomain (ratGL E (m + 1)).range 𝓕 μ → IsFundamentalDomain (ratMirU E (m + 1) m) 𝓕P μ →
    ∀ φ φ' : GA E (m + 1) → ℂ, Measurable φ → Measurable φ' → (∀ γ g, φ (ratGL E (m + 1) γ * g) = φ g) →
    (∀ γ g, φ' (ratGL E (m + 1) γ * g) = φ' g) → ∀ (N : ℕ) (Φ : (Fin (m + 1) → Cinf E) → ℂ), Continuous Φ → ∀ x : ℝ,
    ∫⁻ g in 𝓕P, ‖Psi φ φ' Φ N g (GlobalTheory.ZEul.lastRow g) * (detPow E (m + 1) x g : ℂ)‖ₑ ∂μ ≠ ⊤ →
    Zint μ 𝓕 φ φ' Φ N x = ∫ g in 𝓕P, Psi φ φ' Φ N g (GlobalTheory.ZEul.lastRow g) * (detPow E (m + 1) x g : ℂ) ∂μ := by
  intro E _ _ _ m μ _ 𝓕 𝓕P h𝓕 h𝓕P φ φ' hφm hφ'm hφ hφ' N Φ hΦ x hfin
  set l : Fin (m + 1) := Fin.last m with hl
  let F : GA E (m + 1) → (Fin (m + 1) → Ad E) → ℂ := fun g y => Psi φ φ' Φ N g y * (detPow E (m + 1) x g : ℂ)
  have hv : (Pi.single l 1 : Fin (m + 1) → E) ≠ 0 := fun h0 => by simpa using congrFun h0 l
  have hP' : ∀ γ : GL (Fin (m + 1)) E,
      γ ∈ mirU E (m + 1) m ↔ (Pi.single l 1 : Fin (m + 1) → E) ᵥ* γ.val = Pi.single l 1 := fun γ => by
    rw [mem_mirU_last, Matrix.single_one_vecMul, funext_iff]
    simp only [Pi.single_apply, Matrix.row]
    exact Iff.rfl
  have he : ∀ g : GA E (m + 1),
      (algebraMap E (Ad E) ∘ (Pi.single l 1 : Fin (m + 1) → E)) ᵥ* g.val = GlobalTheory.ZEul.lastRow g := fun g => by
    have h1 : algebraMap E (Ad E) ∘ (Pi.single l 1 : Fin (m + 1) → E) = Pi.single l 1 := by
      funext j
      simp only [Function.comp_apply, Pi.single_apply]
      split_ifs <;> simp
    rw [h1, Matrix.single_one_vecMul]
    rfl
  have hF : ∀ γ g y, F (ratGL E (m + 1) γ * g) y = F g y := fun γ g y => by
    simp only [F, Psi, mul_assoc (ratGL E (m + 1) γ) g, hφ, hφ', GlobalTheory.RSJ.Model.detPow_mul,
      GlobalTheory.RSJ.Model.detPow_ratGL, one_mul]
  have hm : Measurable fun g => F g (GlobalTheory.ZEul.lastRow g) := GlobalTheory.ZUnfTheta.measurable_integrand hφm hφ'm hΦ N x
  have h𝓕P' : IsFundamentalDomain ((mirU E (m + 1) m).map (ratGL E (m + 1))) 𝓕P μ := h𝓕P
  have hlin := GlobalTheory.ThetaUnfold.lintegral_tsum_vecMul μ hv hP' h𝓕 h𝓕P' (fun g y => ‖F g y‖ₑ)
    (fun γ g y => by simp only [hF]) (by simp only [he]; exact hm.enorm.aemeasurable)
  have hfin' : ∫⁻ g in 𝓕, ∑' ξ : {ξ : Fin (m + 1) → E // ξ ≠ 0},
      ‖F g ((algebraMap E (Ad E) ∘ ξ.1) ᵥ* g.val)‖ₑ ∂μ ≠ ⊤ := by
    rw [hlin]
    simpa only [he] using hfin
  obtain ⟨-, -, -, hint⟩ := GlobalTheory.ThetaUnfold.integral_tsum_vecMul μ hv hP' h𝓕 h𝓕P' F hF
    (by simp only [he]; exact hm.aestronglyMeasurable) hfin'
  simp only [he] at hint
  unfold Zint thetaSum
  rw [← hint]
  congr 1
  funext g
  rw [← tsum_mul_right]
  rfl
