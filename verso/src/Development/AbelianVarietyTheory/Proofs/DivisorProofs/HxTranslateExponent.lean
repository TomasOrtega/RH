import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PerCEmb
import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThAHeisEntireLinearInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiHalfSymplecticOrthonormalFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermCColMulVec
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FockHxDifferentiable

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh

open GlobalTheory.FinTranslate

/- English proof (translation)
Establish `h1` using `fock_hx_conj X bas idx x hs hd z a`. Establish `h2` using `fock_hx_conj X bas idx x hs hd a a`. Establish `h3 : hx X bas idx x (z + a) (-a) = -hx X bas idx x (z + a) a`. Rewrite using `[← neg_one_smul ℂ a, fock_hx_smul_right]`. Simplify using the standard rewrite rules.

Rewrite using `[h3]`. Simplify using `only [fock_hx_add_left, fock_hx_add_right, fock_hx_smul_left]`. Rewrite using `[h1]`. Establish `h4 : (hx X bas idx x a a).im = 0` using `conj_eq_iff_im.1 h2.symm`. Generalize the expression as in `hx X bas idx x z a = s`.

Generalize the expression as in `hx X bas idx x z z = t`. Generalize the expression as in `hx X bas idx x a a = q at h4`. Establish `h5 : ((s.im : ℝ) : ℂ) = (s - conj s) / (2 * I)` using `im_eq_sub_conj s`. Simplify using `only [neg_im, add_im, h4, add_zero, ofReal_neg, h5]`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem hx_translate_exponent {E : Type} [Field E] [NumberField E] [IsCMField E] {r g : ℕ} (X : Data E r)
    (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (x : Frame X.Ψ r) (hs : IsSympl X bas)
    (hd : x ∈ X.dom) (z a : Fin g → ℂ) :
    (Real.pi : ℂ) * I * (((hx X bas idx x (z + a) (-a)).im : ℝ) : ℂ) +
        -(Real.pi / 2 : ℂ) * hx X bas idx x (z + a) (z + a) =
      -(Real.pi / 2 : ℂ) * hx X bas idx x z z + -(Real.pi * hx X bas idx x (z + (1 / 2 : ℂ) • a) a) := by
  have h1 := fock_hx_conj X bas idx x hs hd z a
  have h2 := fock_hx_conj X bas idx x hs hd a a
  have h3 : hx X bas idx x (z + a) (-a) = -hx X bas idx x (z + a) a := by
    rw [← neg_one_smul ℂ a, fock_hx_smul_right]; simp
  rw [h3]
  simp only [fock_hx_add_left, fock_hx_add_right, fock_hx_smul_left]
  rw [h1]
  have h4 : (hx X bas idx x a a).im = 0 := conj_eq_iff_im.1 h2.symm
  generalize hx X bas idx x z a = s
  generalize hx X bas idx x z z = t
  generalize hx X bas idx x a a = q at h4
  have h5 : ((s.im : ℝ) : ℂ) = (s - conj s) / (2 * I) := im_eq_sub_conj s
  simp only [neg_im, add_im, h4, add_zero, ofReal_neg, h5]
  field_simp
  ring

/- English proof (translation)
Introduce `D ψ θ V W r g hr X bas idx hψ hθ hV he hM hs x hx0 f φ hf hR γ u hu`. Establish `hd : x ∈ X.dom` using `mem_dom_of_isOrtho hx0`. Take `⟨hsb, hth⟩` from `(thA_heis_entire_linear_injective D.host.E r g V.rank X bas idx hs he x hd φ hR.1).1 (-(colsR hr γ)) |> fun h => (⟨(h 0).1, fun z => (h z).2⟩ : _ ∧ ∀ z, _)`. Use `⟨hsb, fun w hw => ?_⟩` and prove the remaining obligations. Take `⟨hrat, hadd, -⟩` from `RealCoord.zOf_coordinates D ψ θ V W r g hr X bas idx hψ hθ hV he hM hs x`.

Establish `hsy : ∀ v w : WO V W, v.map (finPart D) = 0 → ψ (symplOH V W v w) = cexp (Real.pi * I * ((∑ b, (hx X bas idx x (zOf θ V W hr X idx x v b) (zOf θ V W hr X idx x w b)).im : ℝ) : ℂ))` using `by first`. Consider the case `exact GlobalTheory.AdThSympl.psi_symplOH_eq D ψ θ V W r g hr X bas idx hψ hθ hV he hM hs x hd`. Consider the case `exact GlobalTheory.AdThSympl.psi_symplOH_eq D ψ θ V W r g hr X bas idx hψ hθ hV he hM hs x hx0`. Take `⟨v, hv⟩ : ∃ v : WO V W, ratW W V γ = v + u` from `⟨ratW W V γ - u, (sub_add_cancel _ _).symm⟩`. Establish `hvf : v.map (finPart D) = 0`.

Establish `h` using `hu.2`. Rewrite `h` using `[hv, Matrix.map_add _ (finPart D).map_add]`. Conclude with `left_eq_add.1 (h.trans (add_comm _ _))`. Establish `hvi : v.map (infPart D) = (ratW W V γ).map (infPart D)`. Rewrite using `[hv, Matrix.map_add _ (infPart D).map_add, hu.1, add_zero]`.

Take `⟨w', hw'⟩ : ∃ w' : WO V W, w = w' + v` from `⟨w - v, (sub_add_cancel _ _).symm⟩`. Establish `hw'f : w'.map (finPart D) = 0`. Establish `h` using `hw`. Rewrite `h` using `[hw', Matrix.map_add _ (finPart D).map_add, hvf, add_zero]`. Then use the resulting hypothesis. Establish `hzv` using `hrat γ v hvi`.

Establish `hneg : ∀ b, pv X idx x ((-(colsR hr γ)) b) = -pv X idx x (colsR hr γ b)`. Introduce `b`. Establish `h0 : per X x 0 = 0` using `by simpa using per_add X x 0 0`. Establish `h1` using `per_add X x (colsR hr γ b) (-(colsR hr γ b))`. Rewrite `h1` using `[add_neg_cancel, h0]`.

Use function extensionality and compare the values at `j`. Establish `h2` using `congrFun h1 (idx j)`. Simplify using `only [Pi.add_apply, Pi.zero_apply] at h2`. Conclude with `eq_neg_of_add_eq_zero_right h2.symm`. Establish `hz' : zOf θ V W hr X idx x w' = fun b => zOf θ V W hr X idx x w b + pv X idx x ((-(colsR hr γ)) b)`.

Use function extensionality and compare the values at `b`. Rewrite using `[hneg, hw', hadd, hzv]`. Simplify using the standard rewrite rules. Establish `hzv' : zOf θ V W hr X idx x v = fun b => -pv X idx x ((-(colsR hr γ)) b)`. Use function extensionality and compare the values at `b`.

Rewrite using `[hneg, hzv, neg_neg]`. Establish `e1 : w + u = ratW W V γ + w'` using `by rw [hw', hv]; abel`. Establish `e2 : -symplOH V W (ratW W V γ) w' = symplOH V W w' v`. Rewrite using `[hv, symplOH_add_left, symplOH_fin_real hu.1 hw'f, add_zero, symplOH_skew V W v w']`. Rewrite using `[heisO, symplOH_real_fin hu.1 hw, AddChar.map_zero_eq_one, _root_.one_mul, e1, hf.quasi, e2, hsy w' v hw'f, hR.2 w' hw'f, hth, hz', hzv', ← _root_.mul_assoc, ← _root_.mul_assoc, ← Complex.exp_add, ← Complex.exp_add]`.

Use `congr 2`. Rewrite using `[ofReal_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl fun b _ => hx_translate_exponent X bas idx x hs hd _ _`.
-/
theorem reads_heisO_finOf : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (r g : ℕ) (hr : W.rank = r) (X : Data D.host.E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsStdChar D ψ (-1) → IsInfFam θ → V.gram = 1 → Even V.rank → IsMod W hr X → IsSympl X bas → ∀ x : Frame X.Ψ r, IsONFr X x → ∀ (f : WO V W → ℂ) (φ : TF V.rank g), IsThetaFunO ψ V W f → Reads θ V W hr X bas idx f φ x → ∀ γ u, IsFinOf V W γ u → Reads θ V W hr X bas idx (heisO ψ V W u f) (heisG X bas (-(colsR hr γ)) φ) x := by
  intro D ψ θ V W r g hr X bas idx hψ hθ hV he hM hs x hx0 f φ hf hR γ u hu
  have hd : x ∈ X.dom := mem_dom_of_isOrtho hx0
  obtain ⟨hsb, hth⟩ := (thA_heis_entire_linear_injective D.host.E r g V.rank X bas idx hs he x hd φ hR.1).1
    (-(colsR hr γ))
    |> fun h => (⟨(h 0).1, fun z => (h z).2⟩ : _ ∧ ∀ z, _)
  refine ⟨hsb, fun w hw => ?_⟩
  obtain ⟨hrat, hadd, -⟩ := RealCoord.zOf_coordinates D ψ θ V W r g hr X bas idx hψ hθ hV he hM hs x
  have hsy : ∀ v w : WO V W, v.map (finPart D) = 0 → ψ (symplOH V W v w) = cexp (Real.pi * I *
      ((∑ b, (hx X bas idx x (zOf θ V W hr X idx x v b) (zOf θ V W hr X idx x w b)).im : ℝ) : ℂ)) := by
    first
      | exact GlobalTheory.AdThSympl.psi_symplOH_eq D ψ θ V W r g hr X bas idx hψ hθ hV he hM hs x hd
      | exact GlobalTheory.AdThSympl.psi_symplOH_eq D ψ θ V W r g hr X bas idx hψ hθ hV he hM hs x hx0
  obtain ⟨v, hv⟩ : ∃ v : WO V W, ratW W V γ = v + u := ⟨ratW W V γ - u, (sub_add_cancel _ _).symm⟩
  have hvf : v.map (finPart D) = 0 := by
    have h := hu.2
    rw [hv, Matrix.map_add _ (finPart D).map_add] at h
    exact left_eq_add.1 (h.trans (add_comm _ _))
  have hvi : v.map (infPart D) = (ratW W V γ).map (infPart D) := by
    rw [hv, Matrix.map_add _ (infPart D).map_add, hu.1, add_zero]
  obtain ⟨w', hw'⟩ : ∃ w' : WO V W, w = w' + v := ⟨w - v, (sub_add_cancel _ _).symm⟩
  have hw'f : w'.map (finPart D) = 0 := by
    have h := hw
    rwa [hw', Matrix.map_add _ (finPart D).map_add, hvf, add_zero] at h
  have hzv := hrat γ v hvi
  have hneg : ∀ b, pv X idx x ((-(colsR hr γ)) b) = -pv X idx x (colsR hr γ b) := by
    intro b
    have h0 : per X x 0 = 0 := by simpa using per_add X x 0 0
    have h1 := per_add X x (colsR hr γ b) (-(colsR hr γ b))
    rw [add_neg_cancel, h0] at h1
    funext j
    have h2 := congrFun h1 (idx j)
    simp only [Pi.add_apply, Pi.zero_apply] at h2
    exact eq_neg_of_add_eq_zero_right h2.symm
  have hz' : zOf θ V W hr X idx x w' =
      fun b => zOf θ V W hr X idx x w b + pv X idx x ((-(colsR hr γ)) b) := by
    funext b
    rw [hneg, hw', hadd, hzv]
    simp
  have hzv' : zOf θ V W hr X idx x v = fun b => -pv X idx x ((-(colsR hr γ)) b) := by
    funext b
    rw [hneg, hzv, neg_neg]
  have e1 : w + u = ratW W V γ + w' := by rw [hw', hv]; abel
  have e2 : -symplOH V W (ratW W V γ) w' = symplOH V W w' v := by
    rw [hv, symplOH_add_left, symplOH_fin_real hu.1 hw'f, add_zero, symplOH_skew V W v w']
  rw [heisO, symplOH_real_fin hu.1 hw, AddChar.map_zero_eq_one, _root_.one_mul, e1, hf.quasi, e2, hsy w' v hw'f,
    hR.2 w' hw'f, hth, hz', hzv', ← _root_.mul_assoc, ← _root_.mul_assoc, ← Complex.exp_add, ← Complex.exp_add]
  congr 2
  rw [ofReal_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun b _ => hx_translate_exponent X bas idx x hs hd _ _

end GlobalTheory.AdTh
