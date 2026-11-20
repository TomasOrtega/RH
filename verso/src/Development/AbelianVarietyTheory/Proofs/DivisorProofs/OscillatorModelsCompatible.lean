import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Development.AbelianVarietyTheory.Counterexamples.RotationExamples.OfBeforeProjector
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SecBCAndCuspBC

noncomputable section

namespace GlobalTheory.PhRatCommon

section Lemmas

open NumberField
open scoped TensorProduct

open Formalism Formalism.IndefR Formalism.IndefR.FWT Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links
  Formalism.IndefR.Mult Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AdTh

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c c' : Coeff l} (hle : c.F ≤ c'.F) {r : ℕ}

/- English proof (translation)
Distinguish the cases in `hx : x ∈ ((U (σ'.comp (incF c c' hle))).X k).dom`. Use `letI : Algebra c.F (CAt σ') := (σ'.comp (incF c c' hle)).toAlgebra`. Establish `e` using `h (CAt σ') (fun _ => rfl) ((unfBC hle U σ').un k ⟨x, hx⟩)`. Establish `e1 : rdU (unfBC hle U σ') f' k x = toC (evR Xo c' f' ((unfBC hle U σ').un k ⟨x, hx⟩))` using `dif_pos hx`. Rewrite using `[e1, e]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Establish `e2 : rdU (U (σ'.comp (incF c c' hle))) (fs j) k x = toC (evR Xo c (fs j) ((U (σ'.comp (incF c c' hle))).un k ⟨x, hx⟩))` using `dif_pos hx`. Rewrite using `[e2]`. Both sides reduce to the same expression. Establish `e1 : rdU (unfBC hle U σ') f' k x = 0` using `dif_neg hx`.

Rewrite using `[e1]`. Use `(Finset.sum_eq_zero fun j _ => ?_).symm` and prove the remaining obligations. Establish `e2 : rdU (U (σ'.comp (incF c c' hle))) (fs j) k x = 0` using `dif_neg hx`. Rewrite using `[e2, mul_zero]`.
-/
theorem rdU_of_isBC (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ' : c'.F →+* ℂ) {m : ℕ} {f' : Rul Xo c'} {as : Fin m → c'.F}
    {fs : Fin m → Rul Xo c} (h : IsBC hle f' as fs) (k : (U (σ'.comp (incF c c' hle))).Comp)
    (x : Frame ((U (σ'.comp (incF c c' hle))).X k).Ψ r) :
    rdU (unfBC hle U σ') f' k x = ∑ j, σ' (as j) * rdU (U (σ'.comp (incF c c' hle))) (fs j) k x := by
  by_cases hx : x ∈ ((U (σ'.comp (incF c c' hle))).X k).dom
  · letI : Algebra c.F (CAt σ') := (σ'.comp (incF c c' hle)).toAlgebra
    have e := h (CAt σ') (fun _ => rfl) ((unfBC hle U σ').un k ⟨x, hx⟩)
    have e1 : rdU (unfBC hle U σ') f' k x = toC (evR Xo c' f' ((unfBC hle U σ').un k ⟨x, hx⟩)) := dif_pos hx
    rw [e1, e]
    refine Finset.sum_congr rfl fun j _ => ?_
    have e2 : rdU (U (σ'.comp (incF c c' hle))) (fs j) k x =
      toC (evR Xo c (fs j) ((U (σ'.comp (incF c c' hle))).un k ⟨x, hx⟩)) := dif_pos hx
    rw [e2]
    rfl
  · have e1 : rdU (unfBC hle U σ') f' k x = 0 := dif_neg hx
    rw [e1]
    refine (Finset.sum_eq_zero fun j _ => ?_).symm
    have e2 : rdU (U (σ'.comp (incF c c' hle))) (fs j) k x = 0 := dif_neg hx
    rw [e2, mul_zero]

/- English proof (translation)
Take `⟨m, b, fs, hfs, hbc⟩` from `(GlobalTheory.FieldBC.secBC_and_cuspBC E H Dw l Xo c c' hle).2 r U a n f' hf`. Conclude with `⟨m, b, fun j => ⟨fs j, hfs j⟩, rdU_of_isBC hle U σ' hbc⟩`.
-/
theorem exists_rdU_eq_sum (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ' : c'.F →+* ℂ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ)
    (f' : Rul Xo c') (hf : f' ∈ cusp Xo c' (unfBC hle U) a n) :
    ∃ (m : ℕ) (b : Fin m → c'.F) (fs : Fin m → cusp Xo c U a n), ∀ k x,
      rdU (unfBC hle U σ') f' k x = ∑ j, σ' (b j) * rdU (U (σ'.comp (incF c c' hle))) (fs j : Rul Xo c) k x := by
  obtain ⟨m, b, fs, hfs, hbc⟩ := (GlobalTheory.FieldBC.secBC_and_cuspBC E H Dw l Xo c c' hle).2 r U a n f' hf
  exact ⟨m, b, fun j => ⟨fs j, hfs j⟩, rdU_of_isBC hle U σ' hbc⟩

end Gen

/- English proof (translation)
Rewrite using `[h, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[ha, hp]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sum_shape {m : ℕ} {c l u x : ℂ} {a a' y p : Fin m → ℂ} (h : x = ∑ j, a j * y j) (ha : ∀ j, a' j = a j)
    (hp : ∀ j, p j = c * u * y j) : c * l * u * x = ∑ j, a' j * (l * p j) := by
  rw [h, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ha, hp]
  ring

end Lemmas

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

end GlobalTheory.PhRatCommon
