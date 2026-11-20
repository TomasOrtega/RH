import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

open scoped ContDiff

namespace GlobalTheory.CjNeg

variable {D : D7}

/- English proof (translation)
Distinguish the cases in `h : IsUnit A.det`. Conclude with `Matrix.inv_eq_left_inv (by rw [neg_mul_neg, Matrix.nonsing_inv_mul A h])`. Establish `h' : ¬ IsUnit (-A).det`. Rewrite using `[Matrix.det_neg]`. Introduce `hu`.

Conclude with `h (isUnit_of_mul_isUnit_right hu)`. Rewrite using `[Matrix.nonsing_inv_apply_not_isUnit _ h, Matrix.nonsing_inv_apply_not_isUnit _ h', neg_zero]`.
-/
theorem inv_neg_mat {n : ℕ} (A : Matrix (Fin n) (Fin n) D.host.E) : (-A)⁻¹ = -A⁻¹ := by
  by_cases h : IsUnit A.det
  · exact Matrix.inv_eq_left_inv (by rw [neg_mul_neg, Matrix.nonsing_inv_mul A h])
  · have h' : ¬ IsUnit (-A).det := by
      rw [Matrix.det_neg]
      intro hu
      exact h (isUnit_of_mul_isUnit_right hu)
    rw [Matrix.nonsing_inv_apply_not_isUnit _ h, Matrix.nonsing_inv_apply_not_isUnit _ h', neg_zero]

/- English proof (translation)
Establish `hn : ‖ψ a‖ = 1` using `hψ.1.2.1 a`. Establish `h1 : ψ a * ψ (-a) = 1`. Rewrite using `[← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]`. Establish `h2 : starRingEnd ℂ (ψ a) * ψ a = 1`. Rewrite using `[mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]`.

Simplify using the standard rewrite rules. Combine the equalities or inequalities in the displayed calculation.
-/
theorem conj_psi {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (a : AF D.host.F) :
    starRingEnd ℂ (ψ a) = ψ (-a) := by
  have hn : ‖ψ a‖ = 1 := hψ.1.2.1 a
  have h1 : ψ a * ψ (-a) = 1 := by
    rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  have h2 : starRingEnd ℂ (ψ a) * ψ a = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]; simp
  calc starRingEnd ℂ (ψ a) = starRingEnd ℂ (ψ a) * (ψ a * ψ (-a)) := by rw [h1, mul_one]
    _ = ψ (-a) := by rw [← mul_assoc, h2, one_mul]

/- English proof (translation)
Simplify using `only [symplOH, symplO, hO, GlobalTheory.ChiGrid.negSp_gram, Matrix.neg_apply, map_neg, neg_mul, mul_neg, Finset.sum_neg_distrib]`.
-/
theorem symplOH_negT (S T : HSp D) (x y : WO S T) :
    symplOH S (GlobalTheory.ChiGrid.negSp T) x y = -symplOH S T x y := by
  simp only [symplOH, symplO, hO, GlobalTheory.ChiGrid.negSp_gram, Matrix.neg_apply, map_neg, neg_mul, mul_neg,
    Finset.sum_neg_distrib]

/- English proof (translation)
Simplify using `only [symplOH, symplO, hO, GlobalTheory.ChiGrid.negSp_gram, inv_neg_mat, Matrix.neg_apply, map_neg, neg_mul, mul_neg, Finset.sum_neg_distrib]`.
-/
theorem symplOH_negS (S T : HSp D) (x y : WO S T) :
    symplOH (GlobalTheory.ChiGrid.negSp S) T x y = -symplOH S T x y := by
  simp only [symplOH, symplO, hO, GlobalTheory.ChiGrid.negSp_gram, inv_neg_mat, Matrix.neg_apply, map_neg, neg_mul, mul_neg,
    Finset.sum_neg_distrib]

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger in
/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `only [heisO, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, id_eq, map_mul, conj_psi hψ, symplOH_negT]`.
-/
theorem heis_negT {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (w : WO S T)
    (f : WO S T → ℂ) :
    heisO ψ S (GlobalTheory.ChiGrid.negSp T) w (cj id f) = cj id (heisO ψ S T w f) := by
  funext x
  simp only [heisO, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, id_eq, map_mul, conj_psi hψ, symplOH_negT]

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger in
/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `only [heisO, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, id_eq, map_mul, conj_psi hψ, symplOH_negS]`.
-/
theorem heis_negS {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (w : WO S T)
    (f : WO S T → ℂ) :
    heisO ψ (GlobalTheory.ChiGrid.negSp S) T w (cj id f) = cj id (heisO ψ S T w f) := by
  funext x
  simp only [heisO, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, id_eq, map_mul, conj_psi hψ, symplOH_negS]

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger in
/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `only [heisO, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, id_eq, map_mul, conj_psi hψ, symplOH_negT, neg_neg]`.
-/
theorem heis_negT' {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (w : WO S T)
    (f : WO S T → ℂ) :
    heisO ψ S T w (cj id f) = cj id (heisO ψ S (GlobalTheory.ChiGrid.negSp T) w f) := by
  funext x
  simp only [heisO, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, id_eq, map_mul, conj_psi hψ, symplOH_negT, neg_neg]

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger in
/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `only [heisO, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, id_eq, map_mul, conj_psi hψ, symplOH_negS, neg_neg]`.
-/
theorem heis_negS' {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (w : WO S T)
    (f : WO S T → ℂ) :
    heisO ψ S T w (cj id f) = cj id (heisO ψ (GlobalTheory.ChiGrid.negSp S) T w f) := by
  funext x
  simp only [heisO, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, id_eq, map_mul, conj_psi hψ, symplOH_negS, neg_neg]

/- English proof (translation)
The claim follows from `Complex.conjCLE.contDiff.comp hg`.
-/
theorem contDiff_conj {k : ℕ} {g : (Fin k → ℝ) → ℂ} (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ fun t => starRingEnd ℂ (g t) :=
  Complex.conjCLE.contDiff.comp hg

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger in
/- English proof (translation)
Use `show starRingEnd ℂ (f (ratW T S γ + w)) = ψ (-(symplOH S (GlobalTheory.ChiGrid.negSp T) (ratW T S γ) w)) * starRingEnd ℂ (f w)`. Rewrite using `[hf.quasi, map_mul, conj_psi hψ, symplOH_negT]`. Use `level := by`. Take `⟨U, hU, h⟩` from `hf.level`. Conclude with `⟨U, hU, fun u hu hu0 => by rw [heis_negT hψ, h u hu hu0]⟩`.

Use `cont := Complex.continuous_conj.comp hf.cont`. Use `smooth k L hL hL0 w := contDiff_conj (hf.smooth k L hL hL0 w)`.
-/
theorem theta_negT {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ S (GlobalTheory.ChiGrid.negSp T) (cj id f) where
  quasi γ w := by
    show starRingEnd ℂ (f (ratW T S γ + w)) = ψ (-(symplOH S (GlobalTheory.ChiGrid.negSp T) (ratW T S γ) w)) * starRingEnd ℂ (f w)
    rw [hf.quasi, map_mul, conj_psi hψ, symplOH_negT]
  level := by
    obtain ⟨U, hU, h⟩ := hf.level
    exact ⟨U, hU, fun u hu hu0 => by rw [heis_negT hψ, h u hu hu0]⟩
  cont := Complex.continuous_conj.comp hf.cont
  smooth k L hL hL0 w := contDiff_conj (hf.smooth k L hL hL0 w)

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger in
/- English proof (translation)
Use `show starRingEnd ℂ (f (ratW T S γ + w)) = ψ (-(symplOH S T (ratW T S γ) w)) * starRingEnd ℂ (f w)`. Establish `hq : f (ratW T S γ + w) = ψ (-(symplOH S (GlobalTheory.ChiGrid.negSp T) (ratW T S γ) w)) * f w` using `hf.quasi γ w`. Rewrite using `[hq, map_mul, conj_psi hψ, symplOH_negT, neg_neg]`. Use `level := by`. Take `⟨U, hU, h⟩` from `hf.level`.

Conclude with `⟨U, hU, fun u hu hu0 => by rw [heis_negT' hψ, h u hu hu0]⟩`. Use `cont := Complex.continuous_conj.comp hf.cont`. Use `smooth k L hL hL0 w := contDiff_conj (hf.smooth k L hL hL0 w)`.
-/
theorem theta_negT' {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S (GlobalTheory.ChiGrid.negSp T) f) : IsThetaFunO ψ S T (cj id f) where
  quasi γ w := by
    show starRingEnd ℂ (f (ratW T S γ + w)) = ψ (-(symplOH S T (ratW T S γ) w)) * starRingEnd ℂ (f w)
    have hq : f (ratW T S γ + w) = ψ (-(symplOH S (GlobalTheory.ChiGrid.negSp T) (ratW T S γ) w)) * f w := hf.quasi γ w
    rw [hq, map_mul, conj_psi hψ, symplOH_negT, neg_neg]
  level := by
    obtain ⟨U, hU, h⟩ := hf.level
    exact ⟨U, hU, fun u hu hu0 => by rw [heis_negT' hψ, h u hu hu0]⟩
  cont := Complex.continuous_conj.comp hf.cont
  smooth k L hL hL0 w := contDiff_conj (hf.smooth k L hL hL0 w)

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger in
/- English proof (translation)
Use `show starRingEnd ℂ (f (ratW T S γ + w)) = ψ (-(symplOH (GlobalTheory.ChiGrid.negSp S) T (ratW T S γ) w)) * starRingEnd ℂ (f w)`. Rewrite using `[hf.quasi, map_mul, conj_psi hψ, symplOH_negS]`. Use `level := by`. Take `⟨U, hU, h⟩` from `hf.level`. Conclude with `⟨U, hU, fun u hu hu0 => by rw [heis_negS hψ, h u hu hu0]⟩`.

Use `cont := Complex.continuous_conj.comp hf.cont`. Use `smooth k L hL hL0 w := contDiff_conj (hf.smooth k L hL hL0 w)`.
-/
theorem theta_negS {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ (GlobalTheory.ChiGrid.negSp S) T (cj id f) where
  quasi γ w := by
    show starRingEnd ℂ (f (ratW T S γ + w)) = ψ (-(symplOH (GlobalTheory.ChiGrid.negSp S) T (ratW T S γ) w)) * starRingEnd ℂ (f w)
    rw [hf.quasi, map_mul, conj_psi hψ, symplOH_negS]
  level := by
    obtain ⟨U, hU, h⟩ := hf.level
    exact ⟨U, hU, fun u hu hu0 => by rw [heis_negS hψ, h u hu hu0]⟩
  cont := Complex.continuous_conj.comp hf.cont
  smooth k L hL hL0 w := contDiff_conj (hf.smooth k L hL hL0 w)

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger in
/- English proof (translation)
Use `show starRingEnd ℂ (f (ratW T S γ + w)) = ψ (-(symplOH S T (ratW T S γ) w)) * starRingEnd ℂ (f w)`. Establish `hq : f (ratW T S γ + w) = ψ (-(symplOH (GlobalTheory.ChiGrid.negSp S) T (ratW T S γ) w)) * f w` using `hf.quasi γ w`. Rewrite using `[hq, map_mul, conj_psi hψ, symplOH_negS, neg_neg]`. Use `level := by`. Take `⟨U, hU, h⟩` from `hf.level`.

Conclude with `⟨U, hU, fun u hu hu0 => by rw [heis_negS' hψ, h u hu hu0]⟩`. Use `cont := Complex.continuous_conj.comp hf.cont`. Use `smooth k L hL hL0 w := contDiff_conj (hf.smooth k L hL hL0 w)`.
-/
theorem theta_negS' {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ (GlobalTheory.ChiGrid.negSp S) T f) : IsThetaFunO ψ S T (cj id f) where
  quasi γ w := by
    show starRingEnd ℂ (f (ratW T S γ + w)) = ψ (-(symplOH S T (ratW T S γ) w)) * starRingEnd ℂ (f w)
    have hq : f (ratW T S γ + w) = ψ (-(symplOH (GlobalTheory.ChiGrid.negSp S) T (ratW T S γ) w)) * f w := hf.quasi γ w
    rw [hq, map_mul, conj_psi hψ, symplOH_negS, neg_neg]
  level := by
    obtain ⟨U, hU, h⟩ := hf.level
    exact ⟨U, hU, fun u hu hu0 => by rw [heis_negS' hψ, h u hu hu0]⟩
  cont := Complex.continuous_conj.comp hf.cont
  smooth k L hL hL0 w := contDiff_conj (hf.smooth k L hL hL0 w)

/- English proof (translation)
The claim follows from `GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj_cj id id (fun _ => rfl) f`.
-/
theorem cj_id_cj_id {S T : HSp D} (f : WO S T → ℂ) : GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id f) = f :=
  GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj_cj id id (fun _ => rfl) f

/- English proof (translation)
Introduce `D ψ hψ S T`. Use `⟨fun f => ⟨⟨fun h => ?_, theta_negT hψ⟩, ⟨fun h => ?_, theta_negS hψ⟩⟩, fun w f => ⟨heis_negT hψ S T w f, heis_negS hψ S T w f⟩⟩` and prove the remaining obligations. Simplify `theta_negT' hψ h` using `only [cj_id_cj_id]`. Simplify `theta_negS' hψ h` using `only [cj_id_cj_id]`.
-/
theorem theta_heis_neg : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ S T : HSp D, (∀ f : WO S T → ℂ, (IsThetaFunO ψ S (GlobalTheory.ChiGrid.negSp T) (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id f) ↔ IsThetaFunO ψ S T f) ∧ (IsThetaFunO ψ (GlobalTheory.ChiGrid.negSp S) T (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id f) ↔ IsThetaFunO ψ S T f)) ∧ ∀ (w : WO S T) (f : WO S T → ℂ), heisO ψ S (GlobalTheory.ChiGrid.negSp T) w (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id f) = GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id (heisO ψ S T w f) ∧ heisO ψ (GlobalTheory.ChiGrid.negSp S) T w (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id f) = GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id (heisO ψ S T w f) := by
  intro D ψ hψ S T
  refine ⟨fun f => ⟨⟨fun h => ?_, theta_negT hψ⟩, ⟨fun h => ?_, theta_negS hψ⟩⟩, fun w f => ⟨heis_negT hψ S T w f, heis_negS hψ S T w f⟩⟩
  · simpa only [cj_id_cj_id] using theta_negT' hψ h
  · simpa only [cj_id_cj_id] using theta_negS' hψ h

end GlobalTheory.CjNeg
