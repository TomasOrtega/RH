import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Admissible
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ThresholdProductsBounded

open Formalism.FourierDecayAlt Formalism.MainNotions.S GlobalTheory.ThA Formalism.QuantumDeterminants MeasureTheory Matrix
open Formalism.FourierDecayAlt.P.Dx2.OrbJ

namespace GlobalTheory.ThA.QuotCut

/- English proof (translation)
The claim follows from `continuous_pi fun i => continuous_pi fun j => hF.matrix_elem i j`.
-/
private lemma continuous_of_symm_of_continuous {X : Type*} [TopologicalSpace X] {n : ℕ} {F : X → Matrix (Fin n) (Fin n) ℂ}
    (hF : Continuous F) : Continuous (fun y => (Matrix.of.symm (F y) : Fin n → Fin n → ℂ)) :=
  continuous_pi fun i => continuous_pi fun j => hF.matrix_elem i j

/- English proof (translation)
Establish `hc : Continuous (fun a : Fin n → Fin n → ℂ => Matrix.of a)` using `continuous_id`. Establish `hdet : Measurable (fun a : Fin n → Fin n → ℂ => ((Matrix.of a).det)⁻¹)` using `hc.matrix_det.measurable.inv`. Use `measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_` and prove the remaining obligations. Establish `e : (fun a : Fin n → Fin n → ℂ => (Matrix.of.symm ((Matrix.of a)⁻¹) : Fin n → Fin n → ℂ) i j) = fun a => ((Matrix.of a).det)⁻¹ * (Matrix.of a).adjugate i j`. Use function extensionality and compare the values at `a`.

Use `show ((Matrix.of a)⁻¹) i j = _`. Rewrite using `[Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul]`. Rewrite using `[e]`. Conclude with `hdet.mul (hc.matrix_adjugate.matrix_elem i j).measurable`.
-/
private lemma measurable_inv_apply_of_measurable_entries {n : ℕ} :
    Measurable (fun a : Fin n → Fin n → ℂ => (Matrix.of.symm ((Matrix.of a)⁻¹) : Fin n → Fin n → ℂ)) := by
  have hc : Continuous (fun a : Fin n → Fin n → ℂ => Matrix.of a) := continuous_id
  have hdet : Measurable (fun a : Fin n → Fin n → ℂ => ((Matrix.of a).det)⁻¹) :=
    hc.matrix_det.measurable.inv
  refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
  have e : (fun a : Fin n → Fin n → ℂ => (Matrix.of.symm ((Matrix.of a)⁻¹) : Fin n → Fin n → ℂ) i j)
      = fun a => ((Matrix.of a).det)⁻¹ * (Matrix.of a).adjugate i j := by
    funext a
    show ((Matrix.of a)⁻¹) i j = _
    rw [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul]
  rw [e]
  exact hdet.mul (hc.matrix_adjugate.matrix_elem i j).measurable

/- English proof (translation)
Establish `h1 : Continuous (fun q : (Fin n → Fin n → ℂ) × (Fin n → Fin n → ℂ) => Matrix.of q.1)` using `continuous_fst`. Establish `h2 : Continuous (fun q : (Fin n → Fin n → ℂ) × (Fin n → Fin n → ℂ) => Matrix.of q.2)` using `continuous_snd`. Conclude with `(continuous_of_symm_of_continuous (h1.matrix_mul h2)).measurable`.
-/
private lemma measurable_mul_apply_of_measurable_entries {n : ℕ} : Measurable (fun q : (Fin n → Fin n → ℂ) × (Fin n → Fin n → ℂ) =>
    (Matrix.of.symm (Matrix.of q.1 * Matrix.of q.2) : Fin n → Fin n → ℂ)) := by
  have h1 : Continuous (fun q : (Fin n → Fin n → ℂ) × (Fin n → Fin n → ℂ) => Matrix.of q.1) := continuous_fst
  have h2 : Continuous (fun q : (Fin n → Fin n → ℂ) × (Fin n → Fin n → ℂ) => Matrix.of q.2) := continuous_snd
  exact (continuous_of_symm_of_continuous (h1.matrix_mul h2)).measurable

/- English proof (translation)
Establish `ha : Continuous (fun q : Mt k r × B.SS k r => Matrix.of q.1)` using `continuous_fst`. Establish `h12 : Continuous (fun q : Mt k r × B.SS k r => Matrix.of q.2.1.2)` using `continuous_snd.fst.snd`. Establish `h22 : Continuous (fun q : Mt k r × B.SS k r => Matrix.of q.2.2.2)` using `continuous_snd.snd.snd`. Establish `hxi : Continuous (fun _ : Mt k r × B.SS k r => x⁻¹)` using `continuous_const`. Establish `hxc : Continuous (fun _ : Mt k r × B.SS k r => x)` using `continuous_const`.

Establish `c1` using `continuous_of_symm_of_continuous (ha.matrix_mul h12)`. Establish `c2` using `continuous_of_symm_of_continuous (((hxi.matrix_mul ha).matrix_mul hxc).matrix_mul h22)`. Conclude with `(((continuous_snd.fst.fst).prodMk c1).prodMk ((continuous_snd.snd.fst).prodMk c2)).measurable`.
-/
private lemma measurable_actR_of {k r : ℕ} (x : B.Mat k r) :
    Measurable (fun q : Mt k r × B.SS k r => C6.actR x (Matrix.of q.1) q.2) := by
  have ha : Continuous (fun q : Mt k r × B.SS k r => Matrix.of q.1) := continuous_fst
  have h12 : Continuous (fun q : Mt k r × B.SS k r => Matrix.of q.2.1.2) := continuous_snd.fst.snd
  have h22 : Continuous (fun q : Mt k r × B.SS k r => Matrix.of q.2.2.2) := continuous_snd.snd.snd
  have hxi : Continuous (fun _ : Mt k r × B.SS k r => x⁻¹) := continuous_const
  have hxc : Continuous (fun _ : Mt k r × B.SS k r => x) := continuous_const
  have c1 := continuous_of_symm_of_continuous (ha.matrix_mul h12)
  have c2 := continuous_of_symm_of_continuous (((hxi.matrix_mul ha).matrix_mul hxc).matrix_mul h22)
  exact (((continuous_snd.fst.fst).prodMk c1).prodMk ((continuous_snd.snd.fst).prodMk c2)).measurable

/- English proof (translation)
Take `⟨⟨h, n⟩, ⟨h', n'⟩⟩` from `q`. Establish `e1 : A⁻¹ * (A * Matrix.of n) = Matrix.of n` using `Matrix.nonsing_inv_mul_cancel_left _ _ hA`. Establish `e2 : x⁻¹ * A⁻¹ * x * (x⁻¹ * A * x * Matrix.of n') = Matrix.of n'`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[Matrix.mul_nonsing_inv_cancel_left _ _ hx, Matrix.nonsing_inv_mul_cancel_left _ _ hA, Matrix.nonsing_inv_mul_cancel_left _ _ hx]`.

Use `show ((h, Matrix.of.symm (A⁻¹ * (A * Matrix.of n))), (h', Matrix.of.symm (x⁻¹ * A⁻¹ * x * (x⁻¹ * A * x * Matrix.of n')))) = ((h, n), (h', n'))`. Rewrite using `[e1, e2]`. Both sides reduce to the same expression.
-/
private lemma actR_inv_actR {k r : ℕ} (x : B.Mat k r) (hx : IsUnit x.det) (A : B.Mat k r) (hA : IsUnit A.det)
    (q : B.SS k r) : C6.actR x A⁻¹ (C6.actR x A q) = q := by
  obtain ⟨⟨h, n⟩, ⟨h', n'⟩⟩ := q
  have e1 : A⁻¹ * (A * Matrix.of n) = Matrix.of n := Matrix.nonsing_inv_mul_cancel_left _ _ hA
  have e2 : x⁻¹ * A⁻¹ * x * (x⁻¹ * A * x * Matrix.of n') = Matrix.of n' := by
    simp only [Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv_cancel_left _ _ hx, Matrix.nonsing_inv_mul_cancel_left _ _ hA,
      Matrix.nonsing_inv_mul_cancel_left _ _ hx]
  show ((h, Matrix.of.symm (A⁻¹ * (A * Matrix.of n))),
      (h', Matrix.of.symm (x⁻¹ * A⁻¹ * x * (x⁻¹ * A * x * Matrix.of n')))) = ((h, n), (h', n'))
  rw [e1, e2]
  rfl

/- English proof (translation)
The claim follows from `measurable_id`.
-/
private lemma measurable_of_symm_of {n : ℕ} :
    Measurable fun a : Fin n → Fin n → ℂ => (Matrix.of.symm (Matrix.of a) : Fin n → Fin n → ℂ) :=
  measurable_id

/- English proof (translation)
Establish `hFe : ∀ i l, Measurable fun a => F a i l` using `fun i l => measurable_pi_iff.mp (measurable_pi_iff.mp hF i) l`. Establish `hGe : ∀ i l, Measurable fun a => G a i l` using `fun i l => measurable_pi_iff.mp (measurable_pi_iff.mp hG i) l`. Use `measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_` and prove the remaining obligations. Use `show Measurable fun a => (F a * G a) i j`. Simplify using `only [Matrix.mul_apply]`.

Conclude with `Finset.measurable_sum _ fun l _ => (hFe i l).mul (hGe l j)`.
-/
private lemma measurable_of_symm_mul {α : Type*} [MeasurableSpace α] {n : ℕ} {F G : α → Matrix (Fin n) (Fin n) ℂ}
    (hF : Measurable fun a => (Matrix.of.symm (F a) : Fin n → Fin n → ℂ))
    (hG : Measurable fun a => (Matrix.of.symm (G a) : Fin n → Fin n → ℂ)) :
    Measurable fun a => (Matrix.of.symm (F a * G a) : Fin n → Fin n → ℂ) := by
  have hFe : ∀ i l, Measurable fun a => F a i l := fun i l => measurable_pi_iff.mp (measurable_pi_iff.mp hF i) l
  have hGe : ∀ i l, Measurable fun a => G a i l := fun i l => measurable_pi_iff.mp (measurable_pi_iff.mp hG i) l
  refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
  show Measurable fun a => (F a * G a) i j
  simp only [Matrix.mul_apply]
  exact Finset.measurable_sum _ fun l _ => (hFe i l).mul (hGe l j)

/- English proof (translation)
Establish `hm` using `measurable_mul_apply_of_measurable_entries (n := n)`. Establish `hi` using `measurable_inv_apply_of_measurable_entries (n := n)`. Establish `key : ∀ g : (Fin n → Fin n → ℂ) → ENNReal, Measurable g → ∀ h : (Fin n → Fin n → ℂ) → ENNReal, Measurable h → (∫⁻ b, g b ∂μR) * (∫⁻ a, h a ∂μR) = (∫⁻ b, h b ∂μR) * ∫⁻ a, g (Matrix.of.symm (Matrix.of a)⁻¹) ∂μR`. Introduce `g hg h hh`. Establish `hmb : ∀ b : Fin n → Fin n → ℂ, Measurable fun a : Fin n → Fin n → ℂ => g (Matrix.of.symm (Matrix.of b * (Matrix.of a)⁻¹))` using `fun b => hg.comp (measurable_of_symm_mul (F := fun _ : Fin n → Fin n → ℂ => Matrix.of b) (G := fun a : Fin n → Fin n → ℂ => (Matrix.of a)⁻¹) measurable_const hi)`.

Establish `hmh : ∀ b : Fin n → Fin n → ℂ, Measurable fun a : Fin n → Fin n → ℂ => h (Matrix.of.symm (Matrix.of b * Matrix.of a))` using `fun b => hh.comp (measurable_of_symm_mul (F := fun _ : Fin n → Fin n → ℂ => Matrix.of b) (G := fun a : Fin n → Fin n → ℂ => Matrix.of a) measurable_const measurable_of_symm_of)`. Combine the equalities or inequalities in the displayed calculation. Use `lintegral_congr_ae (hU.mono fun b hb => ?_)` and prove the remaining obligations. Simplify using `only`. Rewrite using `[hleft _ hb h hh]`.

Use `_ = ∫⁻ b, ∫⁻ a, g b * h (Matrix.of.symm (Matrix.of b * Matrix.of a)) ∂μR ∂μR := by`. Use `lintegral_congr fun b => ?_` and prove the remaining obligations. Conclude with `(lintegral_const_mul _ (hmh b)).symm`. Use `_ = ∫⁻ a, ∫⁻ b, g b * h (Matrix.of.symm (Matrix.of b * Matrix.of a)) ∂μR ∂μR := by`. Use `lintegral_lintegral_swap ?_` and prove the remaining obligations.

Conclude with `((hg.comp measurable_fst).mul (hh.comp hm)).aemeasurable`. Use `_ = ∫⁻ a, ∫⁻ b, g (Matrix.of.symm (Matrix.of b * (Matrix.of a)⁻¹)) * h b ∂μR ∂μR := by`. Use `lintegral_congr_ae (hU.mono fun a ha => ?_)` and prove the remaining obligations. Establish `hua` using `hUu _ ha`. Establish `hψ : Measurable fun c : Fin n → Fin n → ℂ => g (Matrix.of.symm (Matrix.of c * (Matrix.of a)⁻¹)) * h c` using `(hg.comp (measurable_of_symm_mul (F := fun c : Fin n → Fin n → ℂ => Matrix.of c) (G := fun _ : Fin n → Fin n → ℂ => (Matrix.of a)⁻¹) measurable_of_symm_of measurable_const)).mul hh`.

Use `hright _ ha _ hψ` as an intermediate fact. Establish `e : ∀ b : Fin n → Fin n → ℂ, Matrix.of.symm (Matrix.of (Matrix.of.symm (Matrix.of b * Matrix.of a)) * (Matrix.of a)⁻¹) = b`. Introduce `b`. Rewrite using `[Equiv.apply_symm_apply, Matrix.mul_nonsing_inv_cancel_right _ _ hua]`. Both sides reduce to the same expression.

Simplify using `only [e] at this`. Conclude with `this`. Use `_ = ∫⁻ b, ∫⁻ a, g (Matrix.of.symm (Matrix.of b * (Matrix.of a)⁻¹)) * h b ∂μR ∂μR := by`. Use `lintegral_lintegral_swap ?_` and prove the remaining obligations. Conclude with `((hg.comp (measurable_of_symm_mul (F := fun q : (Fin n → Fin n → ℂ) × (Fin n → Fin n → ℂ) => Matrix.of q.2) (G := fun q : (Fin n → Fin n → ℂ) × (Fin n → Fin n → ℂ) => (Matrix.of q.1)⁻¹) measurable_snd (hi.comp measurable_fst))).mul (hh.comp measurable_snd)).aemeasurable`.

Use `_ = ∫⁻ b, h b * ∫⁻ a, g (Matrix.of.symm (Matrix.of b * (Matrix.of a)⁻¹)) ∂μR ∂μR := by`. Use `lintegral_congr fun b => ?_` and prove the remaining obligations. Rewrite using `[lintegral_mul_const _ (hmb b), mul_comm]`. Use `_ = ∫⁻ b, h b * ∫⁻ a, g (Matrix.of.symm (Matrix.of a)⁻¹) ∂μR ∂μR := by`. Use `lintegral_congr_ae (hU.mono fun b hb => ?_)` and prove the remaining obligations.

Establish `hub` using `hUu _ hb`. Use `hright _ hb _ (hmb b)` as an intermediate fact. Establish `e : ∀ a : Fin n → Fin n → ℂ, Matrix.of.symm (Matrix.of b * (Matrix.of (Matrix.of.symm (Matrix.of a * Matrix.of b)))⁻¹) = Matrix.of.symm (Matrix.of a)⁻¹`. Introduce `a`. Rewrite using `[Equiv.apply_symm_apply, Matrix.mul_inv_rev, Matrix.mul_nonsing_inv_cancel_left _ _ hub]`.

Simplify using `only [e] at this`. Simplify using `only`. Rewrite using `[this]`. Use `_ = (∫⁻ b, h b ∂μR) * ∫⁻ a, g (Matrix.of.symm (Matrix.of a)⁻¹) ∂μR := lintegral_mul_const _ hh`. Take `⟨g0, hg0pos, hg0m, hg0lt⟩` from `exists_pos_lintegral_lt_of_sigmaFinite μR (ε := 1) one_ne_zero`.

Establish `hg0m' : Measurable fun a => (g0 a : ENNReal)` using `hg0m.coe_nnreal_ennreal`. Establish `htop : (∫⁻ a, (g0 a : ENNReal) ∂μR) ≠ ⊤` using `(hg0lt.trans ENNReal.one_lt_top).ne`. Establish `hz : (∫⁻ a, (g0 a : ENNReal) ∂μR) ≠ 0`. Introduce `h0`. Rewrite `h0` using `[lintegral_eq_zero_iff hg0m']`.

Establish `hf : ∀ᵐ a ∂μR, False` using `h0.mono fun a ha => by`. Simplify using `only [Pi.zero_apply, ENNReal.coe_eq_zero] at ha`. Conclude with `(hg0pos a).ne' ha`. Conclude with `hne (ae_eq_bot.mp (Filter.eventually_false_iff_eq_bot.mp hf))`. Establish `K` using `key u hu _ hg0m'`.

Rewrite `K` using `[mul_comm]`. Conclude with `((ENNReal.mul_right_inj hz htop).mp K).symm`.
-/
private lemma lintegral_inv_eq_of_mul_invariant {n : ℕ} (U : Set (Matrix (Fin n) (Fin n) ℂ)) (μR : Measure (Fin n → Fin n → ℂ))
    [SigmaFinite μR] (hne : μR ≠ 0)
    (hU : ∀ᵐ a ∂μR, Matrix.of a ∈ U) (hUu : ∀ a ∈ U, IsUnit a.det)
    (hleft : ∀ a ∈ U, ∀ h : (Fin n → Fin n → ℂ) → ENNReal, Measurable h →
        ∫⁻ b, h (Matrix.of.symm (a * Matrix.of b)) ∂μR = ∫⁻ b, h b ∂μR)
    (hright : ∀ a ∈ U, ∀ h : (Fin n → Fin n → ℂ) → ENNReal, Measurable h →
        ∫⁻ b, h (Matrix.of.symm (Matrix.of b * a)) ∂μR = ∫⁻ b, h b ∂μR)
    (u : (Fin n → Fin n → ℂ) → ENNReal) (hu : Measurable u) :
    ∫⁻ a, u (Matrix.of.symm (Matrix.of a)⁻¹) ∂μR = ∫⁻ a, u a ∂μR := by
  have hm := measurable_mul_apply_of_measurable_entries (n := n)
  have hi := measurable_inv_apply_of_measurable_entries (n := n)
  have key : ∀ g : (Fin n → Fin n → ℂ) → ENNReal, Measurable g → ∀ h : (Fin n → Fin n → ℂ) → ENNReal,
      Measurable h → (∫⁻ b, g b ∂μR) * (∫⁻ a, h a ∂μR)
        = (∫⁻ b, h b ∂μR) * ∫⁻ a, g (Matrix.of.symm (Matrix.of a)⁻¹) ∂μR := by
    intro g hg h hh
    have hmb : ∀ b : Fin n → Fin n → ℂ,
        Measurable fun a : Fin n → Fin n → ℂ => g (Matrix.of.symm (Matrix.of b * (Matrix.of a)⁻¹)) :=
      fun b => hg.comp (measurable_of_symm_mul (F := fun _ : Fin n → Fin n → ℂ => Matrix.of b)
        (G := fun a : Fin n → Fin n → ℂ => (Matrix.of a)⁻¹) measurable_const hi)
    have hmh : ∀ b : Fin n → Fin n → ℂ,
        Measurable fun a : Fin n → Fin n → ℂ => h (Matrix.of.symm (Matrix.of b * Matrix.of a)) :=
      fun b => hh.comp (measurable_of_symm_mul (F := fun _ : Fin n → Fin n → ℂ => Matrix.of b)
        (G := fun a : Fin n → Fin n → ℂ => Matrix.of a) measurable_const measurable_of_symm_of)
    calc (∫⁻ b, g b ∂μR) * (∫⁻ a, h a ∂μR)
        = ∫⁻ b, g b * ∫⁻ a, h a ∂μR ∂μR := (lintegral_mul_const _ hg).symm
      _ = ∫⁻ b, g b * ∫⁻ a, h (Matrix.of.symm (Matrix.of b * Matrix.of a)) ∂μR ∂μR := by
          refine lintegral_congr_ae (hU.mono fun b hb => ?_)
          dsimp only
          rw [hleft _ hb h hh]
      _ = ∫⁻ b, ∫⁻ a, g b * h (Matrix.of.symm (Matrix.of b * Matrix.of a)) ∂μR ∂μR := by
          refine lintegral_congr fun b => ?_
          exact (lintegral_const_mul _ (hmh b)).symm
      _ = ∫⁻ a, ∫⁻ b, g b * h (Matrix.of.symm (Matrix.of b * Matrix.of a)) ∂μR ∂μR := by
          refine lintegral_lintegral_swap ?_
          exact ((hg.comp measurable_fst).mul (hh.comp hm)).aemeasurable
      _ = ∫⁻ a, ∫⁻ b, g (Matrix.of.symm (Matrix.of b * (Matrix.of a)⁻¹)) * h b ∂μR ∂μR := by
          refine lintegral_congr_ae (hU.mono fun a ha => ?_)
          have hua := hUu _ ha
          have hψ : Measurable fun c : Fin n → Fin n → ℂ =>
              g (Matrix.of.symm (Matrix.of c * (Matrix.of a)⁻¹)) * h c :=
            (hg.comp (measurable_of_symm_mul (F := fun c : Fin n → Fin n → ℂ => Matrix.of c)
              (G := fun _ : Fin n → Fin n → ℂ => (Matrix.of a)⁻¹) measurable_of_symm_of measurable_const)).mul hh
          have := hright _ ha _ hψ
          have e : ∀ b : Fin n → Fin n → ℂ,
              Matrix.of.symm (Matrix.of (Matrix.of.symm (Matrix.of b * Matrix.of a)) * (Matrix.of a)⁻¹) = b := by
            intro b
            rw [Equiv.apply_symm_apply, Matrix.mul_nonsing_inv_cancel_right _ _ hua]
            rfl
          simp only [e] at this
          exact this
      _ = ∫⁻ b, ∫⁻ a, g (Matrix.of.symm (Matrix.of b * (Matrix.of a)⁻¹)) * h b ∂μR ∂μR := by
          refine lintegral_lintegral_swap ?_
          exact ((hg.comp (measurable_of_symm_mul
            (F := fun q : (Fin n → Fin n → ℂ) × (Fin n → Fin n → ℂ) => Matrix.of q.2)
            (G := fun q : (Fin n → Fin n → ℂ) × (Fin n → Fin n → ℂ) => (Matrix.of q.1)⁻¹)
            measurable_snd (hi.comp measurable_fst))).mul (hh.comp measurable_snd)).aemeasurable
      _ = ∫⁻ b, h b * ∫⁻ a, g (Matrix.of.symm (Matrix.of b * (Matrix.of a)⁻¹)) ∂μR ∂μR := by
          refine lintegral_congr fun b => ?_
          rw [lintegral_mul_const _ (hmb b), mul_comm]
      _ = ∫⁻ b, h b * ∫⁻ a, g (Matrix.of.symm (Matrix.of a)⁻¹) ∂μR ∂μR := by
          refine lintegral_congr_ae (hU.mono fun b hb => ?_)
          have hub := hUu _ hb
          have := hright _ hb _ (hmb b)
          have e : ∀ a : Fin n → Fin n → ℂ,
              Matrix.of.symm (Matrix.of b * (Matrix.of (Matrix.of.symm (Matrix.of a * Matrix.of b)))⁻¹)
                = Matrix.of.symm (Matrix.of a)⁻¹ := by
            intro a
            rw [Equiv.apply_symm_apply, Matrix.mul_inv_rev, Matrix.mul_nonsing_inv_cancel_left _ _ hub]
          simp only [e] at this
          dsimp only
          rw [this]
      _ = (∫⁻ b, h b ∂μR) * ∫⁻ a, g (Matrix.of.symm (Matrix.of a)⁻¹) ∂μR := lintegral_mul_const _ hh
  obtain ⟨g0, hg0pos, hg0m, hg0lt⟩ := exists_pos_lintegral_lt_of_sigmaFinite μR (ε := 1) one_ne_zero
  have hg0m' : Measurable fun a => (g0 a : ENNReal) := hg0m.coe_nnreal_ennreal
  have htop : (∫⁻ a, (g0 a : ENNReal) ∂μR) ≠ ⊤ := (hg0lt.trans ENNReal.one_lt_top).ne
  have hz : (∫⁻ a, (g0 a : ENNReal) ∂μR) ≠ 0 := by
    intro h0
    rw [lintegral_eq_zero_iff hg0m'] at h0
    have hf : ∀ᵐ a ∂μR, False := h0.mono fun a ha => by
      simp only [Pi.zero_apply, ENNReal.coe_eq_zero] at ha
      exact (hg0pos a).ne' ha
    exact hne (ae_eq_bot.mp (Filter.eventually_false_iff_eq_bot.mp hf))
  have K := key u hu _ hg0m'
  rw [mul_comm] at K
  exact ((ENNReal.mul_right_inj hz htop).mp K).symm

/- English proof (translation)
Establish `hRs : ∀ a ∈ C6.Rset x, IsUnit a.det` using `fun a ha => WeylGroupFacts.isUnit_of_uh ha.1.1`. Establish `: IsFiniteMeasureOnCompacts μR` using `⟨fun K hK => hR.finite_compact K hK⟩`. Establish `: SigmaFinite μR` using `inferInstance`. Establish `hU : ∀ᵐ a ∂μR, Matrix.of a ∈ C6.Rset x` using `ae_iff.mpr (by exact hR.conc)`. Establish `hact` using `measurable_actR_of x`.

Establish `hleft : ∀ a ∈ C6.Rset x, ∀ h : Mt k r → ENNReal, Measurable h → ∫⁻ b, h (Matrix.of.symm (a * Matrix.of b)) ∂μR = ∫⁻ b, h b ∂μR`. Introduce `a ha h hh`. Establish `hm : Measurable (fun c : Mt k r => (Matrix.of.symm (a * Matrix.of c) : Mt k r))` using `measurable_of_symm_mul (F := fun _ : Mt k r => a) (G := fun c : Mt k r => Matrix.of c) measurable_const measurable_id`. Establish `e : μR.map (fun c : Mt k r => (Matrix.of.symm (a * Matrix.of c) : Mt k r)) = μR` using `hR.left a ha`. Combine the equalities or inequalities in the displayed calculation.

Establish `hright : ∀ a ∈ C6.Rset x, ∀ h : Mt k r → ENNReal, Measurable h → ∫⁻ b, h (Matrix.of.symm (Matrix.of b * a)) ∂μR = ∫⁻ b, h b ∂μR`. Introduce `a ha h hh`. Establish `hm : Measurable (fun c : Mt k r => (Matrix.of.symm (Matrix.of c * a) : Mt k r))` using `measurable_of_symm_mul (F := fun c : Mt k r => Matrix.of c) (G := fun _ : Mt k r => a) measurable_id measurable_const`. Establish `e : μR.map (fun c : Mt k r => (Matrix.of.symm (Matrix.of c * a) : Mt k r)) = μR` using `hR.right a ha`. Combine the equalities or inequalities in the displayed calculation.

Establish `hF : Measurable fun p => ∫⁻ a, f (C6.actR x (Matrix.of a) p) ∂μR` using `(hf.comp (hact.comp measurable_swap)).lintegral_prod_right'`. Establish `hfa : ∀ p : B.SS k r, Measurable fun a : Mt k r => f (C6.actR x (Matrix.of a) p)` using `fun p => hf.comp (hact.comp (measurable_id.prodMk (measurable_const : Measurable fun _ : Mt k r => p)))`. Establish `hΘa : ∀ p : B.SS k r, Measurable fun a : Mt k r => Θ (C6.actR x (Matrix.of a) p)` using `fun p => hΘ.comp (hact.comp (measurable_id.prodMk (measurable_const : Measurable fun _ : Mt k r => p)))`. Establish `hΘi : ∀ p : B.SS k r, Measurable fun a : Mt k r => Θ (C6.actR x (Matrix.of a)⁻¹ p)` using `fun p => hΘ.comp (hact.comp (measurable_inv_apply_of_measurable_entries.prodMk (measurable_const : Measurable fun _ : Mt k r => p)))`. Rewrite using `[lintegral_withDensity_eq_lintegral_mul _ hΘ hF]`.

Use `symm`. Combine the equalities or inequalities in the displayed calculation. Use `lintegral_congr fun p => ?_` and prove the remaining obligations. Rewrite using `[Pi.mul_apply, lintegral_const_mul _ (hfa p)]`. Use `_ = ∫⁻ a, ∫⁻ p, Θ p * f (C6.actR x (Matrix.of a) p) ∂μ ∂μR := by`.

Use `lintegral_lintegral_swap ?_` and prove the remaining obligations. Conclude with `((hΘ.comp measurable_fst).mul (hf.comp (hact.comp measurable_swap))).aemeasurable`. Use `_ = ∫⁻ a, ∫⁻ p, Θ (C6.actR x (Matrix.of a)⁻¹ p) * f p ∂μ ∂μR := by`. Use `lintegral_congr_ae (hU.mono fun a ha => ?_)` and prove the remaining obligations. Establish `hmp` using `hinvμ _ ha`.

Establish `hu` using `hRs _ ha`. Establish `G : Measurable fun p => Θ (C6.actR x (Matrix.of a)⁻¹ p) * f p` using `(hΘ.comp (hact.comp ((measurable_const : Measurable fun _ : B.SS k r => (Matrix.of.symm (Matrix.of a)⁻¹ : Mt k r)).prodMk measurable_id))).mul hf`. Use `Eq.trans ?_ (hmp.lintegral_comp G)` and prove the remaining obligations. Use `lintegral_congr fun p => ?_` and prove the remaining obligations. Simplify using `only [actR_inv_actR x hx _ hu]`.

Use `_ = ∫⁻ p, ∫⁻ a, Θ (C6.actR x (Matrix.of a)⁻¹ p) * f p ∂μR ∂μ := by`. Use `lintegral_lintegral_swap ?_` and prove the remaining obligations. Conclude with `((hΘ.comp (hact.comp ((measurable_inv_apply_of_measurable_entries.comp measurable_fst).prodMk measurable_snd))).mul (hf.comp measurable_snd)).aemeasurable`. Use `_ = ∫⁻ p, f p * ∫⁻ a, Θ (C6.actR x (Matrix.of a)⁻¹ p) ∂μR ∂μ := by`. Use `lintegral_congr fun p => ?_` and prove the remaining obligations.

Rewrite using `[lintegral_mul_const _ (hΘi p), mul_comm]`. Use `_ = ∫⁻ p, f p * ∫⁻ a, Θ (C6.actR x (Matrix.of a) p) ∂μR ∂μ := by`. Use `lintegral_congr fun p => ?_` and prove the remaining obligations. Use `lintegral_inv_eq_of_mul_invariant (C6.Rset x) μR hR.ne_zero hU hRs hleft hright _ (hΘa p)` as an intermediate fact. Conclude with `congrArg (f p * ·) this`.

Use `_ = ∫⁻ p, f p ∂μ := lintegral_congr_ae (h1.mono fun p hp => by dsimp only; rw [hp, mul_one])`.
-/
theorem weil {k r : ℕ} (x : B.Mat k r) (hx : IsUnit x.det) (μR : Measure (Mt k r))
    (hR : B.IsHaarOn (C6.Rset x) μR) (μ : Measure (B.SS k r)) [SFinite μ]
    (hinvμ : ∀ a ∈ C6.Rset x, MeasurePreserving (C6.actR x a) μ μ)
    (Θ : B.SS k r → ENNReal) (hΘ : Measurable Θ)
    (h1 : ∀ᵐ p ∂μ, ∫⁻ a, Θ (C6.actR x (Matrix.of a) p) ∂μR = 1)
    (f : B.SS k r → ENNReal) (hf : Measurable f) :
    ∫⁻ p, f p ∂μ = ∫⁻ p, (∫⁻ a, f (C6.actR x (Matrix.of a) p) ∂μR) ∂(μ.withDensity Θ) := by
  have hRs : ∀ a ∈ C6.Rset x, IsUnit a.det := fun a ha => WeylGroupFacts.isUnit_of_uh ha.1.1
  have : IsFiniteMeasureOnCompacts μR := ⟨fun K hK => hR.finite_compact K hK⟩
  have : SigmaFinite μR := inferInstance
  have hU : ∀ᵐ a ∂μR, Matrix.of a ∈ C6.Rset x := ae_iff.mpr (by exact hR.conc)
  have hact := measurable_actR_of x
  have hleft : ∀ a ∈ C6.Rset x, ∀ h : Mt k r → ENNReal, Measurable h →
      ∫⁻ b, h (Matrix.of.symm (a * Matrix.of b)) ∂μR = ∫⁻ b, h b ∂μR := by
    intro a ha h hh
    have hm : Measurable (fun c : Mt k r => (Matrix.of.symm (a * Matrix.of c) : Mt k r)) :=
      measurable_of_symm_mul (F := fun _ : Mt k r => a) (G := fun c : Mt k r => Matrix.of c) measurable_const measurable_id
    have e : μR.map (fun c : Mt k r => (Matrix.of.symm (a * Matrix.of c) : Mt k r)) = μR := hR.left a ha
    calc ∫⁻ b, h (Matrix.of.symm (a * Matrix.of b)) ∂μR
        = ∫⁻ b, h b ∂(μR.map (fun c : Mt k r => (Matrix.of.symm (a * Matrix.of c) : Mt k r))) :=
          (lintegral_map hh hm).symm
      _ = ∫⁻ b, h b ∂μR := by rw [e]
  have hright : ∀ a ∈ C6.Rset x, ∀ h : Mt k r → ENNReal, Measurable h →
      ∫⁻ b, h (Matrix.of.symm (Matrix.of b * a)) ∂μR = ∫⁻ b, h b ∂μR := by
    intro a ha h hh
    have hm : Measurable (fun c : Mt k r => (Matrix.of.symm (Matrix.of c * a) : Mt k r)) :=
      measurable_of_symm_mul (F := fun c : Mt k r => Matrix.of c) (G := fun _ : Mt k r => a) measurable_id measurable_const
    have e : μR.map (fun c : Mt k r => (Matrix.of.symm (Matrix.of c * a) : Mt k r)) = μR := hR.right a ha
    calc ∫⁻ b, h (Matrix.of.symm (Matrix.of b * a)) ∂μR
        = ∫⁻ b, h b ∂(μR.map (fun c : Mt k r => (Matrix.of.symm (Matrix.of c * a) : Mt k r))) :=
          (lintegral_map hh hm).symm
      _ = ∫⁻ b, h b ∂μR := by rw [e]
  have hF : Measurable fun p => ∫⁻ a, f (C6.actR x (Matrix.of a) p) ∂μR :=
    (hf.comp (hact.comp measurable_swap)).lintegral_prod_right'
  have hfa : ∀ p : B.SS k r, Measurable fun a : Mt k r => f (C6.actR x (Matrix.of a) p) :=
    fun p => hf.comp (hact.comp (measurable_id.prodMk (measurable_const : Measurable fun _ : Mt k r => p)))
  have hΘa : ∀ p : B.SS k r, Measurable fun a : Mt k r => Θ (C6.actR x (Matrix.of a) p) :=
    fun p => hΘ.comp (hact.comp (measurable_id.prodMk (measurable_const : Measurable fun _ : Mt k r => p)))
  have hΘi : ∀ p : B.SS k r, Measurable fun a : Mt k r => Θ (C6.actR x (Matrix.of a)⁻¹ p) :=
    fun p => hΘ.comp (hact.comp (measurable_inv_apply_of_measurable_entries.prodMk (measurable_const : Measurable fun _ : Mt k r => p)))
  rw [lintegral_withDensity_eq_lintegral_mul _ hΘ hF]
  symm
  calc ∫⁻ p, (Θ * fun p => ∫⁻ a, f (C6.actR x (Matrix.of a) p) ∂μR) p ∂μ
      = ∫⁻ p, ∫⁻ a, Θ p * f (C6.actR x (Matrix.of a) p) ∂μR ∂μ := by
        refine lintegral_congr fun p => ?_
        rw [Pi.mul_apply, lintegral_const_mul _ (hfa p)]
    _ = ∫⁻ a, ∫⁻ p, Θ p * f (C6.actR x (Matrix.of a) p) ∂μ ∂μR := by
        refine lintegral_lintegral_swap ?_
        exact ((hΘ.comp measurable_fst).mul (hf.comp (hact.comp measurable_swap))).aemeasurable
    _ = ∫⁻ a, ∫⁻ p, Θ (C6.actR x (Matrix.of a)⁻¹ p) * f p ∂μ ∂μR := by
        refine lintegral_congr_ae (hU.mono fun a ha => ?_)
        have hmp := hinvμ _ ha
        have hu := hRs _ ha
        have G : Measurable fun p => Θ (C6.actR x (Matrix.of a)⁻¹ p) * f p :=
          (hΘ.comp (hact.comp ((measurable_const : Measurable fun _ : B.SS k r =>
            (Matrix.of.symm (Matrix.of a)⁻¹ : Mt k r)).prodMk measurable_id))).mul hf
        refine Eq.trans ?_ (hmp.lintegral_comp G)
        refine lintegral_congr fun p => ?_
        simp only [actR_inv_actR x hx _ hu]
    _ = ∫⁻ p, ∫⁻ a, Θ (C6.actR x (Matrix.of a)⁻¹ p) * f p ∂μR ∂μ := by
        refine lintegral_lintegral_swap ?_
        exact ((hΘ.comp (hact.comp ((measurable_inv_apply_of_measurable_entries.comp measurable_fst).prodMk measurable_snd))).mul
          (hf.comp measurable_snd)).aemeasurable
    _ = ∫⁻ p, f p * ∫⁻ a, Θ (C6.actR x (Matrix.of a)⁻¹ p) ∂μR ∂μ := by
        refine lintegral_congr fun p => ?_
        rw [lintegral_mul_const _ (hΘi p), mul_comm]
    _ = ∫⁻ p, f p * ∫⁻ a, Θ (C6.actR x (Matrix.of a) p) ∂μR ∂μ := by
        refine lintegral_congr fun p => ?_
        have := lintegral_inv_eq_of_mul_invariant (C6.Rset x) μR hR.ne_zero hU hRs hleft hright _ (hΘa p)
        exact congrArg (f p * ·) this
    _ = ∫⁻ p, f p ∂μ := lintegral_congr_ae (h1.mono fun p hp => by dsimp only; rw [hp, mul_one])

/- English proof (translation)
Introduce `k r L x μR θ cN hcN hκ hx hR hθ hθ0 h1`. Establish `hxu : IsUnit x.det` using `WeylGroupFacts.isUnit_of_uh hx`. Establish `hH : B.IsHaarOn (Nset k r) (Formalism.FourierDecayAlt.D.muN k r)` using `P.Dx2.MN.haar r`. Establish `: IsFiniteMeasureOnCompacts (Formalism.FourierDecayAlt.D.muN k r)` using `⟨fun K hK => hH.finite_compact K hK⟩`. Establish `: SigmaFinite (Formalism.FourierDecayAlt.D.muN k r)` using `inferInstance`.

Establish `hμN : L.μN = (L.κN * ENNReal.ofReal cN) • Formalism.FourierDecayAlt.D.muN k r`. Establish `e1 : Formalism.MainNotions.S.haarLie (Nset k r) L.κN = L.κN • Formalism.MainNotions.S.haarLie (Nset k r) 1`. Unfold `Formalism.MainNotions.S.haarLie`. Rewrite using `[one_smul]`. Use `show Formalism.MainNotions.S.haarLie (Nset k r) L.κN = _`.

Rewrite using `[e1, hcN.2, smul_smul]`. Establish `: SFinite L.μN` using `by rw [hμN]; infer_instance`. Establish `: SigmaFinite L.μW` using `L.hμW.1.1`. Establish `: SigmaFinite L.μW'` using `L.hμW'.1.1`. Establish `: SFinite (pairMeas L)` using `by unfold pairMeas; infer_instance`.

Establish `hN : ∀ b ∈ Nset k r, MeasurePreserving (fun c : Mt k r => (Matrix.of.symm (b * Matrix.of c) : Mt k r)) L.μN L.μN`. Introduce `b hb`. Establish `hc : Continuous (fun c : Mt k r => Matrix.of c)` using `continuous_id`. Establish `hbc : Continuous (fun _ : Mt k r => b)` using `continuous_const`. Use `⟨(continuous_pi fun i => continuous_pi fun j => (hbc.matrix_mul hc).matrix_elem i j).measurable, ?_⟩` and prove the remaining obligations.

Rewrite using `[hμN, Measure.map_smul]`. Use `congr 1`. Conclude with `hH.left b hb`. Establish `hinv : ∀ a ∈ C6.Rset x, MeasurePreserving (C6.actR x a) (pairMeas L) (pairMeas L)`. Introduce `a ha`.

Establish `e : C6.actR x a = Prod.map (Prod.map id (fun c : Mt k r => (Matrix.of.symm (a * Matrix.of c) : Mt k r))) (Prod.map id (fun c : Mt k r => (Matrix.of.symm (x⁻¹ * a * x * Matrix.of c) : Mt k r)))` using `rfl`. Rewrite using `[e]`. Conclude with `((MeasurePreserving.id L.μW).prod (hN a ha.1)).prod ((MeasurePreserving.id L.μW').prod (hN _ ha.2))`. Establish `aW : ∀ᵐ h ∂L.μW, Matrix.of h ∈ UWset k r L.z` using `ae_iff.mpr L.hμW.1.2.2.1`. Establish `aW' : ∀ᵐ h ∂L.μW', Matrix.of h ∈ UWset k r L.z'` using `ae_iff.mpr L.hμW'.1.2.2.1`.

Establish `aN : ∀ᵐ n ∂L.μN, Matrix.of n ∈ Nset k r`. Use `ae_iff.mpr ?_` and prove the remaining obligations. Rewrite using `[hμN, Measure.smul_apply, smul_eq_mul]`. Conclude with `mul_eq_zero_of_right _ hH.conc`. Establish `aP : ∀ᵐ p ∂pairMeas L, (Matrix.of p.1.1 ∈ UWset k r L.z ∧ Matrix.of p.1.2 ∈ Nset k r) ∧ (Matrix.of p.2.1 ∈ UWset k r L.z' ∧ Matrix.of p.2.2 ∈ Nset k r)` using `by show ∀ᵐ p ∂((L.μW.prod L.μN).prod (L.μW'.prod L.μN)), _`.

Establish `q1 : ∀ᵐ z ∂(L.μW.prod L.μN), Matrix.of z.1 ∈ UWset k r L.z ∧ Matrix.of z.2 ∈ Nset k r` using `(Measure.quasiMeasurePreserving_fst.ae aW).and (Measure.quasiMeasurePreserving_snd.ae aN)`. Establish `q2 : ∀ᵐ z ∂(L.μW'.prod L.μN), Matrix.of z.1 ∈ UWset k r L.z' ∧ Matrix.of z.2 ∈ Nset k r` using `(Measure.quasiMeasurePreserving_fst.ae aW').and (Measure.quasiMeasurePreserving_snd.ae aN)`. Conclude with `(Measure.quasiMeasurePreserving_fst.ae q1).and (Measure.quasiMeasurePreserving_snd.ae q2)`. Establish `h1' : ∀ᵐ p ∂pairMeas L, ∫⁻ a, ENNReal.ofReal (θ (C6.actR x (Matrix.of a) p)) ∂μR = 1`. Use `aP.mono fun p hp => ?_` and prove the remaining obligations.

Establish `hI` using `h1 p hp.1.2 hp.2.2 hp.1.1 hp.2.1`. Establish `hint : Integrable (fun a : Mt k r => θ (stabAct x (Matrix.of a) p)) μR`. Assume the negation of the conclusion as `hni`. Rewrite `hI` using `[integral_undef hni]`. Conclude with `zero_ne_one hI`.

Use `ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun a => hθ0 _)` as an intermediate fact. Rewrite `this` using `[hI, ENNReal.ofReal_one]`. Conclude with `this.symm`. Unfold `IsOrbQuot`. Introduce `f hf`.

Conclude with `weil x hxu μR hR (pairMeas L) hinv (fun p => ENNReal.ofReal (θ p)) (ENNReal.measurable_ofReal.comp hθ) h1' f hf`.
-/
theorem isOrbQuot_withDensity : ∀ (k r : ℕ) (L : LocBessel k r) (x : B.Mat k r) (μR : Measure (Mt k r)) (θ : PairSp k r → ℝ) (cN : ℝ), IsRatioN k r cN → L.κN ≠ ⊤ → x ∈ B.GV k r → B.IsHaarOn (RStab k r x) μR → Measurable θ → (∀ p, 0 ≤ θ p) → (∀ p : PairSp k r, Matrix.of p.1.2 ∈ Nset k r → Matrix.of p.2.2 ∈ Nset k r → Matrix.of p.1.1 ∈ UWset k r L.z → Matrix.of p.2.1 ∈ UWset k r L.z' → ∫ a, θ (stabAct x (Matrix.of a) p) ∂μR = 1) → IsOrbQuot L x μR ((pairMeas L).withDensity fun p => ENNReal.ofReal (θ p)) := by
  intro k r L x μR θ cN hcN hκ hx hR hθ hθ0 h1
  have hxu : IsUnit x.det := WeylGroupFacts.isUnit_of_uh hx
  have hH : B.IsHaarOn (Nset k r) (Formalism.FourierDecayAlt.D.muN k r) := P.Dx2.MN.haar r
  have : IsFiniteMeasureOnCompacts (Formalism.FourierDecayAlt.D.muN k r) := ⟨fun K hK => hH.finite_compact K hK⟩
  have : SigmaFinite (Formalism.FourierDecayAlt.D.muN k r) := inferInstance
  have hμN : L.μN = (L.κN * ENNReal.ofReal cN) • Formalism.FourierDecayAlt.D.muN k r := by
    have e1 : Formalism.MainNotions.S.haarLie (Nset k r) L.κN = L.κN • Formalism.MainNotions.S.haarLie (Nset k r) 1 := by
      unfold Formalism.MainNotions.S.haarLie
      rw [one_smul]
    show Formalism.MainNotions.S.haarLie (Nset k r) L.κN = _
    rw [e1, hcN.2, smul_smul]
  have : SFinite L.μN := by rw [hμN]; infer_instance
  have : SigmaFinite L.μW := L.hμW.1.1
  have : SigmaFinite L.μW' := L.hμW'.1.1
  have : SFinite (pairMeas L) := by unfold pairMeas; infer_instance
  have hN : ∀ b ∈ Nset k r, MeasurePreserving (fun c : Mt k r => (Matrix.of.symm (b * Matrix.of c) : Mt k r))
      L.μN L.μN := by
    intro b hb
    have hc : Continuous (fun c : Mt k r => Matrix.of c) := continuous_id
    have hbc : Continuous (fun _ : Mt k r => b) := continuous_const
    refine ⟨(continuous_pi fun i => continuous_pi fun j => (hbc.matrix_mul hc).matrix_elem i j).measurable, ?_⟩
    rw [hμN, Measure.map_smul]
    congr 1
    exact hH.left b hb
  have hinv : ∀ a ∈ C6.Rset x, MeasurePreserving (C6.actR x a) (pairMeas L) (pairMeas L) := by
    intro a ha
    have e : C6.actR x a = Prod.map (Prod.map id (fun c : Mt k r => (Matrix.of.symm (a * Matrix.of c) : Mt k r)))
        (Prod.map id (fun c : Mt k r => (Matrix.of.symm (x⁻¹ * a * x * Matrix.of c) : Mt k r))) := rfl
    rw [e]
    exact ((MeasurePreserving.id L.μW).prod (hN a ha.1)).prod ((MeasurePreserving.id L.μW').prod (hN _ ha.2))
  have aW : ∀ᵐ h ∂L.μW, Matrix.of h ∈ UWset k r L.z := ae_iff.mpr L.hμW.1.2.2.1
  have aW' : ∀ᵐ h ∂L.μW', Matrix.of h ∈ UWset k r L.z' := ae_iff.mpr L.hμW'.1.2.2.1
  have aN : ∀ᵐ n ∂L.μN, Matrix.of n ∈ Nset k r := by
    refine ae_iff.mpr ?_
    rw [hμN, Measure.smul_apply, smul_eq_mul]
    exact mul_eq_zero_of_right _ hH.conc
  have aP : ∀ᵐ p ∂pairMeas L, (Matrix.of p.1.1 ∈ UWset k r L.z ∧ Matrix.of p.1.2 ∈ Nset k r) ∧
      (Matrix.of p.2.1 ∈ UWset k r L.z' ∧ Matrix.of p.2.2 ∈ Nset k r) := by
    show ∀ᵐ p ∂((L.μW.prod L.μN).prod (L.μW'.prod L.μN)), _
    have q1 : ∀ᵐ z ∂(L.μW.prod L.μN), Matrix.of z.1 ∈ UWset k r L.z ∧ Matrix.of z.2 ∈ Nset k r :=
      (Measure.quasiMeasurePreserving_fst.ae aW).and (Measure.quasiMeasurePreserving_snd.ae aN)
    have q2 : ∀ᵐ z ∂(L.μW'.prod L.μN), Matrix.of z.1 ∈ UWset k r L.z' ∧ Matrix.of z.2 ∈ Nset k r :=
      (Measure.quasiMeasurePreserving_fst.ae aW').and (Measure.quasiMeasurePreserving_snd.ae aN)
    exact (Measure.quasiMeasurePreserving_fst.ae q1).and (Measure.quasiMeasurePreserving_snd.ae q2)
  have h1' : ∀ᵐ p ∂pairMeas L, ∫⁻ a, ENNReal.ofReal (θ (C6.actR x (Matrix.of a) p)) ∂μR = 1 := by
    refine aP.mono fun p hp => ?_
    have hI := h1 p hp.1.2 hp.2.2 hp.1.1 hp.2.1
    have hint : Integrable (fun a : Mt k r => θ (stabAct x (Matrix.of a) p)) μR := by
      by_contra hni
      rw [integral_undef hni] at hI
      exact zero_ne_one hI
    have := ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun a => hθ0 _)
    rw [hI, ENNReal.ofReal_one] at this
    exact this.symm
  unfold IsOrbQuot
  intro f hf
  exact weil x hxu μR hR (pairMeas L) hinv (fun p => ENNReal.ofReal (θ p)) (ENNReal.measurable_ofReal.comp hθ)
    h1' f hf

end GlobalTheory.ThA.QuotCut
