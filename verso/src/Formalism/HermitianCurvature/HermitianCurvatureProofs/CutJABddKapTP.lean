import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddKap
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnRepCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnGeomAtGq

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField PI.UnitaryGroupMassFormula.GsFr
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def kcut (t : ℝ) : ℝ := Real.smoothTransition (6 * t - 2)

/- English proof (translation)
The claim follows from `Real.smoothTransition.contDiff.comp (by fun_prop)`.
-/
theorem kcut_contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) kcut :=
  Real.smoothTransition.contDiff.comp (by fun_prop)

/- English proof (translation)
The claim follows from `Real.smoothTransition.zero_of_nonpos (by linarith)`.
-/
theorem kcut_zero {t : ℝ} (ht : t ≤ 1 / 3) : kcut t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

/- English proof (translation)
The claim follows from `Real.smoothTransition.one_of_one_le (by linarith)`.
-/
theorem kcut_one {t : ℝ} (ht : 1 / 2 ≤ t) : kcut t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

def NrmWFacts : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), inWb k r z → 0 < Tz k r z →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun a => PRho.nrmW k r z a) ∧
    ∀ h ∈ UWset k r z, ∀ a, PRho.nrmW k r z (h *ᵥ a) = PRho.nrmW k r z a

/- English proof (translation)
Unfold `PRho.nrmW`. Rewrite using `[SSn.Geom.prWv_eq, SSn.Geom.prW_smul, ← SSn.Geom.prWv_eq]`. Rewrite using `[hm_smul_l, hm_smul_r, ← mul_assoc, Complex.star_def, Complex.mul_conj, Complex.re_ofReal_mul]`.
-/
theorem nrmW_smul {k r : ℕ} (z a : Fin (2 * r + k + 1) → ℂ) (c : ℂ) :
    PRho.nrmW k r z (c • a) = Complex.normSq c * PRho.nrmW k r z a := by
  unfold PRho.nrmW
  rw [SSn.Geom.prWv_eq, SSn.Geom.prW_smul, ← SSn.Geom.prWv_eq]
  rw [hm_smul_l, hm_smul_r, ← mul_assoc, Complex.star_def, Complex.mul_conj, Complex.re_ofReal_mul]

section lm

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def lmul (A : Wp →L[ℂ] Wp) : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp) := ContinuousLinearMap.compL ℂ Wq Wp Wp A

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem lmul_apply (A : Wp →L[ℂ] Wp) (X : Wq →L[ℂ] Wp) : lmul A X = A.comp X := rfl

/- English proof (translation)
Simplify using `only [B.hsInner, B.hsVec, lmul_apply, PiLp.inner_apply, ContinuousLinearMap.comp_apply]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hA]`.
-/
theorem hsInner_lmul (A : Wp →L[ℂ] Wp) (hA : ∀ x y, inner ℂ (A x) y = inner ℂ x (A y)) (X Y : Wq →L[ℂ] Wp) :
    B.hsInner (lmul A X) Y = B.hsInner X (lmul A Y) := by
  simp only [B.hsInner, B.hsVec, lmul_apply, PiLp.inner_apply, ContinuousLinearMap.comp_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hA]

end lm

/- English proof (translation)
Use `⟨0, le_rfl, ?_⟩` and prove the remaining obligations. Introduce `Cc _ E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e hFr hGa hQQ`. Establish `hPl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π'` using `(hB.1.2.2.2.1.2 v).2.2.2.1`. Distinguish the cases in `hk : 2 ≤ S.G.k`. Take `⟨Pr, hs, heqv, hrest⟩` from `hPE (Wp (S.pl v)) (Wq (S.pl v)) (D.parOf S v) (T v).base hPl hk`.

Take `⟨hnc, hninv⟩` from `hNW S.G.k S.G.r (T v).base.z (T v).base.z_mem (T v).base.T_pos`. Use `⟨fun σ a => ((kcut (PRho.nrmW S.G.k S.G.r (T v).base.z a) : ℝ) : ℂ) • lmul (Pr σ a), ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `σ`. Rewrite using `[contDiff_iff_contDiffAt]`. Introduce `a₀`.

Distinguish the cases in `h : 1 / 4 < PRho.nrmW S.G.k S.G.r (T v).base.z a₀`. Establish `hO : IsOpen {a | 1 / 4 < PRho.nrmW S.G.k S.G.r (T v).base.z a}` using `isOpen_lt continuous_const hnc.continuous`. Establish `hl : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun A : Wp (S.pl v) →L[ℂ] Wp (S.pl v) => (lmul A : (Wq (S.pl v) →L[ℂ] Wp (S.pl v)) →L[ℂ] _))` using `(ContinuousLinearMap.compL ℂ (Wq (S.pl v)) (Wp (S.pl v)) (Wp (S.pl v))).contDiff.restrict_scalars ℝ`. Establish `h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun a => ((kcut (PRho.nrmW S.G.k S.G.r (T v).base.z a) : ℝ) : ℂ) • lmul (Pr σ a)) {a | 1 / 4 < PRho.nrmW S.G.k S.G.r (T v).base.z a}` using `((Complex.ofRealCLM.contDiff.comp (kcut_contDiff.comp hnc)).contDiffOn).smul (hl.comp_contDiffOn (hs σ))`. Conclude with `h1.contDiffAt (hO.mem_nhds h)`.

Establish `hO : IsOpen {a | PRho.nrmW S.G.k S.G.r (T v).base.z a < 1 / 3}` using `isOpen_lt hnc.continuous continuous_const`. Establish `hmem : a₀ ∈ {a | PRho.nrmW S.G.k S.G.r (T v).base.z a < 1 / 3}`. Simplify using `only [Set.mem_setOf_eq]`. Combine the linear relations using `[not_lt.1 h]`. Use `(contDiffAt_const (c := (0 : (Wq (S.pl v) →L[ℂ] Wp (S.pl v)) →L[ℂ] (Wq (S.pl v) →L[ℂ] Wp (S.pl v))))).congr_of_eventuallyEq ?_` and prove the remaining obligations.

Use `filter_upwards [hO.mem_nhds hmem] with a ha`. Simplify using `[kcut_zero (le_of_lt ha)]`. Introduce `σ a A B'`. Simplify using `only`. Distinguish the cases in `h : 0 < PRho.nrmW S.G.k S.G.r (T v).base.z a`.

Rewrite using `[ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, kap_hsInner_smul_left, kap_hsInner_smul_right, Complex.conj_ofReal, hsInner_lmul _ ((hrest a h).2.1 σ)]`. Establish `h0 : kcut (PRho.nrmW S.G.k S.G.r (T v).base.z a) = 0` using `kcut_zero (by linarith [not_lt.1 h])`. Simplify using `[h0, B.hsInner, kap_hsVec_zero]`. Introduce `σ h hh h' hh' a X`. Establish `hinv : h⁻¹ ∈ UWset S.G.k S.G.r (T v).base.z` using `Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv hh`.

Establish `hu` using `WeylGroupFacts.isUnit_of_uh hh.1`. Establish `hh1 : h⁻¹ * h = 1` using `by first`. Consider the case `exact Matrix.nonsing_inv_mul _ hu`. Consider the case `exact Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hu)`. Establish `key : ∀ y, (T v).base.π h⁻¹ ((T v).base.π h y) = y`.

Introduce `y`. Rewrite using `[← ContinuousLinearMap.comp_apply, ← (T v).base.π_rep.2 _ hinv _ hh, hh1, (T v).base.π_rep.1]`. Both sides reduce to the same expression. Simplify using `only`. Rewrite using `[hninv h hh a, heqv h hh σ a]`.

Use extensionality with `y`. Simplify using `[lmul_apply, key]`. Introduce `x hx σ ρ`. Simplify using `only`. Take `⟨hP1, hH1, -, -⟩` from `hDU Cc E Wp Wq S T f χ ν' m₀ top A₀ hB v x.2 hx.2`.

Use `set n0 := SSn.nu0 S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec x.2 with hn0`. Establish `hN0 : PRho.nrmW S.G.k S.G.r (T v).base.z n0 = 1`. Unfold `PRho.nrmW`. Rewrite using `[hP1, hH1]`. Simplify using the standard rewrite rules.

Establish `hph : SSn.phD x.1 ≠ 0`. Introduce `h0`. Use `SSn.Geom.phD_norm hx.1` as an intermediate fact. Rewrite `this` using `[h0, norm_zero]`. Conclude with `zero_ne_one this`.

Establish `hN : PRho.nrmW S.G.k S.G.r (T v).base.z (SSn.phD x.1 • n0) = 1`. Rewrite using `[nrmW_smul, hN0, mul_one, Complex.normSq_eq_norm_sq, SSn.Geom.phD_norm hx.1]`. Evaluate the numerical expressions. Establish `hscale : ∀ τ, Pr τ (SSn.phD x.1 • n0) = Pr τ n0` using `fun τ => (hrest n0 (by rw [hN0]; norm_num)).1 τ _ hph`. Establish `hfix : ∀ y, Pr ρ n0 (e ρ x.2 y) = e ρ x.2 y`.

Introduce `y`. Use `((hrest n0 (by rw [hN0]; norm_num)).2.2.2 ρ (e ρ x.2 y)).2 ?_` and prove the remaining obligations. Introduce `Fr hFrm w`. Rewrite `hFrm` using `[hP1]`. Conclude with `hGL Cc E Wp Wq S T f χ ν' m₀ top A₀ v e ⟨hB, hFr, hGa, hQQ⟩ hk x.2 hx.2 ρ Fr hFrm w y`.

Rewrite using `[ContinuousLinearMap.smul_apply, hN, kcut_one (by norm_num), lmul_apply, hscale]`. Simplify using `only [Complex.ofReal_one, one_smul]`. Distinguish the cases in `hσ : σ = ρ`. Substitute `hσ` using the available equality. Rewrite using `[if_pos rfl]`.

Use extensionality with `y`. Conclude with `hfix y`. Rewrite using `[if_neg hσ]`. Use extensionality with `y`. Establish `horth` using `(hrest n0 (by rw [hN0]; norm_num)).2.2.1 σ ρ`.

Rewrite `horth` using `[if_neg hσ]`. Rewrite using `[ContinuousLinearMap.comp_apply, ← hfix y, ← ContinuousLinearMap.comp_apply (Pr σ n0), horth]`. Both sides reduce to the same expression. Establish `hk1 : (D.parOf S v).k - 1 = 0`. Establish `: (D.parOf S v).k = S.G.k` using `rfl`.

Use linear arithmetic over natural numbers and integers. Establish `hsub : ∀ σ ρ : M.Ty (D.parOf S v), σ = ρ`. Introduce `σ ρ`. Use function extensionality and compare the values at `i`. Conclude with `absurd i.2 (by omega)`.

Use `⟨fun _ _ => ContinuousLinearMap.id ℂ _, fun σ => contDiff_const, fun σ a A B' => rfl, fun σ h _ h' _ a X => rfl, ?_⟩` and prove the remaining obligations. Introduce `x _ σ ρ`. Rewrite using `[if_pos (hsub σ ρ)]`. Both sides reduce to the same expression.
-/
theorem typeProj_of (hPE : PRho.PRhoExists) (hGL : PRho.GaugeLines) (hDU : SSn.Rep.DatumUnit)
    (hNW : NrmWFacts) : TypeProj := by
  refine ⟨0, le_rfl, ?_⟩
  intro Cc _ E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e hFr hGa hQQ
  have hPl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hB.1.2.2.2.1.2 v).2.2.2.1
  by_cases hk : 2 ≤ S.G.k
  · obtain ⟨Pr, hs, heqv, hrest⟩ := hPE (Wp (S.pl v)) (Wq (S.pl v)) (D.parOf S v) (T v).base hPl hk
    obtain ⟨hnc, hninv⟩ := hNW S.G.k S.G.r (T v).base.z (T v).base.z_mem (T v).base.T_pos
    refine ⟨fun σ a => ((kcut (PRho.nrmW S.G.k S.G.r (T v).base.z a) : ℝ) : ℂ) • lmul (Pr σ a), ?_, ?_, ?_, ?_⟩
    ·
      intro σ
      rw [contDiff_iff_contDiffAt]
      intro a₀
      by_cases h : 1 / 4 < PRho.nrmW S.G.k S.G.r (T v).base.z a₀
      · have hO : IsOpen {a | 1 / 4 < PRho.nrmW S.G.k S.G.r (T v).base.z a} :=
          isOpen_lt continuous_const hnc.continuous
        have hl : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
            (fun A : Wp (S.pl v) →L[ℂ] Wp (S.pl v) => (lmul A : (Wq (S.pl v) →L[ℂ] Wp (S.pl v)) →L[ℂ] _)) :=
          (ContinuousLinearMap.compL ℂ (Wq (S.pl v)) (Wp (S.pl v)) (Wp (S.pl v))).contDiff.restrict_scalars ℝ
        have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
            (fun a => ((kcut (PRho.nrmW S.G.k S.G.r (T v).base.z a) : ℝ) : ℂ) • lmul (Pr σ a))
            {a | 1 / 4 < PRho.nrmW S.G.k S.G.r (T v).base.z a} :=
          ((Complex.ofRealCLM.contDiff.comp (kcut_contDiff.comp hnc)).contDiffOn).smul
            (hl.comp_contDiffOn (hs σ))
        exact h1.contDiffAt (hO.mem_nhds h)
      · have hO : IsOpen {a | PRho.nrmW S.G.k S.G.r (T v).base.z a < 1 / 3} :=
          isOpen_lt hnc.continuous continuous_const
        have hmem : a₀ ∈ {a | PRho.nrmW S.G.k S.G.r (T v).base.z a < 1 / 3} := by
          simp only [Set.mem_setOf_eq]; linarith [not_lt.1 h]
        refine (contDiffAt_const (c := (0 : (Wq (S.pl v) →L[ℂ] Wp (S.pl v)) →L[ℂ] (Wq (S.pl v) →L[ℂ] Wp (S.pl v))))).congr_of_eventuallyEq ?_
        filter_upwards [hO.mem_nhds hmem] with a ha
        simp [kcut_zero (le_of_lt ha)]
    ·
      intro σ a A B'
      dsimp only
      by_cases h : 0 < PRho.nrmW S.G.k S.G.r (T v).base.z a
      · rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, kap_hsInner_smul_left,
          kap_hsInner_smul_right, Complex.conj_ofReal, hsInner_lmul _ ((hrest a h).2.1 σ)]
      · have h0 : kcut (PRho.nrmW S.G.k S.G.r (T v).base.z a) = 0 := kcut_zero (by linarith [not_lt.1 h])
        simp [h0, B.hsInner, kap_hsVec_zero]
    ·
      intro σ h hh h' hh' a X
      have hinv : h⁻¹ ∈ UWset S.G.k S.G.r (T v).base.z := Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv hh
      have hu := WeylGroupFacts.isUnit_of_uh hh.1
      have hh1 : h⁻¹ * h = 1 := by
        first
          | exact Matrix.nonsing_inv_mul _ hu
          | exact Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hu)
      have key : ∀ y, (T v).base.π h⁻¹ ((T v).base.π h y) = y := by
        intro y
        rw [← ContinuousLinearMap.comp_apply, ← (T v).base.π_rep.2 _ hinv _ hh, hh1, (T v).base.π_rep.1]
        rfl
      dsimp only
      rw [hninv h hh a, heqv h hh σ a]
      ext y
      simp [lmul_apply, key]
    ·
      intro x hx σ ρ
      dsimp only
      obtain ⟨hP1, hH1, -, -⟩ := hDU Cc E Wp Wq S T f χ ν' m₀ top A₀ hB v x.2 hx.2
      set n0 := SSn.nu0 S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec x.2 with hn0
      have hN0 : PRho.nrmW S.G.k S.G.r (T v).base.z n0 = 1 := by
        unfold PRho.nrmW; rw [hP1, hH1]; simp
      have hph : SSn.phD x.1 ≠ 0 := by
        intro h0
        have := SSn.Geom.phD_norm hx.1
        rw [h0, norm_zero] at this
        exact zero_ne_one this
      have hN : PRho.nrmW S.G.k S.G.r (T v).base.z (SSn.phD x.1 • n0) = 1 := by
        rw [nrmW_smul, hN0, mul_one, Complex.normSq_eq_norm_sq, SSn.Geom.phD_norm hx.1]; norm_num
      have hscale : ∀ τ, Pr τ (SSn.phD x.1 • n0) = Pr τ n0 :=
        fun τ => (hrest n0 (by rw [hN0]; norm_num)).1 τ _ hph
      have hfix : ∀ y, Pr ρ n0 (e ρ x.2 y) = e ρ x.2 y := by
        intro y
        refine ((hrest n0 (by rw [hN0]; norm_num)).2.2.2 ρ (e ρ x.2 y)).2 ?_
        intro Fr hFrm w
        rw [hP1] at hFrm
        exact hGL Cc E Wp Wq S T f χ ν' m₀ top A₀ v e ⟨hB, hFr, hGa, hQQ⟩ hk x.2 hx.2 ρ Fr hFrm w y
      rw [ContinuousLinearMap.smul_apply, hN, kcut_one (by norm_num), lmul_apply, hscale]
      simp only [Complex.ofReal_one, one_smul]
      by_cases hσ : σ = ρ
      · subst hσ
        rw [if_pos rfl]
        ext y
        exact hfix y
      · rw [if_neg hσ]
        ext y
        have horth := (hrest n0 (by rw [hN0]; norm_num)).2.2.1 σ ρ
        rw [if_neg hσ] at horth
        rw [ContinuousLinearMap.comp_apply, ← hfix y, ← ContinuousLinearMap.comp_apply (Pr σ n0), horth]
        rfl
  ·
    have hk1 : (D.parOf S v).k - 1 = 0 := by
      have : (D.parOf S v).k = S.G.k := rfl
      omega
    have hsub : ∀ σ ρ : M.Ty (D.parOf S v), σ = ρ := by
      intro σ ρ
      funext i
      exact absurd i.2 (by omega)
    refine ⟨fun _ _ => ContinuousLinearMap.id ℂ _, fun σ => contDiff_const, fun σ a A B' => rfl,
      fun σ h _ h' _ a X => rfl, ?_⟩
    intro x _ σ ρ
    rw [if_pos (hsub σ ρ)]
    rfl

end

end Formalism.FourierDecayAlt.P.CutMP.JA
