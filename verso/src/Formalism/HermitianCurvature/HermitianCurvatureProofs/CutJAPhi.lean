import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJA
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutCutTr
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutRegFF

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA

open NumberField Formalism.FourierDecayAlt.P.CutMP

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/- English proof (translation)
Establish `h1 : ContDiffOn ℝ ∞ (fun x : ℝ => φ (Real.exp (Real.log x))) (Set.Ioi 0)` using `(hφ : ContDiff ℝ ∞ (fun u : ℝ => φ (Real.exp u))).comp_contDiffOn (Real.contDiffOn_log.mono fun x hx => (ne_of_gt (Set.mem_Ioi.1 hx)))`. Conclude with `h1.congr fun x hx => by rw [Real.exp_log (Set.mem_Ioi.1 hx)]`.
-/
theorem smoothLog_contDiffOn {φ : ℝ → ℝ} (hφ : LE.SmoothLog φ) : ContDiffOn ℝ ∞ φ (Set.Ioi 0) := by
  have h1 : ContDiffOn ℝ ∞ (fun x : ℝ => φ (Real.exp (Real.log x))) (Set.Ioi 0) :=
    (hφ : ContDiff ℝ ∞ (fun u : ℝ => φ (Real.exp u))).comp_contDiffOn
      (Real.contDiffOn_log.mono fun x hx => (ne_of_gt (Set.mem_Ioi.1 hx)))
  exact h1.congr fun x hx => by rw [Real.exp_log (Set.mem_Ioi.1 hx)]

section mem

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

/- English proof (translation)
Take `⟨hS, hL, hR, hU⟩` from `hJ`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `g₀ hg₀`. Take `⟨U, F, hU, hgU, hF, hFJ⟩` from `hS g₀ hg₀`. Establish `hGc : Continuous (fun g : Q.Mx k r => Gf k r Bs.z Bs.z' g)` using `(Formalism.FourierDecayAlt.P.JCx1.contDiff_Gf Bs.z Bs.z').continuous`.

Use `⟨U ∩ {g | 0 < Gf k r Bs.z Bs.z' g}, fun g => ((φ (Gf k r Bs.z Bs.z' g) : ℝ) : ℂ) • F g, hU.inter (isOpen_lt continuous_const hGc), ⟨hgU, hD g₀ hg₀.2⟩, ?_, ?_⟩` and prove the remaining obligations. Establish `hc : ContDiffOn ℝ ∞ (fun g : Q.Mx k r => ((φ (Gf k r Bs.z Bs.z' g) : ℝ) : ℂ)) (U ∩ {g | 0 < Gf k r Bs.z Bs.z' g})` using `Complex.ofRealCLM.contDiff.comp_contDiffOn ((smoothLog_contDiffOn hφ).comp (Formalism.FourierDecayAlt.P.JCx1.contDiff_Gf Bs.z Bs.z').contDiffOn fun g hg => hg.2)`. Conclude with `hc.smul (hF.mono Set.inter_subset_left)`. Introduce `g hgU hgG`. Simplify using `only [hFJ g hgU.1 hgG]`.

Introduce `g hg n hn`. Establish `e : Gf k r Bs.z Bs.z' (n * g) = Gf k r Bs.z Bs.z' g`. Use `gf_SgS Bs (n_mem_Sset Bs.z hn) (one_mem_Sset Bs.z') g` as an intermediate fact. Simplify using `using this`. Simplify using `only [e, hL g hg n hn]`.

Rewrite using `[smul_comm]`. Introduce `g hg n hn`. Establish `e : Gf k r Bs.z Bs.z' (g * n) = Gf k r Bs.z Bs.z' g`. Use `gf_SgS Bs (one_mem_Sset Bs.z) (n_mem_Sset Bs.z' hn) g` as an intermediate fact. Simplify using `using this`.

Simplify using `only [e, hR g hg n hn]`. Rewrite using `[smul_comm]`. Introduce `g hg h hh h' hh'`. Establish `e : Gf k r Bs.z Bs.z' (h * g * h') = Gf k r Bs.z Bs.z' g` using `gf_SgS Bs (h_mem_Sset Bs.z hh) (h_mem_Sset Bs.z' hh') g`. Simplify using `only [e, hU g hg h hh h' hh']`.

Rewrite using `[ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]`.
-/
theorem phi_mem_FFl (Bs : B.RealPlaceData k r Wp Wq) {φ : ℝ → ℝ} (hφ : LE.SmoothLog φ)
    {Dm : Set (Q.Mx k r)} (hD : ∀ g ∈ Dm, 0 < Gf k r Bs.z Bs.z' g) {J : Q.Mx k r → (Wq →L[ℂ] Wp)}
    (hJ : J ∈ Q.FFl k r Bs.z Bs.z' Bs.π Bs.π' 0 Dm) :
    (fun g => ((φ (Gf k r Bs.z Bs.z' g) : ℝ) : ℂ) • J g) ∈ Q.FFl k r Bs.z Bs.z' Bs.π Bs.π' 0 Dm := by
  obtain ⟨hS, hL, hR, hU⟩ := hJ
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g₀ hg₀
    obtain ⟨U, F, hU, hgU, hF, hFJ⟩ := hS g₀ hg₀
    have hGc : Continuous (fun g : Q.Mx k r => Gf k r Bs.z Bs.z' g) :=
      (Formalism.FourierDecayAlt.P.JCx1.contDiff_Gf Bs.z Bs.z').continuous
    refine ⟨U ∩ {g | 0 < Gf k r Bs.z Bs.z' g}, fun g => ((φ (Gf k r Bs.z Bs.z' g) : ℝ) : ℂ) • F g,
      hU.inter (isOpen_lt continuous_const hGc), ⟨hgU, hD g₀ hg₀.2⟩, ?_, ?_⟩
    · have hc : ContDiffOn ℝ ∞ (fun g : Q.Mx k r => ((φ (Gf k r Bs.z Bs.z' g) : ℝ) : ℂ))
          (U ∩ {g | 0 < Gf k r Bs.z Bs.z' g}) :=
        Complex.ofRealCLM.contDiff.comp_contDiffOn ((smoothLog_contDiffOn hφ).comp
          (Formalism.FourierDecayAlt.P.JCx1.contDiff_Gf Bs.z Bs.z').contDiffOn fun g hg => hg.2)
      exact hc.smul (hF.mono Set.inter_subset_left)
    · intro g hgU hgG
      simp only [hFJ g hgU.1 hgG]
  · intro g hg n hn
    have e : Gf k r Bs.z Bs.z' (n * g) = Gf k r Bs.z Bs.z' g := by
      have := gf_SgS Bs (n_mem_Sset Bs.z hn) (one_mem_Sset Bs.z') g
      simpa using this
    simp only [e, hL g hg n hn]
    rw [smul_comm]
  · intro g hg n hn
    have e : Gf k r Bs.z Bs.z' (g * n) = Gf k r Bs.z Bs.z' g := by
      have := gf_SgS Bs (one_mem_Sset Bs.z) (n_mem_Sset Bs.z' hn) g
      simpa using this
    simp only [e, hR g hg n hn]
    rw [smul_comm]
  · intro g hg h hh h' hh'
    have e : Gf k r Bs.z Bs.z' (h * g * h') = Gf k r Bs.z Bs.z' g :=
      gf_SgS Bs (h_mem_Sset Bs.z hh) (h_mem_Sset Bs.z' hh') g
    simp only [e, hU g hg h hh h' hh']
    rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]

end mem

/- English proof (translation)
Use `⟨0, ?_⟩` and prove the remaining obligations. Introduce `E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e he φ hφ J hJ`. Establish `hPl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π'` using `(hB.1.2.2.2.1.2 v).2.2.2.1`. Establish `hTT : (D.parOf S v).TT = Tz S.G.k S.G.r (T v).base.z * Tz S.G.k S.G.r (T v).base.z'`. Rewrite using `[hPl.2.2.2.1, hPl.2.2.2.2.1]`.

Both sides reduce to the same expression. Establish `hQ : ∀ x ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT, x ∈ JF.QDom S.G.k S.G.r (T v).base.z (T v).base.z'` using `fun x hx => ⟨hx.1, hTT ▸ hx.2⟩`. Establish `hOm : ∀ q ∈ JF.QDom S.G.k S.G.r (T v).base.z (T v).base.z', B.gq (T v).base q ∈ OmP S T v`. Introduce `q hq`. Establish `h` using `(Formalism.FourierDecayAlt.P.BigCellHermitian.gqDom (T v).base hq).2`.

Conclude with `⟨h.2, fun a => h.1 _ (by simp)⟩`. Establish `hJ' : J ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v)` using `hJ`. Use `⟨phi_mem_FFl (T v).base hφ (fun g hg => hg.1) hJ', ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `ρ`. Use `set u : MA.Qp (D.parOf S v).r (D.parOf S v).TT → ℂ := fun q => ((Real.sqrt (MA.wq S.G.k q.1 (D.parOf S v).TT) : ℝ) : ℂ) * inner ℂ (B.hsVec (e ρ q.1.2)) (B.hsVec (J (B.gq (T v).base q.1))) with hu_def`.

Establish `hu : u ∈ MA.smSub (D.parOf S v).r (D.parOf S v).TT` using `by show ContDiffOn ℝ MA.sm (MA.ext u) (MA.Qset _ _)`. Establish `hg : ContDiffOn ℝ ∞ (fun x : MA.E (D.parOf S v).r => J (B.gq (T v).base x)) (MA.Qset (D.parOf S v).r (D.parOf S v).TT)` using `(cutTr_jgq_smooth (T v).base _ _ hJ'.1 hOm).mono hQ`. Establish `he' : ContDiffOn ℝ ∞ (fun x : MA.E (D.parOf S v).r => e ρ x.2) (MA.Qset (D.parOf S v).r (D.parOf S v).TT)` using `(he.1 ρ).comp contDiff_snd.contDiffOn fun x hx => hx.2`. Establish `hwc : ContDiff ℝ ∞ (fun x : MA.E (D.parOf S v).r => MA.wq S.G.k x (D.parOf S v).TT)`. Establish `hn` using `cutTr_normSq_contDiff`.

Unfold `MA.wq`. Use `fun_prop`. Establish `hwp : ∀ x ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT, MA.wq S.G.k x (D.parOf S v).TT ≠ 0`. Introduce `x hx`. Unfold `MA.wq`.

Conclude with `(mul_pos (Finset.prod_pos fun l _ => pow_pos (Complex.normSq_pos.2 (hx.1 l)) _) (pow_pos (sub_pos.2 hx.2) _)).ne'`. Establish `hw : ContDiffOn ℝ ∞ (fun x : MA.E (D.parOf S v).r => ((Real.sqrt (MA.wq S.G.k x (D.parOf S v).TT) : ℝ) : ℂ)) (MA.Qset (D.parOf S v).r (D.parOf S v).TT)` using `Complex.ofRealCLM.contDiff.comp_contDiffOn (hwc.contDiffOn.sqrt hwp)`. Use `(hw.mul ((cutTr_hsVec_contDiff.comp_contDiffOn he').inner ℂ (cutTr_hsVec_contDiff.comp_contDiffOn hg))).congr ?_` and prove the remaining obligations. Introduce `x hx`. Simplify using `[MA.ext, hx, hu_def]`.

Use `set p : MA.Qp (D.parOf S v).r (D.parOf S v).TT → ℂ := fun q => ((φ (MA.Gq (D.parOf S v) q) : ℝ) : ℂ) with hp_def`. Establish `hp : p ∈ MA.smSub (D.parOf S v).r (D.parOf S v).TT` using `by show ContDiffOn ℝ MA.sm (MA.ext p) (MA.Qset _ _)`. Establish `hG : ContDiff ℝ ∞ (fun x : MA.E (D.parOf S v).r => (∏ l, Complex.normSq (x.1 l)) * (Complex.normSq x.2 - (D.parOf S v).TT))`. Establish `hn` using `cutTr_normSq_contDiff`. Use `fun_prop`.

Establish `hGp : ∀ x ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT, (∏ l, Complex.normSq (x.1 l)) * (Complex.normSq x.2 - (D.parOf S v).TT) ∈ Set.Ioi (0 : ℝ)`. Introduce `x hx`. Conclude with `mul_pos (Finset.prod_pos fun l _ => Complex.normSq_pos.2 (hx.1 l)) (sub_pos.2 hx.2)`. Establish `hc : ContDiffOn ℝ ∞ (fun x : MA.E (D.parOf S v).r => ((φ ((∏ l, Complex.normSq (x.1 l)) * (Complex.normSq x.2 - (D.parOf S v).TT)) : ℝ) : ℂ)) (MA.Qset (D.parOf S v).r (D.parOf S v).TT)` using `Complex.ofRealCLM.contDiff.comp_contDiffOn ((smoothLog_contDiffOn hφ).comp hG.contDiffOn hGp)`. Use `hc.congr ?_` and prove the remaining obligations.

Introduce `x hx`. Simplify using `[MA.ext, hx, hp_def, MA.Gq]`. Establish `hL : trJ S T v e (mulG S T v φ J) ρ = MA.toSm (D.parOf S v) (fun q => p q * u q)`. Unfold `trJ`. Use `congr 1`.

Use function extensionality and compare the values at `q`. Simplify using `only [mulG, GfP]`. Rewrite using `[Formalism.FourierDecayAlt.P.JCTx2.hsVec_smul', inner_smul_right, cutTr_Gf_gq (T v).base q.2.1 (hTT ▸ q.2.2)]`. Simplify using `only [hu_def, hp_def, MA.Gq, hTT]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hR : (trJ S T v e J ρ) = ⟨u, hu⟩`. Unfold `trJ MA.toSm`. Rewrite using `[dif_pos hu]`. Establish `hP : MA.toSm (D.parOf S v) p = ⟨p, hp⟩`. Unfold `MA.toSm`.

Rewrite using `[dif_pos hp]`. Rewrite using `[hL, hR, hP]`. Establish `hm : (fun q => p q * u q) ∈ MA.smSub (D.parOf S v).r (D.parOf S v).TT` using `Subalgebra.mul_mem _ hp hu`. Unfold `MA.toSm`. Rewrite using `[dif_pos hm]`.

Both sides reduce to the same expression.
-/
theorem phi_operator_transfer_holds : JAPhiOp := by
  refine ⟨0, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e he φ hφ J hJ
  have hPl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hB.1.2.2.2.1.2 v).2.2.2.1
  have hTT : (D.parOf S v).TT = Tz S.G.k S.G.r (T v).base.z * Tz S.G.k S.G.r (T v).base.z' := by
    rw [hPl.2.2.2.1, hPl.2.2.2.2.1]; rfl
  have hQ : ∀ x ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT, x ∈ JF.QDom S.G.k S.G.r (T v).base.z (T v).base.z' :=
    fun x hx => ⟨hx.1, hTT ▸ hx.2⟩
  have hOm : ∀ q ∈ JF.QDom S.G.k S.G.r (T v).base.z (T v).base.z', B.gq (T v).base q ∈ OmP S T v := by
    intro q hq
    have h := (Formalism.FourierDecayAlt.P.BigCellHermitian.gqDom (T v).base hq).2
    exact ⟨h.2, fun a => h.1 _ (by simp)⟩
  have hJ' : J ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v) := hJ
  refine ⟨phi_mem_FFl (T v).base hφ (fun g hg => hg.1) hJ', ?_⟩
  funext ρ
  set u : MA.Qp (D.parOf S v).r (D.parOf S v).TT → ℂ := fun q =>
    ((Real.sqrt (MA.wq S.G.k q.1 (D.parOf S v).TT) : ℝ) : ℂ) *
      inner ℂ (B.hsVec (e ρ q.1.2)) (B.hsVec (J (B.gq (T v).base q.1))) with hu_def
  have hu : u ∈ MA.smSub (D.parOf S v).r (D.parOf S v).TT := by
    show ContDiffOn ℝ MA.sm (MA.ext u) (MA.Qset _ _)
    have hg : ContDiffOn ℝ ∞ (fun x : MA.E (D.parOf S v).r => J (B.gq (T v).base x))
        (MA.Qset (D.parOf S v).r (D.parOf S v).TT) :=
      (cutTr_jgq_smooth (T v).base _ _ hJ'.1 hOm).mono hQ
    have he' : ContDiffOn ℝ ∞ (fun x : MA.E (D.parOf S v).r => e ρ x.2) (MA.Qset (D.parOf S v).r (D.parOf S v).TT) :=
      (he.1 ρ).comp contDiff_snd.contDiffOn fun x hx => hx.2
    have hwc : ContDiff ℝ ∞ (fun x : MA.E (D.parOf S v).r => MA.wq S.G.k x (D.parOf S v).TT) := by
      have hn := cutTr_normSq_contDiff
      unfold MA.wq
      fun_prop
    have hwp : ∀ x ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT, MA.wq S.G.k x (D.parOf S v).TT ≠ 0 := by
      intro x hx
      unfold MA.wq
      exact (mul_pos (Finset.prod_pos fun l _ => pow_pos (Complex.normSq_pos.2 (hx.1 l)) _)
        (pow_pos (sub_pos.2 hx.2) _)).ne'
    have hw : ContDiffOn ℝ ∞ (fun x : MA.E (D.parOf S v).r => ((Real.sqrt (MA.wq S.G.k x (D.parOf S v).TT) : ℝ) : ℂ))
        (MA.Qset (D.parOf S v).r (D.parOf S v).TT) :=
      Complex.ofRealCLM.contDiff.comp_contDiffOn (hwc.contDiffOn.sqrt hwp)
    refine (hw.mul ((cutTr_hsVec_contDiff.comp_contDiffOn he').inner ℂ
      (cutTr_hsVec_contDiff.comp_contDiffOn hg))).congr ?_
    intro x hx
    simp [MA.ext, hx, hu_def]
  set p : MA.Qp (D.parOf S v).r (D.parOf S v).TT → ℂ := fun q => ((φ (MA.Gq (D.parOf S v) q) : ℝ) : ℂ) with hp_def
  have hp : p ∈ MA.smSub (D.parOf S v).r (D.parOf S v).TT := by
    show ContDiffOn ℝ MA.sm (MA.ext p) (MA.Qset _ _)
    have hG : ContDiff ℝ ∞ (fun x : MA.E (D.parOf S v).r =>
        (∏ l, Complex.normSq (x.1 l)) * (Complex.normSq x.2 - (D.parOf S v).TT)) := by
      have hn := cutTr_normSq_contDiff
      fun_prop
    have hGp : ∀ x ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT,
        (∏ l, Complex.normSq (x.1 l)) * (Complex.normSq x.2 - (D.parOf S v).TT) ∈ Set.Ioi (0 : ℝ) := by
      intro x hx
      exact mul_pos (Finset.prod_pos fun l _ => Complex.normSq_pos.2 (hx.1 l)) (sub_pos.2 hx.2)
    have hc : ContDiffOn ℝ ∞ (fun x : MA.E (D.parOf S v).r =>
        ((φ ((∏ l, Complex.normSq (x.1 l)) * (Complex.normSq x.2 - (D.parOf S v).TT)) : ℝ) : ℂ))
        (MA.Qset (D.parOf S v).r (D.parOf S v).TT) :=
      Complex.ofRealCLM.contDiff.comp_contDiffOn ((smoothLog_contDiffOn hφ).comp hG.contDiffOn hGp)
    refine hc.congr ?_
    intro x hx
    simp [MA.ext, hx, hp_def, MA.Gq]
  have hL : trJ S T v e (mulG S T v φ J) ρ = MA.toSm (D.parOf S v) (fun q => p q * u q) := by
    unfold trJ
    congr 1
    funext q
    simp only [mulG, GfP]
    rw [Formalism.FourierDecayAlt.P.JCTx2.hsVec_smul', inner_smul_right,
      cutTr_Gf_gq (T v).base q.2.1 (hTT ▸ q.2.2)]
    simp only [hu_def, hp_def, MA.Gq, hTT]
    ring
  have hR : (trJ S T v e J ρ) = ⟨u, hu⟩ := by
    unfold trJ MA.toSm
    rw [dif_pos hu]
  have hP : MA.toSm (D.parOf S v) p = ⟨p, hp⟩ := by
    unfold MA.toSm
    rw [dif_pos hp]
  rw [hL, hR, hP]
  have hm : (fun q => p q * u q) ∈ MA.smSub (D.parOf S v).r (D.parOf S v).TT := Subalgebra.mul_mem _ hp hu
  unfold MA.toSm
  rw [dif_pos hm]
  rfl

end Formalism.FourierDecayAlt.P.CutMP.JA
