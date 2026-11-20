import Formalism.HermitianCurvature.HermitianCurvatureProofs.WaveLocalBuiltPlaces
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PbFormPos
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGWaveMain
import Formalism.HermitianCurvature.HermitianCurvatureProofs.GramLocSetCApp
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBFCstmt

namespace Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt NumberField MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.PBD
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

def FormPosCpt : Prop :=
  P5.ThmPActualCpt → ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (j : ℕ) (hj : j ≤ P.r) (w : List C.Letter), KB.CutWord P p.l0 w → ∀ x, (∀ e, KB.CptCoef (p.T.bs j) (x e)) →
    0 ≤ p.form j hj w x x

section cv

variable {k ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def CV {S : Type} (Bs : B.RealPlaceData k ρ Wp Wq) (x : Wd.Ix S → B.Mat k ρ → (Wq →L[ℂ] Wp)) : Prop :=
  ∀ e, KB.CptCoef Bs (x e)

variable {S : Type} {Bs : B.RealPlaceData k ρ Wp Wq}

/- English proof (translation)
Assemble the required witnesses or components as `⟨Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_zero, ⟨0, fun g _ h => (h rfl).elim⟩, ⟨1, one_pos, fun g _ h => (h rfl).elim⟩⟩`.
-/
theorem cpt_zero : KB.CptCoef Bs (fun _ : B.Mat k ρ => (0 : Wq →L[ℂ] Wp)) :=
  ⟨Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_zero, ⟨0, fun g _ h => (h rfl).elim⟩, ⟨1, one_pos, fun g _ h => (h rfl).elim⟩⟩

/- English proof (translation)
Take `⟨h1, ⟨R, hR⟩, ⟨ε, hε, hGε⟩⟩` from `hF`. Take `⟨h1', ⟨R', hR'⟩, ⟨ε', hε', hGε'⟩⟩` from `hG`. Use `⟨Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_add h1 h1', ⟨max R R', fun g hg hne => ?_⟩, ⟨min ε ε', lt_min hε hε', fun g hg hne => ?_⟩⟩` and prove the remaining obligations. Distinguish the cases in `h0 : F g = 0`. Conclude with `(hR' g hg (by simpa [h0] using hne)).trans (le_max_right _ _)`.

Conclude with `(hR g hg h0).trans (le_max_left _ _)`. Distinguish the cases in `h0 : F g = 0`. Conclude with `(min_le_right _ _).trans (hGε' g hg (by simpa [h0] using hne))`. Conclude with `(min_le_left _ _).trans (hGε g hg h0)`.
-/
theorem cpt_add {F G : B.Mat k ρ → (Wq →L[ℂ] Wp)} (hF : KB.CptCoef Bs F) (hG : KB.CptCoef Bs G) :
    KB.CptCoef Bs (fun g => F g + G g) := by
  obtain ⟨h1, ⟨R, hR⟩, ⟨ε, hε, hGε⟩⟩ := hF
  obtain ⟨h1', ⟨R', hR'⟩, ⟨ε', hε', hGε'⟩⟩ := hG
  refine ⟨Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_add h1 h1', ⟨max R R', fun g hg hne => ?_⟩, ⟨min ε ε', lt_min hε hε', fun g hg hne => ?_⟩⟩
  · by_cases h0 : F g = 0
    · exact (hR' g hg (by simpa [h0] using hne)).trans (le_max_right _ _)
    · exact (hR g hg h0).trans (le_max_left _ _)
  · by_cases h0 : F g = 0
    · exact (min_le_right _ _).trans (hGε' g hg (by simpa [h0] using hne))
    · exact (min_le_left _ _).trans (hGε g hg h0)

/- English proof (translation)
Take `⟨h1, ⟨R, hR⟩, ⟨ε, hε, hGε⟩⟩` from `hF`. Use `⟨Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_smul c h1, ⟨R, fun g hg hne => hR g hg fun h0 => hne (by simp [h0])⟩, ⟨ε, hε, fun g hg hne => hGε g hg fun h0 => hne (by simp [h0])⟩⟩` and prove the remaining obligations.
-/
theorem cpt_smul (c : ℂ) {F : B.Mat k ρ → (Wq →L[ℂ] Wp)} (hF : KB.CptCoef Bs F) :
    KB.CptCoef Bs (fun g => c • F g) := by
  obtain ⟨h1, ⟨R, hR⟩, ⟨ε, hε, hGε⟩⟩ := hF
  refine ⟨Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_smul c h1, ⟨R, fun g hg hne => hR g hg fun h0 => hne (by simp [h0])⟩,
    ⟨ε, hε, fun g hg hne => hGε g hg fun h0 => hne (by simp [h0])⟩⟩

/- English proof (translation)
Introduce `_` and use `cpt_zero`.
-/
theorem cv_zero : CV (S := S) Bs 0 := fun _ => cpt_zero

/- English proof (translation)
Introduce `e` and use `cpt_add (hx e) (hy e)`.
-/
theorem cv_add {x y : Wd.Ix S → B.Mat k ρ → (Wq →L[ℂ] Wp)} (hx : CV Bs x) (hy : CV Bs y) : CV Bs (x + y) :=
  fun e => cpt_add (hx e) (hy e)

/- English proof (translation)
Introduce `e` and use `cpt_smul c (hx e)`.
-/
theorem cv_smul (c : ℂ) {x : Wd.Ix S → B.Mat k ρ → (Wq →L[ℂ] Wp)} (hx : CV Bs x) : CV Bs (c • x) :=
  fun e => cpt_smul c (hx e)

/- English proof (translation)
The claim follows from `common_eps (fun e ε => JC.NiceCoef Bs ε (x e)) (fun e ε ε' h _ h' => nice_mono h h') fun e => nice_of_cpt (hx e)`.
-/
theorem nv_of_cv [Fintype (Wd.Ix S)] {x : Wd.Ix S → B.Mat k ρ → (Wq →L[ℂ] Wp)} (hx : CV Bs x) :
    ∃ ε, 0 < ε ∧ NV Bs ε x :=
  common_eps (fun e ε => JC.NiceCoef Bs ε (x e)) (fun e ε ε' h _ h' => nice_mono h h') fun e => nice_of_cpt (hx e)

/- English proof (translation)
Take `⟨a, ha, hxa⟩` from `nv_of_cv hx`. Take `⟨b, hb, hyb⟩` from `nv_of_cv hy`. Take `⟨c, hc, hzc⟩` from `nv_of_cv hz`. Use `⟨min a (min b c), lt_min ha (lt_min hb hc), nv_mono hxa (min_le_left _ _), nv_mono hyb ((min_le_right _ _).trans (min_le_left _ _)), nv_mono hzc ((min_le_right _ _).trans (min_le_right _ _))⟩` and prove the remaining obligations.
-/
theorem exists_norm_bound_three_families [Fintype (Wd.Ix S)] {S' S'' : Type} [Fintype (Wd.Ix S')] [Fintype (Wd.Ix S'')]
    {x : Wd.Ix S → B.Mat k ρ → (Wq →L[ℂ] Wp)} {y : Wd.Ix S' → B.Mat k ρ → (Wq →L[ℂ] Wp)}
    {z : Wd.Ix S'' → B.Mat k ρ → (Wq →L[ℂ] Wp)} (hx : CV Bs x) (hy : CV Bs y) (hz : CV Bs z) :
    ∃ ε, 0 < ε ∧ NV Bs ε x ∧ NV Bs ε y ∧ NV Bs ε z := by
  obtain ⟨a, ha, hxa⟩ := nv_of_cv hx
  obtain ⟨b, hb, hyb⟩ := nv_of_cv hy
  obtain ⟨c, hc, hzc⟩ := nv_of_cv hz
  refine ⟨min a (min b c), lt_min ha (lt_min hb hc), nv_mono hxa (min_le_left _ _),
    nv_mono hyb ((min_le_right _ _).trans (min_le_left _ _)), nv_mono hzc ((min_le_right _ _).trans (min_le_right _ _))⟩

end cv

section formsC

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par}
  (p : KB.Pl P Wp Wq) (j : ℕ) (hj : j ≤ P.r) (w : List C.Letter)

/- English proof (translation)
Take `⟨ε, -, a, b, d⟩` from `exists_norm_bound_three_families h₁ h₂ hy`. Conclude with `form_sl p j hj w x₁ x₂ y c a b d`.
-/
theorem form_slC (x₁ x₂ y : Wd.Ix (Fin w.length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)) (c : ℂ)
    (h₁ : CV (p.T.bs j) x₁) (h₂ : CV (p.T.bs j) x₂) (hy : CV (p.T.bs j) y) :
    p.form j hj w (x₁ + c • x₂) y = p.form j hj w x₁ y + c * p.form j hj w x₂ y := by
  obtain ⟨ε, -, a, b, d⟩ := exists_norm_bound_three_families h₁ h₂ hy
  exact form_sl p j hj w x₁ x₂ y c a b d

/- English proof (translation)
Take `⟨ε, -, a, b, d⟩` from `exists_norm_bound_three_families hx h₁ h₂`. Conclude with `form_sr p j hj w x y₁ y₂ c a b d`.
-/
theorem form_srC (x y₁ y₂ : Wd.Ix (Fin w.length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)) (c : ℂ)
    (hx : CV (p.T.bs j) x) (h₁ : CV (p.T.bs j) y₁) (h₂ : CV (p.T.bs j) y₂) :
    p.form j hj w x (y₁ + c • y₂) = p.form j hj w x y₁ + conj c * p.form j hj w x y₂ := by
  obtain ⟨ε, -, a, b, d⟩ := exists_norm_bound_three_families hx h₁ h₂
  exact form_sr p j hj w x y₁ y₂ c a b d

variable (ys : List ℝ)

/- English proof (translation)
Take `⟨ε, -, a, b, d⟩` from `exists_norm_bound_three_families h₁ h₂ hy`. Conclude with `pj_sl p j hj w ys x₁ x₂ y c a b d`.
-/
theorem pj_slC (x₁ x₂ : Wd.Ix (Fin (KB.plusW ys w).length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp))
    (y : Wd.Ix (Fin (KB.minusW ys w).length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)) (c : ℂ)
    (h₁ : CV (p.T.bs j) x₁) (h₂ : CV (p.T.bs j) x₂) (hy : CV (p.T.bs j) y) :
    KB.pairJ (p.form j hj w) ys (x₁ + c • x₂) y =
      KB.pairJ (p.form j hj w) ys x₁ y + c * KB.pairJ (p.form j hj w) ys x₂ y := by
  obtain ⟨ε, -, a, b, d⟩ := exists_norm_bound_three_families h₁ h₂ hy
  exact pj_sl p j hj w ys x₁ x₂ y c a b d

/- English proof (translation)
Take `⟨ε, -, a, b, d⟩` from `exists_norm_bound_three_families hx h₁ h₂`. Conclude with `pj_sr p j hj w ys x y₁ y₂ c a b d`.
-/
theorem pj_srC (x : Wd.Ix (Fin (KB.plusW ys w).length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp))
    (y₁ y₂ : Wd.Ix (Fin (KB.minusW ys w).length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)) (c : ℂ)
    (hx : CV (p.T.bs j) x) (h₁ : CV (p.T.bs j) y₁) (h₂ : CV (p.T.bs j) y₂) :
    KB.pairJ (p.form j hj w) ys x (y₁ + c • y₂) =
      KB.pairJ (p.form j hj w) ys x y₁ + conj c * KB.pairJ (p.form j hj w) ys x y₂ := by
  obtain ⟨ε, -, a, b, d⟩ := exists_norm_bound_three_families hx h₁ h₂
  exact pj_sr p j hj w ys x y₁ y₂ c a b d

end formsC

section hatC

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]

/- English proof (translation)
Establish `hgpos` using `g_pos_of_built hB`. Establish `hB'` using `hB`. Take `⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hv⟩` from `hB'`. Take `⟨hl0, hInD, -, -, -⟩` from `hv v`. Establish `hH : D.IsLocPt (stdS S h) j` using `(isLocPt_toStd_iff _ _ hgpos h 1 j).2 hh`.

Establish `hH' : D.IsLocPt (stdS S h') j` using `(isLocPt_toStd_iff _ _ hgpos h' 1 j).2 hh'`. Take `⟨φ, -, -, hφ, hφint⟩` from `hPSC (Wp (S.pl v)) (Wq (S.pl v)) (D.parOf S v) (p v) (F v ε) j hj w (stdS S h) (stdS S h') hH hH' Cb (by rw [hl0]; exact hInD) (hF v ε hε) (by rw [hl0]; exact hw)`. Establish `hlam_pos` using `lamS_pos S hgpos j`. Take `⟨g, hgdef⟩ : ∃ g : ℂ → ℂ, g = fun c' => P5.fsv (sW S j l) c' * φ c'` from `⟨_, rfl⟩`. Establish `hae : (fun c : ℂ => KB.gN (setC S p F) v ε (j + 1) w (h ++ [(1, c)]) (h' ++ [(1, c)]) * KB.psiL (setC S p F) l c) =ᵐ[volume] fun c => ((Kc S v j w h h' : ℝ) : ℂ) * g (lamS S j • c)` using `by filter_upwards [ae_ne_zero_complex] with c hc`.

Establish `hlc : (lamS S j : ℂ) * c ≠ 0` using `mul_ne_zero (by exact_mod_cast hlam_pos.ne') hc`. Simplify using `only [hgdef, Complex.real_smul]`. Rewrite using `[gN_setC_app hB F v ε j hj w h h' hh.2 hh'.2 c hc, hφ _ hlc]`. Establish `: KB.psiL (setC S p F) l c = KB.psiL S l c` using `rfl`. Rewrite using `[this, psiL_eq_fsv S hgpos j l c]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hint : KB.hatB (setC S p F) v ε (j + 1) 1 w l h h' = ((KB.dlB S (j + 1) 1 : ℝ) : ℂ)⁻¹ * ∫ c, ((Kc S v j w h h' : ℝ) : ℂ) * g (lamS S j • c)`. Unfold `KB.hatB`. Rewrite using `[show j + 1 + 1 - 1 = j + 1 by omega, integral_congr_ae hae]`. Both sides reduce to the same expression.

Establish `hcs : ∫ c, ((Kc S v j w h h' : ℝ) : ℂ) * g (lamS S j • c) = ((Kc S v j w h h' : ℝ) : ℂ) * (((|(lamS S j ^ 2)⁻¹| : ℝ) : ℂ) * ∫ c, P5.fsv (sW S j l) c * φ c)`. Rewrite using `[integral_const_mul, Measure.integral_comp_smul, Complex.finrank_real_complex, Complex.real_smul, hgdef]`. Establish `gen : ∀ X : ℂ, ((KB.dlB S (j + 1) 1 : ℝ) : ℂ)⁻¹ * (((Kc S v j w h h' : ℝ) : ℂ) * (((|(lamS S j ^ 2)⁻¹| : ℝ) : ℂ) * X)) = ((dW S v j w h h' : ℝ) : ℂ) * X`. Introduce `X`. Rewrite using `[← kc_scal hB v j hj w h h']`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Conclude with `(hint.trans ((congrArg (fun Z => ((KB.dlB S (j + 1) 1 : ℝ) : ℂ)⁻¹ * Z) hcs).trans (gen _))).trans (congrArg (fun X => ((dW S v j w h h' : ℝ) : ℂ) * X) (hφint (sW S j l)))`.
-/
theorem hatB_setC_C (hPSC : StandardPairingDecay.PStdC) {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq}
    {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
    {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}
    (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀)
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
    (hF : ∀ v ε, 0 < ε → KB.CptCoef (p v).T.base (F v ε))
    (v : Fin S.f) (ε : ℝ) (hε : 0 < ε) (j : ℕ) (hj : j ≤ S.G.r) (w : List C.Letter)
    (hw : KB.CutWord (D.parOf S v) (S.l + 1) w) (l : ℂ) (h h' : C.LPt) (hh : D.IsLocPt h j)
    (hh' : D.IsLocPt h' j) :
    KB.hatB (setC S p F) v ε (j + 1) 1 w l h h' =
      ((dW S v j w h h' : ℝ) : ℂ) * (p v).form j hj w
        (KB.waveG ((p v).T.bs j) (sW S j l) w
          (KB.slv (p v).T (F v ε) j hj w (stdS S h) ((stdS_size S h).trans hh.2)))
        (KB.slv (p v).T (F v ε) j hj w (stdS S h') ((stdS_size S h').trans hh'.2)) := by
  have hgpos := g_pos_of_built hB
  have hB' := hB
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hv⟩ := hB'
  obtain ⟨hl0, hInD, -, -, -⟩ := hv v
  have hH : D.IsLocPt (stdS S h) j := (isLocPt_toStd_iff _ _ hgpos h 1 j).2 hh
  have hH' : D.IsLocPt (stdS S h') j := (isLocPt_toStd_iff _ _ hgpos h' 1 j).2 hh'
  obtain ⟨φ, -, -, hφ, hφint⟩ := hPSC (Wp (S.pl v)) (Wq (S.pl v)) (D.parOf S v) (p v) (F v ε) j hj w
    (stdS S h) (stdS S h') hH hH' Cb (by rw [hl0]; exact hInD) (hF v ε hε) (by rw [hl0]; exact hw)
  have hlam_pos := lamS_pos S hgpos j
  obtain ⟨g, hgdef⟩ : ∃ g : ℂ → ℂ, g = fun c' => P5.fsv (sW S j l) c' * φ c' := ⟨_, rfl⟩
  have hae : (fun c : ℂ => KB.gN (setC S p F) v ε (j + 1) w (h ++ [(1, c)]) (h' ++ [(1, c)]) *
      KB.psiL (setC S p F) l c) =ᵐ[volume]
      fun c => ((Kc S v j w h h' : ℝ) : ℂ) * g (lamS S j • c) := by
    filter_upwards [ae_ne_zero_complex] with c hc
    have hlc : (lamS S j : ℂ) * c ≠ 0 := mul_ne_zero (by exact_mod_cast hlam_pos.ne') hc
    simp only [hgdef, Complex.real_smul]
    rw [gN_setC_app hB F v ε j hj w h h' hh.2 hh'.2 c hc, hφ _ hlc]
    have : KB.psiL (setC S p F) l c = KB.psiL S l c := rfl
    rw [this, psiL_eq_fsv S hgpos j l c]
    ring
  have hint : KB.hatB (setC S p F) v ε (j + 1) 1 w l h h' = ((KB.dlB S (j + 1) 1 : ℝ) : ℂ)⁻¹ *
      ∫ c, ((Kc S v j w h h' : ℝ) : ℂ) * g (lamS S j • c) := by
    unfold KB.hatB
    rw [show j + 1 + 1 - 1 = j + 1 by omega, integral_congr_ae hae]
    rfl
  have hcs : ∫ c, ((Kc S v j w h h' : ℝ) : ℂ) * g (lamS S j • c) =
      ((Kc S v j w h h' : ℝ) : ℂ) * (((|(lamS S j ^ 2)⁻¹| : ℝ) : ℂ) * ∫ c, P5.fsv (sW S j l) c * φ c) := by
    rw [integral_const_mul, Measure.integral_comp_smul, Complex.finrank_real_complex, Complex.real_smul, hgdef]
  have gen : ∀ X : ℂ, ((KB.dlB S (j + 1) 1 : ℝ) : ℂ)⁻¹ *
      (((Kc S v j w h h' : ℝ) : ℂ) * (((|(lamS S j ^ 2)⁻¹| : ℝ) : ℂ) * X)) = ((dW S v j w h h' : ℝ) : ℂ) * X := by
    intro X
    rw [← kc_scal hB v j hj w h h']
    push_cast
    ring
  exact (hint.trans ((congrArg (fun Z => ((KB.dlB S (j + 1) 1 : ℝ) : ℂ)⁻¹ * Z) hcs).trans (gen _))).trans
    (congrArg (fun X => ((dW S v j w h h' : ℝ) : ℂ) * X) (hφint (sW S j l)))

end hatC

section hatUC

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
  {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq} {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
  {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}

/- English proof (translation)
Establish `hgpos` using `g_pos_of_built hB`. Take `⟨ε1, hε1, hx, hx'⟩` from `nv_pair (uB_nv hB F hF v ε hε j hj w h) (uB_nv hB F hF v ε hε j hj w h')`. Establish `hwx` using `PBFV.waveG_nice ((p v).T.bs j) ε1 (sW S j l) w _ hx`. Distinguish the cases in `hloc : D.IsLocPt h j ∧ D.IsLocPt h' j`. Take `⟨hh, hh'⟩` from `hloc`.

Establish `hH : D.IsLocPt (stdS S h) j` using `(PBD.isLocPt_toStd_iff _ _ hgpos h 1 j).2 hh`. Establish `hH' : D.IsLocPt (stdS S h') j` using `(PBD.isLocPt_toStd_iff _ _ hgpos h' 1 j).2 hh'`. Take `⟨ε2, hε2, hs, hs'⟩` from `nv_pair (slv_nv (p v) (hF v ε hε) j hj w (stdS S h) hH) (slv_nv (p v) (hF v ε hε) j hj w (stdS S h') hH')`. Rewrite using `[hatB_setC_C hPSC hB F hF v ε hε j hj w hw l h h' hh hh']`. Establish `e1 : uB S p F v ε j hj w h = (((√(nnS S h) / bS S h : ℝ) : ℂ)) • KB.slv (p v).T (F v ε) j hj w (stdS S h) ((stdS_size S h).trans hh.2)`.

Unfold `uB`. Rewrite using `[dif_pos hh]`. Establish `e2 : uB S p F v ε j hj w h' = (((√(nnS S h') / bS S h' : ℝ) : ℂ)) • KB.slv (p v).T (F v ε) j hj w (stdS S h') ((stdS_size S h').trans hh'.2)`. Unfold `uB`. Rewrite using `[dif_pos hh']`.

Establish `hws` using `PBFV.waveG_nice ((p v).T.bs j) ε2 (sW S j l) w _ hs`. Establish `ew : KB.waveG ((p v).T.bs j) (sW S j l) w ((((√(nnS S h) / bS S h : ℝ) : ℂ)) • KB.slv (p v).T (F v ε) j hj w (stdS S h) ((stdS_size S h).trans hh.2)) = (((√(nnS S h) / bS S h : ℝ) : ℂ)) • KB.waveG ((p v).T.bs j) (sW S j l) w (KB.slv (p v).T (F v ε) j hj w (stdS S h) ((stdS_size S …`. Use `PBG.waveG_add_smul ((p v).T.bs j) (sW S j l) w 0 (KB.slv (p v).T (F v ε) j hj w (stdS S h) ((stdS_size S h).trans hh.2)) (((√(nnS S h) / bS S h : ℝ) : ℂ))` as an intermediate fact. Rewrite `this` using `[zero_add, PBG.waveG_zero, zero_add]`. Conclude with `this`.

Rewrite using `[e1, e2, ew, form_smul_l (p v) j hj w _ _ _ hws (nv_smul _ hs'), form_smul_r (p v) j hj w _ _ _ hws hs', Complex.conj_ofReal, dW_split]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hatB_setC_zero hB F v ε j w l h h' hsz hsz' hloc]`. Establish `: uB S p F v ε j hj w h = 0 ∨ uB S p F v ε j hj w h' = 0`.

Distinguish the cases in `hh : D.IsLocPt h j`. Use `right`. Unfold `uB`. Rewrite using `[dif_neg (fun hh' => hloc ⟨hh, hh'⟩)]`. Use `left`.

Unfold `uB`. Rewrite using `[dif_neg hh]`. Break down `this with h0 | h0` into its components or cases. Rewrite using `[h0, PBG.waveG_zero, form_zero_l (p v) j hj w _ hx', mul_zero]`. Rewrite using `[h0, form_zero_r (p v) j hj w _ hwx, mul_zero]`.
-/
theorem hatB_uB_C (hPSC : StandardPairingDecay.PStdC) (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀)
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
    (hF : ∀ v ε, 0 < ε → KB.CptCoef (p v).T.base (F v ε)) (v : Fin S.f) (ε : ℝ) (hε : 0 < ε) (j : ℕ)
    (hj : j ≤ S.G.r) (w : List C.Letter) (hw : KB.CutWord (D.parOf S v) (S.l + 1) w) (l : ℂ) (h h' : C.LPt)
    (hsz : D.ptSize h = j) (hsz' : D.ptSize h' = j) :
    KB.hatB (setC S p F) v ε (j + 1) 1 w l h h' =
      ((1 / (ΓS S j * S.sizeAt v w) : ℝ) : ℂ) * (p v).form j hj w
        (KB.waveG ((p v).T.bs j) (sW S j l) w (uB S p F v ε j hj w h)) (uB S p F v ε j hj w h') := by
  have hgpos := g_pos_of_built hB
  obtain ⟨ε1, hε1, hx, hx'⟩ := nv_pair (uB_nv hB F hF v ε hε j hj w h) (uB_nv hB F hF v ε hε j hj w h')
  have hwx := PBFV.waveG_nice ((p v).T.bs j) ε1 (sW S j l) w _ hx
  by_cases hloc : D.IsLocPt h j ∧ D.IsLocPt h' j
  · obtain ⟨hh, hh'⟩ := hloc
    have hH : D.IsLocPt (stdS S h) j := (PBD.isLocPt_toStd_iff _ _ hgpos h 1 j).2 hh
    have hH' : D.IsLocPt (stdS S h') j := (PBD.isLocPt_toStd_iff _ _ hgpos h' 1 j).2 hh'
    obtain ⟨ε2, hε2, hs, hs'⟩ := nv_pair (slv_nv (p v) (hF v ε hε) j hj w (stdS S h) hH)
      (slv_nv (p v) (hF v ε hε) j hj w (stdS S h') hH')
    rw [hatB_setC_C hPSC hB F hF v ε hε j hj w hw l h h' hh hh']
    have e1 : uB S p F v ε j hj w h = (((√(nnS S h) / bS S h : ℝ) : ℂ)) •
        KB.slv (p v).T (F v ε) j hj w (stdS S h) ((stdS_size S h).trans hh.2) := by
      unfold uB; rw [dif_pos hh]
    have e2 : uB S p F v ε j hj w h' = (((√(nnS S h') / bS S h' : ℝ) : ℂ)) •
        KB.slv (p v).T (F v ε) j hj w (stdS S h') ((stdS_size S h').trans hh'.2) := by
      unfold uB; rw [dif_pos hh']
    have hws := PBFV.waveG_nice ((p v).T.bs j) ε2 (sW S j l) w _ hs
    have ew : KB.waveG ((p v).T.bs j) (sW S j l) w ((((√(nnS S h) / bS S h : ℝ) : ℂ)) •
        KB.slv (p v).T (F v ε) j hj w (stdS S h) ((stdS_size S h).trans hh.2)) =
        (((√(nnS S h) / bS S h : ℝ) : ℂ)) • KB.waveG ((p v).T.bs j) (sW S j l) w
          (KB.slv (p v).T (F v ε) j hj w (stdS S h) ((stdS_size S h).trans hh.2)) := by
      have := PBG.waveG_add_smul ((p v).T.bs j) (sW S j l) w 0
        (KB.slv (p v).T (F v ε) j hj w (stdS S h) ((stdS_size S h).trans hh.2)) (((√(nnS S h) / bS S h : ℝ) : ℂ))
      rw [zero_add, PBG.waveG_zero, zero_add] at this
      exact this
    rw [e1, e2, ew, form_smul_l (p v) j hj w _ _ _ hws (nv_smul _ hs'), form_smul_r (p v) j hj w _ _ _ hws hs',
      Complex.conj_ofReal, dW_split]
    push_cast
    ring
  · rw [hatB_setC_zero hB F v ε j w l h h' hsz hsz' hloc]
    have : uB S p F v ε j hj w h = 0 ∨ uB S p F v ε j hj w h' = 0 := by
      by_cases hh : D.IsLocPt h j
      · right; unfold uB; rw [dif_neg (fun hh' => hloc ⟨hh, hh'⟩)]
      · left; unfold uB; rw [dif_neg hh]
    rcases this with h0 | h0
    · rw [h0, PBG.waveG_zero, form_zero_l (p v) j hj w _ hx', mul_zero]
    · rw [h0, form_zero_r (p v) j hj w _ hwx, mul_zero]

/- English proof (translation)
Establish `hgpos` using `g_pos_of_built hB`. Distinguish the cases in `hh : D.IsLocPt h j`. Rewrite using `[uB_pos S p F v ε j hj w h hh]`. Establish `hH : D.IsLocPt (stdS S h) j` using `(PBD.isLocPt_toStd_iff _ _ hgpos h 1 j).2 hh`. Conclude with `cv_smul _ fun e => Formalism.FourierDecayAlt.P.slice_compact_support_coefficient _ _ (D.parOf S v) (p v) (F v ε) j hj w (stdS S h) hH (hF v ε hε) e`.

Rewrite using `[uB_neg S p F v ε j hj w h hh]`. Conclude with `cv_zero`.
-/
theorem uB_cv (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀)
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
    (hF : ∀ v ε, 0 < ε → KB.CptCoef (p v).T.base (F v ε)) (v : Fin S.f) (ε : ℝ) (hε : 0 < ε) (j : ℕ)
    (hj : j ≤ S.G.r) (w : List C.Letter) (h : C.LPt) : CV ((p v).T.bs j) (uB S p F v ε j hj w h) := by
  have hgpos := g_pos_of_built hB
  by_cases hh : D.IsLocPt h j
  · rw [uB_pos S p F v ε j hj w h hh]
    have hH : D.IsLocPt (stdS S h) j := (PBD.isLocPt_toStd_iff _ _ hgpos h 1 j).2 hh
    exact cv_smul _ fun e => Formalism.FourierDecayAlt.P.slice_compact_support_coefficient _ _ (D.parOf S v) (p v) (F v ε) j hj w (stdS S h) hH
      (hF v ε hε) e
  · rw [uB_neg S p F v ε j hj w h hh]; exact cv_zero

/- English proof (translation)
Unfold `uY`. Use `split_ifs`. Conclude with `uB_cv hB F hF v ε hε j hj w h`. Conclude with `cv_zero`.
-/
theorem uY_cv (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀)
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
    (hF : ∀ v ε, 0 < ε → KB.CptCoef (p v).T.base (F v ε)) (v : Fin S.f) (ε : ℝ) (hε : 0 < ε) (j : ℕ)
    (hj : j ≤ S.G.r) (w : List C.Letter) (Y : Finset C.LPt) (h : C.LPt) :
    CV ((p v).T.bs j) (uY S p F v ε j hj w Y h) := by
  unfold uY
  split_ifs
  · exact uB_cv hB F hF v ε hε j hj w h
  · exact cv_zero

end hatUC

end

end Formalism.FourierDecayAlt.P.PBL
