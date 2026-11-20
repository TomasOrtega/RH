import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicConnectionAddSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SuperconnCompPeriodTranslationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SuperconnSquarePeriodFunctionStatement

set_option autoImplicit false

noncomputable section

open Matrix Set Filter Topology
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff

namespace GlobalTheory.TorsionForm.TranslInv

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g n : ℕ}

/- English proof (translation)
Use extensionality with `k`. Simplify using `only [per, Pi.add_apply, Complex.ofReal_add, Matrix.vecMul, dotProduct, add_mul, Finset.sum_add_distrib]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem per_add' (τ : Matrix (Fin g) (Fin g) ℂ) (x y : Fl g) : per τ (x + y) = per τ x + per τ y := by
  ext k
  simp only [per, Pi.add_apply, Complex.ofReal_add, Matrix.vecMul, dotProduct, add_mul,
    Finset.sum_add_distrib]
  ring

/- English proof (translation)
Establish `hτ' : ∀ i k, ContDiffOn ℝ ∞ (fun b => τ b i k) B` using `fun i k => ((GlobalTheory.FlatSmooth.analyticOnNhd_of_differentiableOn hτ.1 (hτ.2.1 i k)).contDiffOn hτ.1.uniqueDiffOn).restrict_scalars ℝ`. Use `contDiffOn_pi.2 fun k => ?_` and prove the remaining obligations. Simplify using `only [per, Pi.add_apply, Matrix.vecMul, dotProduct]`. Conclude with `(ContDiffOn.sum fun i _ => contDiffOn_const.mul (hτ' i k)).add contDiffOn_const`.
-/
theorem contDiffOn_per [FiniteDimensional ℂ E] {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ} (hτ : IsPeriodMap B τ)
    (x : Fl g) : ContDiffOn ℝ ∞ (fun b => per (τ b) x) B := by
  have hτ' : ∀ i k, ContDiffOn ℝ ∞ (fun b => τ b i k) B := fun i k =>
    ((GlobalTheory.FlatSmooth.analyticOnNhd_of_differentiableOn hτ.1 (hτ.2.1 i k)).contDiffOn
      hτ.1.uniqueDiffOn).restrict_scalars ℝ
  refine contDiffOn_pi.2 fun k => ?_
  simp only [per, Pi.add_apply, Matrix.vecMul, dotProduct]
  exact (ContDiffOn.sum fun i _ => contDiffOn_const.mul (hτ' i k)).add contDiffOn_const

/- English proof (translation)
Establish `hmaps : MapsTo (transl τ x) (cov B g) (cov B g)` using `fun P hP => ⟨hP.1, trivial⟩`. Establish `hc : ContDiffOn ℝ ∞ (fun b => per (τ b) x) B` using `contDiffOn_per hτ x`. Establish `hT : ContDiffOn ℝ ∞ (transl τ x) (cov B g)` using `contDiffOn_fst.prodMk (contDiffOn_snd.add (hc.comp contDiffOn_fst fun P hP => hP.1))`. Establish `hh' : ContDiffOn ℝ ∞ (fun P => h (transl τ x P)) (cov B g)` using `hh.comp hT hmaps`. Establish `hpos' : ∀ P ∈ cov B g, 0 < h (transl τ x P)` using `fun P hP => hpos _ (hmaps hP)`.

Establish `hE` using `GlobalTheory.T.superconn_square_period_function hτ hh' hpos' β u hc hb hf z`. Unfold `curv`. Rewrite using `[← hE]`. Establish `hopen : IsOpen (cov B g)` using `hτ.1.prod isOpen_univ`. Establish `hmem : ((b, z) : Pt E g) ∈ cov B g` using `⟨hb, trivial⟩`.

Establish `key : (superconn τ (fun P => h (transl τ x P)) β u fun P => f (P.2 + per (τ P.1) x)) =ᶠ[𝓝 (b, z)] fun Q => superconn τ h β u (fun P => f P.2) (transl τ x Q)` using `by filter_upwards [hopen.mem_nhds hmem] with Q hQ`. Conclude with `GlobalTheory.T.superconn_comp_period_translation hτ h β u x (fun P => f P.2) hQ.1`. Rewrite using `[superconn_congr _ _ _ _ key]`. Conclude with `GlobalTheory.T.superconn_comp_period_translation hτ h β u x _ hb`.
-/
theorem curv_transl [FiniteDimensional ℂ E] {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}
    (hτ : IsPeriodMap B τ) {h : Pt E g → ℝ} (hh : ContDiffOn ℝ ∞ h (cov B g))
    (hpos : ∀ P ∈ cov B g, 0 < h P) (β : Fin n → E) (u : ℝ) (x : Fl g) {b : E} (hb : b ∈ B)
    {f : (Fin g → ℂ) → Ext (n + n + g)} (hf : ContDiff ℝ ∞ f) (z : Fin g → ℂ) :
    curv τ (fun P => h (transl τ x P)) β b u (fun y => f (y + per (τ b) x)) z =
      curv τ h β b u f (z + per (τ b) x) := by
  have hmaps : MapsTo (transl τ x) (cov B g) (cov B g) := fun P hP => ⟨hP.1, trivial⟩
  have hc : ContDiffOn ℝ ∞ (fun b => per (τ b) x) B := contDiffOn_per hτ x
  have hT : ContDiffOn ℝ ∞ (transl τ x) (cov B g) :=
    contDiffOn_fst.prodMk (contDiffOn_snd.add (hc.comp contDiffOn_fst fun P hP => hP.1))
  have hh' : ContDiffOn ℝ ∞ (fun P => h (transl τ x P)) (cov B g) := hh.comp hT hmaps
  have hpos' : ∀ P ∈ cov B g, 0 < h (transl τ x P) := fun P hP => hpos _ (hmaps hP)
  have hE := GlobalTheory.T.superconn_square_period_function hτ hh' hpos' β u hc hb hf z
  unfold curv
  rw [← hE]
  have hopen : IsOpen (cov B g) := hτ.1.prod isOpen_univ
  have hmem : ((b, z) : Pt E g) ∈ cov B g := ⟨hb, trivial⟩
  have key : (superconn τ (fun P => h (transl τ x P)) β u fun P => f (P.2 + per (τ P.1) x)) =ᶠ[𝓝 (b, z)]
      fun Q => superconn τ h β u (fun P => f P.2) (transl τ x Q) := by
    filter_upwards [hopen.mem_nhds hmem] with Q hQ
    exact GlobalTheory.T.superconn_comp_period_translation hτ h β u x (fun P => f P.2) hQ.1
  rw [superconn_congr _ _ _ _ key]
  exact GlobalTheory.T.superconn_comp_period_translation hτ h β u x _ hb

/- English proof (translation)
The claim follows from `(MeasureTheory.measurePreserving_add_right MeasureTheory.volume x).setIntegral_preimage_emb (MeasurableEquiv.addRight x).measurableEmbedding G D`.
-/
theorem setIntegral_add_right' {F' : Type} [NormedAddCommGroup F'] [NormedSpace ℝ F'] (D : Set (Fl g))
    (x : Fl g) (G : Fl g → F') :
    ∫ y in (· + x) ⁻¹' D, G (y + x) = ∫ y in D, G y :=
  (MeasureTheory.measurePreserving_add_right MeasureTheory.volume x).setIntegral_preimage_emb
    (MeasurableEquiv.addRight x).measurableEmbedding G D

open MeasureTheory

/- English proof (translation)
Introduce `E _ _ _ g n B τ M j h hD x β b hb T hT`. Take `⟨F, ⟨D, hDf, hK⟩, hMel⟩` from `hT`. Take `⟨hτ, -, -, hh⟩` from `hD`. Use `⟨F, ⟨(· + x) ⁻¹' D, ?_, fun u hu => ?_⟩, hMel⟩` and prove the remaining obligations. Use `hDf.preimage_of_equiv (measurePreserving_add_right volume x).quasiMeasurePreserving Function.bijective_id fun l y => ?_` and prove the remaining obligations.

Simplify using `only [id, vadd_eq_add, Submodule.vadd_def, add_assoc]`. Take `⟨K, hKh, hF⟩` from `hK u hu`. Use `⟨fun t z z' => K t (z + per (τ b) x) (z' + per (τ b) x), ⟨?_, ?_, ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Conclude with `hKh.1.comp (contDiff_fst.prodMk ((contDiff_snd.fst.add contDiff_const).prodMk (contDiff_snd.snd.add contDiff_const))).contDiffOn fun a ha => ⟨ha.1, trivial⟩`. Introduce `t ht l hl z z'`.

Establish `e` using `hKh.2.1 t ht l hl (z + per (τ b) x) (z' + per (τ b) x)`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Simplify using `only [translPullFactor, transl]`. Rewrite using `[add_right_comm z]`. Conclude with `e.1`.

Simplify using `only [translPullFactor, transl]`. Rewrite using `[add_right_comm z']`. Conclude with `e.2`. Introduce `t ht z z' w`. Establish `hf : ContDiff ℝ ∞ (fun y => K t y (z' + per (τ b) x) w)`.

Establish `h1 : ContDiffOn ℝ ∞ (fun y => K t y (z' + per (τ b) x)) univ` using `hKh.1.comp (f := fun y : Fin g → ℂ => (t, y, z' + per (τ b) x)) (contDiff_const.prodMk (contDiff_id.prodMk contDiff_const)).contDiffOn fun y _ => ⟨ht, trivial⟩`. Conclude with `((ContinuousLinearMap.apply ℂ (Ext (n + n + g)) w).restrictScalars ℝ).contDiff.comp (contDiffOn_univ.1 h1)`. Establish `e` using `curv_transl hτ hh.1 hh.2.1 β u x hb hf z`. Simplify using `only at e ⊢`. Rewrite using `[e]`.

Conclude with `hKh.2.2.1 t ht (z + per (τ b) x) (z' + per (τ b) x) w`. Introduce `f hf`. Establish `hf' : IsSec τ M j b (fun y => f (y - per (τ b) x))`. Use `⟨hf.1.comp (contDiff_id.sub contDiff_const), fun l hl z => ?_⟩` and prove the remaining obligations. Establish `e` using `hf.2 l hl (z - per (τ b) x)`.

Simplify using `only [translPullFactor, transl, sub_add_cancel] at e`. Use `show f (z + per (τ b) l - per (τ b) x) = j l (b, z) • f (z - per (τ b) x)`. Rewrite using `[show z + per (τ b) l - per (τ b) x = z - per (τ b) x + per (τ b) l by abel, e]`. Establish `h1` using `(hKh.2.2.2 _ hf').comp (· + per (τ b) x) (continuous_id.add continuous_const)`. Use `h1 using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `t z`. Simplify using `only [Function.comp]`. Rewrite using `[← setIntegral_add_right' D x]`. Use `congr 1`. Use function extensionality and compare the values at `y`.

Rewrite using `[per_add', add_sub_cancel_right]`. Use function extensionality and compare the values at `z`. Simplify using the standard rewrite rules. Rewrite using `[hF]`. Use `congr 1`.

Rewrite using `[← setIntegral_add_right' D x (fun y => strN (K 1 (per (τ b) y) (per (τ b) y)))]`. Simplify using `only [per_add']`.
-/
theorem translationInv : TranslationInv := by
  intro E _ _ _ g n B τ M j h hD x β b hb T hT
  obtain ⟨F, ⟨D, hDf, hK⟩, hMel⟩ := hT
  obtain ⟨hτ, -, -, hh⟩ := hD
  refine ⟨F, ⟨(· + x) ⁻¹' D, ?_, fun u hu => ?_⟩, hMel⟩
  · refine hDf.preimage_of_equiv (measurePreserving_add_right volume x).quasiMeasurePreserving
      Function.bijective_id fun l y => ?_
    simp only [id, vadd_eq_add, Submodule.vadd_def, add_assoc]
  obtain ⟨K, hKh, hF⟩ := hK u hu
  refine ⟨fun t z z' => K t (z + per (τ b) x) (z' + per (τ b) x), ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · exact hKh.1.comp (contDiff_fst.prodMk ((contDiff_snd.fst.add contDiff_const).prodMk
      (contDiff_snd.snd.add contDiff_const))).contDiffOn fun a ha => ⟨ha.1, trivial⟩
  · intro t ht l hl z z'
    have e := hKh.2.1 t ht l hl (z + per (τ b) x) (z' + per (τ b) x)
    refine ⟨?_, ?_⟩
    · simp only [translPullFactor, transl]
      rw [add_right_comm z]
      exact e.1
    · simp only [translPullFactor, transl]
      rw [add_right_comm z']
      exact e.2
  · intro t ht z z' w
    have hf : ContDiff ℝ ∞ (fun y => K t y (z' + per (τ b) x) w) := by
      have h1 : ContDiffOn ℝ ∞ (fun y => K t y (z' + per (τ b) x)) univ :=
        hKh.1.comp (f := fun y : Fin g → ℂ => (t, y, z' + per (τ b) x))
          (contDiff_const.prodMk (contDiff_id.prodMk contDiff_const)).contDiffOn
          fun y _ => ⟨ht, trivial⟩
      exact ((ContinuousLinearMap.apply ℂ (Ext (n + n + g)) w).restrictScalars ℝ).contDiff.comp
        (contDiffOn_univ.1 h1)
    have e := curv_transl hτ hh.1 hh.2.1 β u x hb hf z
    simp only at e ⊢
    rw [e]
    exact hKh.2.2.1 t ht (z + per (τ b) x) (z' + per (τ b) x) w
  · intro f hf
    have hf' : IsSec τ M j b (fun y => f (y - per (τ b) x)) := by
      refine ⟨hf.1.comp (contDiff_id.sub contDiff_const), fun l hl z => ?_⟩
      have e := hf.2 l hl (z - per (τ b) x)
      simp only [translPullFactor, transl, sub_add_cancel] at e
      show f (z + per (τ b) l - per (τ b) x) = j l (b, z) • f (z - per (τ b) x)
      rw [show z + per (τ b) l - per (τ b) x = z - per (τ b) x + per (τ b) l by abel, e]
    have h1 := (hKh.2.2.2 _ hf').comp (· + per (τ b) x) (continuous_id.add continuous_const)
    convert h1 using 1
    · funext t z
      simp only [Function.comp]
      rw [← setIntegral_add_right' D x]
      congr 1
      funext y
      rw [per_add', add_sub_cancel_right]
    · funext z
      simp
  · rw [hF]
    congr 1
    rw [← setIntegral_add_right' D x (fun y => strN (K 1 (per (τ b) y) (per (τ b) y)))]
    simp only [per_add']

end GlobalTheory.TorsionForm.TranslInv
