import Mathlib
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.RigFrame
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.UnitFramesGeneratorRatioModulusOne

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif GlobalTheory.FrameNorm
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.FrameNorm

open GlobalTheory.UnitFrameGen MeasureTheory in

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo σ' g ty F i P' P h x' x s' s a m' m hp' hp hg hu' hxx hbc hA' hA`. Take `⟨Hm, χ, fr, θ, Fd, hH, -, him, hd, hn, hc, h0, ha, hv, hF, hI⟩` from `hA`. Take `⟨Hm', χ', fr', θ', Fd', hH', -, him', hd', hn', hc', h0', ha', hv', hF', hI'⟩` from `hA'`. Take `⟨hdet, huu, hex⟩` from `GlobalTheory.FamRigid.ex_eq_of_level_group GlobalTheory.latMinkowski E H Dw l Xo _ g _ F i P P' (LinearEquiv.refl _ _) h hp hp' (fun _ _ => rfl) (fun _ _ => ⟨0, by simp⟩) (fun _ => ⟨0, by simp⟩) hg`. Establish `hspan : Submodule.span ℝ (P.range : Set (Fin g → ℂ)) = ⊤`.

Rewrite using `[AddMonoidHom.coe_range]`. Conclude with `hp.2.2.2.1`. Establish `hHH : ∀ z w, hermForm Hm' (h *ᵥ z) (h *ᵥ w) = hermForm Hm z w` using `hermForm_eq_of_im _ hspan Hm Hm' h (by`. Introduce and unpack `_ ⟨a, rfl⟩ _ ⟨b, rfl⟩`. Rewrite using `[← hg, ← hg, him, him'])`.

Establish `hexp : ∀ a ∈ P.range, ∀ z, F.ex i P (z + a) = F.ex i P z` using `fun a ha z => by`. Rewrite using `[F.ex_add i P hp, (F.ex_ker i P hp a).2 ha]`. Conclude with `@_root_.mul_one _ (CategoryTheory.Hom.monoid).toMulOneClass _`. Establish `hcov : ∀ z, ∃ j, ⊤ ≤ (F.ex i P z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j` using `fun z => GlobalTheory.ThetaPtChg.exists_chart_point Xo.univ.t.PP.isLB _`. Establish `tr : ∀ j z, ⊤ ≤ (F.ex i P z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → ⊤ ≤ (F.ex i P' (h *ᵥ z)).left ⁻¹ᵁ Xo.univ.t.PP.L.U j` using `fun j z hz => by rw [hex]; exact hz`.

Establish `hm : ∀ j, ∀ a ∈ P.range, ∀ z, ⊤ ≤ (F.ex i P z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → ‖fr j z‖ = Real.exp (Real.pi * (hermForm Hm z a).re + Real.pi / 2 * (hermForm Hm a a).re) * ‖fr j (z + a)‖`. Introduce and unpack `j _ ⟨a, rfl⟩ z hz`. Conclude with `norm_factor Hm _ _ _ _ _ (ha a j z).1 ((ha a j z).2 hz)`. Establish `dl : Differentiable ℂ (fun z' : Fin g → ℂ => h *ᵥ z')` using `(LinearMap.toContinuousLinearMap (Matrix.mulVecLin h)).differentiable`. Establish `hfr : ∀ j z, ⊤ ≤ (F.ex i P z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr' j (h *ᵥ z) = fr j z` using `frames_eq P.range hspan (fun j => {z | ⊤ ≤ (F.ex i P z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j}) (fun j => GlobalTheory.FamilyUnif_isOpen_ex F i P hp _) hcov (fun j a ha z hz => by rw [Set.mem_setOf_eq, hexp a ha]; exact hz) fr (fun j z => fr' j (h *ᵥ z)) (fun j j' z => valAt' (F.ex i P z). …`.

Establish `e2` using `hc' j j' (h *ᵥ z) ((top_le_preimage_inf _ _ _).2 ⟨tr _ _ h1, tr _ _ h2⟩)`. Rewrite `e2` using `[hex]`. Conclude with `e2)`. Use the proof step `(fun j hz => by`. Establish `t0` using `tr j 0 hz`.

Simplify using `only [Matrix.mulVec_zero] at t0 ⊢`. Rewrite using `[h0 j hz, h0' j t0, hxx])`. Use `hm (by`. Introduce and unpack `j _ ⟨a, rfl⟩ z hz`. Use `norm_factor Hm' _ _ _ _ _ (ha' a j (h *ᵥ z)).1 ((ha' a j (h *ᵥ z)).2 (tr j z hz))` as an intermediate fact.

Rewrite `this` using `[hg, hHH, hHH, ← Matrix.mulVec_add]`. Conclude with `this)`. Establish `hS : Out.SecTwistSt` using `GlobalTheory.abelianSchemeLaws_all.2.secTwist`. Establish `hw0 : ∀ z, (F.ex i P z).left ≫ Xo.univ.t.G.hom = x'` using `fun z => by`. Rewrite using `[← hex z]`.

Conclude with `(Over.w (F.ex i P' (h *ᵥ z))).trans hu'.symm`. Establish `hθ : ∀ z, θ z = a * θ' (h *ᵥ z)` using `fun z => by`. Take `⟨j, hj⟩` from `hcov z`. Establish `hval` using `GlobalTheory.ThetaPtChg.val_of_secBC hS (Xo := Xo) _ _ hxx _ _ _ hbc (Over.homMk (F.ex i P z).left (hw0 z)) j _ _ (fun pt h1 h2 => hv' j (h *ᵥ z) pt (h1.trans (hex z).symm) h2 (tr j z hj)) (fun pt h1 h2 => hv j z pt h1 h2 hj)`. Rewrite `hval` using `[hfr j z hj, ← mul_assoc]`.

Conclude with `mul_right_cancel₀ (hn j z hj) hval`. Establish `hθp : ∀ b ∈ P.range, ∀ z, ‖θ' (h *ᵥ (z + b))‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm (z + b) (z + b)).re) = ‖θ' (h *ᵥ z)‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm z z).re)` using `fun b hb z => by`. Take `⟨j, hj⟩` from `hcov z`. Establish `hj' : ⊤ ≤ (F.ex i P (z + b)).left ⁻¹ᵁ Xo.univ.t.PP.L.U j` using `by rw [hexp b hb]; exact hj`. Set `p : Over.mk x' ⟶ Xo.univ.t.G` to `Over.homMk (F.ex i P z).left (hw0 z)`.

Establish `e1` using `congrArg CommaMorphism.left (CartesianMonoidalCategory.lift_snd (𝟙 _) p)`. Establish `e2` using `congrArg CommaMorphism.left (CartesianMonoidalCategory.lift_fst (𝟙 _) p)`. Establish `v1` using `hv' j (h *ᵥ z) _ (by rw [hex]; exact e1) e2 (tr j z hj)`. Establish `v2` using `hv' j (h *ᵥ (z + b)) _ (by rw [hex, hexp b hb]; exact e1) e2 (tr j _ hj')`. Rewrite `v1` using `[hfr j _ hj]`.

Rewrite `v2` using `[hfr j _ hj']`. Conclude with `normSq_periodic hH _ _ _ _ z b (hn j _ hj') (v2.symm.trans v1) (hm j b hb z hj)`. Use `haveI : Countable P.range := by haveI := hp.2.2.1`. Conclude with `TopologicalSpace.separableSpace_iff_countable.1 inferInstance`. Establish `hinj : Function.Injective (fun z : Fin g → ℂ => h *ᵥ z)` using `Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det h).2 hdet)`.

Establish `hmean` using `mean_comp_eq P.range P'.range h hdet (fun z => ⟨?_, ?_⟩) Fd Fd' hF hF' (fun z => ‖θ' z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm' z z).re)) (fun b hb z => by simp only [hHH, hθp b hb z])`. Rewrite using `[← hI, ← hI', ← hmean, ← mul_div_assoc, ← integral_const_mul]`. Use `congr 2`. Use function extensionality and compare the values at `z`. Rewrite using `[hθ, hHH, norm_mul, mul_pow, mul_assoc]`.

Introduce and unpack `⟨b, hb⟩`. Use `⟨b, hinj ?_⟩` and prove the remaining obligations. Simplify using `only`. Rewrite using `[← hg, hb]`. Introduce and unpack `⟨b, rfl⟩`.

Conclude with `⟨b, hg b⟩`.
-/
theorem ahMean_eq_of_secBC : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (σ' : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ' ty) (k : Fin F.n) (P P' : (F.Di k).La →+ (Fin g → ℂ)) (h₀ : Matrix (Fin g) (Fin g) ℂ) (x x' : Sp ℂ ⟶ Xo.X) (s : LB.Sec (PPx x)) (s' : LB.Sec (PPx x')) (a : ℂ) (m m' : ℝ), IsPeriod (F.Di k) ty P → IsPeriod (F.Di k) ty P' → (∀ v, P v = h₀ *ᵥ P' v) → x = F.u k P → x' = x → SecBC (RingHom.id ℂ) a x x' s s' → AHMean F k P x s m → AHMean F k P' x' s' m' → m' = ‖a‖ ^ 2 * m := by
  intro E _ _ _ H Dw l Xo σ' g ty F i P' P h x' x s' s a m' m hp' hp hg hu' hxx hbc hA' hA
  obtain ⟨Hm, χ, fr, θ, Fd, hH, -, him, hd, hn, hc, h0, ha, hv, hF, hI⟩ := hA
  obtain ⟨Hm', χ', fr', θ', Fd', hH', -, him', hd', hn', hc', h0', ha', hv', hF', hI'⟩ := hA'
  obtain ⟨hdet, huu, hex⟩ := GlobalTheory.FamRigid.ex_eq_of_level_group GlobalTheory.latMinkowski E H Dw l Xo _ g _ F i
    P P' (LinearEquiv.refl _ _) h hp hp' (fun _ _ => rfl) (fun _ _ => ⟨0, by simp⟩) (fun _ => ⟨0, by simp⟩) hg
  have hspan : Submodule.span ℝ (P.range : Set (Fin g → ℂ)) = ⊤ := by
    rw [AddMonoidHom.coe_range]; exact hp.2.2.2.1
  have hHH : ∀ z w, hermForm Hm' (h *ᵥ z) (h *ᵥ w) = hermForm Hm z w :=
    hermForm_eq_of_im _ hspan Hm Hm' h (by
      rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      rw [← hg, ← hg, him, him'])
  have hexp : ∀ a ∈ P.range, ∀ z, F.ex i P (z + a) = F.ex i P z := fun a ha z => by
    rw [F.ex_add i P hp, (F.ex_ker i P hp a).2 ha]
    exact @_root_.mul_one _ (CategoryTheory.Hom.monoid).toMulOneClass _
  have hcov : ∀ z, ∃ j, ⊤ ≤ (F.ex i P z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := fun z =>
    GlobalTheory.ThetaPtChg.exists_chart_point Xo.univ.t.PP.isLB _
  have tr : ∀ j z, ⊤ ≤ (F.ex i P z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      ⊤ ≤ (F.ex i P' (h *ᵥ z)).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := fun j z hz => by rw [hex]; exact hz
  have hm : ∀ j, ∀ a ∈ P.range, ∀ z, ⊤ ≤ (F.ex i P z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → ‖fr j z‖ =
      Real.exp (Real.pi * (hermForm Hm z a).re + Real.pi / 2 * (hermForm Hm a a).re) * ‖fr j (z + a)‖ := by
    rintro j _ ⟨a, rfl⟩ z hz
    exact norm_factor Hm _ _ _ _ _ (ha a j z).1 ((ha a j z).2 hz)
  have dl : Differentiable ℂ (fun z' : Fin g → ℂ => h *ᵥ z') :=
    (LinearMap.toContinuousLinearMap (Matrix.mulVecLin h)).differentiable
  have hfr : ∀ j z, ⊤ ≤ (F.ex i P z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr' j (h *ᵥ z) = fr j z :=
    frames_eq P.range hspan (fun j => {z | ⊤ ≤ (F.ex i P z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j})
      (fun j => GlobalTheory.FamilyUnif_isOpen_ex F i P hp _) hcov
      (fun j a ha z hz => by rw [Set.mem_setOf_eq, hexp a ha]; exact hz)
      fr (fun j z => fr' j (h *ᵥ z))
      (fun j j' z => valAt' (F.ex i P z).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j')
        (Xo.univ.t.PP.L.g j j').val)
      (fun a z => Real.exp (Real.pi * (hermForm Hm z a).re + Real.pi / 2 * (hermForm Hm a a).re))
      hd (fun j => (hd' j).comp dl.differentiableOn fun z hz => tr j z hz) hn
      (fun j j' z h1 h2 => hc j j' z ((top_le_preimage_inf _ _ _).2 ⟨h1, h2⟩))
      (fun j j' z h1 h2 => by
        have e2 := hc' j j' (h *ᵥ z) ((top_le_preimage_inf _ _ _).2 ⟨tr _ _ h1, tr _ _ h2⟩)
        rw [hex] at e2
        exact e2)
      (fun j hz => by
        have t0 := tr j 0 hz
        simp only [Matrix.mulVec_zero] at t0 ⊢
        rw [h0 j hz, h0' j t0, hxx])
      hm (by
        rintro j _ ⟨a, rfl⟩ z hz
        have := norm_factor Hm' _ _ _ _ _ (ha' a j (h *ᵥ z)).1 ((ha' a j (h *ᵥ z)).2 (tr j z hz))
        rw [hg, hHH, hHH, ← Matrix.mulVec_add] at this
        exact this)
  have hS : Out.SecTwistSt := GlobalTheory.abelianSchemeLaws_all.2.secTwist
  have hw0 : ∀ z, (F.ex i P z).left ≫ Xo.univ.t.G.hom = x' := fun z => by
    rw [← hex z]
    exact (Over.w (F.ex i P' (h *ᵥ z))).trans hu'.symm
  have hθ : ∀ z, θ z = a * θ' (h *ᵥ z) := fun z => by
    obtain ⟨j, hj⟩ := hcov z
    have hval := GlobalTheory.ThetaPtChg.val_of_secBC hS (Xo := Xo) _ _ hxx _ _ _ hbc
      (Over.homMk (F.ex i P z).left (hw0 z)) j _ _
      (fun pt h1 h2 => hv' j (h *ᵥ z) pt (h1.trans (hex z).symm) h2 (tr j z hj))
      (fun pt h1 h2 => hv j z pt h1 h2 hj)
    rw [hfr j z hj, ← mul_assoc] at hval
    exact mul_right_cancel₀ (hn j z hj) hval
  have hθp : ∀ b ∈ P.range, ∀ z, ‖θ' (h *ᵥ (z + b))‖ ^ 2 *
      Real.exp (-Real.pi * (hermForm Hm (z + b) (z + b)).re) =
      ‖θ' (h *ᵥ z)‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm z z).re) := fun b hb z => by
    obtain ⟨j, hj⟩ := hcov z
    have hj' : ⊤ ≤ (F.ex i P (z + b)).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := by rw [hexp b hb]; exact hj
    let p : Over.mk x' ⟶ Xo.univ.t.G := Over.homMk (F.ex i P z).left (hw0 z)
    have e1 := congrArg CommaMorphism.left (CartesianMonoidalCategory.lift_snd (𝟙 _) p)
    have e2 := congrArg CommaMorphism.left (CartesianMonoidalCategory.lift_fst (𝟙 _) p)
    have v1 := hv' j (h *ᵥ z) _ (by rw [hex]; exact e1) e2 (tr j z hj)
    have v2 := hv' j (h *ᵥ (z + b)) _ (by rw [hex, hexp b hb]; exact e1) e2 (tr j _ hj')
    rw [hfr j _ hj] at v1
    rw [hfr j _ hj'] at v2
    exact normSq_periodic hH _ _ _ _ z b (hn j _ hj') (v2.symm.trans v1) (hm j b hb z hj)
  haveI : Countable P.range := by
    haveI := hp.2.2.1
    exact TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have hinj : Function.Injective (fun z : Fin g → ℂ => h *ᵥ z) :=
    Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det h).2 hdet)
  have hmean := mean_comp_eq P.range P'.range h hdet (fun z => ⟨?_, ?_⟩) Fd Fd' hF hF'
    (fun z => ‖θ' z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm' z z).re))
    (fun b hb z => by simp only [hHH, hθp b hb z])
  · rw [← hI, ← hI', ← hmean, ← mul_div_assoc, ← integral_const_mul]
    congr 2
    funext z
    rw [hθ, hHH, norm_mul, mul_pow, mul_assoc]
  · rintro ⟨b, hb⟩
    refine ⟨b, hinj ?_⟩
    simp only
    rw [← hg, hb]
  · rintro ⟨b, rfl⟩
    exact ⟨b, hg b⟩

end GlobalTheory.FrameNorm
