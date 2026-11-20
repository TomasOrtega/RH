import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDIdentSpec
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OperatorPreservesFusionForms
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SumDualVectorEqZeta
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAdjointnessFromHermitian
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTRadAdj

open MeasureTheory Filter Topology
open scoped Matrix ContDiff InnerProductSpace ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE.QQA

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P.CutSE

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Loc

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ}

/- English proof (translation)
Introduce `_ _` and use `⟨Set.univ, fun _ => 0, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩`.
-/
theorem smoothLev_zero {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (D : Set (Mx k r)) :
    SmoothLev k r (Fin.last r) D (fun _ : Mx k r => (0 : E)) :=
  fun _ _ => ⟨Set.univ, fun _ => 0, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩

/- English proof (translation)
Introduce `g₀ hg₀` and use `hf g₀ ⟨hg₀.1, h hg₀.2⟩`.
-/
theorem smoothLev_mono {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {D D' : Set (Mx k r)} (h : D ⊆ D')
    {f : Mx k r → E} (hf : SmoothLev k r (Fin.last r) D' f) : SmoothLev k r (Fin.last r) D f :=
  fun g₀ hg₀ => hf g₀ ⟨hg₀.1, h hg₀.2⟩

/- English proof (translation)
Establish `h` using `(Formalism.FourierDecayAlt.P.transfer_linear_local E k r z z' (Fin.last r) D Y p q (fun _ => (0 : E)) (fun _ => (0 : E)) 1 hD (smoothLev_zero D) (smoothLev_zero D) g hg).1`. Simplify using `only [smul_zero, add_zero, one_smul] at h`. Establish `h2 : tL k r z z' (Fin.last r) Y p q (fun _ : Mx k r => (0 : E)) g + tL k r z z' (Fin.last r) Y p q (fun _ : Mx k r => (0 : E)) g = tL k r z z' (Fin.last r) Y p q (fun _ : Mx k r => (0 : E)) g + 0`. Rewrite using `[add_zero]`. Conclude with `h.symm`.

Conclude with `add_left_cancel h2`.
-/
theorem tL_zero_at {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {D : Set (Mx k r)} (hD : IsOpen D) (Y : ℂ)
    (p q : Fin 2) {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r) ∩ D) :
    tL k r z z' (Fin.last r) Y p q (fun _ : Mx k r => (0 : E)) g = 0 := by
  have h := (Formalism.FourierDecayAlt.P.transfer_linear_local E k r z z' (Fin.last r) D Y p q (fun _ => (0 : E)) (fun _ => (0 : E)) 1 hD
    (smoothLev_zero D) (smoothLev_zero D) g hg).1
  simp only [smul_zero, add_zero, one_smul] at h
  have h2 : tL k r z z' (Fin.last r) Y p q (fun _ : Mx k r => (0 : E)) g +
      tL k r z z' (Fin.last r) Y p q (fun _ : Mx k r => (0 : E)) g =
      tL k r z z' (Fin.last r) Y p q (fun _ : Mx k r => (0 : E)) g + 0 := by
    rw [add_zero]; exact h.symm
  exact add_left_cancel h2

/- English proof (translation)
Rewrite using `[(Formalism.FourierDecayAlt.P.transfer_linear_local E k r z z' (Fin.last r) D Y p q f (fun _ => (0 : E)) 0 hD hf (smoothLev_zero D) g hg).2 h0]`. Conclude with `tL_zero_at hD Y p q hg`.
-/
theorem tL_eq_zero_local {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {D : Set (Mx k r)} (hD : IsOpen D)
    {f : Mx k r → E} (hf : SmoothLev k r (Fin.last r) D f) (h0 : ∀ x ∈ Glev k r (Fin.last r) ∩ D, f x = 0) (Y : ℂ)
    (p q : Fin 2) {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r) ∩ D) : tL k r z z' (Fin.last r) Y p q f g = 0 := by
  rw [(Formalism.FourierDecayAlt.P.transfer_linear_local E k r z z' (Fin.last r) D Y p q f (fun _ => (0 : E)) 0 hD hf (smoothLev_zero D)
    g hg).2 h0]
  exact tL_zero_at hD Y p q hg

/- English proof (translation)
Establish `: LocallyCompactSpace (Mx k r)` using `(inferInstance : LocallyCompactSpace (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ))`. Take `⟨L, hLc, hKL, hLD⟩` from `exists_compact_between hKc (Qx5.Dp_open k r z z') hKD`. Take `⟨f₁, hsupp, hf₁, hrange⟩` from `(isOpen_interior : IsOpen (interior L)).exists_contDiff_support_eq (n := ⊤)`. Establish `hf₁c : Continuous f₁` using `hf₁.continuous`. Establish `hpos : ∀ g ∈ Kc, 0 < f₁ g` using `fun g hg => by`.

Establish `h1 : g ∈ Function.support f₁` using `by rw [hsupp]; exact hKL hg`. Conclude with `lt_of_le_of_ne (hrange ⟨g, rfl⟩).1 (Ne.symm h1)`. Choose the witnesses or unpack the hypotheses as in `⟨m, hm, hmK⟩ : ∃ m : ℝ, 0 < m ∧ ∀ g ∈ Kc, m ≤ f₁ g := by`. Break down `Kc.eq_empty_or_nonempty with h | h` into its components or cases. Conclude with `⟨1, one_pos, by simp [h]⟩`.

Take `⟨g₁, hg₁, hmin⟩` from `hKc.exists_isMinOn h hf₁c.continuousOn`. Conclude with `⟨f₁ g₁, hpos g₁ hg₁, fun g hg => hmin hg⟩`. Use `⟨fun g => Real.smoothTransition (2 * f₁ g / m), {g | m / 2 < f₁ g}, L, Real.smoothTransition.contDiff.comp ((contDiff_const.mul hf₁).div_const m), isOpen_lt continuous_const hf₁c, fun g hg => by have := hmK g hg; show m / 2 < f₁ g; linarith, hLc, hLD, fun g hg => ?_, fun g hg => …` and prove the remaining obligations. Establish `hg' : m / 2 < f₁ g` using `hg`. Conclude with `Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ hm]; linarith)`.

Establish `h0 : f₁ g = 0`. Assume the negation of the conclusion as `h`. Establish `h1 : g ∈ Function.support f₁` using `h`. Rewrite `h1` using `[hsupp]`. Conclude with `hg (interior_subset h1)`.

Use `show Real.smoothTransition (2 * f₁ g / m) = 0`. Rewrite using `[h0, mul_zero, zero_div]`. Conclude with `Real.smoothTransition.zero_of_nonpos le_rfl`.
-/
theorem bump_exists {Kc : Set (Mx k r)} (hKc : IsCompact Kc) (hKD : Kc ⊆ Qx5.Dp k r z z') :
    ∃ (χ : Mx k r → ℝ) (O L : Set (Mx k r)), ContDiff ℝ ∞ χ ∧ IsOpen O ∧ Kc ⊆ O ∧ IsCompact L ∧
      L ⊆ Qx5.Dp k r z z' ∧ (∀ g ∈ O, χ g = 1) ∧ ∀ g, g ∉ L → χ g = 0 := by
  have : LocallyCompactSpace (Mx k r) :=
    (inferInstance : LocallyCompactSpace (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ))
  obtain ⟨L, hLc, hKL, hLD⟩ := exists_compact_between hKc (Qx5.Dp_open k r z z') hKD
  obtain ⟨f₁, hsupp, hf₁, hrange⟩ := (isOpen_interior : IsOpen (interior L)).exists_contDiff_support_eq (n := ⊤)
  have hf₁c : Continuous f₁ := hf₁.continuous
  have hpos : ∀ g ∈ Kc, 0 < f₁ g := fun g hg => by
    have h1 : g ∈ Function.support f₁ := by rw [hsupp]; exact hKL hg
    exact lt_of_le_of_ne (hrange ⟨g, rfl⟩).1 (Ne.symm h1)
  obtain ⟨m, hm, hmK⟩ : ∃ m : ℝ, 0 < m ∧ ∀ g ∈ Kc, m ≤ f₁ g := by
    rcases Kc.eq_empty_or_nonempty with h | h
    · exact ⟨1, one_pos, by simp [h]⟩
    · obtain ⟨g₁, hg₁, hmin⟩ := hKc.exists_isMinOn h hf₁c.continuousOn
      exact ⟨f₁ g₁, hpos g₁ hg₁, fun g hg => hmin hg⟩
  refine ⟨fun g => Real.smoothTransition (2 * f₁ g / m), {g | m / 2 < f₁ g}, L,
    Real.smoothTransition.contDiff.comp ((contDiff_const.mul hf₁).div_const m),
    isOpen_lt continuous_const hf₁c, fun g hg => by have := hmK g hg; show m / 2 < f₁ g; linarith, hLc, hLD,
    fun g hg => ?_, fun g hg => ?_⟩
  · have hg' : m / 2 < f₁ g := hg
    exact Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ hm]; linarith)
  · have h0 : f₁ g = 0 := by
      by_contra h
      have h1 : g ∈ Function.support f₁ := h
      rw [hsupp] at h1
      exact hg (interior_subset h1)
    show Real.smoothTransition (2 * f₁ g / m) = 0
    rw [h0, mul_zero, zero_div]
    exact Real.smoothTransition.zero_of_nonpos le_rfl

end Loc

section Rad

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

/- English proof (translation)
Distinguish the cases in `hx : x ∈ DomR k r z z'`. Rewrite using `[X.t_apply Y a b Ψ x hx]`. Conclude with `tL_eq_zero_local (hO.inter (Qx5.Dp_open k r z z')) (smoothLev_mono Set.inter_subset_right (Qx5.slice_smooth Ψ.2 hx.1)) (fun g hg => h0 g ⟨hg.1, hg.2.1⟩) Y a b ⟨hx.2.1, hxO, hx.2.2⟩`. Conclude with `Formalism.FourierDecayAlt.P5.radSp_zero_off _ hx`.
-/
theorem t_zero_near (X : ActualOps k r z z' π π') (Ψ : RadSp k r z z' π π') (Y : ℂ) (a b : Fin 2)
    {x : (Fin r → ℂ) × Mx k r} {O : Set (Mx k r)} (hO : IsOpen O) (hxO : x.2 ∈ O)
    (h0 : ∀ g ∈ Glev k r (Fin.last r) ∩ O, (Ψ : Fn k r (Wq →L[ℂ] Wp)) x.1 g = 0) :
    (X.t Y a b Ψ : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 = 0 := by
  by_cases hx : x ∈ DomR k r z z'
  · rw [X.t_apply Y a b Ψ x hx]
    exact tL_eq_zero_local (hO.inter (Qx5.Dp_open k r z z'))
      (smoothLev_mono Set.inter_subset_right (Qx5.slice_smooth Ψ.2 hx.1))
      (fun g hg => h0 g ⟨hg.1, hg.2.1⟩) Y a b ⟨hx.2.1, hxO, hx.2.2⟩
  · exact Formalism.FourierDecayAlt.P5.radSp_zero_off _ hx

/- English proof (translation)
Take `⟨K, hK, hKD, h0⟩` from `hΨ`. Use `⟨K, hK, hKD, fun x hx => ?_⟩` and prove the remaining obligations. Establish `hO : IsOpen {g : Mx k r | (x.1, g) ∉ K}` using `hK.isClosed.isOpen_compl.preimage (continuous_const.prodMk continuous_id)`. Conclude with `t_zero_near X Ψ Y a b hO (show (x.1, x.2) ∉ K from hx) fun g hg => h0 (x.1, g) hg.2`.
-/
theorem entry_operator_preserves_tests (X : ActualOps k r z z' π π') (Y : ℂ) (a b : Fin 2) {Ψ : RadSp k r z z' π π'} (hΨ : RTest Ψ) :
    RTest (X.t Y a b Ψ) := by
  obtain ⟨K, hK, hKD, h0⟩ := hΨ
  refine ⟨K, hK, hKD, fun x hx => ?_⟩
  have hO : IsOpen {g : Mx k r | (x.1, g) ∉ K} :=
    hK.isClosed.isOpen_compl.preimage (continuous_const.prodMk continuous_id)
  exact t_zero_near X Ψ Y a b hO (show (x.1, x.2) ∉ K from hx) fun g hg => h0 (x.1, g) hg.2

/- English proof (translation)
Take `⟨K, hK, hKD, h0⟩` from `hΨ`. Use `⟨Prod.snd '' (K ∩ Prod.fst ⁻¹' {c}), (hK.inter_right (isClosed_singleton.preimage continuous_fst)).image continuous_snd, ?_, fun g hg => h0 (c, g) fun hcg => hg ⟨(c, g), ⟨hcg, rfl⟩, rfl⟩⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨x, ⟨hxK, -⟩, rfl⟩`. Conclude with `(hKD hxK).2.2`.
-/
theorem slice_cpt {Ψ : RadSp k r z z' π π'} (hΨ : RTest Ψ) (c : Fin r → ℂ) :
    ∃ Kc : Set (Mx k r), IsCompact Kc ∧ Kc ⊆ Qx5.Dp k r z z' ∧
      ∀ g, g ∉ Kc → (Ψ : Fn k r (Wq →L[ℂ] Wp)) c g = 0 := by
  obtain ⟨K, hK, hKD, h0⟩ := hΨ
  refine ⟨Prod.snd '' (K ∩ Prod.fst ⁻¹' {c}),
    (hK.inter_right (isClosed_singleton.preimage continuous_fst)).image continuous_snd, ?_,
    fun g hg => h0 (c, g) fun hcg => hg ⟨(c, g), ⟨hcg, rfl⟩, rfl⟩⟩
  rintro _ ⟨x, ⟨hxK, -⟩, rfl⟩
  exact (hKD hxK).2.2

/- English proof (translation)
Take `⟨χ, O, L, hχs, hO, hKO, hLc, hLD, χ1, χ0⟩` from `bump_exists hKc hKD`. Take `⟨fΨ, hfΨ⟩ : ∃ f : Mx k r → ℂ, f = fun y => φ ((Ψ : Fn k r (Wq →L[ℂ] Wp)) c y)` from `⟨_, rfl⟩`. Take `⟨fΦ, hfΦ⟩ : ∃ f : Mx k r → ℂ, f = fun y => (χ y : ℂ) * φ ((Φ : Fn k r (Wq →L[ℂ] Wp)) c y)` from `⟨_, rfl⟩`. Establish `hsΨ : SmoothLev k r (Fin.last r) Set.univ fΨ`. Rewrite using `[hfΨ]`.

Conclude with `Qx5.smooth_clm φ (Qx5.smooth_univ Ψ.2 hc hKc hKD fun g _ hg => h0 g hg)`. Establish `hcΨ : CptOn k r (Fin.last r) fΨ` using `⟨Kc, hKc, fun g _ hg => by rw [hfΨ]; simp [h0 g hg]⟩`. Establish `hsΦ : SmoothLev k r (Fin.last r) Set.univ fΦ`. Introduce `g₀ hg₀`. Distinguish the cases in `hgL : g₀ ∈ L`.

Take `⟨U, F, hU, hgU, hF, he⟩` from `Qx5.smooth_clm φ (Qx5.slice_smooth Φ.2 hc) g₀ ⟨hg₀.1, hLD hgL⟩`. Use `⟨U, fun y => (χ y : ℂ) * F y, hU, hgU, (Complex.ofRealCLM.contDiff.comp_contDiffOn hχs.contDiffOn).mul hF, fun y hy hyG => ?_⟩` and prove the remaining obligations. Rewrite using `[hfΦ]`. Use `show (χ y : ℂ) * φ ((Φ : Fn k r (Wq →L[ℂ] Wp)) c y) = (χ y : ℂ) * F y`. Rewrite using `[← he y hy hyG]`.

Use `⟨Lᶜ, fun _ => 0, hLc.isClosed.isOpen_compl, hgL, contDiffOn_const, fun y hy _ => ?_⟩` and prove the remaining obligations. Rewrite using `[hfΦ]`. Use `show (χ y : ℂ) * φ ((Φ : Fn k r (Wq →L[ℂ] Wp)) c y) = 0`. Rewrite using `[χ0 y hy, Complex.ofReal_zero, zero_mul]`. Establish `hcΦ : CptOn k r (Fin.last r) fΦ` using `⟨L, hLc, fun g _ hg => by rw [hfΦ]; simp [χ0 g hg]⟩`.

Establish `hh` using `Formalism.FourierDecayAlt.P.hermitian_haar_invariance k r z z' (Fin.last r) μ hμ hz hz' fΨ fΦ hsΨ hsΦ hcΨ hcΦ (star Y) b a`. Rewrite `hh` using `[star_star]`. Establish `eA : ∀ x : Mx k r, φ ((Ψ : Fn k r (Wq →L[ℂ] Wp)) c x) * star (φ ((X.t Y a b Φ : Fn k r (Wq →L[ℂ] Wp)) c x)) = fΨ x * star (tL k r z z' (Fin.last r) Y a b fΦ x)`. Introduce `x`. Rewrite using `[Qx5.key_pt X Φ Ψ hc Y a b φ x, hfΨ]`.

Distinguish the cases in `hx0 : (Ψ : Fn k r (Wq →L[ℂ] Wp)) c x = 0`. Simplify using `[hx0]`. Establish `hxK : x ∈ Kc`. Assume the negation of the conclusion as `h`. Conclude with `hx0 (h0 x h)`.

Establish `hxG : x ∈ Glev k r (Fin.last r)`. Assume the negation of the conclusion as `h`. Conclude with `hx0 (Formalism.FourierDecayAlt.P5.radSp_zero_off Ψ (x := (c, x)) fun hd => h hd.2.1)`. Establish `hloc` using `(Formalism.FourierDecayAlt.P.transfer_linear_local ℂ k r z z' (Fin.last r) (O ∩ Qx5.Dp k r z z') Y a b (fun y => φ ((Φ : Fn k r (Wq →L[ℂ] Wp)) c y)) fΦ 0 (hO.inter (Qx5.Dp_open k r z z')) (smoothLev_mono Set.inter_subset_right (Qx5.smooth_clm φ (Qx5.slice_smooth Φ.2 hc))) (smooth …`. Rewrite using `[hloc]`.

Establish `eB : ∀ x : Mx k r, φ ((X.t (star Y) b a Ψ : Fn k r (Wq →L[ℂ] Wp)) c x) * star (φ ((Φ : Fn k r (Wq →L[ℂ] Wp)) c x)) = tL k r z z' (Fin.last r) (star Y) b a fΨ x * star (fΦ x)`. Introduce `x`. Establish `e0 : φ ((X.t (star Y) b a Ψ : Fn k r (Wq →L[ℂ] Wp)) c x) * star (φ ((Φ : Fn k r (Wq →L[ℂ] Wp)) c x)) = tL k r z z' (Fin.last r) (star Y) b a (fun y => φ ((Ψ : Fn k r (Wq →L[ℂ] Wp)) c y)) x * star (φ ((Φ : Fn k r (Wq →L[ℂ] Wp)) c x))`. Use `congrArg star (Qx5.key_pt X Ψ Φ hc (star Y) b a φ x)` as an intermediate fact. Simplify `this` using `[mul_comm]`.

Rewrite using `[e0, hfΨ, hfΦ]`. Use `show _ = _ * star ((χ x : ℂ) * φ ((Φ : Fn k r (Wq →L[ℂ] Wp)) c x))`. Distinguish the cases in `hxO : x ∈ O`. Rewrite using `[χ1 x hxO, Complex.ofReal_one, one_mul]`. Distinguish the cases in `hxD : (c, x) ∈ DomR k r z z'`.

Establish `hxK : x ∉ Kc` using `fun h => hxO (hKO h)`. Establish `ht0 : tL k r z z' (Fin.last r) (star Y) b a (fun y => φ ((Ψ : Fn k r (Wq →L[ℂ] Wp)) c y)) x = 0` using `tL_eq_zero_local hKc.isClosed.isOpen_compl (smoothLev_mono (Set.subset_univ _) (hfΨ ▸ hsΨ)) (fun y hy => by simp [h0 y hy.2]) (star Y) b a ⟨hxD.2.1, hxK⟩`. Rewrite using `[ht0, zero_mul, zero_mul]`. Establish `hΦ0 : (Φ : Fn k r (Wq →L[ℂ] Wp)) c x = 0` using `Formalism.FourierDecayAlt.P5.radSp_zero_off Φ (x := (c, x)) hxD`. Rewrite using `[hΦ0]`.

Simplify using the standard rewrite rules. Simplify using `only [eA, eB]`. Conclude with `hh.symm`.
-/
theorem slice_adj_clm (hz : inWb k r z) (hz' : inWb k r z') (X : ActualOps k r z z' π π') {μ : Measure (Mt k r)}
    (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ) (Φ Ψ : RadSp k r z z' π π') {c : Fin r → ℂ} (hc : c ∈ OmX r)
    {Kc : Set (Mx k r)} (hKc : IsCompact Kc) (hKD : Kc ⊆ Qx5.Dp k r z z')
    (h0 : ∀ g, g ∉ Kc → (Ψ : Fn k r (Wq →L[ℂ] Wp)) c g = 0) (Y : ℂ) (a b : Fin 2) (φ : (Wq →L[ℂ] Wp) →L[ℂ] ℂ) :
    (∫ x : Mt k r, φ ((Ψ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x)) *
        star (φ ((X.t Y a b Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x))) ∂μ) =
      ∫ x : Mt k r, φ ((X.t (star Y) b a Ψ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x)) *
        star (φ ((Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x))) ∂μ := by
  obtain ⟨χ, O, L, hχs, hO, hKO, hLc, hLD, χ1, χ0⟩ := bump_exists hKc hKD
  obtain ⟨fΨ, hfΨ⟩ : ∃ f : Mx k r → ℂ, f = fun y => φ ((Ψ : Fn k r (Wq →L[ℂ] Wp)) c y) := ⟨_, rfl⟩
  obtain ⟨fΦ, hfΦ⟩ : ∃ f : Mx k r → ℂ, f = fun y => (χ y : ℂ) * φ ((Φ : Fn k r (Wq →L[ℂ] Wp)) c y) := ⟨_, rfl⟩
  have hsΨ : SmoothLev k r (Fin.last r) Set.univ fΨ := by
    rw [hfΨ]; exact Qx5.smooth_clm φ (Qx5.smooth_univ Ψ.2 hc hKc hKD fun g _ hg => h0 g hg)
  have hcΨ : CptOn k r (Fin.last r) fΨ := ⟨Kc, hKc, fun g _ hg => by rw [hfΨ]; simp [h0 g hg]⟩
  have hsΦ : SmoothLev k r (Fin.last r) Set.univ fΦ := by
    intro g₀ hg₀
    by_cases hgL : g₀ ∈ L
    · obtain ⟨U, F, hU, hgU, hF, he⟩ := Qx5.smooth_clm φ (Qx5.slice_smooth Φ.2 hc) g₀ ⟨hg₀.1, hLD hgL⟩
      refine ⟨U, fun y => (χ y : ℂ) * F y, hU, hgU,
        (Complex.ofRealCLM.contDiff.comp_contDiffOn hχs.contDiffOn).mul hF, fun y hy hyG => ?_⟩
      rw [hfΦ]
      show (χ y : ℂ) * φ ((Φ : Fn k r (Wq →L[ℂ] Wp)) c y) = (χ y : ℂ) * F y
      rw [← he y hy hyG]
    · refine ⟨Lᶜ, fun _ => 0, hLc.isClosed.isOpen_compl, hgL, contDiffOn_const, fun y hy _ => ?_⟩
      rw [hfΦ]
      show (χ y : ℂ) * φ ((Φ : Fn k r (Wq →L[ℂ] Wp)) c y) = 0
      rw [χ0 y hy, Complex.ofReal_zero, zero_mul]
  have hcΦ : CptOn k r (Fin.last r) fΦ := ⟨L, hLc, fun g _ hg => by rw [hfΦ]; simp [χ0 g hg]⟩
  have hh := Formalism.FourierDecayAlt.P.hermitian_haar_invariance k r z z' (Fin.last r) μ hμ hz hz' fΨ fΦ hsΨ hsΦ hcΨ hcΦ (star Y) b a
  rw [star_star] at hh
  have eA : ∀ x : Mx k r, φ ((Ψ : Fn k r (Wq →L[ℂ] Wp)) c x) * star (φ ((X.t Y a b Φ : Fn k r (Wq →L[ℂ] Wp)) c x)) =
      fΨ x * star (tL k r z z' (Fin.last r) Y a b fΦ x) := by
    intro x
    rw [Qx5.key_pt X Φ Ψ hc Y a b φ x, hfΨ]
    by_cases hx0 : (Ψ : Fn k r (Wq →L[ℂ] Wp)) c x = 0
    · simp [hx0]
    · have hxK : x ∈ Kc := by
        by_contra h
        exact hx0 (h0 x h)
      have hxG : x ∈ Glev k r (Fin.last r) := by
        by_contra h
        exact hx0 (Formalism.FourierDecayAlt.P5.radSp_zero_off Ψ (x := (c, x)) fun hd => h hd.2.1)
      have hloc := (Formalism.FourierDecayAlt.P.transfer_linear_local ℂ k r z z' (Fin.last r) (O ∩ Qx5.Dp k r z z') Y a b
        (fun y => φ ((Φ : Fn k r (Wq →L[ℂ] Wp)) c y)) fΦ 0 (hO.inter (Qx5.Dp_open k r z z'))
        (smoothLev_mono Set.inter_subset_right (Qx5.smooth_clm φ (Qx5.slice_smooth Φ.2 hc)))
        (smoothLev_mono (Set.subset_univ _) hsΦ) x ⟨hxG, hKO hxK, hKD hxK⟩).2
        (fun y hy => by rw [hfΦ]; show _ = (χ y : ℂ) * _; rw [χ1 y hy.2.1, Complex.ofReal_one, one_mul])
      rw [hloc]
  have eB : ∀ x : Mx k r, φ ((X.t (star Y) b a Ψ : Fn k r (Wq →L[ℂ] Wp)) c x) *
      star (φ ((Φ : Fn k r (Wq →L[ℂ] Wp)) c x)) =
      tL k r z z' (Fin.last r) (star Y) b a fΨ x * star (fΦ x) := by
    intro x
    have e0 : φ ((X.t (star Y) b a Ψ : Fn k r (Wq →L[ℂ] Wp)) c x) * star (φ ((Φ : Fn k r (Wq →L[ℂ] Wp)) c x)) =
        tL k r z z' (Fin.last r) (star Y) b a (fun y => φ ((Ψ : Fn k r (Wq →L[ℂ] Wp)) c y)) x *
          star (φ ((Φ : Fn k r (Wq →L[ℂ] Wp)) c x)) := by
      have := congrArg star (Qx5.key_pt X Ψ Φ hc (star Y) b a φ x)
      simpa [mul_comm] using this
    rw [e0, hfΨ, hfΦ]
    show _ = _ * star ((χ x : ℂ) * φ ((Φ : Fn k r (Wq →L[ℂ] Wp)) c x))
    by_cases hxO : x ∈ O
    · rw [χ1 x hxO, Complex.ofReal_one, one_mul]
    · by_cases hxD : (c, x) ∈ DomR k r z z'
      · have hxK : x ∉ Kc := fun h => hxO (hKO h)
        have ht0 : tL k r z z' (Fin.last r) (star Y) b a (fun y => φ ((Ψ : Fn k r (Wq →L[ℂ] Wp)) c y)) x = 0 :=
          tL_eq_zero_local hKc.isClosed.isOpen_compl
            (smoothLev_mono (Set.subset_univ _) (hfΨ ▸ hsΨ))
            (fun y hy => by simp [h0 y hy.2]) (star Y) b a ⟨hxD.2.1, hxK⟩
        rw [ht0, zero_mul, zero_mul]
      · have hΦ0 : (Φ : Fn k r (Wq →L[ℂ] Wp)) c x = 0 := Formalism.FourierDecayAlt.P5.radSp_zero_off Φ (x := (c, x)) hxD
        rw [hΦ0]
        simp
  simp only [eA, eB]
  exact hh.symm

/- English proof (translation)
Establish `htΨ : ∀ g ∈ Glev k r (Fin.last r), g ∉ Kc → (X.t (star Y) b a Ψ : Fn k r (Wq →L[ℂ] Wp)) c g = 0` using `fun g _ hg => t_zero_near X Ψ (star Y) b a (x := (c, g)) hKc.isClosed.isOpen_compl hg (fun g' hg' => h0 g' hg'.2)`. Simplify using `only [Qx5.inner_coef]`. Rewrite using `[integral_finsetSum _ fun j _ => (Qx5.integrable_pair hμ (X.t Y a b Φ) Ψ hc hKc hKD (fun g _ hg => h0 g hg) _).1, integral_finsetSum _ fun j _ => (Qx5.integrable_pair hμ Φ (X.t (star Y) b a Ψ) hc hKc hKD htΨ _).1]`. Conclude with `Finset.sum_congr rfl fun j _ => slice_adj_clm hz hz' X hμ Φ Ψ hc hKc hKD h0 Y a b _`.
-/
theorem slice_adj (hz : inWb k r z) (hz' : inWb k r z') (X : ActualOps k r z z' π π')
    {μ : Measure (Mt k r)} (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ) (Φ Ψ : RadSp k r z z' π π') {c : Fin r → ℂ}
    (hc : c ∈ OmX r) {Kc : Set (Mx k r)} (hKc : IsCompact Kc) (hKD : Kc ⊆ Qx5.Dp k r z z')
    (h0 : ∀ g, g ∉ Kc → (Ψ : Fn k r (Wq →L[ℂ] Wp)) c g = 0) (Y : ℂ) (a b : Fin 2) (v : Wq) :
    (∫ x : Mt k r, inner ℂ ((X.t Y a b Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x) v)
        ((Ψ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x) v) ∂μ) =
      ∫ x : Mt k r, inner ℂ ((Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x) v)
        ((X.t (star Y) b a Ψ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x) v) ∂μ := by
  have htΨ : ∀ g ∈ Glev k r (Fin.last r), g ∉ Kc → (X.t (star Y) b a Ψ : Fn k r (Wq →L[ℂ] Wp)) c g = 0 :=
    fun g _ hg => t_zero_near X Ψ (star Y) b a (x := (c, g)) hKc.isClosed.isOpen_compl hg
      (fun g' hg' => h0 g' hg'.2)
  simp only [Qx5.inner_coef]
  rw [integral_finsetSum _ fun j _ =>
      (Qx5.integrable_pair hμ (X.t Y a b Φ) Ψ hc hKc hKD (fun g _ hg => h0 g hg) _).1,
    integral_finsetSum _ fun j _ => (Qx5.integrable_pair hμ Φ (X.t (star Y) b a Ψ) hc hKc hKD htΨ _).1]
  exact Finset.sum_congr rfl fun j _ => slice_adj_clm hz hz' X hμ Φ Ψ hc hKc hKD h0 Y a b _

/- English proof (translation)
Unfold `radIp`. Use `congr 1`. Use function extensionality and compare the values at `c`. Distinguish the cases in `hc : c ∈ OmX r`. Take `⟨Kc, hKc, hKD, h0⟩` from `slice_cpt hΨ c`.

Establish `htΨ : ∀ g ∈ Glev k r (Fin.last r), g ∉ Kc → (X.t (star Y) b a Ψ : Fn k r (Wq →L[ℂ] Wp)) c g = 0` using `fun g _ hg => t_zero_near X Ψ (star Y) b a (x := (c, g)) hKc.isClosed.isOpen_compl hg (fun g' hg' => h0 g' hg'.2)`. Rewrite using `[Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.RadAdj.int_hs_sum hμ (X.t Y a b Φ) Ψ hc hKc hKD (fun g _ hg => Or.inr (h0 g hg)), Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.RadAdj.int_hs_sum hμ Φ (X.t (star Y) b a Ψ) hc hKc hKD (fun g hg hgK => Or.inr (htΨ g hg hgK))]`. Conclude with `Finset.sum_congr rfl fun i _ => slice_adj hz hz' X hμ Φ Ψ hc hKc hKD h0 Y a b _`. Establish `hz0 : ∀ (Θ : RadSp k r z z' π π') (g : Mx k r), (Θ : Fn k r (Wq →L[ℂ] Wp)) c g = 0` using `fun Θ g => Formalism.FourierDecayAlt.P5.radSp_zero_off Θ (x := (c, g)) fun hd => hc hd.1`. Simplify using `only [hz0]`.
-/
theorem radIp_adj (hz : inWb k r z) (hz' : inWb k r z')
    (X : ActualOps k r z z' π π') {μ : Measure (Mt k r)} (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ)
    (Φ Ψ : RadSp k r z z' π π') (hΨ : RTest Ψ) (Y : ℂ) (a b : Fin 2) :
    radIp μ (X.t Y a b Φ) Ψ = radIp μ Φ (X.t (star Y) b a Ψ) := by
  unfold radIp
  congr 1
  funext c
  by_cases hc : c ∈ OmX r
  · obtain ⟨Kc, hKc, hKD, h0⟩ := slice_cpt hΨ c
    have htΨ : ∀ g ∈ Glev k r (Fin.last r), g ∉ Kc → (X.t (star Y) b a Ψ : Fn k r (Wq →L[ℂ] Wp)) c g = 0 :=
      fun g _ hg => t_zero_near X Ψ (star Y) b a (x := (c, g)) hKc.isClosed.isOpen_compl hg
        (fun g' hg' => h0 g' hg'.2)
    rw [Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.RadAdj.int_hs_sum hμ (X.t Y a b Φ) Ψ hc hKc hKD (fun g _ hg => Or.inr (h0 g hg)),
      Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.RadAdj.int_hs_sum hμ Φ (X.t (star Y) b a Ψ) hc hKc hKD
        (fun g hg hgK => Or.inr (htΨ g hg hgK))]
    exact Finset.sum_congr rfl fun i _ => slice_adj hz hz' X hμ Φ Ψ hc hKc hKD h0 Y a b _
  · have hz0 : ∀ (Θ : RadSp k r z z' π π') (g : Mx k r), (Θ : Fn k r (Wq →L[ℂ] Wp)) c g = 0 := fun Θ g =>
      Formalism.FourierDecayAlt.P5.radSp_zero_off Θ (x := (c, g)) fun hd => hc hd.1
    simp only [hz0]

/- English proof (translation)
Use `⟨fun Ψ hΨ => entry_operator_preserves_tests X Y a b hΨ, fun Ψ hΨ => entry_operator_preserves_tests X (star Y) b a hΨ, fun Φ Ψ hΨ => radIp_adj hz hz' X hμ Φ Ψ hΨ Y a b, fun Φ Ψ hΨ => ?_⟩` and prove the remaining obligations. Establish `h` using `radIp_adj hz hz' X hμ Φ Ψ hΨ (star Y) b a`. Rewrite `h` using `[star_star]`. Conclude with `h`.
-/
theorem rAdj_XQQ (hz : inWb k r z) (hz' : inWb k r z')
    (X : ActualOps k r z z' π π') {μ : Measure (Mt k r)} (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ) (Y : ℂ)
    (a b : Fin 2) : RAdj μ (X.QQ Y a b) := by
  refine ⟨fun Ψ hΨ => entry_operator_preserves_tests X Y a b hΨ, fun Ψ hΨ => entry_operator_preserves_tests X (star Y) b a hΨ,
    fun Φ Ψ hΨ => radIp_adj hz hz' X hμ Φ Ψ hΨ Y a b, fun Φ Ψ hΨ => ?_⟩
  have h := radIp_adj hz hz' X hμ Φ Ψ hΨ (star Y) b a
  rw [star_star] at h
  exact h

/- English proof (translation)
Unfold `B.hsVec`. Both sides reduce to the same expression.
-/
theorem hsVec_smul_q (w : ℂ) (A : Wq →L[ℂ] Wp) : B.hsVec (w • A) = w • B.hsVec A := by
  unfold B.hsVec
  rfl

/- English proof (translation)
Unfold `radIp`. Rewrite using `[← integral_const_mul]`. Use `congr 1`. Use function extensionality and compare the values at `c`. Rewrite using `[← integral_const_mul]`.

Use `congr 1`. Use function extensionality and compare the values at `x`. Simplify using `only [Submodule.coe_smul, Pi.smul_apply]`. Rewrite using `[hsVec_smul_q, inner_smul_left]`.
-/
theorem radIp_smul_left (μ : Measure (Mt k r)) (w : ℂ) (Φ Ψ : RadSp k r z z' π π') :
    radIp μ (w • Φ) Ψ = starRingEnd ℂ w * radIp μ Φ Ψ := by
  unfold radIp
  rw [← integral_const_mul]
  congr 1
  funext c
  rw [← integral_const_mul]
  congr 1
  funext x
  simp only [Submodule.coe_smul, Pi.smul_apply]
  rw [hsVec_smul_q, inner_smul_left]

/- English proof (translation)
Unfold `radIp`. Rewrite using `[← integral_const_mul]`. Use `congr 1`. Use function extensionality and compare the values at `c`. Rewrite using `[← integral_const_mul]`.

Use `congr 1`. Use function extensionality and compare the values at `x`. Simplify using `only [Submodule.coe_smul, Pi.smul_apply]`. Rewrite using `[hsVec_smul_q, inner_smul_right]`.
-/
theorem radIp_smul_right (μ : Measure (Mt k r)) (w : ℂ) (Φ Ψ : RadSp k r z z' π π') :
    radIp μ Φ (w • Ψ) = w * radIp μ Φ Ψ := by
  unfold radIp
  rw [← integral_const_mul]
  congr 1
  funext c
  rw [← integral_const_mul]
  congr 1
  funext x
  simp only [Submodule.coe_smul, Pi.smul_apply]
  rw [hsVec_smul_q, inner_smul_right]

/- English proof (translation)
Take `⟨h1, h2, h3, h4⟩` from `ha`. Establish `es : s • a = algebraMap ℂ (Pr (RadSp k r z z' π π')) s * a` using `Algebra.smul_def s a`. Establish `e1 : ∀ Φ, (s • a).1 Φ = s • a.1 Φ` using `fun Φ => by`. Rewrite using `[es, rds_fst_mul, Module.End.mul_apply, rds_fst_alg, Module.algebraMap_end_apply]`. Establish `e2 : ∀ Φ, (s • a).2.unop Φ = s • a.2.unop Φ` using `fun Φ => by`.

Rewrite using `[es, rds_snd_mul, Module.End.mul_apply, rds_snd_alg, Module.algebraMap_end_apply, map_smul, hs]`. Use `⟨fun Ψ hΨ => ?_, fun Ψ hΨ => ?_, fun Φ Ψ hΨ => ?_, fun Φ Ψ hΨ => ?_⟩` and prove the remaining obligations. Rewrite using `[e1]`. Conclude with `rTest_smul s (h1 Ψ hΨ)`. Rewrite using `[e2]`.

Conclude with `rTest_smul s (h2 Ψ hΨ)`. Rewrite using `[e1, e2, radIp_smul_left, radIp_smul_right, h3 Φ Ψ hΨ, hs]`. Rewrite using `[e1, e2, radIp_smul_left, radIp_smul_right, h4 Φ Ψ hΨ, hs]`.
-/
theorem rAdj_smul_real {μ : Measure (Mt k r)} {a : Pr (RadSp k r z z' π π')}
    (ha : RAdj μ a) (s : ℂ) (hs : starRingEnd ℂ s = s) : RAdj μ (s • a) := by
  obtain ⟨h1, h2, h3, h4⟩ := ha
  have es : s • a = algebraMap ℂ (Pr (RadSp k r z z' π π')) s * a := Algebra.smul_def s a
  have e1 : ∀ Φ, (s • a).1 Φ = s • a.1 Φ := fun Φ => by
    rw [es, rds_fst_mul, Module.End.mul_apply, rds_fst_alg, Module.algebraMap_end_apply]
  have e2 : ∀ Φ, (s • a).2.unop Φ = s • a.2.unop Φ := fun Φ => by
    rw [es, rds_snd_mul, Module.End.mul_apply, rds_snd_alg, Module.algebraMap_end_apply, map_smul, hs]
  refine ⟨fun Ψ hΨ => ?_, fun Ψ hΨ => ?_, fun Φ Ψ hΨ => ?_, fun Φ Ψ hΨ => ?_⟩
  · rw [e1]; exact rTest_smul s (h1 Ψ hΨ)
  · rw [e2]; exact rTest_smul s (h2 Ψ hΨ)
  · rw [e1, e2, radIp_smul_left, radIp_smul_right, h3 Φ Ψ hΨ, hs]
  · rw [e1, e2, radIp_smul_left, radIp_smul_right, h4 Φ Ψ hΨ, hs]

end Rad

end Formalism.FourierDecayAlt.P.CutSE.QQA

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

/- English proof (translation)
Introduce `Wp Wq _ _ _ _ _ _ P z z' π π' X μ L st l0 D hD _ _ _ _ _ _ _ Y a b`. Establish `hz : inWb P.k P.r z` using `hD.1.2.1`. Establish `hz' : inWb P.k P.r z'` using `hD.1.2.2.1`. Rewrite using `[hD.2.2.2.1 Y, Matrix.smul_apply]`. Use `QQA.rAdj_smul_real (QQA.rAdj_XQQ hz hz' X hD.2.1 Y a b) _ ?_` and prove the remaining obligations.

Simplify using `[M.sgn]`.
-/
theorem spectral_quadratic_adjoint : RDSQQAdj := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' X μ L st l0 D hD _ _ _ _ _ _ _ Y a b
  have hz : inWb P.k P.r z := hD.1.2.1
  have hz' : inWb P.k P.r z' := hD.1.2.2.1
  rw [hD.2.2.2.1 Y, Matrix.smul_apply]
  refine QQA.rAdj_smul_real (QQA.rAdj_XQQ hz hz' X hD.2.1 Y a b) _ ?_
  simp [M.sgn]

end Formalism.FourierDecayAlt.P.CutSE
