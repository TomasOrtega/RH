import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.HeckeInj
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.ArchSlotEx
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.ArchBasic
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.PositionOf
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.CvBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.TypeFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.AmpGrp
import GroundTheory.AutomorphicForms.L2LocalComponents.ArchBump
import GroundTheory.AutomorphicForms.GKModules.ParametricIntegral
import GroundTheory.AutomorphicForms.GKModules.Garding
import GroundTheory.AutomorphicForms.TensorProductTheorem.NonemptyAdelicDecomposition

open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open GlobalTheory.CuspRep UpperTheory.V.Published
open scoped ComplexConjugate Classical ContDiff Manifold

open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.Amp

/- English proof (translation)
Use `set h := isExpLieAlgebra K n`. Rewrite using `[IsExpLieAlgebra.isSmoothFun_iff]`. Introduce `g`. Use `letI := h.chartedSpace`. Use `haveI := h.lieGroup ∞`.

Establish `hfg : ContMDiff 𝓘(ℝ, archLie K n) 𝓘(ℝ, ℂ) ∞ (fun x : archGroup K n => f (g * x))` using `ContMDiff.comp (I' := 𝓘(ℝ, archLie K n)) hf (contMDiff_const.mul contMDiff_id)`. Use `set Φ : archLie K n → archGroup K n → ℂ := fun Y y => f (g * h.expG Y * y) with hΦdef`. Establish `hΦ : ∀ y₀ : archGroup K n, ContDiff ℝ ∞ (fun q : archLie K n × archLie K n => Φ q.1 (y₀ * h.expG q.2))` using `fun y₀ => by`. Simplify `h.contDiff_comp_expG_mul_expG hfg contDiff_fst y₀ contDiff_snd` using `[hΦdef, mul_assoc]`. Establish `hΦY : ∀ y, ContDiff ℝ ∞ (fun Y => Φ Y y)` using `fun y => by`.

Simplify `h.contDiff_comp_expG_mul_expG hfg contDiff_id y (contDiff_const (c := (0 : archLie K n)))` using `[hΦdef, mul_assoc]`. Establish `e1 : (fun Y : archLie K n => ec κ e f (g * h.expG Y)) = fun Y => ∫ k : archCompact K n, e k * Φ Y (k : archGroup K n)⁻¹ ∂κ`. Use function extensionality and compare the values at `Y`. Simplify using `only [ec, hk, hΦdef]`. Rewrite using `[e1]`.

Establish `hD : ∀ (j : ℕ) (Y : archLie K n) (k : archCompact K n), iteratedFDeriv ℝ j (fun Y => e k * Φ Y (k : archGroup K n)⁻¹) Y = e k • iteratedFDeriv ℝ j (fun Y => Φ Y (k : archGroup K n)⁻¹) Y`. Introduce `j Y k`. Establish `e2 : (fun Y => e k * Φ Y (k : archGroup K n)⁻¹) = e k • fun Y => Φ Y (k : archGroup K n)⁻¹`. Use function extensionality and compare the values at `Y`. Simplify using `[smul_eq_mul]`.

Rewrite using `[e2, iteratedFDeriv_const_smul_apply ((hΦY _).contDiffAt.of_le (by exact_mod_cast le_top))]`. Use `contDiff_integral_of_iteratedFDeriv (μ := κ) (fun Y (k : archCompact K n) => e k * Φ Y (k : archGroup K n)⁻¹) (fun k => contDiff_const.mul (hΦY _)) (fun j => ?_) (fun Y₀ => ⟨Set.univ, Filter.univ_mem, Set.univ, isCompact_univ, fun Y _ k hy => (hy (Set.mem_univ _)).elim⟩)` and prove the remaining obligations. Establish `hc` using `h.continuous_iteratedFDeriv_param Φ hΦ j`. Establish `hc' : Continuous fun q : archLie K n × archCompact K n => iteratedFDeriv ℝ j (fun Y => Φ Y (q.2 : archGroup K n)⁻¹) q.1` using `hc.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd).inv)`. Conclude with `((he.comp continuous_snd).smul hc').congr fun q => (hD j q.1 q.2).symm`.
-/
private theorem ec_smooth {K : Type} [Field K] [NumberField K] {n : ℕ} (κ : Measure (archCompact K n)) [IsProbabilityMeasure κ]
    {e : archCompact K n → ℂ} (he : Continuous e) {f : archGroup K n → ℂ} (hf : (isExpLieAlgebra K n).IsSmoothFun f)
    (hk : ∀ (k : archCompact K n) g, f ((k : archGroup K n)⁻¹ * g) = f (g * (k : archGroup K n)⁻¹)) :
    (isExpLieAlgebra K n).IsSmoothFun (ec κ e f) := by
  set h := isExpLieAlgebra K n
  rw [IsExpLieAlgebra.isSmoothFun_iff]
  intro g
  letI := h.chartedSpace
  haveI := h.lieGroup ∞
  have hfg : ContMDiff 𝓘(ℝ, archLie K n) 𝓘(ℝ, ℂ) ∞ (fun x : archGroup K n => f (g * x)) :=
    ContMDiff.comp (I' := 𝓘(ℝ, archLie K n)) hf (contMDiff_const.mul contMDiff_id)
  set Φ : archLie K n → archGroup K n → ℂ := fun Y y => f (g * h.expG Y * y) with hΦdef
  have hΦ : ∀ y₀ : archGroup K n, ContDiff ℝ ∞ (fun q : archLie K n × archLie K n => Φ q.1 (y₀ * h.expG q.2)) := fun y₀ => by
    simpa [hΦdef, mul_assoc] using h.contDiff_comp_expG_mul_expG hfg contDiff_fst y₀ contDiff_snd
  have hΦY : ∀ y, ContDiff ℝ ∞ (fun Y => Φ Y y) := fun y => by
    simpa [hΦdef, mul_assoc] using h.contDiff_comp_expG_mul_expG hfg contDiff_id y (contDiff_const (c := (0 : archLie K n)))
  have e1 : (fun Y : archLie K n => ec κ e f (g * h.expG Y)) = fun Y => ∫ k : archCompact K n, e k * Φ Y (k : archGroup K n)⁻¹ ∂κ := by
    funext Y
    simp only [ec, hk, hΦdef]
  rw [e1]
  have hD : ∀ (j : ℕ) (Y : archLie K n) (k : archCompact K n),
      iteratedFDeriv ℝ j (fun Y => e k * Φ Y (k : archGroup K n)⁻¹) Y =
        e k • iteratedFDeriv ℝ j (fun Y => Φ Y (k : archGroup K n)⁻¹) Y := by
    intro j Y k
    have e2 : (fun Y => e k * Φ Y (k : archGroup K n)⁻¹) = e k • fun Y => Φ Y (k : archGroup K n)⁻¹ := by
      funext Y; simp [smul_eq_mul]
    rw [e2, iteratedFDeriv_const_smul_apply ((hΦY _).contDiffAt.of_le (by exact_mod_cast le_top))]
  refine contDiff_integral_of_iteratedFDeriv (μ := κ) (fun Y (k : archCompact K n) => e k * Φ Y (k : archGroup K n)⁻¹)
    (fun k => contDiff_const.mul (hΦY _)) (fun j => ?_) (fun Y₀ => ⟨Set.univ, Filter.univ_mem, Set.univ, isCompact_univ, fun Y _ k hy => (hy (Set.mem_univ _)).elim⟩)
  have hc := h.continuous_iteratedFDeriv_param Φ hΦ j
  have hc' : Continuous fun q : archLie K n × archCompact K n => iteratedFDeriv ℝ j (fun Y => Φ Y (q.2 : archGroup K n)⁻¹) q.1 :=
    hc.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd).inv)
  exact ((he.comp continuous_snd).smul hc').congr fun q => (hD j q.1 q.2).symm

/- English proof (translation)
Establish `hI : 0 ≤ ∫ g, ‖ec κ e (fun x => (ρ x : ℂ)) g‖ ∂ν` using `integral_nonneg fun _ => norm_nonneg _`. Use `⟨1 / (1 + ∫ g, ‖ec κ e (fun x => (ρ x : ℂ)) g‖ ∂ν), by positivity, ?_⟩` and prove the remaining obligations. Establish `e1 : ∀ (t : ℝ), 0 < t → ∀ g, ‖ec κ e (fun x => ((t * ρ x : ℝ) : ℂ)) g‖ = t * ‖ec κ e (fun x => (ρ x : ℂ)) g‖` using `fun t ht g => by`. Establish `h1 : ec κ e (fun x => ((t * ρ x : ℝ) : ℂ)) g = (t : ℂ) * ec κ e (fun x => (ρ x : ℂ)) g`. Simplify using `only [ec, Complex.ofReal_mul, mul_left_comm _ (t : ℂ), integral_const_mul]`.

Rewrite using `[h1, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.le]`. Simplify using `only [e1 _ (by positivity : 0 < 1 / (1 + ∫ g, ‖ec κ e (fun x => (ρ x : ℂ)) g‖ ∂ν)), integral_const_mul]`. Rewrite using `[one_div, inv_mul_le_iff₀ (by positivity)]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem sc_norm {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] {K : Subgroup G} (κ : Measure K) (e : K → ℂ)
    (ν : Measure G) (ρ : G → ℝ) :
    ∃ t : ℝ, 0 < t ∧ ∫ g, ‖ec κ e (fun x => ((t * ρ x : ℝ) : ℂ)) g‖ ∂ν ≤ 1 := by
  have hI : 0 ≤ ∫ g, ‖ec κ e (fun x => (ρ x : ℂ)) g‖ ∂ν := integral_nonneg fun _ => norm_nonneg _
  refine ⟨1 / (1 + ∫ g, ‖ec κ e (fun x => (ρ x : ℂ)) g‖ ∂ν), by positivity, ?_⟩
  have e1 : ∀ (t : ℝ), 0 < t → ∀ g, ‖ec κ e (fun x => ((t * ρ x : ℝ) : ℂ)) g‖ = t * ‖ec κ e (fun x => (ρ x : ℂ)) g‖ := fun t ht g => by
    have h1 : ec κ e (fun x => ((t * ρ x : ℝ) : ℂ)) g = (t : ℂ) * ec κ e (fun x => (ρ x : ℂ)) g := by
      simp only [ec, Complex.ofReal_mul, mul_left_comm _ (t : ℂ), integral_const_mul]
    rw [h1, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.le]
  simp only [e1 _ (by positivity : 0 < 1 / (1 + ∫ g, ‖ec κ e (fun x => (ρ x : ℂ)) g‖ ∂ν)), integral_const_mul]
  rw [one_div, inv_mul_le_iff₀ (by positivity)]
  linarith

/- English proof (translation)
Establish `e1 : (fun x => ((t * ρ x : ℝ) : ℂ)) = fun y => (t : ℂ) * (ρ y : ℂ)`. Use function extensionality and compare the values at `x`. Use `push_cast`. Both sides reduce to the same expression. Rewrite using `[e1]`.

Conclude with `(hρ.const_mul (t : ℂ)).1`.
-/
private theorem sc_smooth {K : Type} [Field K] [NumberField K] {n : ℕ} {ρ : archGroup K n → ℝ}
    (hρ : (isExpLieAlgebra K n).IsTestFunction fun a => (ρ a : ℂ)) (t : ℝ) :
    (isExpLieAlgebra K n).IsSmoothFun fun x => ((t * ρ x : ℝ) : ℂ) := by
  have e1 : (fun x => ((t * ρ x : ℝ) : ℂ)) = fun y => (t : ℂ) * (ρ y : ℂ) := by
    funext x
    push_cast
    rfl
  rw [e1]
  exact (hρ.const_mul (t : ℂ)).1

/- English proof (translation)
Establish `e1 : (⇑b : archGroup K n → ℂ) = f` using `funext h`. Unfold `LeftFin`. Rewrite using `[e1]`. Conclude with `hf`.
-/
private theorem leftFin_of {K : Type} [Field K] [NumberField K] {n : ℕ} {b : TI K n} {f : archGroup K n → ℂ} (h : ∀ g, b g = f g)
    (hf : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : archCompact K n => fun g : archGroup K n => f ((k : archGroup K n) * g)))) :
    LeftFin b := by
  have e1 : (⇑b : archGroup K n → ℂ) = f := funext h
  unfold LeftFin
  rw [e1]
  exact hf

/- English proof (translation)
Establish `e1 : (⇑b : archGroup K n → ℂ) = f` using `funext h`. Unfold `SmoothT`. Rewrite using `[show (fun g => b g) = f from e1]`. Conclude with `hf`.
-/
private theorem smoothT_of {K : Type} [Field K] [NumberField K] {n : ℕ} {b : TI K n} {f : archGroup K n → ℂ} (h : ∀ g, b g = f g)
    (hf : (isExpLieAlgebra K n).IsSmoothFun f) : SmoothT b := by
  have e1 : (⇑b : archGroup K n → ℂ) = f := funext h
  unfold SmoothT
  rw [show (fun g => b g) = f from e1]
  exact hf

/- English proof (translation)
Assemble the required witnesses or components as `⟨⟨⟨f, hc⟩, hs⟩, fun _ => rfl⟩`.
-/
private theorem exTI {K : Type} [Field K] [NumberField K] {n : ℕ} {f : archGroup K n → ℂ} (hc : Continuous f) (hs : HasCompactSupport f) :
    ∃ b : TI K n, ∀ g, b g = f g :=
  ⟨⟨⟨f, hc⟩, hs⟩, fun _ => rfl⟩

/- English proof (translation)
Use `haveI := h.haar.prob`. Use `haveI : κ.IsMulLeftInvariant := ⟨fun k => (h.haar.left k).map_eq⟩`. Take `⟨ρ, hρ0, hρt, hρ1, -, hρc, hρN, -⟩` from `exists_archBump ν hN`. Establish `hρcont : Continuous ρ` using `Complex.continuous_re.comp hρt.continuous`. Establish `hρcs : HasCompactSupport ρ` using `hρt.2.comp_left (g := Complex.re) rfl`.

Take `⟨t, ht, hn⟩` from `sc_norm κ e ν ρ`. Establish `hβc : Continuous fun x => t * ρ x` using `continuous_const.mul hρcont`. Establish `hβs : HasCompactSupport fun x => t * ρ x` using `hρcs.mul_left`. Establish `hβc' : Continuous fun x => ((t * ρ x : ℝ) : ℂ)` using `Complex.continuous_ofReal.comp hβc`. Establish `hβs' : HasCompactSupport fun x => ((t * ρ x : ℝ) : ℂ)` using `hβs.comp_left Complex.ofReal_zero`.

Take `⟨b, hb⟩` from `exTI (ec_cont κ h.cont hβc') (ec_cs κ e hβs')`. Use `⟨fun x => t * ρ x, b, hβc, hβs, fun x => mul_nonneg ht.le (hρ0 x), ?_, fun x hx => hρN x (right_ne_zero_of_mul hx), hb, smoothT_of hb (ec_smooth κ h.cont (sc_smooth hρt t) fun k g => ?_), leftFin_of hb (ec_fin κ h.cont h.idem hβc'), ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `h0 push Not at h0`. Establish `h2 : ∀ x, ρ x = 0` using `fun x => (mul_eq_zero.1 (h0 x)).resolve_left ht.ne'`. Simplify using `[h2] at hρ1`.

Establish `h3` using `hρc (k : archGroup K n)⁻¹ (inv_mem k.2) (g * (k : archGroup K n)⁻¹)`. Establish `h4 : (k : archGroup K n)⁻¹ * (g * (k : archGroup K n)⁻¹) * ((k : archGroup K n)⁻¹)⁻¹ = (k : archGroup K n)⁻¹ * g` using `by group`. Rewrite `h3` using `[h4]`. Simplify using `only [h3]`. Simplify `hn` using `only [hb]`.
-/
private theorem exB {K : Type} [Field K] [NumberField K] {n : ℕ} {κ : Measure (archCompact K n)} {e : archCompact K n → ℂ}
    (h : IdemA κ e) (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] {N : Set (archGroup K n)} (hN : N ∈ 𝓝 (1 : archGroup K n)) :
    ∃ (β : archGroup K n → ℝ) (b : TI K n), Continuous β ∧ HasCompactSupport β ∧ (∀ x, 0 ≤ β x) ∧ (∃ x, β x ≠ 0) ∧
      (∀ x, β x ≠ 0 → x ∈ N) ∧ (∀ g, b g = ec κ e (fun x => (β x : ℂ)) g) ∧ SmoothT b ∧ LeftFin b ∧ ∫ g, ‖b g‖ ∂ν ≤ 1 := by
  haveI := h.haar.prob
  haveI : κ.IsMulLeftInvariant := ⟨fun k => (h.haar.left k).map_eq⟩
  obtain ⟨ρ, hρ0, hρt, hρ1, -, hρc, hρN, -⟩ := exists_archBump ν hN
  have hρcont : Continuous ρ := Complex.continuous_re.comp hρt.continuous
  have hρcs : HasCompactSupport ρ := hρt.2.comp_left (g := Complex.re) rfl
  obtain ⟨t, ht, hn⟩ := sc_norm κ e ν ρ
  have hβc : Continuous fun x => t * ρ x := continuous_const.mul hρcont
  have hβs : HasCompactSupport fun x => t * ρ x := hρcs.mul_left
  have hβc' : Continuous fun x => ((t * ρ x : ℝ) : ℂ) := Complex.continuous_ofReal.comp hβc
  have hβs' : HasCompactSupport fun x => ((t * ρ x : ℝ) : ℂ) := hβs.comp_left Complex.ofReal_zero
  obtain ⟨b, hb⟩ := exTI (ec_cont κ h.cont hβc') (ec_cs κ e hβs')
  refine ⟨fun x => t * ρ x, b, hβc, hβs, fun x => mul_nonneg ht.le (hρ0 x), ?_, fun x hx => hρN x (right_ne_zero_of_mul hx), hb,
    smoothT_of hb (ec_smooth κ h.cont (sc_smooth hρt t) fun k g => ?_), leftFin_of hb (ec_fin κ h.cont h.idem hβc'), ?_⟩
  · by_contra h0
    push Not at h0
    have h2 : ∀ x, ρ x = 0 := fun x => (mul_eq_zero.1 (h0 x)).resolve_left ht.ne'
    simp [h2] at hρ1
  · have h3 := hρc (k : archGroup K n)⁻¹ (inv_mem k.2) (g * (k : archGroup K n)⁻¹)
    have h4 : (k : archGroup K n)⁻¹ * (g * (k : archGroup K n)⁻¹) * ((k : archGroup K n)⁻¹)⁻¹ = (k : archGroup K n)⁻¹ * g := by group
    rw [h4] at h3
    simp only [h3]
  · simpa only [hb] using hn

/- English proof (translation)
The claim follows from `int_surj (Measure.pi fun _ => α) κ s hs hm ho hf`.
-/
private theorem int_surj_pi {A K : Type} [Group A] [TopologicalSpace A] [IsTopologicalGroup A] [CompactSpace A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A] [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [SecondCountableTopology K]
    [MeasurableSpace K] [BorelSpace K] (m : ℕ) (α : Measure A) [IsProbabilityMeasure α] [α.IsMulRightInvariant] (κ : Measure K)
    [IsProbabilityMeasure κ] [κ.IsMulLeftInvariant] (s : (Fin m → A) → K) (hs : Continuous s) (hm : ∀ x y, s (x * y) = s x * s y)
    (ho : Function.Surjective s) {f : K → ℂ} (hf : Continuous f) :
    ∫ k, f k ∂κ = ∫ x, f (s x) ∂(Measure.pi fun _ => α) :=
  int_surj (Measure.pi fun _ => α) κ s hs hm ho hf

section Tens

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyComplex F]
  {σ : E ≃ₐ[F] E} (D : InfD σ 1) {n : ℕ}

/- English proof (translation)
Use `haveI := hE.haar.prob`. Use `haveI := hF.haar.prob`. Use `haveI : κ.IsMulLeftInvariant := ⟨fun k => (hE.haar.left k).map_eq⟩`. Use `haveI : κF.IsMulRightInvariant := ⟨fun k => (hF.haar.right k).map_eq⟩`. Take `⟨hgc, hcg, hgm, hgcont, hccont, -⟩` from `archBasic F E σ 1 D n`.

Establish `hcomp` using `(positionOf F E σ 1 D).2 n`. Set `s : (Fin (1 + 1) → archCompact F n) → archCompact E n` to `fun kk => ⟨glueA D n (fun i => kk i), (hcomp _).2 fun i => by rw [hgc]; exact (kk i).2⟩`. Establish `hsc : Continuous s` using `Continuous.subtype_mk (hgcont.comp (continuous_pi fun i => continuous_subtype_val.comp (continuous_apply i))) _`. Establish `hsm : ∀ x y, s (x * y) = s x * s y` using `fun x y => Subtype.ext (hgm _ _)`. Establish `hss : Function.Surjective s` using `fun k => ⟨fun i => ⟨compA D n i k, (hcomp k).1 k.2 i⟩, Subtype.ext (hcg k)⟩`.

Establish `hsk : ∀ kk i, compA D n i (s kk : archGroup E n) = kk i` using `fun kk i => hgc _ i`. Establish `hes : ∀ kk, e (s kk) = ∏ i, eF (kk i)` using `fun kk => hSq (s kk) kk fun i => (hsk kk i).symm`. Establish `hcf : Continuous fun k : archCompact E n => e k * ((∏ i, β (compA D n i ((k : archGroup E n)⁻¹ * x)) : ℝ) : ℂ)`. Use `hE.cont.mul (Complex.continuous_ofReal.comp (continuous_finset_prod _ fun i _ => hβ.comp ((hccont i).comp ?_)))` and prove the remaining obligations. Use `fun_prop`.

Unfold `ec`. Use `haveI : SecondCountableTopology (archCompact F n) := TopologicalSpace.Subtype.secondCountableTopology _`. Use `haveI : SecondCountableTopology (archCompact E n) := TopologicalSpace.Subtype.secondCountableTopology _`. Rewrite using `[int_surj_pi (1 + 1) κF κ s hsc hsm hss hcf]`. Establish `e1 : ∀ kk : Fin (1 + 1) → archCompact F n, e (s kk) * ((∏ i, β (compA D n i ((s kk : archGroup E n)⁻¹ * x)) : ℝ) : ℂ) = ∏ i, (eF (kk i) * (β ((kk i : archGroup F n)⁻¹ * compA D n i x) : ℂ))` using `fun kk => by`.

Rewrite using `[hes, Finset.prod_mul_distrib]`. Simplify using `only [map_mul, map_inv, hsk, Complex.ofReal_prod]`. Simplify using `only [e1]`. Conclude with `integral_fintype_prod_eq_prod (μ := fun _ => κF) fun i k => eF k * (β ((k : archGroup F n)⁻¹ * compA D n i x) : ℂ)`.
-/
private theorem tens_ec {κF : Measure (archCompact F n)} {eF : archCompact F n → ℂ} {κ : Measure (archCompact E n)}
    {e : archCompact E n → ℂ} (hF : IdemA κF eF) (hE : IdemA κ e) (hSq : IsSq D eF e) {β : archGroup F n → ℝ} (hβ : Continuous β)
    (x : archGroup E n) :
    ec κ e (fun y => ((∏ i, β (compA D n i y) : ℝ) : ℂ)) x = ∏ i, ec κF eF (fun y => (β y : ℂ)) (compA D n i x) := by
  haveI := hE.haar.prob
  haveI := hF.haar.prob
  haveI : κ.IsMulLeftInvariant := ⟨fun k => (hE.haar.left k).map_eq⟩
  haveI : κF.IsMulRightInvariant := ⟨fun k => (hF.haar.right k).map_eq⟩
  obtain ⟨hgc, hcg, hgm, hgcont, hccont, -⟩ := archBasic F E σ 1 D n
  have hcomp := (positionOf F E σ 1 D).2 n
  let s : (Fin (1 + 1) → archCompact F n) → archCompact E n := fun kk =>
    ⟨glueA D n (fun i => kk i), (hcomp _).2 fun i => by rw [hgc]; exact (kk i).2⟩
  have hsc : Continuous s := Continuous.subtype_mk (hgcont.comp (continuous_pi fun i => continuous_subtype_val.comp (continuous_apply i))) _
  have hsm : ∀ x y, s (x * y) = s x * s y := fun x y => Subtype.ext (hgm _ _)
  have hss : Function.Surjective s := fun k => ⟨fun i => ⟨compA D n i k, (hcomp k).1 k.2 i⟩, Subtype.ext (hcg k)⟩
  have hsk : ∀ kk i, compA D n i (s kk : archGroup E n) = kk i := fun kk i => hgc _ i
  have hes : ∀ kk, e (s kk) = ∏ i, eF (kk i) := fun kk => hSq (s kk) kk fun i => (hsk kk i).symm
  have hcf : Continuous fun k : archCompact E n => e k * ((∏ i, β (compA D n i ((k : archGroup E n)⁻¹ * x)) : ℝ) : ℂ) := by
    refine hE.cont.mul (Complex.continuous_ofReal.comp (continuous_finset_prod _ fun i _ => hβ.comp ((hccont i).comp ?_)))
    fun_prop
  unfold ec
  haveI : SecondCountableTopology (archCompact F n) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : SecondCountableTopology (archCompact E n) := TopologicalSpace.Subtype.secondCountableTopology _
  rw [int_surj_pi (1 + 1) κF κ s hsc hsm hss hcf]
  have e1 : ∀ kk : Fin (1 + 1) → archCompact F n,
      e (s kk) * ((∏ i, β (compA D n i ((s kk : archGroup E n)⁻¹ * x)) : ℝ) : ℂ) =
        ∏ i, (eF (kk i) * (β ((kk i : archGroup F n)⁻¹ * compA D n i x) : ℂ)) := fun kk => by
    rw [hes, Finset.prod_mul_distrib]
    simp only [map_mul, map_inv, hsk, Complex.ofReal_prod]
  simp only [e1]
  exact integral_fintype_prod_eq_prod (μ := fun _ => κF) fun i k => eF k * (β ((k : archGroup F n)⁻¹ * compA D n i x) : ℂ)

/- English proof (translation)
Take `⟨hgc, hcg, hgm, hgcont, hccont, -⟩` from `archBasic F E σ 1 D n`. Establish `hc : Continuous fun y => bE y * conj (bE (y⁻¹ * x)⁻¹)` using `by fun_prop`. Establish `e0 : ∫ y, bE y * conj (bE (y⁻¹ * x)⁻¹) ∂νE = ∫ yy, bE (glueA D n yy) * conj (bE ((glueA D n yy)⁻¹ * x)⁻¹) ∂(Measure.pi fun _ => νF)`. Rewrite using `[hs.meas]`. Conclude with `integral_map hgcont.aemeasurable hc.aestronglyMeasurable`.

Establish `e1 : ∀ yy : Fin (1 + 1) → archGroup F n, bE (glueA D n yy) * conj (bE ((glueA D n yy)⁻¹ * x)⁻¹) = ∏ i, (b (yy i) * conj (b ((yy i)⁻¹ * compA D n i x)⁻¹))` using `fun yy => by`. Rewrite using `[hb, hb, map_prod, Finset.prod_mul_distrib]`. Simplify using `only [map_mul, map_inv, hgc]`. Simplify using `only [cv]`. Rewrite using `[e0]`.

Simplify using `only [e1]`. Rewrite using `[integral_fintype_prod_eq_prod (μ := fun _ => νF) fun i y => b y * conj (b (y⁻¹ * compA D n i x)⁻¹), hs.tens x]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hs.sq]`. Both sides reduce to the same expression.
-/
private theorem tens_cv {νE : Measure (archGroup E n)} {νF : Measure (archGroup F n)} [νE.IsHaarMeasure] [νF.IsHaarMeasure]
    {b a : TI F n} {aE : TI E n} {aF : TI F n} (hs : ArchSlot D νE νF b a aE aF) {bE : archGroup E n → ℂ} (hbc : Continuous bE)
    (hb : ∀ x, bE x = ∏ i, b (compA D n i x)) (x : archGroup E n) :
    aE x = cv νE bE (fun y => conj (bE y⁻¹)) x := by
  obtain ⟨hgc, hcg, hgm, hgcont, hccont, -⟩ := archBasic F E σ 1 D n
  have hc : Continuous fun y => bE y * conj (bE (y⁻¹ * x)⁻¹) := by fun_prop
  have e0 : ∫ y, bE y * conj (bE (y⁻¹ * x)⁻¹) ∂νE =
      ∫ yy, bE (glueA D n yy) * conj (bE ((glueA D n yy)⁻¹ * x)⁻¹) ∂(Measure.pi fun _ => νF) := by
    rw [hs.meas]
    exact integral_map hgcont.aemeasurable hc.aestronglyMeasurable
  have e1 : ∀ yy : Fin (1 + 1) → archGroup F n, bE (glueA D n yy) * conj (bE ((glueA D n yy)⁻¹ * x)⁻¹) =
      ∏ i, (b (yy i) * conj (b ((yy i)⁻¹ * compA D n i x)⁻¹)) := fun yy => by
    rw [hb, hb, map_prod, Finset.prod_mul_distrib]
    simp only [map_mul, map_inv, hgc]
  simp only [cv]
  rw [e0]
  simp only [e1]
  rw [integral_fintype_prod_eq_prod (μ := fun _ => νF)
    fun i y => b y * conj (b (y⁻¹ * compA D n i x)⁻¹), hs.tens x]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [hs.sq]
  rfl

end Tens

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ _ σ D n hn κF eF κ e hF hE hSq νE _ νF _ hν φ hφ hφ0 hfix`. Use `haveI := hE.haar.prob`. Use `haveI : κ.IsMulLeftInvariant := ⟨fun k => (hE.haar.left k).map_eq⟩`. Use `haveI : νE.IsInvInvariant := isInvInvariant_archGroup νE`. Take `⟨hgc, hcg, hgm, hgcont, hccont, -, -, htens⟩` from `archBasic F E σ 1 D n`.

Choose the witnesses or unpack the hypotheses as in `⟨g₀, hg₀⟩ : ∃ g, φ g ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push Not at h`. Conclude with `hφ0 (funext h)`. Use `set ψ : archGroup E n → ℂ := fun x => φ (g₀ * archP E n x) with hψdef`.

Establish `hψ : Continuous ψ` using `hφ.comp (continuous_const.mul continuous_archP)`. Establish `hψf : ∀ w, ∫ k : archCompact E n, e k * ψ (w * k) ∂κ = ψ w` using `fun w => by`. Use `hfix (g₀ * archP E n w)` as an intermediate fact. Simplify `this` using `[hψdef, arc1, map_mul, mul_assoc]`. Establish `hψ1 : ψ 1 ≠ 0` using `by simpa [hψdef] using hg₀`.

Take `⟨O, hO, hne⟩` from `sq_ne κ νE hE.cont hE.star hψ hψf hψ1`. Establish `hglue1 : glueA D n 1 = 1`. Use `hcg 1` as an intermediate fact. Simplify using `only [map_one] at this`. Conclude with `this`.

Establish `hpre : glueA D n ⁻¹' O ∈ 𝓝 (1 : Fin (1 + 1) → archGroup F n)` using `hgcont.continuousAt.preimage_mem_nhds (by rw [hglue1]; exact hO)`. Rewrite `hpre` using `[nhds_pi, Filter.mem_pi]`. Take `⟨I, -, t, ht, hsub⟩` from `hpre`. Establish `hN : (⋂ i, t i) ∈ 𝓝 (1 : archGroup F n)` using `Filter.iInter_mem.2 ht`. Take `⟨β, b, hβc, hβs, hβ0, ⟨x₀, hx₀⟩, hβN, hbe, hbsm, hbfin, hbn⟩` from `exB hF νF hN`.

Take `⟨νE', _, a, aE, aF, hs⟩` from `archPositionEx F E σ 1 D n νF b hbsm hbfin hbn`. Establish `hs' : ArchSlot D νE νF b a aE aF` using `(hs.meas.trans hν.symm) ▸ hs`. Use `set βE : archGroup E n → ℝ := fun y => ∏ i, β (compA D n i y) with hβE`. Establish `hβEc : Continuous βE` using `continuous_finset_prod _ fun i _ => hβc.comp (hccont i)`. Establish `hβEc' : Continuous fun y => (βE y : ℂ)` using `by fun_prop`.

Establish `hbE : ∀ x, ec κ e (fun y => (βE y : ℂ)) x = ∏ i, b (compA D n i x)` using `fun x => by`. Simplify using `only [hbe]`. Conclude with `tens_ec D hF hE hSq hβc x`. Establish `hbEc` using `ec_cont κ hE.cont hβEc'`. Establish `hH` using `tens_cv D hs' hbEc hbE`.

Establish `hβs' : HasCompactSupport fun y => (β y : ℂ)` using `hβs.comp_left Complex.ofReal_zero`. Take `⟨βTI, hβTI⟩` from `exTI (Complex.continuous_ofReal.comp hβc) hβs'`. Take `⟨βT, hβT⟩` from `htens fun _ => βTI`. Establish `hβEs : HasCompactSupport βE`. Use `βT.hasCompactSupport.mono fun y hy hz => hy ?_` and prove the remaining obligations.

Establish `e1 : βT y = (βE y : ℂ)`. Rewrite using `[hβT y]`. Simplify using `[hβE, hβTI]`. Rewrite `hz` using `[e1]`. Conclude with `hz` after adjusting the coercions.

Establish `hβEs' : HasCompactSupport fun y => (βE y : ℂ)` using `hβEs.comp_left Complex.ofReal_zero`. Use `⟨b, a, aE, aF, hs', fun g => ?_, g₀, ?_⟩` and prove the remaining obligations. Simplify using `only [hH]`. Conclude with `bi_sq κ νE hE.cont hE.star hbEc (ec_cs κ e hβEs') (ec_idem κ hE.cont hE.idem hβEc') g`. Simplify using `only [hH]`.

Use `hne βE hβEc hβEs (fun y => Finset.prod_nonneg fun i _ => hβ0 _) ⟨glueA D n fun _ => x₀, ?_⟩ fun y hy => ?_` and prove the remaining obligations. Simplify using `only [hβE, hgc]`. Conclude with `Finset.prod_ne_zero_iff.2 fun _ _ => hx₀`. Establish `h1 : ∀ i, β (compA D n i y) ≠ 0` using `fun i => Finset.prod_ne_zero_iff.1 hy i (Finset.mem_univ _)`. Establish `h2 : (fun i => compA D n i y) ∈ glueA D n ⁻¹' O` using `hsub fun i _ => Set.mem_iInter.1 (hβN _ (h1 i)) i`.

Simplify `h2` using `[Set.mem_preimage, hcg]`.
-/
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.ampEx :
    AmpEx := by
  intro F E _ _ _ _ _ _ _ σ D n hn κF eF κ e hF hE hSq νE _ νF _ hν φ hφ hφ0 hfix
  haveI := hE.haar.prob
  haveI : κ.IsMulLeftInvariant := ⟨fun k => (hE.haar.left k).map_eq⟩
  haveI : νE.IsInvInvariant := isInvInvariant_archGroup νE
  obtain ⟨hgc, hcg, hgm, hgcont, hccont, -, -, htens⟩ := archBasic F E σ 1 D n
  obtain ⟨g₀, hg₀⟩ : ∃ g, φ g ≠ 0 := by
    by_contra h
    push Not at h
    exact hφ0 (funext h)
  set ψ : archGroup E n → ℂ := fun x => φ (g₀ * archP E n x) with hψdef
  have hψ : Continuous ψ := hφ.comp (continuous_const.mul continuous_archP)
  have hψf : ∀ w, ∫ k : archCompact E n, e k * ψ (w * k) ∂κ = ψ w := fun w => by
    have := hfix (g₀ * archP E n w)
    simpa [hψdef, arc1, map_mul, mul_assoc] using this
  have hψ1 : ψ 1 ≠ 0 := by simpa [hψdef] using hg₀
  obtain ⟨O, hO, hne⟩ := sq_ne κ νE hE.cont hE.star hψ hψf hψ1
  have hglue1 : glueA D n 1 = 1 := by
    have := hcg 1
    simp only [map_one] at this
    exact this
  have hpre : glueA D n ⁻¹' O ∈ 𝓝 (1 : Fin (1 + 1) → archGroup F n) :=
    hgcont.continuousAt.preimage_mem_nhds (by rw [hglue1]; exact hO)
  rw [nhds_pi, Filter.mem_pi] at hpre
  obtain ⟨I, -, t, ht, hsub⟩ := hpre
  have hN : (⋂ i, t i) ∈ 𝓝 (1 : archGroup F n) := Filter.iInter_mem.2 ht
  obtain ⟨β, b, hβc, hβs, hβ0, ⟨x₀, hx₀⟩, hβN, hbe, hbsm, hbfin, hbn⟩ := exB hF νF hN
  obtain ⟨νE', _, a, aE, aF, hs⟩ := archPositionEx F E σ 1 D n νF b hbsm hbfin hbn
  have hs' : ArchSlot D νE νF b a aE aF := (hs.meas.trans hν.symm) ▸ hs
  set βE : archGroup E n → ℝ := fun y => ∏ i, β (compA D n i y) with hβE
  have hβEc : Continuous βE := continuous_finset_prod _ fun i _ => hβc.comp (hccont i)
  have hβEc' : Continuous fun y => (βE y : ℂ) := by fun_prop
  have hbE : ∀ x, ec κ e (fun y => (βE y : ℂ)) x = ∏ i, b (compA D n i x) := fun x => by
    simp only [hbe]
    exact tens_ec D hF hE hSq hβc x
  have hbEc := ec_cont κ hE.cont hβEc'
  have hH := tens_cv D hs' hbEc hbE
  have hβs' : HasCompactSupport fun y => (β y : ℂ) := hβs.comp_left Complex.ofReal_zero
  obtain ⟨βTI, hβTI⟩ := exTI (Complex.continuous_ofReal.comp hβc) hβs'
  obtain ⟨βT, hβT⟩ := htens fun _ => βTI
  have hβEs : HasCompactSupport βE := by
    refine βT.hasCompactSupport.mono fun y hy hz => hy ?_
    have e1 : βT y = (βE y : ℂ) := by
      rw [hβT y]
      simp [hβE, hβTI]
    rw [e1] at hz
    exact_mod_cast hz
  have hβEs' : HasCompactSupport fun y => (βE y : ℂ) := hβEs.comp_left Complex.ofReal_zero
  refine ⟨b, a, aE, aF, hs', fun g => ?_, g₀, ?_⟩
  · simp only [hH]
    exact bi_sq κ νE hE.cont hE.star hbEc (ec_cs κ e hβEs') (ec_idem κ hE.cont hE.idem hβEc') g
  · simp only [hH]
    refine hne βE hβEc hβEs (fun y => Finset.prod_nonneg fun i _ => hβ0 _) ⟨glueA D n fun _ => x₀, ?_⟩ fun y hy => ?_
    · simp only [hβE, hgc]
      exact Finset.prod_ne_zero_iff.2 fun _ _ => hx₀
    · have h1 : ∀ i, β (compA D n i y) ≠ 0 := fun i => Finset.prod_ne_zero_iff.1 hy i (Finset.mem_univ _)
      have h2 : (fun i => compA D n i y) ∈ glueA D n ⁻¹' O := hsub fun i _ => Set.mem_iInter.1 (hβN _ (h1 i)) i
      simpa [Set.mem_preimage, hcg] using h2
