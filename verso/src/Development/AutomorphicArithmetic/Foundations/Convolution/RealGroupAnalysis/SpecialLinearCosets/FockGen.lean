import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.GoodU
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.RationalGL2InfiniteFiniteFactor
import GroundTheory.GlobalFields.TateThesis.GaussianSchwartz

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.ConvolutionTheory.R2.I
open scoped Classical

private noncomputable def scaleEquiv (F : Type) [Field F] [NumberField F] [IsTotallyReal F]
    (c : Fin 4 × InfinitePlace F → ℝ) (hc : ∀ p, c p ≠ 0) :
    (Fin 4 → NumberField.mixedEmbedding.mixedSpace F) ≃L[ℝ] EuclideanSpace ℝ (Fin 4 × InfinitePlace F) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun x => WithLp.toLp 2 fun p => c p * (x p.1).1 ⟨p.2, IsTotallyReal.isReal p.2⟩
      map_add' := fun x y => by ext p; simp [mul_add]
      map_smul' := fun a x => by ext p; simp; ring
      invFun := fun y i => (fun w => (c (i, w.1))⁻¹ * y (i, w.1), fun _ => 0)
      left_inv := fun x => by
        funext i
        refine Prod.ext (funext fun w => ?_) (funext fun w => ?_)
        · simp [hc]
        · exact absurd (IsTotallyReal.isReal w.1) (InfinitePlace.not_isReal_iff_isComplex.2 w.2)
      right_inv := fun y => by ext p; simp [hc] }

/- English proof (translation)
Simplify using `only [infPartPi, homeomorphMixedSpace_apply, InfiniteAdeleRing.ringEquiv_mixedSpace_apply]`. Express the relevant statement in the definitionally equal form `_ = InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w) ((v i).1 w)`. Rewrite using `[InfinitePlace.Completion.ringEquivRealOfIsReal_apply]`.
-/
private theorem coord_infPart {F : Type} [Field F] [NumberField F] [IsTotallyReal F]
    (v : Fin 4 → A F) (i : Fin 4) (w : InfinitePlace F) :
    (infPartPi v i).1 ⟨w, IsTotallyReal.isReal w⟩ = TR.pInf F (v i) w := by
  simp only [infPartPi, homeomorphMixedSpace_apply, InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  change _ = InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w) ((v i).1 w)
  rw [InfinitePlace.Completion.ringEquivRealOfIsReal_apply]

/- English proof (translation)
Proceed by induction on `hp using Algebra.adjoin_induction with`. Consider the case `mem p hp`. Take `⟨i, w, rfl⟩` from `hp`. Set `l : (Fin 4 → NumberField.mixedEmbedding.mixedSpace F) →L[ℝ] ℝ` to `(ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : {w : InfinitePlace F // w.IsReal} => ℝ) ⟨w, IsTotallyReal.isReal w⟩).comp ((ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.proj (R := ℝ) i))`. Use `⟨fun x => ((l x : ℝ) : ℂ), Complex.ofRealCLM.hasTemperateGrowth.comp l.hasTemperateGrowth, fun X => ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `_ = (((infPartPi X i).1 ⟨w, IsTotallyReal.isReal w⟩ : ℝ) : ℂ)`. Rewrite using `[coord_infPart]`. Consider the case `algebraMap r`. Conclude with `⟨fun _ => r, Function.HasTemperateGrowth.const r, fun X => rfl⟩`. Consider the case `add p q _ _ hp hq`.

Take `⟨f, hf, hfp⟩` from `hp`. Take `⟨g, hg, hgq⟩` from `hq`. Conclude with `⟨fun x => f x + g x, hf.add hg, fun X => by simp [hfp, hgq]⟩`. Consider the case `mul p q _ _ hp hq`. Take `⟨f, hf, hfp⟩` from `hp`.

Take `⟨g, hg, hgq⟩` from `hq`. Conclude with `⟨fun x => f x * g x, hf.mul hg, fun X => by simp [hfp, hgq]⟩`.
-/
private theorem poly_temperate {F : Type} [Field F] [NumberField F] [IsTotallyReal F]
    {p : V4 F → ℂ} (hp : p ∈ polyFn (F := F)) :
    ∃ f : (Fin 4 → NumberField.mixedEmbedding.mixedSpace F) → ℂ, f.HasTemperateGrowth ∧
      ∀ X, p X = f (infPartPi X) := by
  induction hp using Algebra.adjoin_induction with
  | mem p hp =>
    obtain ⟨i, w, rfl⟩ := hp
    let l : (Fin 4 → NumberField.mixedEmbedding.mixedSpace F) →L[ℝ] ℝ :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : {w : InfinitePlace F // w.IsReal} => ℝ)
        ⟨w, IsTotallyReal.isReal w⟩).comp
      ((ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.proj (R := ℝ) i))
    refine ⟨fun x => ((l x : ℝ) : ℂ), Complex.ofRealCLM.hasTemperateGrowth.comp l.hasTemperateGrowth, fun X => ?_⟩
    change _ = (((infPartPi X i).1 ⟨w, IsTotallyReal.isReal w⟩ : ℝ) : ℂ)
    rw [coord_infPart]
  | algebraMap r =>
    exact ⟨fun _ => r, Function.HasTemperateGrowth.const r, fun X => rfl⟩
  | add p q _ _ hp hq =>
    obtain ⟨f, hf, hfp⟩ := hp
    obtain ⟨g, hg, hgq⟩ := hq
    exact ⟨fun x => f x + g x, hf.add hg, fun X => by simp [hfp, hgq]⟩
  | mul p q _ _ hp hq =>
    obtain ⟨f, hf, hfp⟩ := hp
    obtain ⟨g, hg, hgq⟩ := hq
    exact ⟨fun x => f x * g x, hf.mul hg, fun X => by simp [hfp, hgq]⟩

/- English proof (translation)
Set `a : Fin 4 × InfinitePlace F → ℝ` to `fun p => ![1, 1, 2, -2 * InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal p.2) δ] p.1`. Establish `ha : ∀ p, 0 < a p`. Introduce and unpack `⟨i, w⟩`. Use `hδ (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w))` as an intermediate fact. Apply the tactic sequence `fin_cases i <;> simp [a] <;> linarith`.

Establish `hc : ∀ p, √(a p) ≠ 0` using `fun p => (Real.sqrt_pos.2 (ha p)).ne'`. Use `⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (scaleEquiv F (fun p => √(a p)) hc) (gaussianSchwartz (EuclideanSpace ℝ (Fin 4 × InfinitePlace F))), fun X => ?_⟩` and prove the remaining obligations. Establish `hn : ‖scaleEquiv F (fun p => √(a p)) hc (infPartPi X)‖ ^ 2 = ∑ w, TR.pInf F (X 0 ^ 2 + X 1 ^ 2 + 2 * (X 2 ^ 2 - rt δ * X 3 ^ 2)) w`. Rewrite using `[EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type, Finset.sum_comm]`. Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations.

Establish `h : ∀ i, (scaleEquiv F (fun p => √(a p)) hc (infPartPi X)) (i, w) ^ 2 = a (i, w) * TR.pInf F (X i) w ^ 2`. Introduce `i`. Express the relevant statement in the definitionally equal form `(√(a (i, w)) * (infPartPi X i).1 ⟨w, IsTotallyReal.isReal w⟩) ^ 2 = _`. Rewrite using `[coord_infPart, mul_pow, Real.sq_sqrt (ha _).le]`. Establish `hd : TR.pInf F (rt δ) w = InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w) δ` using `congrFun (GlobalTheory.HilbertThetaSeries.RatPts.pInf_algebraMap F δ) w`.

Simplify using `only [Fin.sum_univ_four, h, map_add, map_mul, map_pow, map_sub, Pi.add_apply, Pi.mul_apply, Pi.pow_apply, Pi.sub_apply, map_ofNat, Pi.ofNat_apply, hd]`. Simplify using `[a]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply, gaussianSchwartz_apply, hn]`. Simplify using `only [gauss]`.

Use `push_cast`. Both sides reduce to the same expression.
-/
private theorem gauss_schwartz {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (δ : F)
    (hδ : ∀ φ : F →+* ℝ, φ δ < 0) :
    ∃ s : SchwartzMap (Fin 4 → NumberField.mixedEmbedding.mixedSpace F) ℂ, ∀ X, gauss δ X = s (infPartPi X) := by
  let a : Fin 4 × InfinitePlace F → ℝ := fun p =>
    ![1, 1, 2, -2 * InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal p.2) δ] p.1
  have ha : ∀ p, 0 < a p := by
    rintro ⟨i, w⟩
    have := hδ (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w))
    fin_cases i <;> simp [a] <;> linarith
  have hc : ∀ p, √(a p) ≠ 0 := fun p => (Real.sqrt_pos.2 (ha p)).ne'
  refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (scaleEquiv F (fun p => √(a p)) hc)
      (gaussianSchwartz (EuclideanSpace ℝ (Fin 4 × InfinitePlace F))), fun X => ?_⟩
  have hn : ‖scaleEquiv F (fun p => √(a p)) hc (infPartPi X)‖ ^ 2 =
      ∑ w, TR.pInf F (X 0 ^ 2 + X 1 ^ 2 + 2 * (X 2 ^ 2 - rt δ * X 3 ^ 2)) w := by
    rw [EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun w _ => ?_
    have h : ∀ i, (scaleEquiv F (fun p => √(a p)) hc (infPartPi X)) (i, w) ^ 2 = a (i, w) * TR.pInf F (X i) w ^ 2 := by
      intro i
      change (√(a (i, w)) * (infPartPi X i).1 ⟨w, IsTotallyReal.isReal w⟩) ^ 2 = _
      rw [coord_infPart, mul_pow, Real.sq_sqrt (ha _).le]
    have hd : TR.pInf F (rt δ) w = InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w) δ :=
      congrFun (GlobalTheory.HilbertThetaSeries.RatPts.pInf_algebraMap F δ) w
    simp only [Fin.sum_univ_four, h, map_add, map_mul, map_pow, map_sub, Pi.add_apply, Pi.mul_apply, Pi.pow_apply, Pi.sub_apply, map_ofNat, Pi.ofNat_apply, hd]
    simp [a]
    ring
  simp only [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply, gaussianSchwartz_apply, hn]
  simp only [gauss]
  push_cast
  rfl

/- English proof (translation)
Introduce `F _ _ _ δ hδ p hp g hg`. Take `⟨f, hf, hfp⟩` from `poly_temperate hp`. Take `⟨s, hs⟩` from `gauss_schwartz δ hδ`. Establish `h` using `schwartzBruhatTensorPi_mem (SchwartzMap.smulLeftCLM ℂ f s) hg`. Use `h using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `X`. Simplify using `only [schwartzBruhatTensorPi, SchwartzMap.smulLeftCLM_apply_apply hf, hfp, hs, smul_eq_mul]`.
-/
theorem UpperTheory.ConvolutionTheory.R2.I.fockGen :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (δ : F), (∀ φ : F →+* ℝ, φ δ < 0) →
      ∀ p ∈ polyFn (F := F), ∀ g ∈ finiteSchwartzBruhatPi F (ι := Fin 4),
        (fun X => p X * gauss δ X * g (finPartPi X)) ∈ schwartzBruhatPi F (Fin 4) := by
  intro F _ _ _ δ hδ p hp g hg
  obtain ⟨f, hf, hfp⟩ := poly_temperate hp
  obtain ⟨s, hs⟩ := gauss_schwartz δ hδ
  have h := schwartzBruhatTensorPi_mem (SchwartzMap.smulLeftCLM ℂ f s) hg
  convert h using 1
  funext X
  simp only [schwartzBruhatTensorPi, SchwartzMap.smulLeftCLM_apply_apply hf, hfp, hs, smul_eq_mul]
