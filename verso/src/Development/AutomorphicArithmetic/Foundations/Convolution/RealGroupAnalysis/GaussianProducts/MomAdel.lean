import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ExistsRowSec
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.MomChar
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.CharZero
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ProdExt

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

/- English proof (translation)
Rewrite using `[totallyDisconnectedSpace_iff_connectedComponent_zero]`. Use `Set.eq_singleton_iff_unique_mem.mpr ⟨mem_connectedComponent, fun x hx => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Establish `hr : (Valued.v : Valuation (v.adicCompletion F) _).restrict x ≠ 0` using `(Valuation.zero_iff _).not.mpr hne`. Establish `hc` using `Valued.isClopen_ball (R := v.adicCompletion F) ((Valued.v : Valuation (v.adicCompletion F) _).restrict x)`.

Establish `h0 : (0 : v.adicCompletion F) ∈ {y | (Valued.v : Valuation (v.adicCompletion F) _).restrict y < (Valued.v : Valuation (v.adicCompletion F) _).restrict x}`. Simplify using `only [Set.mem_ofPred_eq, map_zero]`. Conclude with `pos_iff_ne_zero.mpr hr`. Establish `h1` using `hc.connectedComponent_subset h0 hx`. Conclude with `(lt_irrefl ((Valued.v : Valuation (v.adicCompletion F) _).restrict x)) h1`.
-/
private theorem td_adic {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    TotallyDisconnectedSpace (v.adicCompletion F) := by
  rw [totallyDisconnectedSpace_iff_connectedComponent_zero]
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨mem_connectedComponent, fun x hx => ?_⟩
  by_contra hne
  have hr : (Valued.v : Valuation (v.adicCompletion F) _).restrict x ≠ 0 :=
    (Valuation.zero_iff _).not.mpr hne
  have hc := Valued.isClopen_ball (R := v.adicCompletion F)
    ((Valued.v : Valuation (v.adicCompletion F) _).restrict x)
  have h0 : (0 : v.adicCompletion F) ∈
      {y | (Valued.v : Valuation (v.adicCompletion F) _).restrict y <
        (Valued.v : Valuation (v.adicCompletion F) _).restrict x} := by
    simp only [Set.mem_ofPred_eq, map_zero]
    exact pos_iff_ne_zero.mpr hr
  have h1 := hc.connectedComponent_subset h0 hx
  exact (lt_irrefl ((Valued.v : Valuation (v.adicCompletion F) _).restrict x)) h1

/- English proof (translation)
Use `haveI : ∀ v : HeightOneSpectrum (𝓞 F), TotallyDisconnectedSpace (v.adicCompletion F) := fun v => td_adic v`. Use `⟨isTotallyDisconnected_of_image (f := fun (x : FiniteAdeleRing (𝓞 F) F) v => x v) (continuous_pi fun v => RestrictedProduct.continuous_eval v).continuousOn (fun x y h => Subtype.ext (funext fun v => congrFun h v)) (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩` and prove the remaining obligations.
-/
private theorem td_fin (F : Type) [Field F] [NumberField F] :
    TotallyDisconnectedSpace (FiniteAdeleRing (𝓞 F) F) := by
  haveI : ∀ v : HeightOneSpectrum (𝓞 F), TotallyDisconnectedSpace (v.adicCompletion F) :=
    fun v => td_adic v
  refine ⟨isTotallyDisconnected_of_image (f := fun (x : FiniteAdeleRing (𝓞 F) F) v => x v)
    (continuous_pi fun v => RestrictedProduct.continuous_eval v).continuousOn
    (fun x y h => Subtype.ext (funext fun v => congrFun h v))
    (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩

/- English proof (translation)
Use `haveI := td_fin F`. Establish `hb : TopologicalSpace.IsTopologicalBasis {s : Set (Fin 2 → FiniteAdeleRing (𝓞 F) F) | IsClopen s}` using `loc_compact_Haus_tot_disc_of_zero_dim`. Use `TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds (fun T hT => hT.2) ?_` and prove the remaining obligations. Introduce `x U hx hU`. Take `⟨K, hKc, hxK, hKU⟩` from `exists_compact_subset hU hx`.

Take `⟨C, hC, hxC, hCU⟩` from `hb.exists_subset_of_mem_open hxK isOpen_interior`. Conclude with `⟨C, ⟨hKc.of_isClosed_subset hC.isClosed (hCU.trans interior_subset), hC.isOpen⟩, hxC, hCU.trans (interior_subset.trans hKU)⟩`.
-/
private theorem basis_fin (F : Type) [Field F] [NumberField F] :
    TopologicalSpace.IsTopologicalBasis
      {T : Set (Fin 2 → FiniteAdeleRing (𝓞 F) F) | IsCompact T ∧ IsOpen T} := by
  haveI := td_fin F
  have hb : TopologicalSpace.IsTopologicalBasis
      {s : Set (Fin 2 → FiniteAdeleRing (𝓞 F) F) | IsClopen s} :=
    loc_compact_Haus_tot_disc_of_zero_dim
  refine TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds (fun T hT => hT.2) ?_
  intro x U hx hU
  obtain ⟨K, hKc, hxK, hKU⟩ := exists_compact_subset hU hx
  obtain ⟨C, hC, hxC, hCU⟩ := hb.exists_subset_of_mem_open hxK isOpen_interior
  exact ⟨C, ⟨hKc.of_isClosed_subset hC.isClosed (hCU.trans interior_subset), hC.isOpen⟩, hxC,
    hCU.trans (interior_subset.trans hKU)⟩

section
variable (F : Type) [Field F] [NumberField F] [IsTotallyReal F]

/- English proof (translation)
The claim follows from `continuous_pi fun w => (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).continuous.comp (continuous_apply w)`.
-/
private theorem cont_symm : Continuous (TR.infEq F).symm :=
  continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).continuous.comp
      (continuous_apply w)

/- English proof (translation)
The claim follows from `(cont_symm F).comp continuous_fst`.
-/
private theorem cont_pInf : Continuous (TR.pInf F) := (cont_symm F).comp continuous_fst

private noncomputable def xc (v : Fin 2 → A F) : Fin 2 × InfinitePlace F → ℝ := fun p => TR.pInf F (v p.1) p.2

private noncomputable def ec (y : (Fin 2 × InfinitePlace F → ℝ) × (Fin 2 → FiniteAdeleRing (𝓞 F) F)) :
    Fin 2 → A F :=
  fun i => ((TR.infEq F (fun w => y.1 (i, w)), y.2 i) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)

/- English proof (translation)
The claim follows from `continuous_pi fun p => (continuous_apply p.2).comp ((cont_pInf F).comp (continuous_apply p.1))`.
-/
private theorem cont_xc : Continuous (xc F) :=
  continuous_pi fun p => (continuous_apply p.2).comp ((cont_pInf F).comp (continuous_apply p.1))

/- English proof (translation)
The claim follows from `continuous_pi fun i => continuous_snd.comp (continuous_apply i)`.
-/
private theorem cont_fin : Continuous (finPartPi : (Fin 2 → A F) → Fin 2 → FiniteAdeleRing (𝓞 F) F) :=
  continuous_pi fun i => continuous_snd.comp (continuous_apply i)

/- English proof (translation)
Use `continuous_pi fun i => ?_` and prove the remaining obligations. Conclude with `((TR.continuous_infEq F).comp (continuous_pi fun w => (continuous_apply (i, w)).comp continuous_fst)).prodMk ((continuous_apply i).comp continuous_snd)`.
-/
private theorem cont_ec : Continuous (ec F) := by
  refine continuous_pi fun i => ?_
  exact ((TR.continuous_infEq F).comp (continuous_pi fun w =>
    (continuous_apply (i, w)).comp continuous_fst)).prodMk ((continuous_apply i).comp continuous_snd)

/- English proof (translation)
Use function extensionality and compare the values at `i`. Use `TR.ad_ext ?_ rfl` and prove the remaining obligations. Conclude with `(TR.infEq F).symm_apply_apply _`.
-/
private theorem ec_xc (v : Fin 2 → A F) : ec F (xc F v, finPartPi v) = v := by
  funext i
  refine TR.ad_ext ?_ rfl
  exact (TR.infEq F).symm_apply_apply _

/- English proof (translation)
Establish `h : (fun v : Fin 2 → A F => ((∑ p, t p * xc F v p : ℝ) : ℂ)) = ∑ p, (t p : ℂ) • (fun v : Fin 2 → A F => ((TR.pInf F (v p.1) p.2 : ℝ) : ℂ))`. Use function extensionality and compare the values at `v`. Simplify using `[Finset.sum_apply, xc]`. Establish `h1 : (fun v : Fin 2 → A F => ((∑ p, t p * xc F v p : ℝ) : ℂ)) ∈ polyOn F (Fin 2)`. Rewrite using `[h]`.

Use `Subalgebra.sum_mem _ fun p _ => Subalgebra.smul_mem _ ?_ _` and prove the remaining obligations. Conclude with `Algebra.subset_adjoin (show _ ∈ {g : (Fin 2 → A F) → ℂ | ∃ i w, g = fun v => ((TR.pInf F (v i) w : ℝ) : ℂ)} from ⟨p.1, p.2, rfl⟩)`. Conclude with `Subalgebra.pow_mem _ h1 n`.
-/
private theorem poly_mem (t : Fin 2 × InfinitePlace F → ℝ) (n : ℕ) :
    (fun v : Fin 2 → A F => ((∑ p, t p * xc F v p : ℝ) : ℂ) ^ n) ∈ polyOn F (Fin 2) := by
  have h : (fun v : Fin 2 → A F => ((∑ p, t p * xc F v p : ℝ) : ℂ))
      = ∑ p, (t p : ℂ) • (fun v : Fin 2 → A F => ((TR.pInf F (v p.1) p.2 : ℝ) : ℂ)) := by
    funext v
    simp [Finset.sum_apply, xc]
  have h1 : (fun v : Fin 2 → A F => ((∑ p, t p * xc F v p : ℝ) : ℂ)) ∈ polyOn F (Fin 2) := by
    rw [h]
    refine Subalgebra.sum_mem _ fun p _ => Subalgebra.smul_mem _ ?_ _
    exact Algebra.subset_adjoin (show _ ∈ {g : (Fin 2 → A F) → ℂ | ∃ i w, g = fun v => ((TR.pInf F (v i) w : ℝ) : ℂ)} from ⟨p.1, p.2, rfl⟩)
  exact Subalgebra.pow_mem _ h1 n

/- English proof (translation)
Rewrite using `[Fintype.sum_prod_type]`. Both sides reduce to the same expression.
-/
private theorem sum_xc (v : Fin 2 → A F) : ∑ p, |xc F v p| = sz v := by
  rw [Fintype.sum_prod_type]; rfl

end

/- English proof (translation)
Introduce `F _ _ _ Ω _ ν r ρ hr hint hmom q hq hq1`. Establish `hρ : Integrable ρ ν` using `by simpa using hint 0`. Establish `hX : Measurable fun ω => xc F (r ω)` using `(cont_xc F).measurable.comp hr`. Establish `hs : Measurable fun ω => (finPartPi (r ω) : Fin 2 → FiniteAdeleRing (𝓞 F) F)` using `(cont_fin F).measurable.comp hr`. Establish `hT : ∀ (T : Set (Fin 2 → FiniteAdeleRing (𝓞 F) F)) (S : Set (Fin 2 × InfinitePlace F → ℝ)), MeasurableSet S → IsCompact T → IsOpen T → ∫ ω, S.indicator 1 (xc F (r ω)) * (T.indicator 1 (finPartPi (r ω)) * ρ ω) ∂ν = 0`.

Introduce `T S hS hTc hTo`. Establish `hi : Measurable fun ω => T.indicator (1 : (Fin 2 → FiniteAdeleRing (𝓞 F) F) → ℂ) (finPartPi (r ω))` using `(measurable_one.indicator hTo.measurableSet).comp hs`. Establish `hib : ∀ ω, ‖T.indicator (1 : (Fin 2 → FiniteAdeleRing (𝓞 F) F) → ℂ) (finPartPi (r ω))‖ ≤ 1`. Introduce `ω`. Apply the tactic sequence `by_cases h : finPartPi (r ω) ∈ T <;> simp [h]`.

Establish `hI : ∀ g : Ω → ℂ, Integrable g ν → Integrable (fun ω => T.indicator (1 : (Fin 2 → FiniteAdeleRing (𝓞 F) F) → ℂ) (finPartPi (r ω)) * g ω) ν` using `fun g hg => hg.bdd_mul hi.aestronglyMeasurable (Eventually.of_forall hib)`. Use `charZero Ω _ ν _ _ hX (hI ρ hρ) ?_ S hS` and prove the remaining obligations. Use `momChar Ω _ ν _ _ hX (fun R => ?_) (fun n t => ?_)` and prove the remaining obligations. Simplify using `only [sum_xc]`. Use `(hI _ (hint R)).congr (Eventually.of_forall fun ω => ?_)` and prove the remaining obligations.

Simplify using `only`. Expand and normalize the polynomial expressions, which then agree. Use `hmom _ (poly_mem F t n) T hTc hTo` as an intermediate fact. Rewrite using `[← this]`. Use `integral_congr_ae (Eventually.of_forall fun ω => ?_)` and prove the remaining obligations.

Simplify using `only`. Expand and normalize the polynomial expressions, which then agree. Establish `hQ : Measurable fun y => q (ec F y)` using `hq.comp (cont_ec F).measurable`. Use `prodExt Ω _ _ ν (fun ω => xc F (r ω)) (fun ω => finPartPi (r ω)) ρ (basis_fin F) hX hs hρ (fun S T hS hTc hTo => hT T S hS hTc hTo) _ hQ (fun y => hq1 _)` as an intermediate fact. Simplify `this` using `only [ec_xc]`.
-/
theorem UpperTheory.ConvolutionTheory.R2.G.momAdel :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (Ω : Type) [MeasurableSpace Ω] (ν : Measure Ω) (r : Ω → Fin 2 → A F) (ρ : Ω → ℂ), Measurable r →
    (∀ R : ℝ, Integrable (fun ω => ((Real.exp (R * sz (r ω)) : ℝ) : ℂ) * ρ ω) ν) →
    (∀ p ∈ polyOn F (Fin 2), ∀ T : Set (Fin 2 → FiniteAdeleRing (𝓞 F) F), IsCompact T → IsOpen T → ∫ ω, p (r ω) * T.indicator 1 (finPartPi (r ω)) * ρ ω ∂ν = 0) →
    ∀ q : (Fin 2 → A F) → ℂ, Measurable q → (∀ x, ‖q x‖ ≤ 1) → ∫ ω, q (r ω) * ρ ω ∂ν = 0 := by
  intro F _ _ _ Ω _ ν r ρ hr hint hmom q hq hq1
  have hρ : Integrable ρ ν := by simpa using hint 0
  have hX : Measurable fun ω => xc F (r ω) := (cont_xc F).measurable.comp hr
  have hs : Measurable fun ω => (finPartPi (r ω) : Fin 2 → FiniteAdeleRing (𝓞 F) F) :=
    (cont_fin F).measurable.comp hr
  have hT : ∀ (T : Set (Fin 2 → FiniteAdeleRing (𝓞 F) F)) (S : Set (Fin 2 × InfinitePlace F → ℝ)),
      MeasurableSet S → IsCompact T → IsOpen T →
      ∫ ω, S.indicator 1 (xc F (r ω)) * (T.indicator 1 (finPartPi (r ω)) * ρ ω) ∂ν = 0 := by
    intro T S hS hTc hTo
    have hi : Measurable fun ω => T.indicator (1 : (Fin 2 → FiniteAdeleRing (𝓞 F) F) → ℂ) (finPartPi (r ω)) :=
      (measurable_one.indicator hTo.measurableSet).comp hs
    have hib : ∀ ω, ‖T.indicator (1 : (Fin 2 → FiniteAdeleRing (𝓞 F) F) → ℂ) (finPartPi (r ω))‖ ≤ 1 := by
      intro ω
      by_cases h : finPartPi (r ω) ∈ T <;> simp [h]
    have hI : ∀ g : Ω → ℂ, Integrable g ν →
        Integrable (fun ω => T.indicator (1 : (Fin 2 → FiniteAdeleRing (𝓞 F) F) → ℂ) (finPartPi (r ω)) * g ω) ν :=
      fun g hg => hg.bdd_mul hi.aestronglyMeasurable (Eventually.of_forall hib)
    refine charZero Ω _ ν _ _ hX (hI ρ hρ) ?_ S hS
    refine momChar Ω _ ν _ _ hX (fun R => ?_) (fun n t => ?_)
    · simp only [sum_xc]
      refine (hI _ (hint R)).congr (Eventually.of_forall fun ω => ?_)
      simp only
      ring
    · have := hmom _ (poly_mem F t n) T hTc hTo
      rw [← this]
      refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
      simp only
      ring
  have hQ : Measurable fun y => q (ec F y) := hq.comp (cont_ec F).measurable
  have := prodExt Ω _ _ ν (fun ω => xc F (r ω)) (fun ω => finPartPi (r ω)) ρ (basis_fin F) hX hs hρ
    (fun S T hS hTc hTo => hT T S hS hTc hTo) _ hQ (fun y => hq1 _)
  simpa only [ec_xc] using this
