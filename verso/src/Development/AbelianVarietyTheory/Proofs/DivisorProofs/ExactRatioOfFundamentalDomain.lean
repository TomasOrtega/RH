import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasAtOf
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OneMeasureSizes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.QuotMeasureEqSmul
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HcFiniteAndSchurMult
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CuspFormsRapidDecayStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdLowestKTypeDimsIndepComplexEmbeddingStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open Formalism.MainNotions
open MeasureTheory Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Mult Formalism.BasicNotions.TH Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ExactRatioProof

open scoped InnerProductSpace ComplexConjugate

/- English proof (translation)
The claim follows from `GlobalTheory.T.prod_lowestKTypeDims_indep_complexEmbedding`.
-/
theorem L1 : ∀ (D : D7) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (∏ ρ, ((dimK _ _ (kapAt (Wc D i) σ ρ) : ℚ) : ℂ)) = ((∏ τ, GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.dimAt D i τ : ℝ) : ℂ) := GlobalTheory.T.prod_lowestKTypeDims_indep_complexEmbedding

/- English proof (translation)
Substitute `hV` using the available equality. Establish `hj : InR D ((i : ℕ) + 1)` using `⟨Nat.le_add_left _ _, i.2⟩`. Establish `hmu` using `h.muUnit _ hj s hs`. Establish `hcu` using `h.cUnit _ hj s hs`. Use `set c := lieFacZ (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.expW D i) with hcdef`.

Establish `hc0 : 0 < c` using `lieFacZ_pos _ _`. Unfold `petE`. Rewrite using `[← Real.enorm_eq_ofReal hc0.le, ← eLpNorm_const_smul]`. Use `eLpNorm_congr_norm_ae (Filter.Eventually.of_forall fun q => ?_)` and prove the remaining obligations. Simplify using `only [Pi.smul_apply, smul_eq_mul, norm_norm, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc0, adel_muPin]`.

Rewrite using `[hcu, hmu.2.1]`. Simplify using `only [abs_one, one_mul, abs_norm, abs_of_nonneg (ptN_nonneg _ _ _)]`. Unfold `ptN`. Rewrite using `[pnorm_eq_of_unit _ _ _ _ (hmu.2.2.2 _)]`.
-/
theorem K2aux (D : D7) (T : CoreJ D) (h : LawsJ T) (i : Fin D.R.m) (s : T.Q.c.F →+* ℂ) (hs : GoodEmb T.Q.c s)
    (f : FDSec (T.U ((i : ℕ) + 1) s).X) (W : HSp D) (hV : T.V ((i : ℕ) + 1) s = W) :
    eLpNorm (fun q : AutQ W => ‖(hV ▸ ((lieFacZ (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.expW D i) : ℂ) •
      adel (T.V ((i : ℕ) + 1) s) (T.dict ((i : ℕ) + 1) s)
        (muPin (T.V ((i : ℕ) + 1) s) (T.dict ((i : ℕ) + 1) s) (T.mu ((i : ℕ) + 1) s) (T.cE ((i : ℕ) + 1) s)) f) :
          GA D W → ℂ) q.out‖) 2 (muQ1 W) =
      ENNReal.ofReal (lieFacZ (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.expW D i)) *
        petE (T.V ((i : ℕ) + 1) s) (T.dict ((i : ℕ) + 1) s) (muQ1 (T.V ((i : ℕ) + 1) s))
          (modelWt (T.U ((i : ℕ) + 1) s) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.expW D i)) f := by
  subst hV
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  have hmu := h.muUnit _ hj s hs
  have hcu := h.cUnit _ hj s hs
  set c := lieFacZ (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.expW D i) with hcdef
  have hc0 : 0 < c := lieFacZ_pos _ _
  unfold petE
  rw [← Real.enorm_eq_ofReal hc0.le, ← eLpNorm_const_smul]
  refine eLpNorm_congr_norm_ae (Filter.Eventually.of_forall fun q => ?_)
  simp only [Pi.smul_apply, smul_eq_mul, norm_norm, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hc0, adel_muPin]
  rw [hcu, hmu.2.1]
  simp only [abs_one, one_mul, abs_norm, abs_of_nonneg (ptN_nonneg _ _ _)]
  unfold ptN
  rw [pnorm_eq_of_unit _ _ _ _ (hmu.2.2.2 _)]

/- English proof (translation)
Introduce `D T h i s hs hV f` and use `K2aux D T h i s hs f (Wc D i) hV`.
-/
theorem K2 : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ (i : Fin D.R.m) (s : T.Q.c.F →+* ℂ), GoodEmb T.Q.c s → ∀ (hV : T.V ((i : ℕ) + 1) s = Wc D i) (f : FDSec (T.U ((i : ℕ) + 1) s).X), eLpNorm (fun q : AutQ (Wc D i) => ‖GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.adFun T i hV f q.out‖) 2 (muQ1 (Wc D i)) = ENNReal.ofReal (lieFacZ (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.expW D i)) * petE (T.V ((i : ℕ) + 1) s) (T.dict ((i : ℕ) + 1) s) (muQ1 (T.V ((i : ℕ) + 1) s)) (modelWt (T.U ((i : ℕ) + 1) s) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.expW D i)) f :=
  fun D T h i s hs hV f => K2aux D T h i s hs f (Wc D i) hV

/- English proof (translation)
Introduce `D T h i s hs f hf`. Take `⟨th, hr, -, hdu⟩` from `h.dictU _ ⟨Nat.le_add_left _ _, i.2⟩ s hs`. Conclude with `petE_ne_top _ _ _ prob_le_one hdu.2.2.2.1 hf`.
-/
theorem K3 : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ (i : Fin D.R.m) (s : T.Q.c.F →+* ℂ), GoodEmb T.Q.c s → ∀ f ∈ GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.scalarForms T i s, petE (T.V ((i : ℕ) + 1) s) (T.dict ((i : ℕ) + 1) s) (muQ1 (T.V ((i : ℕ) + 1) s)) (modelWt (T.U ((i : ℕ) + 1) s) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.expW D i)) f ≠ ⊤ := by
  intro D T h i s hs f hf
  obtain ⟨th, hr, -, hdu⟩ := h.dictU _ ⟨Nat.le_add_left _ _, i.2⟩ s hs
  exact petE_ne_top _ _ _ prob_le_one hdu.2.2.2.1 hf

/- English proof (translation)
Introduce `hP D Tu C t0 hC i P μ 𝓕 hF T _ hT ha θ hθ σ M hV F hFm f hf hc`. Establish `hμ : μ.IsHaarMeasure` using `hF.1.1`. Establish `hS : ∃ c, IsMultIP M μ 𝓕 F F c` using `GlobalTheory.MultFinite.schurMult GlobalTheory.T.cusp_forms_rapid_decay μ 𝓕 hθ hμ hF.2 F hFm F hFm`. Use `⟨hS, ?_⟩` and prove the remaining obligations. Choose the witnesses or unpack the hypotheses as in `⟨v, hv1, hnorm⟩ : ∃ v : M.Vec, (∀ τ, ‖(v τ : M.H τ)‖ = 1) ∧ ∀ g, ‖F v g‖ = ‖GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.adFun T i hV f g‖ := by`.

Break down `hc with ⟨-, v, hv, e⟩ | ⟨-, v, hv, e⟩` into its components or cases. Conclude with `⟨v, fun τ => (hv τ).1, fun g => by rw [e]⟩`. Conclude with `⟨v, hv, fun g => by rw [e, RCLike.norm_conj]⟩`. Establish `hFM` using `(GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).1 hFm`. Establish `haut` using `hFM.aut v`.

Establish `h1` using `(ipM_spec M μ 𝓕 F F hS v v).2`. Establish `hprod : ∏ τ, ⟪(v τ : M.H τ), (v τ : M.H τ)⟫_ℂ = 1` using `Finset.prod_eq_one fun τ _ => by rw [inner_self_eq_norm_sq_to_K, hv1 τ]; simp`. Rewrite `h1` using `[hprod, mul_one]`. Establish `hs : GoodEmb T.Q.c (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.gd T σ)` using `goodEmb_goodOf _ _`. Use `set c := lieFacZ (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.expW D i) with hcdef`.

Establish `hc0 : 0 < c` using `lieFacZ_pos _ _`. Use `set ψ : AutQ (Wc D i) → ℂ := fun q => ((‖F v q.out‖ / c : ℝ) : ℂ) with hψdef`. Establish `hK2` using `K2 D T hT i _ hs hV f`. Establish `hK3` using `K3 D T hT i _ hs f hf`. Establish `hE : eLpNorm ψ 2 (muQ1 (Wc D i)) = petE (T.V ((i : ℕ) + 1) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.gd T σ)) (T.dict ((i : ℕ) + 1) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.gd T σ)) (muQ1 (T.V ((i : ℕ) + 1) (GlobalTheory.IndefiniteRowSideFullHecke.O …`.

Establish `e1 : eLpNorm ψ 2 (muQ1 (Wc D i)) = eLpNorm (c⁻¹ • fun q : AutQ (Wc D i) => ‖GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.adFun T i hV f q.out‖) 2 (muQ1 (Wc D i))`. Use `eLpNorm_congr_norm_ae (Filter.Eventually.of_forall fun q => ?_)` and prove the remaining obligations. Simplify using `only [hψdef, Pi.smul_apply, smul_eq_mul, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_norm, abs_of_pos hc0, abs_mul, abs_inv, hnorm]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1, eLpNorm_const_smul, hK2, ← mul_assoc, Real.enorm_eq_ofReal (inv_nonneg.2 hc0.le), ← ENNReal.ofReal_mul (inv_nonneg.2 hc0.le), inv_mul_cancel₀ hc0.ne', ENNReal.ofReal_one, one_mul]`.

Establish `hψm : AEStronglyMeasurable ψ (muQ1 (Wc D i))` using `by haveI : BorelSpace (GA D (Wc D i)) := ⟨rfl⟩`. Establish `hm : Measurable fun q : AutQ (Wc D i) => F v q.out`. Rewrite using `[measurable_from_quotient]`. Establish `e : ((fun q : AutQ (Wc D i) => F v q.out) ∘ Quotient.mk'') = F v` using `funext fun g => by`. Establish `h2 : g * (Quotient.mk (QuotientGroup.rightRel (GQ (Wc D i))) g).out⁻¹ ∈ GQ (Wc D i)` using `QuotientGroup.rightRel_apply.1 (Quotient.mk_out g)`.

Establish `h3` using `haut.left _ h2 (Quotient.mk (QuotientGroup.rightRel (GQ (Wc D i))) g).out`. Rewrite `h3` using `[inv_mul_cancel_right]`. Conclude with `h3.symm`. Rewrite using `[e]`. Conclude with `haut.cont.measurable`.

Use `Measurable.aestronglyMeasurable ?_` and prove the remaining obligations. Conclude with `Complex.measurable_ofReal.comp ((hm.norm).div_const c)`. Establish `hψ : MemLp ψ 2 (muQ1 (Wc D i))` using `⟨hψm, by rw [hE]; exact lt_top_iff_ne_top.2 hK3⟩`. Establish `hI` using `GlobalTheory.ReadingNorm.integral_star_mul (Wc D i) (D.sp.W_sig _) hμ hF.2 (F v) haut.left ψ hψ c (fun q => by`. Simplify using `only [hψdef, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_norm, abs_of_pos hc0]`.

Use the proof step `field_simp)`. Establish `hL : ‖hψ.toLp ψ‖ = (petE (T.V ((i : ℕ) + 1) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.gd T σ)) (T.dict ((i : ℕ) + 1) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.gd T σ)) (muQ1 (T.V ((i : ℕ) + 1) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes. …`. Rewrite using `[Lp.norm_toLp, hE]`. Rewrite using `[Formalism.IndefR.Links.ipAt, ← h1, hI, L1 D i σ, hL]`. Unfold `GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.ratio GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.probSq`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exactRatio : ∀ (hP : Hypotheses2) (D : D7) (Tu : Type) (C : LevCh D Tu) (t0 : Tu) (hC : C.Is t0) (i : Fin D.R.m) (P : LevelP C.Pg D.R.r ℂ) (μ : MeasureTheory.Measure (GA D (Wc D i))) (𝓕 : Set (GA D (Wc D i))) (hF : IsMeasFD (Wc D i) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW C i P) μ 𝓕), GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.ExactRatio C i P μ 𝓕 := by
  intro hP D Tu C t0 hC i P μ 𝓕 hF T _ hT ha θ hθ σ M hV F hFm f hf hc
  have hμ : μ.IsHaarMeasure := hF.1.1
  have hS : ∃ c, IsMultIP M μ 𝓕 F F c :=
    GlobalTheory.MultFinite.schurMult GlobalTheory.T.cusp_forms_rapid_decay μ 𝓕 hθ hμ hF.2 F hFm F hFm
  refine ⟨hS, ?_⟩
  obtain ⟨v, hv1, hnorm⟩ : ∃ v : M.Vec, (∀ τ, ‖(v τ : M.H τ)‖ = 1) ∧
      ∀ g, ‖F v g‖ = ‖GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.adFun T i hV f g‖ := by
    rcases hc with ⟨-, v, hv, e⟩ | ⟨-, v, hv, e⟩
    · exact ⟨v, fun τ => (hv τ).1, fun g => by rw [e]⟩
    · exact ⟨v, hv, fun g => by rw [e, RCLike.norm_conj]⟩
  have hFM := (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).1 hFm
  have haut := hFM.aut v
  have h1 := (ipM_spec M μ 𝓕 F F hS v v).2
  have hprod : ∏ τ, ⟪(v τ : M.H τ), (v τ : M.H τ)⟫_ℂ = 1 :=
    Finset.prod_eq_one fun τ _ => by rw [inner_self_eq_norm_sq_to_K, hv1 τ]; simp
  rw [hprod, mul_one] at h1
  have hs : GoodEmb T.Q.c (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.gd T σ) := goodEmb_goodOf _ _
  set c := lieFacZ (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.expW D i) with hcdef
  have hc0 : 0 < c := lieFacZ_pos _ _
  set ψ : AutQ (Wc D i) → ℂ := fun q => ((‖F v q.out‖ / c : ℝ) : ℂ) with hψdef
  have hK2 := K2 D T hT i _ hs hV f
  have hK3 := K3 D T hT i _ hs f hf
  have hE : eLpNorm ψ 2 (muQ1 (Wc D i)) = petE (T.V ((i : ℕ) + 1) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.gd T σ))
      (T.dict ((i : ℕ) + 1) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.gd T σ)) (muQ1 (T.V ((i : ℕ) + 1) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.gd T σ)))
      (modelWt (T.U ((i : ℕ) + 1) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.gd T σ)) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.expW D i)) f := by
    have e1 : eLpNorm ψ 2 (muQ1 (Wc D i)) =
        eLpNorm (c⁻¹ • fun q : AutQ (Wc D i) => ‖GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.adFun T i hV f q.out‖) 2 (muQ1 (Wc D i)) := by
      refine eLpNorm_congr_norm_ae (Filter.Eventually.of_forall fun q => ?_)
      simp only [hψdef, Pi.smul_apply, smul_eq_mul, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_norm,
        abs_of_pos hc0, abs_mul, abs_inv, hnorm]
      ring
    rw [e1, eLpNorm_const_smul, hK2, ← mul_assoc, Real.enorm_eq_ofReal (inv_nonneg.2 hc0.le),
      ← ENNReal.ofReal_mul (inv_nonneg.2 hc0.le), inv_mul_cancel₀ hc0.ne', ENNReal.ofReal_one, one_mul]
  have hψm : AEStronglyMeasurable ψ (muQ1 (Wc D i)) := by
    haveI : BorelSpace (GA D (Wc D i)) := ⟨rfl⟩
    have hm : Measurable fun q : AutQ (Wc D i) => F v q.out := by
      rw [measurable_from_quotient]
      have e : ((fun q : AutQ (Wc D i) => F v q.out) ∘ Quotient.mk'') = F v := funext fun g => by
        have h2 : g * (Quotient.mk (QuotientGroup.rightRel (GQ (Wc D i))) g).out⁻¹ ∈ GQ (Wc D i) :=
          QuotientGroup.rightRel_apply.1 (Quotient.mk_out g)
        have h3 := haut.left _ h2 (Quotient.mk (QuotientGroup.rightRel (GQ (Wc D i))) g).out
        rw [inv_mul_cancel_right] at h3
        exact h3.symm
      rw [e]
      exact haut.cont.measurable
    refine Measurable.aestronglyMeasurable ?_
    exact Complex.measurable_ofReal.comp ((hm.norm).div_const c)
  have hψ : MemLp ψ 2 (muQ1 (Wc D i)) := ⟨hψm, by rw [hE]; exact lt_top_iff_ne_top.2 hK3⟩
  have hI := GlobalTheory.ReadingNorm.integral_star_mul (Wc D i) (D.sp.W_sig _) hμ hF.2 (F v) haut.left ψ hψ c
    (fun q => by
      simp only [hψdef, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_norm, abs_of_pos hc0]
      field_simp)
  have hL : ‖hψ.toLp ψ‖ = (petE (T.V ((i : ℕ) + 1) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.gd T σ))
      (T.dict ((i : ℕ) + 1) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.gd T σ)) (muQ1 (T.V ((i : ℕ) + 1) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.gd T σ)))
      (modelWt (T.U ((i : ℕ) + 1) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.gd T σ)) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.expW D i)) f).toReal := by
    rw [Lp.norm_toLp, hE]
  rw [Formalism.IndefR.Links.ipAt, ← h1, hI, L1 D i σ, hL]
  unfold GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.ratio GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.probSq
  push_cast
  ring

end GlobalTheory.ExactRatioProof
