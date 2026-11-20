import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.ImportsAlt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LiftedSchrodingerDatum
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilActDefs
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.EisensteinSecondTerm
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SecondOrbitSectionIntegral
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SecondOrbitBijection
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ContinuousThK
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.PadMatrixLowerBlockZero
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LamMapK
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ContinuousPhzK
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.CoordsCK
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.EisensteinTermLeftInvariant
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.BlockDiagonalPreservesFormIff
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.EisensteinSecondTermExpand
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.CountableRationalVectors

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal ENNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Act.C5
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d)
variable {R L}
/- English proof (translation)
Establish `: Countable (rat2 σ d.Y)` using `GlobalTheory.EisBL.DoubledGroupTopology.countable_rational_points_doubled σ d.Y`. Establish `: Countable (_root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d)` using `Quotient.countable`. Establish `: Countable (rat2 σ L.Y)` using `GlobalTheory.EisBL.DoubledGroupTopology.countable_rational_points_doubled σ L.Y`. Establish `: Countable (_root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k L.sd)` using `Quotient.countable`. Establish `: Countable (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.Crat_k L)` using `_root_.PositivityTheory.SiegelWeilFormula.Act.C5.countable_crat_k`.

Establish `: ν.IsAddHaarMeasure` using `hU.2.1`. Establish `: lam.IsAddHaarMeasure` using `hc.2.1`. Establish `: lam'.IsAddHaarMeasure` using `hc'.2.1`. Establish `hψc : Continuous d.B.ψ` using `d.ok.good.std.1`. Take `⟨P, hP, -⟩` from `_root_.PositivityTheory.SiegelWeilFormula.Act.C5.pEquiv_k h`.

Take `⟨cP, hcP0, hcPt, hPc⟩` from `_root_.PositivityTheory.SiegelWeilFormula.Act.C5.lam_map_k (lam := lam) (ν := ν) (lam' := lam') P`. Take `⟨cK, hcK0, hcKt, hκeq⟩` from `_root_.PositivityTheory.SiegelWeilFormula.Act.C5.kap_eq_k (ν := ν) (κ := κ)`. Take `⟨𝓐, h𝓐, h𝓐0, h𝓐t⟩` from `exists_fd_fA (F := F)`. Establish `: IsFiniteMeasure (ν.restrict 𝓤)` using `isFiniteMeasure_restrict.2 (by simp [hU.2.2.2])`. Establish `: IsFiniteMeasure (lam'.restrict 𝓖')` using `isFiniteMeasure_restrict.2 (by simp [hc'.2.2.2])`.

Establish `: IsFiniteMeasure ((lamA F).restrict 𝓐)` using `isFiniteMeasure_restrict.2 h𝓐t`. Take `⟨e, he⟩` from `_root_.PositivityTheory.SiegelWeilFormula.Act.C5.second_orbit_bijection h`. Use `⟨(cP.toReal : ℂ) * ((cK.toReal : ℂ))⁻¹, fun x => ?_⟩` and prove the remaining obligations. Establish `hΦc : Continuous (_root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z)` using `_root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.continuous_phz_k d hf.cont s₁ z`. Take `⟨hi, hs⟩` from `habs x`.

Take `⟨e1, fin1⟩` from `_root_.PositivityTheory.SiegelWeilFormula.Act.C5.second_orbit_section_integral (L := L) (nb := nb) (uM := uM) hU.2.2.2 hc.2.2.2 x hi hs`. Establish `e2` using `_root_.PositivityTheory.SiegelWeilFormula.Act.C5.coordsC_k (R := R) h hc hU hc' hT h𝓐 hP hPc (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.eisensteinSecondTerm L (_root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z)) (fun r hr hx g => _root_.PositivityTheory.SiegelWe …`. Use `set μO := (ν.restrict 𝓤).prod (lam.restrict 𝓖) with hμO`. Use `set μI := (ν.restrict 𝓤).prod ((ν.restrict 𝓤).prod ((lamA F).restrict 𝓐)) with hμI`. Use `set μN := (lam'.restrict 𝓖').prod μI with hμN`.

Establish `hnb' : Continuous nb'` using `kunf.continuous_nb hc'.1`. Establish `hnew : Continuous fun p : nA σ L.Y L.b × ((Fin L.n → AE F E) × ((Fin L.n → AE F E) × AF F)) => _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L p.2.2.1 * (cM (p.2.1, p.2.2.2) * (L.j (nb' p.1) * x))`. Use `((_root_.PositivityTheory.SiegelWeilFormula.Act.C5.continuous_sM'_k (R := R) (L := L)).comp (continuous_fst.comp (continuous_snd.comp continuous_snd))).mul ((hcM.comp ((continuous_fst.comp continuous_snd).prodMk (continuous_snd.comp (continuous_snd.comp continuous_snd)))).mul ((( …` and prove the remaining obligations. Establish `hth' : Continuous fun β : nA σ L.Y L.b => _root_.PositivityTheory.SiegelWeilFormula.Act.C5.th'_k (d` using `d) T' β := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.continuous_th'_k T'`. Set `G : (Σ _ : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k L.sd, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Crat_k L) → nA σ L.Y L.b × ((Fin L.n → AE F E) × ((Fin L.n → AE F E) × AF F)) → ℂ` to `fun y p => _root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (w₁ * (cM y.2.1 * (L.j (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k y.1) * (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L p.2.2.1 * (cM (p.2.1, p.2.2.2) * (L.j (nb' p.1) * x)))))) * _root_ …`.

Establish `hGc : ∀ y, Continuous (G y)` using `fun y => (hΦc.comp (continuous_const.mul (continuous_const.mul (continuous_const.mul hnew)))).mul (hth'.comp continuous_fst)`. Establish `fin2 : ∫⁻ p, ∑' y, ‖G y p‖ₑ ∂μN < ⊤`. Establish `hE` using `_root_.PositivityTheory.SiegelWeilFormula.Act.C5.coordsE_k (R := R) h hc hU hc' hT h𝓐 hP hPc (fun g => ∑' q : {q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d // ¬ _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L (_root_.PositivityTheory.SiegelWeilFormula.Act.r …`. Establish `l1 : ∫⁻ p, (∑' q : {q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d // ¬ _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q)}, ‖_root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (_root_.PositivityT …`. Use `lt_of_eq_of_lt ?_ fin1` and prove the remaining obligations.

Use `lintegral_congr fun p => ?_` and prove the remaining obligations. Rewrite using `[← ENNReal.tsum_mul_right]`. Conclude with `tsum_congr fun q => (enorm_mul _ _).symm`. Rewrite `l1` using `[hE]`. Establish `l2 : ∫⁻ p, (∑' q : {q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d // ¬ _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q)}, ‖_root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (_root_.PositivityT …` using `d) T' p.1‖ₑ ∂μN < ⊤ := by`.

Assume the negation of the conclusion as `hcon`. Rewrite `hcon` using `[not_lt, top_le_iff]`. Rewrite `l1` using `[hcon, ENNReal.mul_top hcP0]`. Conclude with `lt_irrefl _ l1`. Use `lt_of_eq_of_lt (lintegral_congr fun p => ?_) l2` and prove the remaining obligations.

Rewrite using `[(_root_.PositivityTheory.SiegelWeilFormula.Act.C5.eisenstein_second_term_expand h hf z he _).2, ← ENNReal.tsum_mul_right]`. Conclude with `tsum_congr fun y => enorm_mul _ _`. Establish `hGm : ∀ y, AEMeasurable (fun p => ‖G y p‖ₑ) μN` using `fun y => (hGc y).enorm.measurable.aemeasurable`. Establish `hGlt : ∀ y, ∫⁻ p, ‖G y p‖ₑ ∂μN < ⊤` using `fun y => lt_of_le_of_lt (lintegral_mono fun p => ENNReal.le_tsum (f := fun y => ‖G y p‖ₑ) y) fin2`. Establish `hGi : ∀ y, Integrable (G y) μN` using `fun y => ⟨(hGc y).aestronglyMeasurable, hGlt y⟩`.

Establish `hGs : Summable fun y => ∫ p, ‖G y p‖ ∂μN`. Establish `h1 : ∀ y, ∫ p, ‖G y p‖ ∂μN = (∫⁻ p, ‖G y p‖ₑ ∂μN).toReal` using `fun y => integral_norm_eq_lintegral_enorm (hGi y).aestronglyMeasurable`. Repeatedly rewrite using `[h1]`. Use `ENNReal.summable_toReal ?_` and prove the remaining obligations. Rewrite using `[← lintegral_tsum hGm]`.

Conclude with `fin2.ne`. Establish `e3 : ∫ p, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.eisensteinSecondTerm L (_root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z) (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L p.2.2.1 * (cM (p.2.1, p.2.2.2) * (L.j (nb' p.1) * x))) * _root_.PositivityTh …` using `d) T' p.1 ∂μN = ∑' y, ∫ p, G y p ∂μN := by`. Rewrite using `[(hasSum_integral_of_summable_integral_norm hGi hGs).tsum_eq]`. Use `integral_congr_ae (ae_of_all _ fun p => ?_)` and prove the remaining obligations. Simplify using `only [G]`.

Rewrite using `[(_root_.PositivityTheory.SiegelWeilFormula.Act.C5.eisenstein_second_term_expand h hf z he _).1, tsum_mul_right]`. Establish `hsI : Summable fun y => ∫ p, G y p ∂μN` using `hGs.of_norm_bounded (fun y => norm_integral_le_integral_norm _)`. Rewrite `e3` using `[hsI.tsum_sigma]`. Establish `hκ' : ∀ g : (Fin L.n → AE F E) × AF F → ℂ, ∫ c, g c ∂(ν.prod (lamA F)) = ((cK.toReal : ℂ))⁻¹ * ∫ c, g c ∂κ`. Introduce `g`.

Rewrite using `[hκeq, integral_smul_measure, Complex.real_smul, ← mul_assoc, inv_mul_cancel₀, one_mul]`. Conclude with `Complex.ofReal_ne_zero.2 (ENNReal.toReal_ne_zero.2 ⟨hcK0, hcKt⟩)`. Establish `e4 : ∀ q' : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k L.sd, ∑' c₀ : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Crat_k L, ∫ p, G ⟨q', c₀⟩ p ∂μN = ((cK.toReal : ℂ))⁻¹ * ∫ β in 𝓖', (∫ c, _root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (w₁ * (cM c * (L.j ( …` using `d) T' β ∂lam' := by`. Introduce `q'`. Establish `hi' : ∀ c₀ : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Crat_k L, Integrable (G ⟨q', c₀⟩) μN` using `fun c₀ => hGi _`.

Establish `hs' : Summable fun c₀ : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Crat_k L => ∫ p, ‖G ⟨q', c₀⟩ p‖ ∂μN` using `hGs.sigma_factor q'`. Take `⟨-, hex⟩` from `PositivityTheory.SiegelWeilFormula.Act.exch (μ := lam'.restrict 𝓖') (m := μI) (fun c₀ : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Crat_k L => G ⟨q', c₀⟩) hi' hs'`. Establish `hpr : ∀ c₀ : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Crat_k L, ∫ p, G ⟨q', c₀⟩ p ∂μN = ∫ β, ∫ v, G ⟨q', c₀⟩ (β, v) ∂μI ∂(lam'.restrict 𝓖')` using `fun c₀ => integral_prod _ (hi' c₀)`. Repeatedly rewrite using `[hpr]`. Rewrite using `[← hex, ← integral_const_mul]`.

Use `integral_congr_ae ?_` and prove the remaining obligations. Establish `hmq : Measurable fun p : nA σ L.Y L.b × ((Fin L.n → AE F E) × ((Fin L.n → AE F E) × AF F)) => ∑' c₀ : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Crat_k L, ‖G ⟨q', c₀⟩ p‖ₑ` using `Measurable.ennreal_tsum fun c₀ => (hGc _).enorm.measurable`. Establish `hfinq : ∫⁻ p, ∑' c₀ : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Crat_k L, ‖G ⟨q', c₀⟩ p‖ₑ ∂μN < ⊤`. Use `lt_of_le_of_lt (lintegral_mono fun p => ?_) fin2` and prove the remaining obligations. Conclude with `(ENNReal.le_tsum (f := fun q'' => ∑' c₀ : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Crat_k L, ‖G ⟨q'', c₀⟩ p‖ₑ) q').trans (ENNReal.tsum_sigma' (fun y => ‖G y p‖ₑ)).symm.le`.

Rewrite `hfinq` using `[hμN, lintegral_prod _ hmq.aemeasurable]`. Establish `hae` using `ae_lt_top (hmq.lintegral_prod_right') hfinq.ne`. Use `filter_upwards [hae] with β hβ`. Establish `hG' : ∀ v, ∑' c₀ : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Crat_k L, G ⟨q', c₀⟩ (β, v) = (∑' c₀ : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Crat_k L, _root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (w₁ * (cM c₀.1 * (L.j (_root_.PositivityTheory.Siegel …` using `d) T' β := fun v => by simp only [G]; rw [tsum_mul_right]`. Repeatedly rewrite using `[hG']`.

Rewrite using `[integral_mul_const]`. Establish `hjj : L.j (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q') * (L.j (nb' β) * x) = L.j (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q' * nb' β) * x` using `by rw [map_mul, mul_assoc]`. Distinguish the cases in `hθ : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.th'_k (d := d) T' β = 0`. Rewrite using `[hθ, mul_zero, mul_zero, mul_zero]`. Establish `hθe : ‖_root_.PositivityTheory.SiegelWeilFormula.Act.C5.th'_k (d` using `d) T' β‖ₑ ≠ 0 := enorm_ne_zero.2 hθ`.

Establish `hl : ∫⁻ v, ∑' c₀ : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Crat_k L, ‖_root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (w₁ * (cM c₀.1 * (L.j (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q') * (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L …`. Establish `e5 : ∫⁻ v, ∑' c₀ : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Crat_k L, ‖G ⟨q', c₀⟩ (β, v)‖ₑ ∂μI = (∫⁻ v, ∑' c₀ : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Crat_k L, ‖_root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (w₁ * (cM c₀.1 * (L.j (_root_.Positivit …` using `d) T' β‖ₑ := by`. Rewrite using `[← lintegral_mul_const' _ _ enorm_ne_top]`. Use `lintegral_congr fun v => ?_` and prove the remaining obligations. Rewrite using `[← ENNReal.tsum_mul_right]`.

Conclude with `tsum_congr fun c₀ => enorm_mul _ _`. Rewrite `hβ` using `[e5]`. Assume the negation of the conclusion as `hcon`. Rewrite `hcon` using `[not_lt, top_le_iff]`. Rewrite `hβ` using `[hcon, ENNReal.top_mul hθe]`.

Conclude with `lt_irrefl _ hβ`. Establish `hγ : _root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q' ∈ rat2 σ L.Y` using `(Quot.out q').2`. Rewrite `hl` using `[_root_.PositivityTheory.SiegelWeilFormula.Act.C5.unfqE_k h hf z hU h𝓐 hγ (L.j (nb' β) * x)]`. Rewrite using `[_root_.PositivityTheory.SiegelWeilFormula.Act.C5.unfqC_k h hf z hU h𝓐 hγ (L.j (nb' β) * x) hl, hκ']`. Repeatedly rewrite using `[hjj]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1, e2, e3]`. Repeatedly rewrite using `[e4]`. Rewrite using `[tsum_mul_left, Complex.real_smul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem unf_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) {f : d.G → ℂ} {s₁ : ℂ} (hf : IsSec d.K d.χ s₁ f) (z : ℂ)
    {nb : nA σ d.Y d.b → d.G} {lam : Measure (nA σ d.Y d.b)} {𝓖 : Set (nA σ d.Y d.b)}
    (hc : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖)
    {uM : (Fin L.n → AE F E) → d.G} {ν : Measure (Fin L.n → AE F E)} {𝓤 : Set (Fin L.n → AE F E)} (hU : L.UData uM ν 𝓤)
    {T : nF σ d.Y d.b} {T' : nF σ L.Y L.b} (hT : L.IsSub T T')
    {nb' : nA σ L.Y L.b → G2 σ L.Y} {lam' : Measure (nA σ L.Y L.b)} {𝓖' : Set (nA σ L.Y L.b)}
    (hc' : CoefData (σ := σ) (Y := L.Y) L.b nb' lam' 𝓖')
    (habs : ∀ x, (∀ q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d, Integrable (_root_.PositivityTheory.SiegelWeilFormula.Act.kq_k L f s₁ z nb T uM (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q) x) ((ν.restrict 𝓤).prod (lam.restrict 𝓖))) ∧
      Summable fun q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d => ∫ p, ‖_root_.PositivityTheory.SiegelWeilFormula.Act.kq_k L f s₁ z nb T uM (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q) x p‖ ∂((ν.restrict 𝓤).prod (lam.restrict 𝓖)))
    {w₁ : d.G} {cM : (Fin L.n → AE F E) × AF F → d.G} {κ : Measure ((Fin L.n → AE F E) × AF F)} {δ : E}
    (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) (hcM : Continuous cM) (hκ : κ.IsAddHaarMeasure) :
    ∃ K : ℂ, ∀ x, _root_.PositivityTheory.SiegelWeilFormula.Act.secondOrbitSection L f s₁ z nb lam 𝓖 T uM ν 𝓤 x = K * ∑' q' : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k L.sd, ∫ β in 𝓖',
      (∫ c, _root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (w₁ * (cM c * (L.j (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q' * nb' β) * x))) ∂κ) * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.th'_k (d := d) T' β ∂lam' := by
  classical
  have : Countable (rat2 σ d.Y) := GlobalTheory.EisBL.DoubledGroupTopology.countable_rational_points_doubled σ d.Y
  have : Countable (_root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d) := Quotient.countable
  have : Countable (rat2 σ L.Y) := GlobalTheory.EisBL.DoubledGroupTopology.countable_rational_points_doubled σ L.Y
  have : Countable (_root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k L.sd) := Quotient.countable
  have : Countable (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.Crat_k L) := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.countable_crat_k
  have : ν.IsAddHaarMeasure := hU.2.1
  have : lam.IsAddHaarMeasure := hc.2.1
  have : lam'.IsAddHaarMeasure := hc'.2.1
  have hψc : Continuous d.B.ψ := d.ok.good.std.1
  obtain ⟨P, hP, -⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.pEquiv_k h
  obtain ⟨cP, hcP0, hcPt, hPc⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.lam_map_k (lam := lam) (ν := ν) (lam' := lam') P
  obtain ⟨cK, hcK0, hcKt, hκeq⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.kap_eq_k (ν := ν) (κ := κ)
  obtain ⟨𝓐, h𝓐, h𝓐0, h𝓐t⟩ := exists_fd_fA (F := F)
  have : IsFiniteMeasure (ν.restrict 𝓤) := isFiniteMeasure_restrict.2 (by simp [hU.2.2.2])
  have : IsFiniteMeasure (lam'.restrict 𝓖') := isFiniteMeasure_restrict.2 (by simp [hc'.2.2.2])
  have : IsFiniteMeasure ((lamA F).restrict 𝓐) := isFiniteMeasure_restrict.2 h𝓐t
  obtain ⟨e, he⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.second_orbit_bijection h
  refine ⟨(cP.toReal : ℂ) * ((cK.toReal : ℂ))⁻¹, fun x => ?_⟩
  have hΦc : Continuous (_root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z) := _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.continuous_phz_k d hf.cont s₁ z
  obtain ⟨hi, hs⟩ := habs x
  obtain ⟨e1, fin1⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.second_orbit_section_integral (L := L) (nb := nb) (uM := uM) hU.2.2.2 hc.2.2.2 x hi hs
  have e2 := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.coordsC_k (R := R) h hc hU hc' hT h𝓐 hP hPc (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.eisensteinSecondTerm L (_root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z)) (fun r hr hx g => _root_.PositivityTheory.SiegelWeilFormula.Act.C5.eisenstein_term_left_invariant hf z hr hx g) x
  set μO := (ν.restrict 𝓤).prod (lam.restrict 𝓖) with hμO
  set μI := (ν.restrict 𝓤).prod ((ν.restrict 𝓤).prod ((lamA F).restrict 𝓐)) with hμI
  set μN := (lam'.restrict 𝓖').prod μI with hμN
  have hnb' : Continuous nb' := kunf.continuous_nb hc'.1
  have hnew : Continuous fun p : nA σ L.Y L.b × ((Fin L.n → AE F E) × ((Fin L.n → AE F E) × AF F)) =>
      _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L p.2.2.1 * (cM (p.2.1, p.2.2.2) * (L.j (nb' p.1) * x)) := by
    refine ((_root_.PositivityTheory.SiegelWeilFormula.Act.C5.continuous_sM'_k (R := R) (L := L)).comp (continuous_fst.comp (continuous_snd.comp continuous_snd))).mul
      ((hcM.comp ((continuous_fst.comp continuous_snd).prodMk (continuous_snd.comp (continuous_snd.comp continuous_snd)))).mul
        (((L.cont.comp (hnb'.comp continuous_fst))).mul continuous_const))
  have hth' : Continuous fun β : nA σ L.Y L.b => _root_.PositivityTheory.SiegelWeilFormula.Act.C5.th'_k (d := d) T' β := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.continuous_th'_k T'
  let G : (Σ _ : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k L.sd, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Crat_k L) → nA σ L.Y L.b × ((Fin L.n → AE F E) × ((Fin L.n → AE F E) × AF F)) → ℂ :=
    fun y p => _root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (w₁ * (cM y.2.1 * (L.j (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k y.1) * (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L p.2.2.1 * (cM (p.2.1, p.2.2.2) * (L.j (nb' p.1) * x)))))) *
      _root_.PositivityTheory.SiegelWeilFormula.Act.C5.th'_k (d := d) T' p.1
  have hGc : ∀ y, Continuous (G y) := fun y =>
    (hΦc.comp (continuous_const.mul (continuous_const.mul (continuous_const.mul hnew)))).mul (hth'.comp continuous_fst)
  have fin2 : ∫⁻ p, ∑' y, ‖G y p‖ₑ ∂μN < ⊤ := by
    have hE := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.coordsE_k (R := R) h hc hU hc' hT h𝓐 hP hPc
      (fun g => ∑' q : {q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d // ¬ _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q)}, ‖_root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q.1 * g)‖ₑ)
      (Measurable.ennreal_tsum fun q => (hΦc.comp (continuous_const.mul continuous_id)).enorm.measurable)
      (fun r hr hx g => _root_.PositivityTheory.SiegelWeilFormula.Act.C5.eisenstein_norm_sum_invariant hf z hr hx g) x
    have l1 : ∫⁻ p, (∑' q : {q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d // ¬ _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q)}, ‖_root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q.1 * (nb p.2 * (uM p.1 * x)))‖ₑ) *
        ‖_root_.PositivityTheory.SiegelWeilFormula.Act.C5.th_k T p.2‖ₑ ∂μO < ⊤ := by
      refine lt_of_eq_of_lt ?_ fin1
      refine lintegral_congr fun p => ?_
      rw [← ENNReal.tsum_mul_right]
      exact tsum_congr fun q => (enorm_mul _ _).symm
    rw [hE] at l1
    have l2 : ∫⁻ p, (∑' q : {q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d // ¬ _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q)},
        ‖_root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q.1 * (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L p.2.2.1 * (cM (p.2.1, p.2.2.2) * (L.j (nb' p.1) * x))))‖ₑ) * ‖_root_.PositivityTheory.SiegelWeilFormula.Act.C5.th'_k (d := d) T' p.1‖ₑ
        ∂μN < ⊤ := by
      by_contra hcon
      rw [not_lt, top_le_iff] at hcon
      rw [hcon, ENNReal.mul_top hcP0] at l1
      exact lt_irrefl _ l1
    refine lt_of_eq_of_lt (lintegral_congr fun p => ?_) l2
    rw [(_root_.PositivityTheory.SiegelWeilFormula.Act.C5.eisenstein_second_term_expand h hf z he _).2, ← ENNReal.tsum_mul_right]
    exact tsum_congr fun y => enorm_mul _ _
  have hGm : ∀ y, AEMeasurable (fun p => ‖G y p‖ₑ) μN := fun y => (hGc y).enorm.measurable.aemeasurable
  have hGlt : ∀ y, ∫⁻ p, ‖G y p‖ₑ ∂μN < ⊤ := fun y =>
    lt_of_le_of_lt (lintegral_mono fun p => ENNReal.le_tsum (f := fun y => ‖G y p‖ₑ) y) fin2
  have hGi : ∀ y, Integrable (G y) μN := fun y => ⟨(hGc y).aestronglyMeasurable, hGlt y⟩
  have hGs : Summable fun y => ∫ p, ‖G y p‖ ∂μN := by
    have h1 : ∀ y, ∫ p, ‖G y p‖ ∂μN = (∫⁻ p, ‖G y p‖ₑ ∂μN).toReal := fun y =>
      integral_norm_eq_lintegral_enorm (hGi y).aestronglyMeasurable
    simp_rw [h1]
    refine ENNReal.summable_toReal ?_
    rw [← lintegral_tsum hGm]
    exact fin2.ne
  have e3 : ∫ p, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.eisensteinSecondTerm L (_root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z) (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L p.2.2.1 * (cM (p.2.1, p.2.2.2) * (L.j (nb' p.1) * x))) * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.th'_k (d := d) T' p.1 ∂μN =
      ∑' y, ∫ p, G y p ∂μN := by
    rw [(hasSum_integral_of_summable_integral_norm hGi hGs).tsum_eq]
    refine integral_congr_ae (ae_of_all _ fun p => ?_)
    simp only [G]
    rw [(_root_.PositivityTheory.SiegelWeilFormula.Act.C5.eisenstein_second_term_expand h hf z he _).1, tsum_mul_right]
  have hsI : Summable fun y => ∫ p, G y p ∂μN := hGs.of_norm_bounded (fun y => norm_integral_le_integral_norm _)
  rw [hsI.tsum_sigma] at e3
  have hκ' : ∀ g : (Fin L.n → AE F E) × AF F → ℂ, ∫ c, g c ∂(ν.prod (lamA F)) = ((cK.toReal : ℂ))⁻¹ * ∫ c, g c ∂κ := by
    intro g
    rw [hκeq, integral_smul_measure, Complex.real_smul, ← mul_assoc, inv_mul_cancel₀, one_mul]
    exact Complex.ofReal_ne_zero.2 (ENNReal.toReal_ne_zero.2 ⟨hcK0, hcKt⟩)
  have e4 : ∀ q' : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k L.sd, ∑' c₀ : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Crat_k L, ∫ p, G ⟨q', c₀⟩ p ∂μN = ((cK.toReal : ℂ))⁻¹ *
      ∫ β in 𝓖', (∫ c, _root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (w₁ * (cM c * (L.j (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q' * nb' β) * x))) ∂κ) * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.th'_k (d := d) T' β ∂lam' := by
    intro q'
    have hi' : ∀ c₀ : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Crat_k L, Integrable (G ⟨q', c₀⟩) μN := fun c₀ => hGi _
    have hs' : Summable fun c₀ : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Crat_k L => ∫ p, ‖G ⟨q', c₀⟩ p‖ ∂μN := hGs.sigma_factor q'
    obtain ⟨-, hex⟩ := PositivityTheory.SiegelWeilFormula.Act.exch (μ := lam'.restrict 𝓖') (m := μI) (fun c₀ : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Crat_k L => G ⟨q', c₀⟩) hi' hs'
    have hpr : ∀ c₀ : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Crat_k L, ∫ p, G ⟨q', c₀⟩ p ∂μN = ∫ β, ∫ v, G ⟨q', c₀⟩ (β, v) ∂μI ∂(lam'.restrict 𝓖') :=
      fun c₀ => integral_prod _ (hi' c₀)
    simp_rw [hpr]
    rw [← hex, ← integral_const_mul]
    refine integral_congr_ae ?_
    have hmq : Measurable fun p : nA σ L.Y L.b × ((Fin L.n → AE F E) × ((Fin L.n → AE F E) × AF F)) =>
        ∑' c₀ : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Crat_k L, ‖G ⟨q', c₀⟩ p‖ₑ := Measurable.ennreal_tsum fun c₀ => (hGc _).enorm.measurable
    have hfinq : ∫⁻ p, ∑' c₀ : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Crat_k L, ‖G ⟨q', c₀⟩ p‖ₑ ∂μN < ⊤ := by
      refine lt_of_le_of_lt (lintegral_mono fun p => ?_) fin2
      exact (ENNReal.le_tsum (f := fun q'' => ∑' c₀ : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Crat_k L, ‖G ⟨q'', c₀⟩ p‖ₑ) q').trans
        (ENNReal.tsum_sigma' (fun y => ‖G y p‖ₑ)).symm.le
    rw [hμN, lintegral_prod _ hmq.aemeasurable] at hfinq
    have hae := ae_lt_top (hmq.lintegral_prod_right') hfinq.ne
    filter_upwards [hae] with β hβ
    have hG' : ∀ v, ∑' c₀ : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Crat_k L, G ⟨q', c₀⟩ (β, v) = (∑' c₀ : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Crat_k L,
        _root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (w₁ * (cM c₀.1 * (L.j (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q') * (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L v.2.1 * (cM (v.1, v.2.2) * (L.j (nb' β) * x))))))) *
          _root_.PositivityTheory.SiegelWeilFormula.Act.C5.th'_k (d := d) T' β := fun v => by simp only [G]; rw [tsum_mul_right]
    simp_rw [hG']
    rw [integral_mul_const]
    have hjj : L.j (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q') * (L.j (nb' β) * x) = L.j (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q' * nb' β) * x := by rw [map_mul, mul_assoc]
    by_cases hθ : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.th'_k (d := d) T' β = 0
    · rw [hθ, mul_zero, mul_zero, mul_zero]
    · have hθe : ‖_root_.PositivityTheory.SiegelWeilFormula.Act.C5.th'_k (d := d) T' β‖ₑ ≠ 0 := enorm_ne_zero.2 hθ
      have hl : ∫⁻ v, ∑' c₀ : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Crat_k L,
          ‖_root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (w₁ * (cM c₀.1 * (L.j (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q') * (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L v.2.1 * (cM (v.1, v.2.2) * (L.j (nb' β) * x))))))‖ₑ ∂μI < ⊤ := by
        have e5 : ∫⁻ v, ∑' c₀ : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Crat_k L, ‖G ⟨q', c₀⟩ (β, v)‖ₑ ∂μI = (∫⁻ v, ∑' c₀ : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Crat_k L,
            ‖_root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (w₁ * (cM c₀.1 * (L.j (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q') * (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L v.2.1 * (cM (v.1, v.2.2) * (L.j (nb' β) * x))))))‖ₑ ∂μI) *
              ‖_root_.PositivityTheory.SiegelWeilFormula.Act.C5.th'_k (d := d) T' β‖ₑ := by
          rw [← lintegral_mul_const' _ _ enorm_ne_top]
          refine lintegral_congr fun v => ?_
          rw [← ENNReal.tsum_mul_right]
          exact tsum_congr fun c₀ => enorm_mul _ _
        rw [e5] at hβ
        by_contra hcon
        rw [not_lt, top_le_iff] at hcon
        rw [hcon, ENNReal.top_mul hθe] at hβ
        exact lt_irrefl _ hβ
      have hγ : _root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q' ∈ rat2 σ L.Y := (Quot.out q').2
      rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.unfqE_k h hf z hU h𝓐 hγ (L.j (nb' β) * x)] at hl
      rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.unfqC_k h hf z hU h𝓐 hγ (L.j (nb' β) * x) hl, hκ']
      simp_rw [hjj]
      ring
  rw [e1, e2, e3]
  simp_rw [e4]
  rw [tsum_mul_left, Complex.real_smul]
  ring
end PositivityTheory.SiegelWeilFormula.Act.C5
end
end
