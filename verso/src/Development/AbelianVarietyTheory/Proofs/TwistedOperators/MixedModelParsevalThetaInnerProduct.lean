import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CompatibleThetaRestrictions
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralHomFundamentalDomainIsotropicSplitCoords
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedHeisenbergThetaContinuousBoundedStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParsevalMixedModelIsotropicThetaProductStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralParametricUnfoldRationalTranslatesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.MixParseval

set_option maxHeartbeats 400000 in
set_option synthInstance.maxHeartbeats 200000 in

/- English proof (translation)
Introduce `D V V' W r C B hs C' h1 h2 h3 ψ hψ μ 𝓨 hμ μ₀ 𝓕₀ hμ₀ μ' 𝓕' hμ' f₁ f₂ hf₁ hf₂`. Take `⟨i1, i2, i3, i4, i5, -⟩` from `GlobalTheory.MixModel.lattice_Mx D W.rank r`. Take `⟨j1, j2, j3, j4, j5, -⟩` from `GlobalTheory.MixModel.lattice_Mx D W.rank V'.rank`. Use `haveI : BorelSpace (Mx D W.rank r) := ⟨rfl⟩`. Use `haveI : BorelSpace (WO V' W) := ⟨rfl⟩`.

Use `haveI : IsFiniteMeasure (μ.restrict 𝓨) := ⟨by rw [Measure.restrict_apply_univ, hμ.2.2]; exact ENNReal.one_lt_top⟩`. Use `haveI : IsFiniteMeasure (μ'.restrict 𝓕') := ⟨by rw [Measure.restrict_apply_univ, hμ'.2.2]; exact ENNReal.one_lt_top⟩`. Set `R : (WO V W → ℂ) → WO V' W → Mx D W.rank r → ℂ` to `fun f x u => GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (heisO ψ V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' u) f) x`. Set `h : WO V' W → Mx D W.rank r → ℂ` to `fun x u => R f₁ x u * starRingEnd ℂ (R f₂ x u)`. Take `⟨hc₁, M₁, hM₁⟩` from `GlobalTheory.T.restrictedHeisenbergTheta_continuous_bounded D V V' W r C C' B ψ hψ μ 𝓨 hμ f₁ hf₁`.

Take `⟨hc₂, M₂, hM₂⟩` from `GlobalTheory.T.restrictedHeisenbergTheta_continuous_bounded D V V' W r C C' B ψ hψ μ 𝓨 hμ f₂ hf₂`. Establish `hhc : Continuous (Function.uncurry h)` using `hc₁.mul (Complex.continuous_conj.comp hc₂)`. Establish `hhb : ∀ x u, ‖h x u‖ ≤ M₁ * M₂` using `fun x u => by show ‖R f₁ x u * starRingEnd ℂ (R f₂ x u)‖ ≤ _`. Rewrite using `[norm_mul, Complex.norm_conj]`. Conclude with `mul_le_mul (hM₁ x u) (hM₂ x u) (norm_nonneg _) ((norm_nonneg _).trans (hM₁ x u))`.

Take `⟨C₁, hC₁⟩` from `GlobalTheory.OrientedHeis.theta_bounded hψ hf₁`. Take `⟨C₂, hC₂⟩` from `GlobalTheory.OrientedHeis.theta_bounded hψ hf₂`. Establish `hYr : μ.real 𝓨 = 1` using `by simp [Measure.real, hμ.2.2]`. Establish `hsq : ∀ (f : WO V W → ℂ), IsThetaFunO ψ V W f → ∀ Cf : ℝ, (∀ w, ‖f w‖ ≤ Cf) → ∀ x u, Summable (fun ξ : Matrix (Fin W.rank) (Fin r) D.host.E => ‖R f x (ξ.map (incA D) + u)‖ ^ 2) ∧ ∑' ξ : Matrix (Fin W.rank) (Fin r) D.host.E, ‖R f x (ξ.map (incA D) + u)‖ ^ 2 ≤ Cf ^ 2`. Introduce `f hf Cf hCf x u`.

Take `⟨hs1, hs2⟩` from `GlobalTheory.T.parseval_mixedModel_isotropic_thetaProduct D V V' W r C B hs C' h1 h2 h3 ψ hψ μ 𝓨 hμ f f hf hf x u`. Establish `e : ∀ ξ : Matrix (Fin W.rank) (Fin r) D.host.E, ‖R f x (ξ.map (incA D) + u) * starRingEnd ℂ (R f x (ξ.map (incA D) + u))‖ = ‖R f x (ξ.map (incA D) + u)‖ ^ 2` using `fun ξ => by rw [norm_mul, Complex.norm_conj, sq]`. Establish `hsum : Summable (fun ξ : Matrix (Fin W.rank) (Fin r) D.host.E => ‖R f x (ξ.map (incA D) + u)‖ ^ 2)` using `hs1.congr e`. Use `⟨hsum, ?_⟩` and prove the remaining obligations. Establish `e2 : ∀ ξ : Matrix (Fin W.rank) (Fin r) D.host.E, R f x (ξ.map (incA D) + u) * starRingEnd ℂ (R f x (ξ.map (incA D) + u)) = ((‖R f x (ξ.map (incA D) + u)‖ ^ 2 : ℝ) : ℂ)` using `fun ξ => by`.

Rewrite using `[Complex.mul_conj, Complex.normSq_eq_norm_sq]`. Establish `hI` using `hs2.tsum_eq`. Establish `hI' : ((∑' ξ : Matrix (Fin W.rank) (Fin r) D.host.E, ‖R f x (ξ.map (incA D) + u)‖ ^ 2 : ℝ) : ℂ) = ∫ y in 𝓨, f (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C y + GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.midPart V V …`. Rewrite using `[Complex.ofReal_tsum, ← hI]`. Conclude with `tsum_congr fun ξ => (e2 ξ).symm`.

Establish `hnn : 0 ≤ ∑' ξ : Matrix (Fin W.rank) (Fin r) D.host.E, ‖R f x (ξ.map (incA D) + u)‖ ^ 2` using `tsum_nonneg fun _ => by positivity`. Establish `hb : ∀ w, ‖f w * starRingEnd ℂ (f w)‖ ≤ Cf ^ 2` using `fun w => by`. Rewrite using `[norm_mul, Complex.norm_conj, ← sq]`. Conclude with `pow_le_pow_left₀ (norm_nonneg _) (hCf w) 2`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Complex.norm_real, Real.norm_of_nonneg hnn]`. Use `_ ≤ Cf ^ 2 * (μ.restrict 𝓨).real Set.univ := by`. Rewrite using `[hI']`. Conclude with `norm_integral_le_of_norm_le_const (.of_forall fun y => hb _)`. Use `_ = Cf ^ 2 := by simp [Measure.real, Measure.restrict_apply_univ, hμ.2.2]`.

Establish `hb : ∀ x u, Summable (fun ξ : Matrix (Fin W.rank) (Fin r) D.host.E => ‖h x (ξ.map (incA D) + u)‖) ∧ ∑' ξ : Matrix (Fin W.rank) (Fin r) D.host.E, ‖h x (ξ.map (incA D) + u)‖ ≤ (C₁ ^ 2 + C₂ ^ 2) / 2`. Introduce `x u`. Take `⟨s1, t1⟩` from `hsq f₁ hf₁ C₁ hC₁ x u`. Take `⟨s2, t2⟩` from `hsq f₂ hf₂ C₂ hC₂ x u`. Establish `hle : ∀ ξ : Matrix (Fin W.rank) (Fin r) D.host.E, ‖h x (ξ.map (incA D) + u)‖ ≤ (‖R f₁ x (ξ.map (incA D) + u)‖ ^ 2 + ‖R f₂ x (ξ.map (incA D) + u)‖ ^ 2) / 2` using `fun ξ => by show ‖R f₁ x (ξ.map (incA D) + u) * starRingEnd ℂ (R f₂ x (ξ.map (incA D) + u))‖ ≤ _`.

Rewrite using `[norm_mul, Complex.norm_conj]`. Use polynomial arithmetic with `[sq_nonneg (‖R f₁ x (ξ.map (incA D) + u)‖ - ‖R f₂ x (ξ.map (incA D) + u)‖)]`. Establish `hs'` using `(s1.add s2).div_const 2`. Use `⟨Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle hs', ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[tsum_div_const, s1.tsum_add s2]`. Use `_ ≤ (C₁ ^ 2 + C₂ ^ 2) / 2 := by linarith`. Take `⟨hint, hEq⟩` from `GlobalTheory.T.integral_parametric_unfold_rationalTranslates D W.rank r (WO V' W) (μ'.restrict 𝓕') μ 𝓨 hμ h hhc _ hb`. Establish `a1 : ∀ x, Continuous (h x)` using `fun x => hhc.uncurry_left x`. Establish `a2 : ∀ u, Continuous (fun x => h x u)` using `fun u => hhc.uncurry_right u`.

Establish `a3 : ∀ u, AEStronglyMeasurable (fun x => h x u) (μ'.restrict 𝓕')` using `fun u => (a2 u).aestronglyMeasurable`. Use `haveI : FirstCountableTopology (Mx D W.rank r) := @TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _ _ i3`. Establish `hG : Continuous (fun u => ∫ x, h x u ∂(μ'.restrict 𝓕'))` using `continuous_of_dominated (bound := fun _ => M₁ * M₂) a3 (fun u => .of_forall fun x => hhb x u) (integrable_const _) (.of_forall a1)`. Use `⟨hG, hint, ?_⟩` and prove the remaining obligations. Use `show _ = ∫ u, (∫ x, h x u ∂(μ'.restrict 𝓕')) ∂μ`.

Rewrite using `[hEq]`. Take `⟨κ, -, hκ⟩` from `GlobalTheory.TwistHaar.integral_fundamentalDomain_eq_iterated D V V' W r C B hs C' h1 h2 h3 μ 𝓨 hμ μ₀ 𝓕₀ hμ₀.1 hμ₀.2.1 μ' 𝓕' hμ'.1 hμ'.2.1`. Establish `hκ1 : κ = 1`. Establish `e` using `hκ (fun _ => 1) continuous_const ⟨1, fun _ => by simp⟩ (fun _ _ _ => rfl)`. Simplify using `only [setIntegral_const, Measure.real, hμ₀.2.2, hμ.2.2, hμ'.2.2, ENNReal.toReal_one, one_smul] at e`.

Rewrite `e` using `[Complex.real_smul, mul_one]`. Conclude with `e.symm` after adjusting the coercions. Set `H : WO V W → ℂ` to `fun w => f₁ w * starRingEnd ℂ (f₂ w)`. Establish `hHc : Continuous H` using `hf₁.cont.mul (Complex.continuous_conj.comp hf₂.cont)`. Establish `hHb : ∃ b : ℝ, ∀ w, ‖H w‖ ≤ b` using `⟨C₁ * C₂, fun w => by show ‖f₁ w * starRingEnd ℂ (f₂ w)‖ ≤ _`.

Rewrite using `[norm_mul, Complex.norm_conj]`. Conclude with `mul_le_mul (hC₁ w) (hC₂ w) (norm_nonneg _) ((norm_nonneg _).trans (hC₁ w))⟩`. Establish `hHp : ∀ γ ∈ ratL W V, ∀ w, H (γ + w) = H w`. Introduce and unpack `γ ⟨g, rfl⟩ w`. Use `show f₁ (ratW W V g + w) * starRingEnd ℂ (f₂ (ratW W V g + w)) = f₁ w * starRingEnd ℂ (f₂ w)`.

Rewrite using `[hf₁.quasi g w, hf₂.quasi g w, map_mul]`. Establish `hu : ∀ a, ψ a * starRingEnd ℂ (ψ a) = 1` using `fun a => by`. Rewrite using `[Complex.mul_conj, Complex.normSq_eq_norm_sq, hψ.1.2.1]`. Evaluate the numerical expressions. Combine the equalities or inequalities in the displayed calculation.

Use `show ∫ w in 𝓕₀, H w ∂μ₀ = _`. Rewrite using `[hκ H hHc hHb hHp, hκ1, one_smul]`. Use `integral_congr_ae (.of_forall fun t => ?_)` and prove the remaining obligations. Establish `hInt : Integrable (Function.uncurry fun y x => H (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' t + GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C y + GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotro …`. Take `⟨b, hb'⟩` from `hHb`.

Establish `hcont : Continuous (Function.uncurry fun y x => H (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' t + GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C y + GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotr …` using `hHc.comp ((continuous_const.add ((continuous_fst).matrix_mul continuous_const)).add ((continuous_snd).matrix_mul continuous_const))`. Conclude with `Integrable.of_bound hcont.aestronglyMeasurable b (.of_forall fun p => hb' _)`. Use `show ∫ y, ∫ x, H _ ∂(μ'.restrict 𝓕') ∂(μ.restrict 𝓨) = _`. Use `haveI : SFinite (μ'.restrict 𝓕') := instSFiniteOfSigmaFinite`. Use `haveI : SFinite (μ.restrict 𝓨) := instSFiniteOfSigmaFinite`.

Rewrite using `[integral_integral_swap hInt]`. Use `integral_congr_ae (.of_forall fun x => ?_)` and prove the remaining obligations. Establish `hp` using `(GlobalTheory.T.parseval_mixedModel_isotropic_thetaProduct D V V' W r C B hs C' h1 h2 h3 ψ hψ μ 𝓨 hμ f₁ f₂ hf₁ hf₂ x t).2`. Use `Eq.trans ?_ hp.tsum_eq.symm` and prove the remaining obligations. Use `integral_congr_ae (.of_forall fun y => ?_)` and prove the remaining obligations.

Use `show H _ = H _`. Use `congr 1`. Normalize the expressions using the abelian group laws.
-/
theorem parseval : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.IsIsoSplit V V' C B → ∀ C' : Matrix (Fin V.rank) (Fin r) D.host.E, GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D C * V.gram * C' = 1 → GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D C' * V.gram * C' = 0 → GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D C' * V.gram * B = 0 → ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D W.rank r) μ 𝓨 → ∀ (μ₀ : Measure (WO V W)) (𝓕₀ : Set (WO V W)), IsCovolOne (ratL W V) μ₀ 𝓕₀ → ∀ (μ' : Measure (WO V' W)) (𝓕' : Set (WO V' W)), IsCovolOne (ratL W V') μ' 𝓕' → ∀ f₁ f₂, IsThetaFunO ψ V W f₁ → IsThetaFunO ψ V W f₂ → Continuous (fun u : Mx D W.rank r => ∫ x in 𝓕', GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (heisO ψ V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' u) f₁) x * starRingEnd ℂ (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (heisO ψ V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' u) f₂) x) ∂μ') ∧ Integrable (fun u : Mx D W.rank r => ∫ x in 𝓕', GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (heisO ψ V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' u) f₁) x * starRingEnd ℂ (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (heisO ψ V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' u) f₂) x) ∂μ') μ ∧ ∫ w in 𝓕₀, f₁ w * starRingEnd ℂ (f₂ w) ∂μ₀ = ∫ u : Mx D W.rank r, (∫ x in 𝓕', GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (heisO ψ V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' u) f₁) x * starRingEnd ℂ (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (heisO ψ V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' u) f₂) x) ∂μ') ∂μ := by
  intro D V V' W r C B hs C' h1 h2 h3 ψ hψ μ 𝓨 hμ μ₀ 𝓕₀ hμ₀ μ' 𝓕' hμ' f₁ f₂ hf₁ hf₂
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.MixModel.lattice_Mx D W.rank r
  obtain ⟨j1, j2, j3, j4, j5, -⟩ := GlobalTheory.MixModel.lattice_Mx D W.rank V'.rank
  haveI : BorelSpace (Mx D W.rank r) := ⟨rfl⟩
  haveI : BorelSpace (WO V' W) := ⟨rfl⟩
  haveI : IsFiniteMeasure (μ.restrict 𝓨) := ⟨by rw [Measure.restrict_apply_univ, hμ.2.2]; exact ENNReal.one_lt_top⟩
  haveI : IsFiniteMeasure (μ'.restrict 𝓕') := ⟨by rw [Measure.restrict_apply_univ, hμ'.2.2]; exact ENNReal.one_lt_top⟩
  let R : (WO V W → ℂ) → WO V' W → Mx D W.rank r → ℂ := fun f x u =>
    GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (heisO ψ V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' u) f) x
  let h : WO V' W → Mx D W.rank r → ℂ := fun x u => R f₁ x u * starRingEnd ℂ (R f₂ x u)
  obtain ⟨hc₁, M₁, hM₁⟩ := GlobalTheory.T.restrictedHeisenbergTheta_continuous_bounded D V V' W r C C' B ψ hψ μ 𝓨 hμ f₁ hf₁
  obtain ⟨hc₂, M₂, hM₂⟩ := GlobalTheory.T.restrictedHeisenbergTheta_continuous_bounded D V V' W r C C' B ψ hψ μ 𝓨 hμ f₂ hf₂
  have hhc : Continuous (Function.uncurry h) := hc₁.mul (Complex.continuous_conj.comp hc₂)
  have hhb : ∀ x u, ‖h x u‖ ≤ M₁ * M₂ := fun x u => by
    show ‖R f₁ x u * starRingEnd ℂ (R f₂ x u)‖ ≤ _
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul (hM₁ x u) (hM₂ x u) (norm_nonneg _) ((norm_nonneg _).trans (hM₁ x u))
  obtain ⟨C₁, hC₁⟩ := GlobalTheory.OrientedHeis.theta_bounded hψ hf₁
  obtain ⟨C₂, hC₂⟩ := GlobalTheory.OrientedHeis.theta_bounded hψ hf₂
  have hYr : μ.real 𝓨 = 1 := by simp [Measure.real, hμ.2.2]
  have hsq : ∀ (f : WO V W → ℂ), IsThetaFunO ψ V W f → ∀ Cf : ℝ, (∀ w, ‖f w‖ ≤ Cf) → ∀ x u,
      Summable (fun ξ : Matrix (Fin W.rank) (Fin r) D.host.E => ‖R f x (ξ.map (incA D) + u)‖ ^ 2) ∧
      ∑' ξ : Matrix (Fin W.rank) (Fin r) D.host.E, ‖R f x (ξ.map (incA D) + u)‖ ^ 2 ≤ Cf ^ 2 := by
    intro f hf Cf hCf x u
    obtain ⟨hs1, hs2⟩ := GlobalTheory.T.parseval_mixedModel_isotropic_thetaProduct D V V' W r C B hs C' h1 h2 h3 ψ hψ μ 𝓨 hμ f f hf hf x u
    have e : ∀ ξ : Matrix (Fin W.rank) (Fin r) D.host.E,
        ‖R f x (ξ.map (incA D) + u) * starRingEnd ℂ (R f x (ξ.map (incA D) + u))‖ = ‖R f x (ξ.map (incA D) + u)‖ ^ 2 :=
      fun ξ => by rw [norm_mul, Complex.norm_conj, sq]
    have hsum : Summable (fun ξ : Matrix (Fin W.rank) (Fin r) D.host.E => ‖R f x (ξ.map (incA D) + u)‖ ^ 2) :=
      hs1.congr e
    refine ⟨hsum, ?_⟩
    have e2 : ∀ ξ : Matrix (Fin W.rank) (Fin r) D.host.E,
        R f x (ξ.map (incA D) + u) * starRingEnd ℂ (R f x (ξ.map (incA D) + u)) =
          ((‖R f x (ξ.map (incA D) + u)‖ ^ 2 : ℝ) : ℂ) := fun ξ => by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    have hI := hs2.tsum_eq
    have hI' : ((∑' ξ : Matrix (Fin W.rank) (Fin r) D.host.E, ‖R f x (ξ.map (incA D) + u)‖ ^ 2 : ℝ) : ℂ) =
        ∫ y in 𝓨, f (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C y + GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.midPart V V' W B x +
          GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' u) * starRingEnd ℂ (f (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C y +
          GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.midPart V V' W B x + GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' u)) ∂μ := by
      rw [Complex.ofReal_tsum, ← hI]
      exact tsum_congr fun ξ => (e2 ξ).symm
    have hnn : 0 ≤ ∑' ξ : Matrix (Fin W.rank) (Fin r) D.host.E, ‖R f x (ξ.map (incA D) + u)‖ ^ 2 :=
      tsum_nonneg fun _ => by positivity
    have hb : ∀ w, ‖f w * starRingEnd ℂ (f w)‖ ≤ Cf ^ 2 := fun w => by
      rw [norm_mul, Complex.norm_conj, ← sq]
      exact pow_le_pow_left₀ (norm_nonneg _) (hCf w) 2
    calc ∑' ξ : Matrix (Fin W.rank) (Fin r) D.host.E, ‖R f x (ξ.map (incA D) + u)‖ ^ 2
        = ‖((∑' ξ : Matrix (Fin W.rank) (Fin r) D.host.E, ‖R f x (ξ.map (incA D) + u)‖ ^ 2 : ℝ) : ℂ)‖ := by
          rw [Complex.norm_real, Real.norm_of_nonneg hnn]
      _ ≤ Cf ^ 2 * (μ.restrict 𝓨).real Set.univ := by
          rw [hI']
          exact norm_integral_le_of_norm_le_const (.of_forall fun y => hb _)
      _ = Cf ^ 2 := by simp [Measure.real, Measure.restrict_apply_univ, hμ.2.2]
  have hb : ∀ x u, Summable (fun ξ : Matrix (Fin W.rank) (Fin r) D.host.E => ‖h x (ξ.map (incA D) + u)‖) ∧
      ∑' ξ : Matrix (Fin W.rank) (Fin r) D.host.E, ‖h x (ξ.map (incA D) + u)‖ ≤ (C₁ ^ 2 + C₂ ^ 2) / 2 := by
    intro x u
    obtain ⟨s1, t1⟩ := hsq f₁ hf₁ C₁ hC₁ x u
    obtain ⟨s2, t2⟩ := hsq f₂ hf₂ C₂ hC₂ x u
    have hle : ∀ ξ : Matrix (Fin W.rank) (Fin r) D.host.E, ‖h x (ξ.map (incA D) + u)‖ ≤
        (‖R f₁ x (ξ.map (incA D) + u)‖ ^ 2 + ‖R f₂ x (ξ.map (incA D) + u)‖ ^ 2) / 2 := fun ξ => by
      show ‖R f₁ x (ξ.map (incA D) + u) * starRingEnd ℂ (R f₂ x (ξ.map (incA D) + u))‖ ≤ _
      rw [norm_mul, Complex.norm_conj]
      nlinarith [sq_nonneg (‖R f₁ x (ξ.map (incA D) + u)‖ - ‖R f₂ x (ξ.map (incA D) + u)‖)]
    have hs' := (s1.add s2).div_const 2
    refine ⟨Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle hs', ?_⟩
    calc ∑' ξ : Matrix (Fin W.rank) (Fin r) D.host.E, ‖h x (ξ.map (incA D) + u)‖
        ≤ ∑' ξ : Matrix (Fin W.rank) (Fin r) D.host.E,
            (‖R f₁ x (ξ.map (incA D) + u)‖ ^ 2 + ‖R f₂ x (ξ.map (incA D) + u)‖ ^ 2) / 2 :=
          (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle hs').tsum_le_tsum hle hs'
      _ = ((∑' ξ : Matrix (Fin W.rank) (Fin r) D.host.E, ‖R f₁ x (ξ.map (incA D) + u)‖ ^ 2) +
            ∑' ξ : Matrix (Fin W.rank) (Fin r) D.host.E, ‖R f₂ x (ξ.map (incA D) + u)‖ ^ 2) / 2 := by
          rw [tsum_div_const, s1.tsum_add s2]
      _ ≤ (C₁ ^ 2 + C₂ ^ 2) / 2 := by linarith
  obtain ⟨hint, hEq⟩ := GlobalTheory.T.integral_parametric_unfold_rationalTranslates D W.rank r (WO V' W) (μ'.restrict 𝓕') μ 𝓨 hμ h hhc _ hb
  have a1 : ∀ x, Continuous (h x) := fun x => hhc.uncurry_left x
  have a2 : ∀ u, Continuous (fun x => h x u) := fun u => hhc.uncurry_right u
  have a3 : ∀ u, AEStronglyMeasurable (fun x => h x u) (μ'.restrict 𝓕') := fun u => (a2 u).aestronglyMeasurable
  haveI : FirstCountableTopology (Mx D W.rank r) := @TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _ _ i3
  have hG : Continuous (fun u => ∫ x, h x u ∂(μ'.restrict 𝓕')) :=
    continuous_of_dominated (bound := fun _ => M₁ * M₂) a3
      (fun u => .of_forall fun x => hhb x u) (integrable_const _) (.of_forall a1)
  refine ⟨hG, hint, ?_⟩
  show _ = ∫ u, (∫ x, h x u ∂(μ'.restrict 𝓕')) ∂μ
  rw [hEq]
  obtain ⟨κ, -, hκ⟩ := GlobalTheory.TwistHaar.integral_fundamentalDomain_eq_iterated D V V' W r C B hs C' h1 h2 h3 μ 𝓨 hμ
    μ₀ 𝓕₀ hμ₀.1 hμ₀.2.1 μ' 𝓕' hμ'.1 hμ'.2.1
  have hκ1 : κ = 1 := by
    have e := hκ (fun _ => 1) continuous_const ⟨1, fun _ => by simp⟩ (fun _ _ _ => rfl)
    simp only [setIntegral_const, Measure.real, hμ₀.2.2, hμ.2.2, hμ'.2.2, ENNReal.toReal_one, one_smul] at e
    rw [Complex.real_smul, mul_one] at e
    exact_mod_cast e.symm
  let H : WO V W → ℂ := fun w => f₁ w * starRingEnd ℂ (f₂ w)
  have hHc : Continuous H := hf₁.cont.mul (Complex.continuous_conj.comp hf₂.cont)
  have hHb : ∃ b : ℝ, ∀ w, ‖H w‖ ≤ b := ⟨C₁ * C₂, fun w => by
    show ‖f₁ w * starRingEnd ℂ (f₂ w)‖ ≤ _
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul (hC₁ w) (hC₂ w) (norm_nonneg _) ((norm_nonneg _).trans (hC₁ w))⟩
  have hHp : ∀ γ ∈ ratL W V, ∀ w, H (γ + w) = H w := by
    rintro γ ⟨g, rfl⟩ w
    show f₁ (ratW W V g + w) * starRingEnd ℂ (f₂ (ratW W V g + w)) = f₁ w * starRingEnd ℂ (f₂ w)
    rw [hf₁.quasi g w, hf₂.quasi g w, map_mul]
    have hu : ∀ a, ψ a * starRingEnd ℂ (ψ a) = 1 := fun a => by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hψ.1.2.1]; norm_num
    calc ψ (-symplOH V W (ratW W V g) w) * f₁ w * (starRingEnd ℂ (ψ (-symplOH V W (ratW W V g) w)) * starRingEnd ℂ (f₂ w))
        = (ψ (-symplOH V W (ratW W V g) w) * starRingEnd ℂ (ψ (-symplOH V W (ratW W V g) w))) *
            (f₁ w * starRingEnd ℂ (f₂ w)) := by ring
      _ = _ := by rw [hu, one_mul]
  show ∫ w in 𝓕₀, H w ∂μ₀ = _
  rw [hκ H hHc hHb hHp, hκ1, one_smul]
  refine integral_congr_ae (.of_forall fun t => ?_)
  have hInt : Integrable (Function.uncurry fun y x => H (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' t +
      GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C y + GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.midPart V V' W B x)) ((μ.restrict 𝓨).prod (μ'.restrict 𝓕')) := by
    obtain ⟨b, hb'⟩ := hHb
    have hcont : Continuous (Function.uncurry fun y x => H (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' t +
        GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C y + GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.midPart V V' W B x)) :=
      hHc.comp ((continuous_const.add ((continuous_fst).matrix_mul continuous_const)).add
        ((continuous_snd).matrix_mul continuous_const))
    exact Integrable.of_bound hcont.aestronglyMeasurable b (.of_forall fun p => hb' _)
  show ∫ y, ∫ x, H _ ∂(μ'.restrict 𝓕') ∂(μ.restrict 𝓨) = _
  haveI : SFinite (μ'.restrict 𝓕') := instSFiniteOfSigmaFinite
  haveI : SFinite (μ.restrict 𝓨) := instSFiniteOfSigmaFinite
  rw [integral_integral_swap hInt]
  refine integral_congr_ae (.of_forall fun x => ?_)
  have hp := (GlobalTheory.T.parseval_mixedModel_isotropic_thetaProduct D V V' W r C B hs C' h1 h2 h3 ψ hψ μ 𝓨 hμ f₁ f₂ hf₁ hf₂ x t).2
  refine Eq.trans ?_ hp.tsum_eq.symm
  refine integral_congr_ae (.of_forall fun y => ?_)
  show H _ = H _
  congr 1
  abel

end GlobalTheory.MixParseval

end
