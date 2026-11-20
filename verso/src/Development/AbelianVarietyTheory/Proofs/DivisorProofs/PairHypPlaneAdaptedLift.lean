import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermUnipotentIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawPairPlaneDimensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawPairPlaneDescentFirstStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawPairPlaneDescentSecondStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawPairPlaneDescentThird
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawPairPlaneDescentFourthStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawPairPlaneDescentFifthStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawPairPlaneDescentSixthStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawPairPlaneDescentSeventhStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawPairPlaneDescentEighthStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.KernelTower

/- English proof (translation)
Introduce `hKP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ hH' d₂ H hH V₁ M₁ e hV₁ hM₁ he`. Take `⟨C₀, -, hexp⟩` from `GlobalTheory.T.seesaw_pair_plane_dimension hKP F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ hH' d₂ H hH V₁ M₁ e hV₁ hM₁ he`. Establish `hpres : ∀ x, ∀ Φ ∈ schA F (Fin n × Fin d), om x Φ ∈ schA F (Fin n × Fin d)` using `fun x Φ hΦ => (IsUWeilPair.isUSplitting hP.weil).pres x Φ hΦ`. Establish `hcomm : ∀ (u : UA σ X.J) (p : UA σ W.J) (Ψ : Fn F n d), om (u, 1) (om (1, p) Ψ) = om (1, p) (om (u, 1) Ψ)`. Introduce `u p Ψ`.

Rewrite using `[← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]`. Simplify using the standard rewrite rules. Establish `hW : ∀ w : {w : Fin d → E // w ≠ 0 ∧ form σ W.J w w = 0}, ∃ γ ∈ ratU σ W.J, mat γ *ᵥ incV F w.1 = incV F H'.x` using `fun w => GlobalTheory.T.seesaw_pair_plane_descent_eighth hKP F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ hH' d₂ H hH V₁ M₁ e hV₁ hM₁ he w.1 w.2.1 w.2.2`. Use `choose γ hγ1 hγ2 using hW`. Use `⟨C₀, fun Φ hΦ g => ?_⟩` and prove the remaining obligations.

Establish `hgh : ∀ (p h : UA σ W.J), om (g, p * h) Φ = om (1, p) (om (g, h) Φ)`. Introduce `p h`. Establish `e1 : ((g, p * h) : UA σ X.J × UA σ W.J) = (1, p) * (g, h)` using `by simp`. Rewrite using `[e1, map_mul, Module.End.mul_apply]`. Establish `key : ∀ (μ : Measure (unip σ X H)) (𝓕 : Set (unip σ X H)), μ.IsHaarMeasure → IsFundamentalDomain ((ratU σ X.J).subgroupOf (unip σ X H)) 𝓕 μ → μ 𝓕 = 1 → ∀ h, (Summable fun w : Fin d → E => ∫ u in 𝓕, thetaSum F (e (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) (om (u.1, 1 …`.

Introduce `μ 𝓕 hμ h𝓕 h1 h`. Establish `hΨ` using `hpres (g, h) Φ hΦ`. Take `⟨hs, hsw⟩` from `GlobalTheory.T.seesaw_pair_plane_descent_second hKP F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ hH' d₂ H hH V₁ M₁ e hV₁ hM₁ he μ 𝓕 hμ h𝓕 h1 _ hΨ`. Use `⟨hs, ?_⟩` and prove the remaining obligations. Establish `hint : ∫ u in 𝓕, theta om Φ (u.1 * g) h ∂μ = C₀ * ∑' w : Fin d → E, ∫ u in 𝓕, thetaSum F (e (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) (om (u.1, 1) (om (g, h) Φ)))) ∂μ`.

Rewrite using `[← hsw, ← integral_const_mul]`. Use `congr 1`. Use function extensionality and compare the values at `u`. Establish `e1 : ((u.1 * g, h) : UA σ X.J × UA σ W.J) = (u.1, 1) * (g, h)` using `by simp`. Rewrite using `[theta, e1, map_mul, Module.End.mul_apply]`.

Conclude with `(hexp _ (hpres _ _ hΨ)).2`. Establish `hzero : ∫ u in 𝓕, thetaSum F (e (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F (0 : Fin d → E))) (om (u.1, 1) (om (g, h) Φ)))) ∂μ = thetaSum F (e (om (g, h) Φ))`. Establish `e2 : ∀ u : unip σ X H, thetaSum F (e (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F (0 : Fin d → E))) (om (u.1, 1) (om (g, h) Φ)))) = thetaSum F (e (om (g, h) Φ))`. Introduce `u`. Establish `hz : M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F (0 : Fin d → E))) (om (u.1, 1) (om (g, h) Φ)) = om (u.1, 1) (om (g, h) Φ)`.

Establish `h0 : incV F (0 : Fin d → E) = 0`. Use function extensionality and compare the values at `i`. Unfold `incV`. Simplify using the standard rewrite rules. Establish `hv : Matrix.vecMulVec (incV F H.y) (incV F (0 : Fin d → E)) = 0`.

Rewrite using `[h0]`. Use extensionality with `i j`. Simplify using `[Matrix.vecMulVec]`. Rewrite using `[hv]`. Use function extensionality and compare the values at `x`.

Simplify using `[Darboux.rho, schr]`. Rewrite using `[hz, GlobalTheory.T.seesaw_pair_plane_descent_first hKP F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ hH' d₂ H hH V₁ M₁ e hV₁ hM₁ he u.1 u.2 _ hΨ]`. Simplify using `only [e2, setIntegral_const, measureReal_def, h1, ENNReal.toReal_one, one_smul]`. Rewrite using `[hint]`. Use `set a : (Fin d → E) → ℂ := fun w => ∫ u in 𝓕, thetaSum F (e (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) (om (u.1, 1) (om (g, h) Φ)))) ∂μ with ha`.

Establish `hsupp : Function.support (fun w => if w = 0 then 0 else a w) ⊆ {w | w ≠ 0 ∧ form σ W.J w w = 0}`. Introduce `w hw`. Simplify using `only [Function.mem_support, ne_eq, ite_eq_left_iff, not_forall] at hw`. Take `⟨h0, hne⟩` from `hw`. Use `⟨h0, ?_⟩` and prove the remaining obligations.

Assume the negation of the conclusion as `hf`. Conclude with `hne (GlobalTheory.T.seesaw_pair_plane_descent_third hKP F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ hH' d₂ H hH V₁ M₁ e hV₁ hM₁ he μ 𝓕 hμ h𝓕 h1 _ hΨ w hf)`. Establish `hzero' : a 0 = thetaSum F (e (om (g, h) Φ))` using `hzero`. Establish `hsum : (∑' x : ({w | w ≠ 0 ∧ form σ W.J w w = 0} : Set (Fin d → E)), if (x : Fin d → E) = 0 then 0 else a x) = ∑' w : {w : Fin d → E // w ≠ 0 ∧ form σ W.J w w = 0}, a w.1` using `tsum_congr fun w => if_neg w.2.1`. Rewrite using `[hs.tsum_eq_add_tsum_ite 0, ← tsum_subtype_eq_of_support_subset hsupp, hzero', hsum, mul_add]`.

Distinguish the cases in `hex : ∃ (μ₀ : Measure (unip σ X H)) (𝓕₀ : Set (unip σ X H)), μ₀.IsHaarMeasure ∧ IsFundamentalDomain ((ratU σ X.J).subgroupOf (unip σ X H)) 𝓕₀ μ₀ ∧ μ₀ 𝓕₀ = 1`. Use `swap`. Use `⟨0, γ, continuous_const, fun _ _ _ => rfl, fun _ _ _ _ => rfl, fun w => ⟨hγ1 w, hγ2 w⟩, fun _ => by simpa using (summable_zero : Summable fun _ : {w : Fin d → E // w ≠ 0 ∧ form σ W.J w w = 0} => (0 : ℝ)), ⟨0, 0, fun h => by simp⟩, ?_⟩` and prove the remaining obligations. Introduce `μN 𝓕N hμ h𝓕 h1`. Conclude with `(hex ⟨μN, 𝓕N, hμ, h𝓕, h1⟩).elim`.

Take `⟨μ₀, 𝓕₀, hμ₀, h𝓕₀, h₀⟩` from `hex`. Use `set a : (Fin d → E) → UA σ W.J → ℂ := fun w h => ∫ u in 𝓕₀, thetaSum F (e (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) (om (u.1, 1) (om (g, h) Φ)))) ∂μ₀ with ha`. Establish `hre : ∀ w : {w : Fin d → E // w ≠ 0 ∧ form σ W.J w w = 0}, ∀ h, a H'.x (γ w * h) = a w.1 h`. Introduce `w h`. Simplify using `only [ha]`.

Use `congr 1`. Use function extensionality and compare the values at `u`. Rewrite using `[hgh, hcomm]`. Conclude with `GlobalTheory.T.seesaw_pair_plane_descent_fourth hKP F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ hH' d₂ H hH V₁ M₁ e hV₁ hM₁ he (γ w) (hγ1 w) w.1 H'.x (hγ2 w) _ (hpres _ _ (hpres _ _ hΦ))`. Take `⟨C, k, hCk⟩` from `GlobalTheory.T.seesaw_pair_plane_descent_seventh hKP F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ hH' d₂ H hH V₁ M₁ e hV₁ hM₁ he μ₀ 𝓕₀ hμ₀ h𝓕₀ h₀ Φ hΦ g`.

Establish `hsub : ∀ h, Summable fun w : {w : Fin d → E // w ≠ 0 ∧ form σ W.J w w = 0} => ‖a w.1 h‖` using `fun h => (hCk h).1.subtype _`. Use `⟨fun h => C₀ * a H'.x h, γ, continuous_const.mul (GlobalTheory.T.seesaw_pair_plane_descent_sixth hKP F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ hH' d₂ H hH V₁ M₁ e hV₁ hM₁ he μ₀ 𝓕₀ hμ₀ h𝓕₀ h₀ Φ hΦ g), ?_, ?_, fun w => ⟨hγ1 w, hγ2 w⟩, ?_, ⟨‖C₀‖ * C, k, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `u' hu' h`. Simplify using `only [ha]`. Rewrite using `[hgh]`.

Use `congr 1`. Conclude with `GlobalTheory.T.seesaw_pair_plane_descent_fifth hKP F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ hH' d₂ H hH V₁ M₁ e hV₁ hM₁ he μ₀ 𝓕₀ hμ₀ h𝓕₀ h₀ _ (hpres _ _ hΦ) u' hu'`. Introduce `p hp hpx h`. Simplify using `only [ha]`. Use `congr 2`.

Use function extensionality and compare the values at `u`. Rewrite using `[hgh, hcomm]`. Conclude with `GlobalTheory.T.seesaw_pair_plane_descent_fourth hKP F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ hH' d₂ H hH V₁ M₁ e hV₁ hM₁ he p hp H'.x H'.x hpx _ (hpres _ _ (hpres _ _ hΦ))`. Introduce `h`. Simplify using `only [hre, norm_mul]`.

Conclude with `(hsub h).mul_left _`. Introduce `h`. Simplify using `only [hre, norm_mul]`. Rewrite using `[tsum_mul_left, mul_assoc]`. Use `mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)` and prove the remaining obligations.

Use `le_trans ?_ (hCk h).2` and prove the remaining obligations. Conclude with `tsum_comp_le_tsum_of_inj (hCk h).1 (fun _ => norm_nonneg _) Subtype.val_injective`. Introduce `μN 𝓕N hμ h𝓕 h1 h`. Establish `hind : ∫ u in 𝓕N, theta om Φ (u.1 * g) h ∂μN = ∫ u in 𝓕₀, theta om Φ (u.1 * g) h ∂μ₀`. Take `⟨i1, i2, i3, i4⟩` from `GlobalTheory.UnipCT.topFacts (F := F) σ X.J`.

Use `haveI : BorelSpace (UA σ X.J) := ⟨rfl⟩`. Use `haveI : LocallyCompactSpace (unip σ X H) := (GlobalTheory.UnipCT.isClosed_unip σ X H).isClosedEmbedding_subtypeVal.locallyCompactSpace`. Use `haveI := GlobalTheory.UnipCT.countable_ratU (σ := σ) X.J`. Use `haveI : Countable ((ratU σ X.J).subgroupOf (unip σ X H)) := Function.Injective.countable (f := fun x : (ratU σ X.J).subgroupOf (unip σ X H) => (⟨x.1.1, x.2⟩ : ratU σ X.J)) fun x y hxy => by`. Apply `Subtype.ext` to reduce the goal to its premises.

Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `using congrArg Subtype.val hxy`. Use `GlobalTheory.UnipCT.setIntegral_fd_eq ((ratU σ X.J).subgroupOf (unip σ X H)) (fun u => theta om Φ (u.1 * g) h) ?_ μN μ₀ 𝓕N 𝓕₀ h𝓕 h𝓕₀ h1 h₀` and prove the remaining obligations. Introduce `p hp x`. Establish `hTB` using `((GlobalTheory.T.theta_basic_properties hKP.base F E σ B n d X W M χX χW om r s r' s' hP).1 Φ hΦ).2.1`.

Use `hTB p.1 (Subgroup.mem_subgroupOf.1 hp) 1 (one_mem _) (x.1 * g) h` as an intermediate fact. Simplify `this` using `[mul_assoc]`. Rewrite using `[hind, (key μ₀ 𝓕₀ hμ₀ h𝓕₀ h₀ h).2, ← tsum_mul_left]`. Use `congr 1`. Use `tsum_congr fun w => ?_` and prove the remaining obligations.

Use `show _ = C₀ * a H'.x (γ w * h)`. Rewrite using `[hre w h]`.
-/
theorem constantTerm_kernel : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B W W₁ i₀ i₁ →
    ∀ (d₂ : ℕ) (H : Plane E n d₂), (d₂ + 2 = n ∧ form σ X.J H.x H.x = 0 ∧ form σ X.J H.y H.y = 0 ∧ form σ X.J H.x H.y = 1 ∧
        (∀ u, form σ X.J (H.ι *ᵥ u) H.x = 0 ∧ form σ X.J (H.ι *ᵥ u) H.y = 0) ∧ Function.Injective H.ι.mulVec) →
    ∀ (V₁ : Spc F E d₂) (M₁ : Model σ V₁ W) (e : Fn F n d →ₗ[ℂ] Fn F d₂ d),
      V₁.J = H.ιᵀ * X.J * H.ι.map σ → M₁.IsGood B.ψ → IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e →
    ∃ C₀ : ℂ, ∀ Φ ∈ schA F (Fin n × Fin d), ∀ g : UA σ X.J,
      ∃ (T : UA σ W.J → ℂ) (γ : {w : Fin d → E // w ≠ 0 ∧ form σ W.J w w = 0} → UA σ W.J),
        Continuous T ∧ (∀ u ∈ unip σ W H', ∀ h, T (u * h) = T h) ∧
        (∀ p ∈ ratU σ W.J, mat p *ᵥ incV F H'.x = incV F H'.x → ∀ h, T (p * h) = T h) ∧
        (∀ w, γ w ∈ ratU σ W.J ∧ mat (γ w) *ᵥ incV F w.1 = incV F H'.x) ∧
        (∀ h, Summable fun w => ‖T (γ w * h)‖) ∧ (∃ (C : ℝ) (k : ℕ), ∀ h, ∑' w, ‖T (γ w * h)‖ ≤ C * (qht h : ℝ) ^ k) ∧
        ∀ (μN : Measure (unip σ X H)) (𝓕N : Set (unip σ X H)), μN.IsHaarMeasure →
          IsFundamentalDomain ((ratU σ X.J).subgroupOf (unip σ X H)) 𝓕N μN → μN 𝓕N = 1 →
          ∀ h, ∫ u in 𝓕N, theta om Φ (u.1 * g) h ∂μN = C₀ * thetaSum F (e (om (g, h) Φ)) + ∑' w, T (γ w * h) := by
  intro hKP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ hH' d₂ H hH V₁ M₁ e hV₁ hM₁ he
  obtain ⟨C₀, -, hexp⟩ := GlobalTheory.T.seesaw_pair_plane_dimension hKP F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ hH' d₂ H hH V₁ M₁ e hV₁ hM₁ he
  have hpres : ∀ x, ∀ Φ ∈ schA F (Fin n × Fin d), om x Φ ∈ schA F (Fin n × Fin d) :=
    fun x Φ hΦ => (IsUWeilPair.isUSplitting hP.weil).pres x Φ hΦ
  have hcomm : ∀ (u : UA σ X.J) (p : UA σ W.J) (Ψ : Fn F n d), om (u, 1) (om (1, p) Ψ) = om (1, p) (om (u, 1) Ψ) := by
    intro u p Ψ
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    simp
  have hW : ∀ w : {w : Fin d → E // w ≠ 0 ∧ form σ W.J w w = 0}, ∃ γ ∈ ratU σ W.J, mat γ *ᵥ incV F w.1 = incV F H'.x :=
    fun w => GlobalTheory.T.seesaw_pair_plane_descent_eighth hKP F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ hH' d₂ H hH V₁ M₁ e hV₁ hM₁ he w.1 w.2.1 w.2.2
  choose γ hγ1 hγ2 using hW
  refine ⟨C₀, fun Φ hΦ g => ?_⟩
  have hgh : ∀ (p h : UA σ W.J), om (g, p * h) Φ = om (1, p) (om (g, h) Φ) := by
    intro p h
    have e1 : ((g, p * h) : UA σ X.J × UA σ W.J) = (1, p) * (g, h) := by simp
    rw [e1, map_mul, Module.End.mul_apply]

  have key : ∀ (μ : Measure (unip σ X H)) (𝓕 : Set (unip σ X H)), μ.IsHaarMeasure →
      IsFundamentalDomain ((ratU σ X.J).subgroupOf (unip σ X H)) 𝓕 μ → μ 𝓕 = 1 → ∀ h,
      (Summable fun w : Fin d → E => ∫ u in 𝓕, thetaSum F (e (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) (om (u.1, 1) (om (g, h) Φ)))) ∂μ) ∧
      ∫ u in 𝓕, theta om Φ (u.1 * g) h ∂μ = C₀ * thetaSum F (e (om (g, h) Φ)) +
        C₀ * ∑' w : {w : Fin d → E // w ≠ 0 ∧ form σ W.J w w = 0}, ∫ u in 𝓕, thetaSum F (e (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w.1)) (om (u.1, 1) (om (g, h) Φ)))) ∂μ := by
    intro μ 𝓕 hμ h𝓕 h1 h
    have hΨ := hpres (g, h) Φ hΦ
    obtain ⟨hs, hsw⟩ := GlobalTheory.T.seesaw_pair_plane_descent_second hKP F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ hH' d₂ H hH V₁ M₁ e hV₁ hM₁ he μ 𝓕 hμ h𝓕 h1 _ hΨ
    refine ⟨hs, ?_⟩
    have hint : ∫ u in 𝓕, theta om Φ (u.1 * g) h ∂μ = C₀ * ∑' w : Fin d → E, ∫ u in 𝓕, thetaSum F (e (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) (om (u.1, 1) (om (g, h) Φ)))) ∂μ := by
      rw [← hsw, ← integral_const_mul]
      congr 1
      funext u
      have e1 : ((u.1 * g, h) : UA σ X.J × UA σ W.J) = (u.1, 1) * (g, h) := by simp
      rw [theta, e1, map_mul, Module.End.mul_apply]
      exact (hexp _ (hpres _ _ hΨ)).2
    have hzero : ∫ u in 𝓕, thetaSum F (e (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F (0 : Fin d → E))) (om (u.1, 1) (om (g, h) Φ)))) ∂μ = thetaSum F (e (om (g, h) Φ)) := by
      have e2 : ∀ u : unip σ X H, thetaSum F (e (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F (0 : Fin d → E))) (om (u.1, 1) (om (g, h) Φ)))) = thetaSum F (e (om (g, h) Φ)) := by
        intro u
        have hz : M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F (0 : Fin d → E))) (om (u.1, 1) (om (g, h) Φ)) = om (u.1, 1) (om (g, h) Φ) := by
          have h0 : incV F (0 : Fin d → E) = 0 := by
            funext i
            unfold incV
            simp
          have hv : Matrix.vecMulVec (incV F H.y) (incV F (0 : Fin d → E)) = 0 := by
            rw [h0]; ext i j; simp [Matrix.vecMulVec]
          rw [hv]
          funext x
          simp [Darboux.rho, schr]
        rw [hz, GlobalTheory.T.seesaw_pair_plane_descent_first hKP F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ hH' d₂ H hH V₁ M₁ e hV₁ hM₁ he u.1 u.2 _ hΨ]
      simp only [e2, setIntegral_const, measureReal_def, h1, ENNReal.toReal_one, one_smul]
    rw [hint]
    classical
    set a : (Fin d → E) → ℂ := fun w => ∫ u in 𝓕, thetaSum F (e (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) (om (u.1, 1) (om (g, h) Φ)))) ∂μ with ha
    have hsupp : Function.support (fun w => if w = 0 then 0 else a w) ⊆ {w | w ≠ 0 ∧ form σ W.J w w = 0} := by
      intro w hw
      simp only [Function.mem_support, ne_eq, ite_eq_left_iff, not_forall] at hw
      obtain ⟨h0, hne⟩ := hw
      refine ⟨h0, ?_⟩
      by_contra hf
      exact hne (GlobalTheory.T.seesaw_pair_plane_descent_third hKP F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ hH' d₂ H hH V₁ M₁ e hV₁ hM₁ he μ 𝓕 hμ h𝓕 h1 _ hΨ w hf)
    have hzero' : a 0 = thetaSum F (e (om (g, h) Φ)) := hzero
    have hsum : (∑' x : ({w | w ≠ 0 ∧ form σ W.J w w = 0} : Set (Fin d → E)), if (x : Fin d → E) = 0 then 0 else a x) =
        ∑' w : {w : Fin d → E // w ≠ 0 ∧ form σ W.J w w = 0}, a w.1 := tsum_congr fun w => if_neg w.2.1
    rw [hs.tsum_eq_add_tsum_ite 0, ← tsum_subtype_eq_of_support_subset hsupp, hzero', hsum, mul_add]
  classical
  by_cases hex : ∃ (μ₀ : Measure (unip σ X H)) (𝓕₀ : Set (unip σ X H)), μ₀.IsHaarMeasure ∧
      IsFundamentalDomain ((ratU σ X.J).subgroupOf (unip σ X H)) 𝓕₀ μ₀ ∧ μ₀ 𝓕₀ = 1
  swap
  · refine ⟨0, γ, continuous_const, fun _ _ _ => rfl, fun _ _ _ _ => rfl, fun w => ⟨hγ1 w, hγ2 w⟩,
      fun _ => by simpa using (summable_zero : Summable fun _ : {w : Fin d → E // w ≠ 0 ∧ form σ W.J w w = 0} => (0 : ℝ)),
      ⟨0, 0, fun h => by simp⟩, ?_⟩
    intro μN 𝓕N hμ h𝓕 h1
    exact (hex ⟨μN, 𝓕N, hμ, h𝓕, h1⟩).elim
  obtain ⟨μ₀, 𝓕₀, hμ₀, h𝓕₀, h₀⟩ := hex
  set a : (Fin d → E) → UA σ W.J → ℂ := fun w h => ∫ u in 𝓕₀, thetaSum F (e (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) (om (u.1, 1) (om (g, h) Φ)))) ∂μ₀ with ha
  have hre : ∀ w : {w : Fin d → E // w ≠ 0 ∧ form σ W.J w w = 0}, ∀ h, a H'.x (γ w * h) = a w.1 h := by
    intro w h
    simp only [ha]
    congr 1
    funext u
    rw [hgh, hcomm]
    exact GlobalTheory.T.seesaw_pair_plane_descent_fourth hKP F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ hH' d₂ H hH V₁ M₁ e hV₁ hM₁ he (γ w) (hγ1 w) w.1 H'.x (hγ2 w) _ (hpres _ _ (hpres _ _ hΦ))
  obtain ⟨C, k, hCk⟩ := GlobalTheory.T.seesaw_pair_plane_descent_seventh hKP F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ hH' d₂ H hH V₁ M₁ e hV₁ hM₁ he μ₀ 𝓕₀ hμ₀ h𝓕₀ h₀ Φ hΦ g
  have hsub : ∀ h, Summable fun w : {w : Fin d → E // w ≠ 0 ∧ form σ W.J w w = 0} => ‖a w.1 h‖ :=
    fun h => (hCk h).1.subtype _
  refine ⟨fun h => C₀ * a H'.x h, γ, continuous_const.mul (GlobalTheory.T.seesaw_pair_plane_descent_sixth hKP F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ hH' d₂ H hH V₁ M₁ e hV₁ hM₁ he μ₀ 𝓕₀ hμ₀ h𝓕₀ h₀ Φ hΦ g),
    ?_, ?_, fun w => ⟨hγ1 w, hγ2 w⟩, ?_, ⟨‖C₀‖ * C, k, ?_⟩, ?_⟩
  · intro u' hu' h
    simp only [ha]
    rw [hgh]
    congr 1
    exact GlobalTheory.T.seesaw_pair_plane_descent_fifth hKP F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ hH' d₂ H hH V₁ M₁ e hV₁ hM₁ he μ₀ 𝓕₀ hμ₀ h𝓕₀ h₀ _ (hpres _ _ hΦ) u' hu'
  · intro p hp hpx h
    simp only [ha]
    congr 2
    funext u
    rw [hgh, hcomm]
    exact GlobalTheory.T.seesaw_pair_plane_descent_fourth hKP F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ hH' d₂ H hH V₁ M₁ e hV₁ hM₁ he p hp H'.x H'.x hpx _ (hpres _ _ (hpres _ _ hΦ))
  · intro h
    simp only [hre, norm_mul]
    exact (hsub h).mul_left _
  · intro h
    simp only [hre, norm_mul]
    rw [tsum_mul_left, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    refine le_trans ?_ (hCk h).2
    exact tsum_comp_le_tsum_of_inj (hCk h).1 (fun _ => norm_nonneg _) Subtype.val_injective
  · intro μN 𝓕N hμ h𝓕 h1 h

    have hind : ∫ u in 𝓕N, theta om Φ (u.1 * g) h ∂μN = ∫ u in 𝓕₀, theta om Φ (u.1 * g) h ∂μ₀ := by
      obtain ⟨i1, i2, i3, i4⟩ := GlobalTheory.UnipCT.topFacts (F := F) σ X.J
      haveI : BorelSpace (UA σ X.J) := ⟨rfl⟩
      haveI : LocallyCompactSpace (unip σ X H) := (GlobalTheory.UnipCT.isClosed_unip σ X H).isClosedEmbedding_subtypeVal.locallyCompactSpace
      haveI := GlobalTheory.UnipCT.countable_ratU (σ := σ) X.J
      haveI : Countable ((ratU σ X.J).subgroupOf (unip σ X H)) :=
        Function.Injective.countable (f := fun x : (ratU σ X.J).subgroupOf (unip σ X H) => (⟨x.1.1, x.2⟩ : ratU σ X.J))
          fun x y hxy => by
            apply Subtype.ext; apply Subtype.ext
            simpa using congrArg Subtype.val hxy
      refine GlobalTheory.UnipCT.setIntegral_fd_eq ((ratU σ X.J).subgroupOf (unip σ X H)) (fun u => theta om Φ (u.1 * g) h) ?_
        μN μ₀ 𝓕N 𝓕₀ h𝓕 h𝓕₀ h1 h₀
      intro p hp x
      have hTB := ((GlobalTheory.T.theta_basic_properties hKP.base F E σ B n d X W M χX χW om r s r' s' hP).1 Φ hΦ).2.1
      have := hTB p.1 (Subgroup.mem_subgroupOf.1 hp) 1 (one_mem _) (x.1 * g) h
      simpa [mul_assoc] using this
    rw [hind, (key μ₀ 𝓕₀ hμ₀ h𝓕₀ h₀ h).2, ← tsum_mul_left]
    congr 1
    refine tsum_congr fun w => ?_
    show _ = C₀ * a H'.x (γ w * h)
    rw [hre w h]

end GlobalTheory.KernelTower

end
