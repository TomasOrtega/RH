import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelSetWittFrameCompactBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittFrameDarbouxCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusActionModelCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicSchwartzThetaDistributionSumNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxCoordsGoodModelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilEigenBijectiveSchwartzStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilEigenSchwartzSurjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicThetaSumNormLePolynomialScale
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFrameUOfIsWittFrame

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

noncomputable section
namespace GlobalTheory.ThetaSoSiegel

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hpair co hco`. Take `⟨e, ei, ev, hei, hmaps, hheis, hSB, hvac, hstd, hpure, hbij⟩` from `GlobalTheory.T.darboux_coords_good_model F E σ B n d X W M r s r' s' hpair.base hpair.herm hpair.skew hpair.good co hco`. Set `M₁ : Model σ X W` to `⟨co, fun v => ev v (M.vac v), M.μ, M.dom⟩`. Establish `hM₁ : M₁.IsGood B.ψ` using `⟨hco, hvac, hstd, hpair.good.haar, hpair.good.dom⟩`. Establish `hne : ∃ f : SInf F (Fin n × Fin d), f ≠ 0`.

Assume the negation of the conclusion as `hall`. Use `push_neg at hall`. Take `⟨φ, hφ, hθ⟩` from `GlobalTheory.ThetaSumNe.exists_mem_schA_thetaSum_ne_zero F (Fin n × Fin d)`. Establish `hle : schA F (Fin n × Fin d) ≤ ⊥`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations.

Introduce and unpack `Φ ⟨f, g, -, rfl⟩`. Rewrite using `[hall f]`. Use `show pureA F 0 g = 0`. Use function extensionality and compare the values at `x`. Simplify using `[pureA]`.

Establish `h0 : φ = 0` using `(Submodule.mem_bot ℂ).1 (hle hφ)`. Conclude with `hθ (by rw [h0]; simp [thetaSum])`. Establish `hev : IsEv B M M₁ 1 1 ∅ e`. Use `⟨hmaps, fun z Φ hΦ => ?_, fun u hu => hu.elim, ei, ev, ?_, fun v => ⟨rfl, hSB v⟩, hpure⟩` and prove the remaining obligations. Establish `h1 : incM F (1 : Matrix (Fin n) (Fin n) E) = 1` using `Matrix.map_one _ (map_zero _) (map_one _)`.

Establish `h1' : incM F (1 : Matrix (Fin d) (Fin d) E) = 1` using `Matrix.map_one _ (map_zero _) (map_one _)`. Rewrite using `[h1, h1', Matrix.one_mul, Matrix.transpose_one, Matrix.mul_one]`. Conclude with `hheis z Φ hΦ`. Take `⟨f, hf⟩` from `hne`. Take `⟨g, rfl⟩` from `hei f`.

Introduce `h`. Conclude with `hf (by rw [h]; rfl)`. Take `⟨om₁, hW, hint⟩` from `GlobalTheory.T.weil_eigen_bijective_schwartz F E σ B n d X W M χX χW om r s r' s' hpair M₁ hM₁ e hev hbij`. Take `⟨c₀, hc₀, hth⟩` from `GlobalTheory.T.weil_eigen_schwartz_surjective F E σ B n d X W M χX χW om r s r' s' hpair M₁ hM₁ e hev hbij`. Conclude with `⟨M₁, om₁, e, c₀, rfl, ⟨hpair.base, hpair.herm, hpair.skew, hM₁, hpair.hX, hpair.hW, hpair.resX, hpair.resW, hW⟩, hc₀, fun Φ hΦ => ⟨hmaps Φ hΦ, hth Φ hΦ, fun x => hint x Φ hΦ⟩, hM₁, hev⟩`.
-/
theorem change_ev : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J)) (Fin n × Fin d),
    (∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
        co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
    ∃ (M₁ : Model σ X W) (om₁ : Rep σ X W) (e : Fn F n d →ₗ[ℂ] Fn F n d) (c₀ : ℂ),
      M₁.co = co ∧ IsPair B M₁ χX χW om₁ r s r' s' ∧ c₀ ≠ 0 ∧
      (∀ Φ ∈ schA F (Fin n × Fin d), e Φ ∈ schA F (Fin n × Fin d) ∧ thetaSum F (e Φ) = c₀ * thetaSum F Φ ∧
        ∀ x, e (om x Φ) = om₁ x (e Φ)) ∧ M₁.IsGood B.ψ ∧ IsEv B M M₁ 1 1 ∅ e := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hpair co hco
  obtain ⟨e, ei, ev, hei, hmaps, hheis, hSB, hvac, hstd, hpure, hbij⟩ :=
    GlobalTheory.T.darboux_coords_good_model F E σ B n d X W M r s r' s' hpair.base hpair.herm hpair.skew hpair.good co hco
  let M₁ : Model σ X W := ⟨co, fun v => ev v (M.vac v), M.μ, M.dom⟩
  have hM₁ : M₁.IsGood B.ψ := ⟨hco, hvac, hstd, hpair.good.haar, hpair.good.dom⟩
  have hne : ∃ f : SInf F (Fin n × Fin d), f ≠ 0 := by
    by_contra hall
    push_neg at hall
    obtain ⟨φ, hφ, hθ⟩ := GlobalTheory.ThetaSumNe.exists_mem_schA_thetaSum_ne_zero F (Fin n × Fin d)
    have hle : schA F (Fin n × Fin d) ≤ ⊥ := by
      refine Submodule.span_le.2 ?_
      rintro Φ ⟨f, g, -, rfl⟩
      rw [hall f]
      show pureA F 0 g = 0
      funext x
      simp [pureA]
    have h0 : φ = 0 := (Submodule.mem_bot ℂ).1 (hle hφ)
    exact hθ (by rw [h0]; simp [thetaSum])
  have hev : IsEv B M M₁ 1 1 ∅ e := by
    refine ⟨hmaps, fun z Φ hΦ => ?_, fun u hu => hu.elim, ei, ev, ?_, fun v => ⟨rfl, hSB v⟩, hpure⟩
    · have h1 : incM F (1 : Matrix (Fin n) (Fin n) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
      have h1' : incM F (1 : Matrix (Fin d) (Fin d) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
      rw [h1, h1', Matrix.one_mul, Matrix.transpose_one, Matrix.mul_one]
      exact hheis z Φ hΦ
    · obtain ⟨f, hf⟩ := hne
      obtain ⟨g, rfl⟩ := hei f
      intro h
      exact hf (by rw [h]; rfl)
  obtain ⟨om₁, hW, hint⟩ := GlobalTheory.T.weil_eigen_bijective_schwartz F E σ B n d X W M χX χW om r s r' s' hpair M₁ hM₁ e hev hbij
  obtain ⟨c₀, hc₀, hth⟩ := GlobalTheory.T.weil_eigen_schwartz_surjective F E σ B n d X W M χX χW om r s r' s' hpair M₁ hM₁ e hev hbij
  exact ⟨M₁, om₁, e, c₀, rfl, ⟨hpair.base, hpair.herm, hpair.skew, hM₁, hpair.hX, hpair.hW, hpair.resX, hpair.resW, hW⟩,
    hc₀, fun Φ hΦ => ⟨hmaps Φ hΦ, hth Φ hΦ, fun x => hint x Φ hΦ⟩, hM₁, hev⟩

/- English proof (translation)
Establish `hm0 : (m : F) ≠ 0` using `by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hm)`. Use `set b : 𝓞 F := ⟨(m : F) * ξ, hint⟩ with hb`. Establish `hb0 : b ≠ 0`. Introduce `h`. Establish `h2 : ((b : 𝓞 F) : F) = 0` using `by rw [h]; simp`.

Conclude with `mul_ne_zero hm0 hξ h2`. Establish `key : 1 ≤ ‖mixedEmbedding F (b : F)‖`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Establish `hlt : ∀ z : InfinitePlace F, z (b : F) < 1` using `fun z => by`.

Establish `h1 : mixedEmbedding.normAtPlace z (mixedEmbedding F (b : F)) ≤ ‖mixedEmbedding F (b : F)‖`. Distinguish the cases in `hw : z.IsReal`. Rewrite using `[mixedEmbedding.normAtPlace_apply_of_isReal hw]`. Conclude with `(norm_le_pi_norm _ _).trans (norm_fst_le _)`. Establish `hc' : z.IsComplex` using `InfinitePlace.not_isReal_iff_isComplex.mp hw`.

Rewrite using `[mixedEmbedding.normAtPlace_apply_of_isComplex hc']`. Conclude with `(norm_le_pi_norm _ _).trans (norm_snd_le _)`. Rewrite `h1` using `[mixedEmbedding.normAtPlace_apply]`. Conclude with `h1.trans_lt hc`. Set `w : InfinitePlace F` to `Classical.arbitrary _`.

Use `InfinitePlace.one_le_of_lt_one (w := w) hb0 (fun z _ => hlt z)` as an intermediate fact. Conclude with `absurd (hlt w) (not_lt.mpr this)`. Establish `e1 : (b : F) = (m : F) * ξ` using `rfl`. Rewrite `key` using `[e1, map_mul, map_natCast]`. Rewrite using `[GlobalTheory.LatScaleSum.evI_algebraMap]`.

Combine the equalities or inequalities in the displayed calculation. Conclude with `norm_nsmul_le`.
-/
theorem one_le_mul_norm_evI {F : Type} [Field F] [NumberField F] (m : ℕ) (ξ : F) (hξ : ξ ≠ 0) (hm : 1 ≤ m)
    (hint : IsIntegral ℤ ((m : F) * ξ)) : 1 ≤ (m : ℝ) * ‖evI F (algebraMap F (AF F) ξ)‖ := by
  have hm0 : (m : F) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hm)
  set b : 𝓞 F := ⟨(m : F) * ξ, hint⟩ with hb
  have hb0 : b ≠ 0 := by
    intro h
    have h2 : ((b : 𝓞 F) : F) = 0 := by rw [h]; simp
    exact mul_ne_zero hm0 hξ h2
  have key : 1 ≤ ‖mixedEmbedding F (b : F)‖ := by
    by_contra hc
    push_neg at hc
    have hlt : ∀ z : InfinitePlace F, z (b : F) < 1 := fun z => by
      have h1 : mixedEmbedding.normAtPlace z (mixedEmbedding F (b : F)) ≤ ‖mixedEmbedding F (b : F)‖ := by
        by_cases hw : z.IsReal
        · rw [mixedEmbedding.normAtPlace_apply_of_isReal hw]
          exact (norm_le_pi_norm _ _).trans (norm_fst_le _)
        · have hc' : z.IsComplex := InfinitePlace.not_isReal_iff_isComplex.mp hw
          rw [mixedEmbedding.normAtPlace_apply_of_isComplex hc']
          exact (norm_le_pi_norm _ _).trans (norm_snd_le _)
      rw [mixedEmbedding.normAtPlace_apply] at h1
      exact h1.trans_lt hc
    let w : InfinitePlace F := Classical.arbitrary _
    have := InfinitePlace.one_le_of_lt_one (w := w) hb0 (fun z _ => hlt z)
    exact absurd (hlt w) (not_lt.mpr this)
  have e1 : (b : F) = (m : F) * ξ := rfl
  rw [e1, map_mul, map_natCast] at key
  rw [GlobalTheory.LatScaleSum.evI_algebraMap]
  calc (1 : ℝ) ≤ ‖(m : mixedEmbedding.mixedSpace F) * mixedEmbedding F ξ‖ := key
    _ = ‖(m • mixedEmbedding F ξ : mixedEmbedding.mixedSpace F)‖ := by rw [nsmul_eq_mul]
    _ ≤ (m : ℝ) * ‖mixedEmbedding F ξ‖ := by
        exact norm_nsmul_le

open GlobalTheory.TorusTheta in

/- English proof (translation)
Take `⟨co, blk, hrat, hcard, hact⟩` from `GlobalTheory.T.witt_frame_darboux_coordinates F E σ B n d X W M χX χW om r s r' s' hP r₀ Xf Yf hWitt`. Take `⟨M₁, om₁, e, c₀, hco, hP₁, hc₀, he, hgood, hev⟩` from `change_ev F E σ B n d X W M χX χW om r s r' s' hP co hrat`. Establish `hsup` using `GlobalTheory.T.darboux_witt_frame_pair hKP F E σ B n d X W M χX χW om r s r' s' hP r₀ Xf Yf hWitt co blk hrat hcard hact M₁ e hco hgood hev`. Take `⟨N₀, k₃, C₃, hlat⟩` from `GlobalTheory.LatScaleSum.thetaSum_norm_le_pow F (Fin n × Fin d)`. Use `set K : ℕ := Module.finrank ℚ F * d + L with hKdef`.

Use `set D : ℕ := r₀ * K with hDdef`. Take `⟨k₁, hdec₀⟩` from `GlobalTheory.ThetaUnifSiegel.decay_unif hP₁ (N₀ + D)`. Use `⟨k₁ + D + k₃, fun Φ hΦ hSo => ?_⟩` and prove the remaining obligations. Establish `heΦ` using `(he Φ hΦ).1`. Take `⟨C₁, hdec₁⟩` from `hdec₀ (e Φ) heΦ`.

Establish `hdec : ∀ g h (x : Fin n × Fin d → AF F), ‖om₁ (g, h) (e Φ) x‖ * (1 + ‖fun i => evI F (x i)‖) ^ (N₀ + D) ≤ C₁ * ((ht g : ℝ) * ht h) ^ k₁` using `fun g h x => by`. Use `le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (add_nonneg zero_le_one (norm_nonneg _)) (add_le_add_right ?_ 1) (N₀ + D)) (norm_nonneg _)) (hdec₁ g h x)` and prove the remaining obligations. Conclude with `(pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)).2 fun i => Finset.single_le_sum (f := fun i => ‖evI F (x i)‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ i)`. Take `⟨C₂, hden⟩` from `GlobalTheory.ThetaUnifSiegel.denom_lin hP₁ heΦ`. Use `set c' : ℝ := min 1 c ^ r₀ with hc'def`.

Establish `hc'0 : 0 < c'` using `pow_pos (lt_min one_pos hc) _`. Establish `hc'1 : c' ≤ 1` using `pow_le_one₀ (lt_min one_pos hc).le (min_le_left _ _)`. Use `set π₀ : ℝ := c' ^ r₀ with hπ₀def`. Establish `hπ₀ : 0 < π₀` using `pow_pos hc'0 _`. Use `⟨‖c₀‖⁻¹ * |C₃| * (c'⁻¹) ^ N₀ * |C₁| * (π₀⁻¹ + 1) ^ L * |C₂| ^ (D + k₃), ?_⟩` and prove the remaining obligations.

Introduce `t htc a hta a' ha' y h`. Establish `tlow : ∀ i, c' ≤ t i` using `GlobalTheory.ThetaUnifSiegel.min_pow_le_of_mem_cone hc htc`. Establish `tpos : ∀ i, 0 < t i` using `fun i => hc'0.trans_le (tlow i)`. Use `set u : Fin n × Fin d → ℝ := fun j => (blk j).elim 1 t with hudef`. Establish `hulow : ∀ j, c' ≤ u j`.

Introduce `j`. Simplify using `only [hudef]`. Consider the cases of `blk j with`. Consider the case `none => exact hc'1`. Consider the case `some i => exact tlow i`.

Establish `hupos : ∀ j, 0 < u j` using `fun j => hc'0.trans_le (hulow j)`. Take `⟨κ, hκ, hom⟩` from `GlobalTheory.T.torus_action_model_coordinates F E σ B n d X W M₁ χX χW om₁ r s r' s' hP₁ a' u hupos (by rw [hco]; exact hact t tpos a hta a' ha')`. Establish `hΨ0 : om (y, h) Φ ∈ schA F (Fin n × Fin d)` using `(IsUWeilPair.isUSplitting hP.weil).pres _ _ hΦ`. Establish `hT : om (a', 1) (om (y, h) Φ) ∈ schA F (Fin n × Fin d)` using `(IsUWeilPair.isUSplitting hP.weil).pres _ _ hΨ0`. Take `⟨Ψ, hΨdef⟩ : ∃ Ψ, Ψ = om₁ (y, h) (e Φ)` from `⟨_, rfl⟩`.

Establish `hΨ : Ψ ∈ schA F (Fin n × Fin d)` using `hΨdef ▸ (IsUWeilPair.isUSplitting hP₁.weil).pres _ _ heΦ`. Establish `hmul : ((a' * y, h) : UA σ X.J × UA σ W.J) = (a', 1) * (y, h)`. Apply the tactic sequence `ext <;> simp`. Establish `hsplit : om (a' * y, h) Φ = om (a', 1) (om (y, h) Φ)`. Rewrite using `[hmul, map_mul, Module.End.mul_apply]`.

Establish `heT : e (om (a', 1) (om (y, h) Φ)) = om₁ (a', 1) Ψ`. Rewrite using `[(he _ hΨ0).2.2, (he Φ hΦ).2.2, hΨdef]`. Establish `hthT : thetaSum F (om (a', 1) (om (y, h) Φ)) = c₀⁻¹ * thetaSum F (om₁ (a', 1) Ψ)`. Rewrite using `[← heT, (he _ hT).2.1, ← mul_assoc, inv_mul_cancel₀ hc₀, one_mul]`. Establish `hfun : om₁ (a', 1) Ψ = fun x => κ * Ψ (fun j => infScale F (u j) * x j)` using `funext (hom Ψ hΨ)`.

Establish `hkey : theta om Φ (a' * y) h = c₀⁻¹ * (κ * thetaSum F (fun x => Ψ (fun j => infScale F (u j) * x j)))` using `by show thetaSum F (om (a' * y, h) Φ) = _`. Rewrite using `[hsplit, hthT, hfun]`. Unfold `thetaSum`. Rewrite using `[tsum_mul_left]`. Use `set T : ℝ := ∏ i, t i with hTdef`.

Establish `hT0 : 0 < T` using `Finset.prod_pos fun i _ => tpos i`. Establish `hκ' : ‖κ‖ = T ^ (Module.finrank ℚ F * d)`. Establish `h2 : ‖κ‖ ^ 2 = (∏ i, t i ^ (Module.finrank ℚ F * d)) ^ 2`. Rewrite using `[hκ]`. Conclude with `GlobalTheory.ThetaUnifSiegel.prod_elim_pow blk t _ d hcard`.

Establish `hnn : 0 ≤ ∏ i, t i ^ (Module.finrank ℚ F * d)` using `Finset.prod_nonneg fun i _ => pow_nonneg (tpos i).le _`. Rewrite using `[hTdef, ← Finset.prod_pow]`. Conclude with `(pow_left_inj₀ (norm_nonneg _) hnn two_ne_zero).1 h2`. Establish `hκ0 : κ ≠ 0`. Introduce `h0`.

Rewrite `hκ'` using `[h0, norm_zero]`. Conclude with `(pow_pos hT0 _).ne' hκ'.symm`. Use `set P : ℝ := (ht y : ℝ) * ht h with hPdef`. Establish `hP0 : 0 ≤ P` using `mul_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)`. Take `⟨m, hm1, hmC, hmint⟩` from `hden y h`.

Establish `hm0 : (0 : ℝ) ≤ m` using `Nat.cast_nonneg m`. Establish `hmR : (1 : ℝ) ≤ m` using `by exact_mod_cast hm1`. Establish `hC₁P : 0 ≤ C₁ * P ^ k₁` using `le_trans (by positivity) (hdec y h 0)`. Use `set A : ℝ := (c'⁻¹) ^ N₀ * (|C₁| * P ^ k₁) * (m : ℝ) ^ D * (T ^ K)⁻¹ with hAdef`. Establish `hA0 : 0 ≤ A` using `by positivity`.

Establish `hdecay : ∀ ξ : Fin n × Fin d → F, ‖Ψ (fun j => infScale F (u j) * (fun i => algebraMap F (AF F) (ξ i)) j)‖ * (1 + ‖fun i => evI F (algebraMap F (AF F) (ξ i))‖) ^ N₀ ≤ A`. Introduce `ξ`. Use `beta_reduce`. Distinguish the cases in `hz : Ψ (fun j => infScale F (u j) * algebraMap F (AF F) (ξ j)) = 0`. Rewrite using `[hz, norm_zero, zero_mul]`.

Conclude with `hA0`. Establish `hblk : ∀ i : Fin r₀, ∃ j, blk j = some i ∧ ξ j ≠ 0`. Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Take `⟨i, hi⟩` from `hne`.

Establish `h0` using `hsup Φ hΦ hSo (a' * y) h ξ ⟨i, hi⟩`. Rewrite `h0` using `[hsplit, heT, hfun]`. Conclude with `hz ((mul_eq_zero.1 h0).resolve_left hκ0)`. Use `set s0 : ℝ := ‖fun i => evI F (infScale F (u i) * algebraMap F (AF F) (ξ i))‖ with hs0`. Establish `hs00 : 0 ≤ s0` using `norm_nonneg _`.

Establish `h1` using `hdec y h (fun j => infScale F (u j) * algebraMap F (AF F) (ξ j))`. Rewrite `h1` using `[← hΨdef]`. Establish `hti : ∀ i, t i ≤ m * (1 + s0)`. Introduce `i`. Take `⟨j, hj, hξj⟩` from `hblk i`.

Establish `hint` using `hmint _ ξ (fun i => infScale_mul_snd F (u i) _) (by rw [hΨdef] at hz; exact hz) j`. Establish `h1le` using `one_le_mul_norm_evI m (ξ j) hξj hm1 hint`. Establish `huj : u j = t i` using `by simp only [hudef, hj, Option.elim_some]`. Establish `hsj : t i * ‖evI F (algebraMap F (AF F) (ξ j))‖ ≤ s0`. Use `norm_le_pi_norm (fun i => evI F (infScale F (u i) * algebraMap F (AF F) (ξ i))) j` as an intermediate fact.

Rewrite `this` using `[evI_infScale_mul, norm_smul, Real.norm_of_nonneg (hupos j).le, huj]`. Conclude with `this`. Use polynomial arithmetic with `[tpos i, norm_nonneg (evI F (algebraMap F (AF F) (ξ j)))]`. Establish `hTK : T ^ K ≤ (m : ℝ) ^ D * (1 + s0) ^ D`. Establish `hTle : T ≤ ((m : ℝ) * (1 + s0)) ^ r₀`.

Rewrite using `[hTdef]`. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation. Establish `hnorm : c' * ‖fun i => evI F (algebraMap F (AF F) (ξ i))‖ ≤ s0`. Simplify using `only [hs0, evI_infScale_mul]`.

Conclude with `GlobalTheory.ThetaUnifSiegel.mul_norm_le_norm_smul hc'0 u hulow _`. Establish `hpow : (1 + ‖fun i => evI F (algebraMap F (AF F) (ξ i))‖) ^ N₀ ≤ (c'⁻¹) ^ N₀ * (1 + s0) ^ N₀`. Establish `hi : 1 ≤ c'⁻¹` using `one_le_inv₀ hc'0 |>.2 hc'1`. Establish `h3 : ‖fun i => evI F (algebraMap F (AF F) (ξ i))‖ ≤ c'⁻¹ * s0`. Rewrite using `[le_inv_mul_iff₀ hc'0]`.

Conclude with `hnorm`. Establish `hle : 1 + ‖fun i => evI F (algebraMap F (AF F) (ξ i))‖ ≤ c'⁻¹ * (1 + s0)` using `by nlinarith`. Establish `h4` using `pow_le_pow_left₀ (add_nonneg zero_le_one (norm_nonneg _)) hle N₀`. Rewrite `h4` using `[mul_pow]`. Then use the resulting hypothesis. Use `set v : ℝ := ‖Ψ (fun j => infScale F (u j) * algebraMap F (AF F) (ξ j))‖ with hv`.

Establish `hv0 : 0 ≤ v` using `norm_nonneg _`. Establish `hmain : v * (1 + s0) ^ N₀ * T ^ K ≤ (m : ℝ) ^ D * (|C₁| * P ^ k₁)`. Combine the equalities or inequalities in the displayed calculation. Use `mul_le_mul_of_nonneg_left (h1.trans ?_) (by positivity)` and prove the remaining obligations. Conclude with `mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg hP0 _)`.

Establish `hTK0 : 0 < T ^ K` using `pow_pos hT0 _`. Combine the equalities or inequalities in the displayed calculation. Clear the denominators using the available nonvanishing facts. Use `_ ≤ (c'⁻¹) ^ N₀ * ((m : ℝ) ^ D * (|C₁| * P ^ k₁)) * (T ^ K)⁻¹ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmain (by positivity)) (inv_nonneg.2 hTK0.le)`. Use `_ = A := by rw [hAdef]; ring`.

Establish `hint : ∀ ξ : Fin n × Fin d → F, Ψ (fun j => infScale F (u j) * (fun i => algebraMap F (AF F) (ξ i)) j) ≠ 0 → ∀ i, IsIntegral ℤ ((m : F) * ξ i)`. Introduce `ξ hne`. Rewrite `hne` using `[hΨdef]`. Conclude with `hmint _ ξ (fun i => infScale_mul_snd F (u i) _) hne`. Establish `hS` using `hlat A m (fun x => Ψ (fun j => infScale F (u j) * x j)) hm1 hdecay hint`.

Use `set Q : ℝ := ‖thetaSum F (fun x => Ψ (fun j => infScale F (u j) * x j))‖ with hQ`. Establish `hQ' : Q ≤ |C₃| * A * (m : ℝ) ^ k₃` using `hS.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hA0) (pow_nonneg hm0 _))`. Establish `h1T : (1 + T) ^ L ≤ (π₀⁻¹ + 1) ^ L * T ^ L`. Establish `hπT : π₀ ≤ T`. Rewrite using `[hπ₀def, hTdef]`.

Combine the equalities or inequalities in the displayed calculation. Establish `h1 : 1 ≤ π₀⁻¹ * T` using `by rw [le_inv_mul_iff₀ hπ₀, mul_one]; exact hπT`. Rewrite using `[← mul_pow]`. Conclude with `pow_le_pow_left₀ (by positivity) (by nlinarith) L`. Establish `hmk : (m : ℝ) ^ (D + k₃) ≤ |C₂| ^ (D + k₃) * P ^ (D + k₃)`.

Rewrite using `[← mul_pow]`. Conclude with `pow_le_pow_left₀ hm0 (hmC.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hP0)) _`. Establish `hTcancel : T ^ (Module.finrank ℚ F * d) * T ^ L * (T ^ K)⁻¹ = 1`. Rewrite using `[← pow_add, hKdef, mul_inv_cancel₀ (pow_pos hT0 _).ne']`. Rewrite using `[hkey, norm_mul, norm_mul, norm_inv, hκ', ← hQ]`.

Combine the equalities or inequalities in the displayed calculation. Establish `hTf : 0 ≤ T ^ (Module.finrank ℚ F * d)` using `pow_nonneg hT0.le _`. Establish `hc0' : 0 ≤ ‖c₀‖⁻¹` using `inv_nonneg.2 (norm_nonneg _)`. Conclude with `mul_le_mul (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hQ' hTf) hc0') h1T (pow_nonneg (by linarith) _) (mul_nonneg hc0' (mul_nonneg hTf (mul_nonneg (mul_nonneg (abs_nonneg _) hA0) (pow_nonneg hm0 _))))`. Use `_ = ‖c₀‖⁻¹ * |C₃| * (c'⁻¹) ^ N₀ * |C₁| * (π₀⁻¹ + 1) ^ L * P ^ k₁ * (m : ℝ) ^ (D + k₃) * (T ^ (Module.finrank ℚ F * d) * T ^ L * (T ^ K)⁻¹) := by`.

Rewrite using `[hAdef, pow_add]`. Expand and normalize the polynomial expressions, which then agree. Use `_ = ‖c₀‖⁻¹ * |C₃| * (c'⁻¹) ^ N₀ * |C₁| * (π₀⁻¹ + 1) ^ L * P ^ k₁ * (m : ℝ) ^ (D + k₃) := by`. Rewrite using `[hTcancel, mul_one]`. Use `_ ≤ ‖c₀‖⁻¹ * |C₃| * (c'⁻¹) ^ N₀ * |C₁| * (π₀⁻¹ + 1) ^ L * P ^ k₁ * (|C₂| ^ (D + k₃) * P ^ (D + k₃)) := by`.

Conclude with `mul_le_mul_of_nonneg_left hmk (by positivity)`. Use `_ = _ := by rw [show k₁ + D + k₃ = k₁ + (D + k₃) by ring, pow_add]; ring`.
-/
theorem theta_torus_decay (hKP : GlobalTheory.ThK.KP) {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {σ : E →ₐ[F] E} {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W}
    {χX χW : Chr F E} {om : Rep σ X W} {r s r' s' : ℕ} (hP : IsPair B M χX χW om r s r' s') {r₀ : ℕ}
    {Xf Yf : Matrix (Fin n) (Fin r₀) E} (hWitt : GlobalTheory.SiegelSet.IsWittFrame σ ((1 : E) • X.J.map σ) Xf Yf)
    {c : ℝ} (hc : 0 < c) (L : ℕ) :
    ∃ k : ℕ, ∀ Φ ∈ schA F (Fin n × Fin d), Φ ∈ M.So B.ψ B.τ₁ → ∃ C : ℝ, ∀ t ∈ GlobalTheory.SiegelSet.cone r₀ c, ∀ a,
      GlobalTheory.SiegelSet.IsTorusElt σ ((1 : E) • X.J.map σ) Xf Yf t a → ∀ a' : UA σ X.J,
      (a' : GL (Fin n) (AE F E)) = HA.mat (AF F) σ ((1 : E) • X.J.map σ) a → ∀ (y : UA σ X.J) (h : UA σ W.J),
      ‖theta om Φ (a' * y) h‖ * (1 + ∏ i, t i) ^ L ≤ C * ((ht y : ℝ) * ht h) ^ k := by
  obtain ⟨co, blk, hrat, hcard, hact⟩ := GlobalTheory.T.witt_frame_darboux_coordinates F E σ B n d X W M χX χW om r s r' s' hP r₀ Xf Yf hWitt
  obtain ⟨M₁, om₁, e, c₀, hco, hP₁, hc₀, he, hgood, hev⟩ := change_ev F E σ B n d X W M χX χW om r s r' s' hP co hrat
  have hsup := GlobalTheory.T.darboux_witt_frame_pair hKP F E σ B n d X W M χX χW om r s r' s' hP r₀ Xf Yf hWitt co blk hrat hcard hact M₁ e hco
    hgood hev
  obtain ⟨N₀, k₃, C₃, hlat⟩ := GlobalTheory.LatScaleSum.thetaSum_norm_le_pow F (Fin n × Fin d)
  set K : ℕ := Module.finrank ℚ F * d + L with hKdef
  set D : ℕ := r₀ * K with hDdef
  obtain ⟨k₁, hdec₀⟩ := GlobalTheory.ThetaUnifSiegel.decay_unif hP₁ (N₀ + D)
  refine ⟨k₁ + D + k₃, fun Φ hΦ hSo => ?_⟩
  have heΦ := (he Φ hΦ).1
  obtain ⟨C₁, hdec₁⟩ := hdec₀ (e Φ) heΦ
  have hdec : ∀ g h (x : Fin n × Fin d → AF F), ‖om₁ (g, h) (e Φ) x‖ * (1 + ‖fun i => evI F (x i)‖) ^ (N₀ + D) ≤
      C₁ * ((ht g : ℝ) * ht h) ^ k₁ := fun g h x => by
    refine le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (add_nonneg zero_le_one (norm_nonneg _))
      (add_le_add_right ?_ 1) (N₀ + D)) (norm_nonneg _)) (hdec₁ g h x)
    exact (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)).2 fun i =>
      Finset.single_le_sum (f := fun i => ‖evI F (x i)‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ i)
  obtain ⟨C₂, hden⟩ := GlobalTheory.ThetaUnifSiegel.denom_lin hP₁ heΦ
  set c' : ℝ := min 1 c ^ r₀ with hc'def
  have hc'0 : 0 < c' := pow_pos (lt_min one_pos hc) _
  have hc'1 : c' ≤ 1 := pow_le_one₀ (lt_min one_pos hc).le (min_le_left _ _)
  set π₀ : ℝ := c' ^ r₀ with hπ₀def
  have hπ₀ : 0 < π₀ := pow_pos hc'0 _
  refine ⟨‖c₀‖⁻¹ * |C₃| * (c'⁻¹) ^ N₀ * |C₁| * (π₀⁻¹ + 1) ^ L * |C₂| ^ (D + k₃), ?_⟩
  intro t htc a hta a' ha' y h
  have tlow : ∀ i, c' ≤ t i := GlobalTheory.ThetaUnifSiegel.min_pow_le_of_mem_cone hc htc
  have tpos : ∀ i, 0 < t i := fun i => hc'0.trans_le (tlow i)
  set u : Fin n × Fin d → ℝ := fun j => (blk j).elim 1 t with hudef
  have hulow : ∀ j, c' ≤ u j := by
    intro j
    simp only [hudef]
    cases blk j with
    | none => exact hc'1
    | some i => exact tlow i
  have hupos : ∀ j, 0 < u j := fun j => hc'0.trans_le (hulow j)
  obtain ⟨κ, hκ, hom⟩ := GlobalTheory.T.torus_action_model_coordinates F E σ B n d X W M₁ χX χW om₁ r s r' s' hP₁ a' u hupos
    (by rw [hco]; exact hact t tpos a hta a' ha')
  have hΨ0 : om (y, h) Φ ∈ schA F (Fin n × Fin d) := (IsUWeilPair.isUSplitting hP.weil).pres _ _ hΦ
  have hT : om (a', 1) (om (y, h) Φ) ∈ schA F (Fin n × Fin d) := (IsUWeilPair.isUSplitting hP.weil).pres _ _ hΨ0
  obtain ⟨Ψ, hΨdef⟩ : ∃ Ψ, Ψ = om₁ (y, h) (e Φ) := ⟨_, rfl⟩
  have hΨ : Ψ ∈ schA F (Fin n × Fin d) := hΨdef ▸ (IsUWeilPair.isUSplitting hP₁.weil).pres _ _ heΦ
  have hmul : ((a' * y, h) : UA σ X.J × UA σ W.J) = (a', 1) * (y, h) := by
    ext <;> simp
  have hsplit : om (a' * y, h) Φ = om (a', 1) (om (y, h) Φ) := by
    rw [hmul, map_mul, Module.End.mul_apply]
  have heT : e (om (a', 1) (om (y, h) Φ)) = om₁ (a', 1) Ψ := by
    rw [(he _ hΨ0).2.2, (he Φ hΦ).2.2, hΨdef]
  have hthT : thetaSum F (om (a', 1) (om (y, h) Φ)) = c₀⁻¹ * thetaSum F (om₁ (a', 1) Ψ) := by
    rw [← heT, (he _ hT).2.1, ← mul_assoc, inv_mul_cancel₀ hc₀, one_mul]
  have hfun : om₁ (a', 1) Ψ = fun x => κ * Ψ (fun j => infScale F (u j) * x j) := funext (hom Ψ hΨ)
  have hkey : theta om Φ (a' * y) h =
      c₀⁻¹ * (κ * thetaSum F (fun x => Ψ (fun j => infScale F (u j) * x j))) := by
    show thetaSum F (om (a' * y, h) Φ) = _
    rw [hsplit, hthT, hfun]
    unfold thetaSum
    rw [tsum_mul_left]
  set T : ℝ := ∏ i, t i with hTdef
  have hT0 : 0 < T := Finset.prod_pos fun i _ => tpos i
  have hκ' : ‖κ‖ = T ^ (Module.finrank ℚ F * d) := by
    have h2 : ‖κ‖ ^ 2 = (∏ i, t i ^ (Module.finrank ℚ F * d)) ^ 2 := by
      rw [hκ]
      exact GlobalTheory.ThetaUnifSiegel.prod_elim_pow blk t _ d hcard
    have hnn : 0 ≤ ∏ i, t i ^ (Module.finrank ℚ F * d) :=
      Finset.prod_nonneg fun i _ => pow_nonneg (tpos i).le _
    rw [hTdef, ← Finset.prod_pow]
    exact (pow_left_inj₀ (norm_nonneg _) hnn two_ne_zero).1 h2
  have hκ0 : κ ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hκ'
    exact (pow_pos hT0 _).ne' hκ'.symm

  set P : ℝ := (ht y : ℝ) * ht h with hPdef
  have hP0 : 0 ≤ P := mul_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)
  obtain ⟨m, hm1, hmC, hmint⟩ := hden y h
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hC₁P : 0 ≤ C₁ * P ^ k₁ := le_trans (by positivity) (hdec y h 0)
  set A : ℝ := (c'⁻¹) ^ N₀ * (|C₁| * P ^ k₁) * (m : ℝ) ^ D * (T ^ K)⁻¹ with hAdef
  have hA0 : 0 ≤ A := by positivity
  have hdecay : ∀ ξ : Fin n × Fin d → F,
      ‖Ψ (fun j => infScale F (u j) * (fun i => algebraMap F (AF F) (ξ i)) j)‖ *
        (1 + ‖fun i => evI F (algebraMap F (AF F) (ξ i))‖) ^ N₀ ≤ A := by
    intro ξ
    beta_reduce
    by_cases hz : Ψ (fun j => infScale F (u j) * algebraMap F (AF F) (ξ j)) = 0
    · rw [hz, norm_zero, zero_mul]; exact hA0

    have hblk : ∀ i : Fin r₀, ∃ j, blk j = some i ∧ ξ j ≠ 0 := by
      by_contra hne
      push_neg at hne
      obtain ⟨i, hi⟩ := hne
      have h0 := hsup Φ hΦ hSo (a' * y) h ξ ⟨i, hi⟩
      rw [hsplit, heT, hfun] at h0
      exact hz ((mul_eq_zero.1 h0).resolve_left hκ0)
    set s0 : ℝ := ‖fun i => evI F (infScale F (u i) * algebraMap F (AF F) (ξ i))‖ with hs0
    have hs00 : 0 ≤ s0 := norm_nonneg _
    have h1 := hdec y h (fun j => infScale F (u j) * algebraMap F (AF F) (ξ j))
    rw [← hΨdef] at h1

    have hti : ∀ i, t i ≤ m * (1 + s0) := by
      intro i
      obtain ⟨j, hj, hξj⟩ := hblk i
      have hint := hmint _ ξ (fun i => infScale_mul_snd F (u i) _) (by rw [hΨdef] at hz; exact hz) j
      have h1le := one_le_mul_norm_evI m (ξ j) hξj hm1 hint
      have huj : u j = t i := by simp only [hudef, hj, Option.elim_some]
      have hsj : t i * ‖evI F (algebraMap F (AF F) (ξ j))‖ ≤ s0 := by
        have := norm_le_pi_norm (fun i => evI F (infScale F (u i) * algebraMap F (AF F) (ξ i))) j
        rw [evI_infScale_mul, norm_smul, Real.norm_of_nonneg (hupos j).le, huj] at this
        exact this
      nlinarith [tpos i, norm_nonneg (evI F (algebraMap F (AF F) (ξ j)))]
    have hTK : T ^ K ≤ (m : ℝ) ^ D * (1 + s0) ^ D := by
      have hTle : T ≤ ((m : ℝ) * (1 + s0)) ^ r₀ := by
        rw [hTdef]
        calc ∏ i, t i ≤ ∏ _i : Fin r₀, ((m : ℝ) * (1 + s0)) :=
              Finset.prod_le_prod (fun i _ => (tpos i).le) (fun i _ => hti i)
          _ = _ := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      calc T ^ K ≤ (((m : ℝ) * (1 + s0)) ^ r₀) ^ K := pow_le_pow_left₀ hT0.le hTle K
        _ = (m : ℝ) ^ D * (1 + s0) ^ D := by rw [← pow_mul, mul_pow, hDdef]
    have hnorm : c' * ‖fun i => evI F (algebraMap F (AF F) (ξ i))‖ ≤ s0 := by
      simp only [hs0, evI_infScale_mul]
      exact GlobalTheory.ThetaUnifSiegel.mul_norm_le_norm_smul hc'0 u hulow _
    have hpow : (1 + ‖fun i => evI F (algebraMap F (AF F) (ξ i))‖) ^ N₀ ≤ (c'⁻¹) ^ N₀ * (1 + s0) ^ N₀ := by
      have hi : 1 ≤ c'⁻¹ := one_le_inv₀ hc'0 |>.2 hc'1
      have h3 : ‖fun i => evI F (algebraMap F (AF F) (ξ i))‖ ≤ c'⁻¹ * s0 := by
        rw [le_inv_mul_iff₀ hc'0]; exact hnorm
      have hle : 1 + ‖fun i => evI F (algebraMap F (AF F) (ξ i))‖ ≤ c'⁻¹ * (1 + s0) := by nlinarith
      have h4 := pow_le_pow_left₀ (add_nonneg zero_le_one (norm_nonneg _)) hle N₀
      rwa [mul_pow] at h4
    set v : ℝ := ‖Ψ (fun j => infScale F (u j) * algebraMap F (AF F) (ξ j))‖ with hv
    have hv0 : 0 ≤ v := norm_nonneg _

    have hmain : v * (1 + s0) ^ N₀ * T ^ K ≤ (m : ℝ) ^ D * (|C₁| * P ^ k₁) := by
      calc v * (1 + s0) ^ N₀ * T ^ K ≤ v * (1 + s0) ^ N₀ * ((m : ℝ) ^ D * (1 + s0) ^ D) :=
            mul_le_mul_of_nonneg_left hTK (by positivity)
        _ = (m : ℝ) ^ D * (v * (1 + s0) ^ (N₀ + D)) := by rw [pow_add]; ring
        _ ≤ (m : ℝ) ^ D * (|C₁| * P ^ k₁) := by
            refine mul_le_mul_of_nonneg_left (h1.trans ?_) (by positivity)
            exact mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg hP0 _)
    have hTK0 : 0 < T ^ K := pow_pos hT0 _
    calc v * (1 + ‖fun i => evI F (algebraMap F (AF F) (ξ i))‖) ^ N₀
        ≤ v * ((c'⁻¹) ^ N₀ * (1 + s0) ^ N₀) := mul_le_mul_of_nonneg_left hpow hv0
      _ = (c'⁻¹) ^ N₀ * (v * (1 + s0) ^ N₀ * T ^ K) * (T ^ K)⁻¹ := by
          field_simp
      _ ≤ (c'⁻¹) ^ N₀ * ((m : ℝ) ^ D * (|C₁| * P ^ k₁)) * (T ^ K)⁻¹ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmain (by positivity)) (inv_nonneg.2 hTK0.le)
      _ = A := by rw [hAdef]; ring
  have hint : ∀ ξ : Fin n × Fin d → F,
      Ψ (fun j => infScale F (u j) * (fun i => algebraMap F (AF F) (ξ i)) j) ≠ 0 →
        ∀ i, IsIntegral ℤ ((m : F) * ξ i) := by
    intro ξ hne
    rw [hΨdef] at hne
    exact hmint _ ξ (fun i => infScale_mul_snd F (u i) _) hne
  have hS := hlat A m (fun x => Ψ (fun j => infScale F (u j) * x j)) hm1 hdecay hint

  set Q : ℝ := ‖thetaSum F (fun x => Ψ (fun j => infScale F (u j) * x j))‖ with hQ
  have hQ' : Q ≤ |C₃| * A * (m : ℝ) ^ k₃ :=
    hS.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hA0) (pow_nonneg hm0 _))
  have h1T : (1 + T) ^ L ≤ (π₀⁻¹ + 1) ^ L * T ^ L := by
    have hπT : π₀ ≤ T := by
      rw [hπ₀def, hTdef]
      calc c' ^ r₀ = ∏ _i : Fin r₀, c' := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        _ ≤ ∏ i, t i := Finset.prod_le_prod (fun _ _ => hc'0.le) (fun i _ => tlow i)
    have h1 : 1 ≤ π₀⁻¹ * T := by rw [le_inv_mul_iff₀ hπ₀, mul_one]; exact hπT
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by nlinarith) L
  have hmk : (m : ℝ) ^ (D + k₃) ≤ |C₂| ^ (D + k₃) * P ^ (D + k₃) := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hm0 (hmC.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hP0)) _
  have hTcancel : T ^ (Module.finrank ℚ F * d) * T ^ L * (T ^ K)⁻¹ = 1 := by
    rw [← pow_add, hKdef, mul_inv_cancel₀ (pow_pos hT0 _).ne']
  rw [hkey, norm_mul, norm_mul, norm_inv, hκ', ← hQ]
  calc ‖c₀‖⁻¹ * (T ^ (Module.finrank ℚ F * d) * Q) * (1 + T) ^ L
      ≤ ‖c₀‖⁻¹ * (T ^ (Module.finrank ℚ F * d) * (|C₃| * A * (m : ℝ) ^ k₃)) * ((π₀⁻¹ + 1) ^ L * T ^ L) := by
        have hTf : 0 ≤ T ^ (Module.finrank ℚ F * d) := pow_nonneg hT0.le _
        have hc0' : 0 ≤ ‖c₀‖⁻¹ := inv_nonneg.2 (norm_nonneg _)
        exact mul_le_mul (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hQ' hTf) hc0') h1T
          (pow_nonneg (by linarith) _)
          (mul_nonneg hc0' (mul_nonneg hTf (mul_nonneg (mul_nonneg (abs_nonneg _) hA0) (pow_nonneg hm0 _))))
    _ = ‖c₀‖⁻¹ * |C₃| * (c'⁻¹) ^ N₀ * |C₁| * (π₀⁻¹ + 1) ^ L * P ^ k₁ * (m : ℝ) ^ (D + k₃) *
          (T ^ (Module.finrank ℚ F * d) * T ^ L * (T ^ K)⁻¹) := by
        rw [hAdef, pow_add]; ring
    _ = ‖c₀‖⁻¹ * |C₃| * (c'⁻¹) ^ N₀ * |C₁| * (π₀⁻¹ + 1) ^ L * P ^ k₁ * (m : ℝ) ^ (D + k₃) := by
        rw [hTcancel, mul_one]
    _ ≤ ‖c₀‖⁻¹ * |C₃| * (c'⁻¹) ^ N₀ * |C₁| * (π₀⁻¹ + 1) ^ L * P ^ k₁ * (|C₂| ^ (D + k₃) * P ^ (D + k₃)) := by
        exact mul_le_mul_of_nonneg_left hmk (by positivity)
    _ = _ := by rw [show k₁ + D + k₃ = k₁ + (D + k₃) by ring, pow_add]; ring

/- English proof (translation)
Introduce `hKP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP r₀ Xf Yf hfr Ω C₀ K c hΩ hC₀ hK hc hconj hσ e he Cf _ L`. Take `⟨Bd, hBd⟩` from `GlobalTheory.ThetaUnifSiegel.ht_bdd ((1 : E) • X.J.map σ) hC₀ hK`. Take `⟨k₁, hk₁⟩` from `theta_torus_decay hKP hP hfr hc L`. Use `⟨k₁, fun Φ hΦ hSo => ?_⟩` and prove the remaining obligations. Take `⟨C₁, h₁⟩` from `hk₁ Φ hΦ hSo`.

Use `⟨|C₁| * (max Bd 0) ^ k₁, fun h g _ p hp t htc a ha k hk hg => ?_⟩` and prove the remaining obligations. Take `⟨a', ha'⟩` from `GlobalTheory.ThetaUnifSiegel.transp hσ X.J a`. Establish `hy : ((a'⁻¹ * g : UA σ X.J) : GL (Fin n) (AE F E)) = HA.mat (AF F) σ ((1 : E) • X.J.map σ) ((a⁻¹ * p * a) * k)`. Establish `: (a⁻¹ * p * a) * k = a⁻¹ * (p * a * k)` using `by group`. Rewrite using `[this]`.

Express the relevant statement in the definitionally equal form `(a' : GL (Fin n) (AE F E))⁻¹ * (g : GL (Fin n) (AE F E)) = _`. Rewrite using `[ha', hg]`. Both sides reduce to the same expression. Establish `hty : (ht (a'⁻¹ * g) : ℝ) ≤ max Bd 0`. Use `le_trans ?_ (le_max_left _ _)` and prove the remaining obligations.

Use `show (heightGL F ((a'⁻¹ * g : UA σ X.J) : GL (Fin n) (AE F E)) : ℝ) ≤ Bd`. Rewrite using `[hy]`. Conclude with `hBd _ (hconj p hp t htc a ha) k hk`. Establish `hb` using `h₁ t htc a ha a' ha' (a'⁻¹ * g) h`. Rewrite `hb` using `[mul_inv_cancel_left]`.

Establish `h0 : (0 : ℝ) ≤ (ht h : ℝ)` using `NNReal.coe_nonneg _`. Establish `hy0 : (0 : ℝ) ≤ (ht (a'⁻¹ * g) : ℝ)` using `NNReal.coe_nonneg _`. Use `hb.trans ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem theta_decay_height_pow : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ (r₀ : ℕ) (Xf Yf : Matrix (Fin n) (Fin r₀) E),
    GlobalTheory.SiegelSet.IsWittFrame σ ((1 : E) • X.J.map σ) Xf Yf →
    ∀ (Ω C₀ : Set (GAd σ ((1 : E) • X.J.map σ))) (K : Subgroup (GAd σ ((1 : E) • X.J.map σ))) (c : ℝ),
      IsCompact Ω → IsCompact C₀ → IsCompact (K : Set (GAd σ ((1 : E) • X.J.map σ))) → 0 < c →
      (∀ p ∈ Ω, ∀ t ∈ GlobalTheory.SiegelSet.cone r₀ c, ∀ a, GlobalTheory.SiegelSet.IsTorusElt σ ((1 : E) • X.J.map σ) Xf Yf t a →
        a⁻¹ * p * a ∈ C₀) →
      ∀ (hσ : ∀ x, σ (σ x) = x) (e : E) (he : e ≠ 0) (Cf : Set (GFin σ (e • W.J.map σ))), IsCompact Cf →
      ∀ L : ℕ, ∃ N : ℕ, ∀ Φ ∈ schA F (Fin n × Fin d), Φ ∈ M.So B.ψ B.τ₁ → ∃ C : ℝ,
        ∀ (h : UA σ W.J) (g : UA σ X.J), projFin σ (e • W.J.map σ) (GlobalTheory.ThK.SquareIntegrability.toGAd hσ W.J he h) ∈ Cf →
        ∀ p ∈ Ω, ∀ t ∈ GlobalTheory.SiegelSet.cone r₀ c, ∀ a, GlobalTheory.SiegelSet.IsTorusElt σ ((1 : E) • X.J.map σ) Xf Yf t a →
        ∀ k ∈ K, g.1 = HA.mat (AF F) σ ((1 : E) • X.J.map σ) (p * a * k) →
          ‖theta om Φ g h‖ * (1 + ∏ i, t i) ^ L ≤ C * (ht h : ℝ) ^ N := by
  intro hKP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP r₀ Xf Yf hfr Ω C₀ K c hΩ hC₀ hK hc hconj hσ e he Cf _ L
  obtain ⟨Bd, hBd⟩ := GlobalTheory.ThetaUnifSiegel.ht_bdd ((1 : E) • X.J.map σ) hC₀ hK
  obtain ⟨k₁, hk₁⟩ := theta_torus_decay hKP hP hfr hc L
  refine ⟨k₁, fun Φ hΦ hSo => ?_⟩
  obtain ⟨C₁, h₁⟩ := hk₁ Φ hΦ hSo
  refine ⟨|C₁| * (max Bd 0) ^ k₁, fun h g _ p hp t htc a ha k hk hg => ?_⟩
  obtain ⟨a', ha'⟩ := GlobalTheory.ThetaUnifSiegel.transp hσ X.J a
  have hy : ((a'⁻¹ * g : UA σ X.J) : GL (Fin n) (AE F E)) =
      HA.mat (AF F) σ ((1 : E) • X.J.map σ) ((a⁻¹ * p * a) * k) := by
    have : (a⁻¹ * p * a) * k = a⁻¹ * (p * a * k) := by group
    rw [this]
    change (a' : GL (Fin n) (AE F E))⁻¹ * (g : GL (Fin n) (AE F E)) = _
    rw [ha', hg]
    rfl
  have hty : (ht (a'⁻¹ * g) : ℝ) ≤ max Bd 0 := by
    refine le_trans ?_ (le_max_left _ _)
    show (heightGL F ((a'⁻¹ * g : UA σ X.J) : GL (Fin n) (AE F E)) : ℝ) ≤ Bd
    rw [hy]
    exact hBd _ (hconj p hp t htc a ha) k hk
  have hb := h₁ t htc a ha a' ha' (a'⁻¹ * g) h
  rw [mul_inv_cancel_left] at hb
  have h0 : (0 : ℝ) ≤ (ht h : ℝ) := NNReal.coe_nonneg _
  have hy0 : (0 : ℝ) ≤ (ht (a'⁻¹ * g) : ℝ) := NNReal.coe_nonneg _
  refine hb.trans ?_
  calc C₁ * ((ht (a'⁻¹ * g) : ℝ) * ht h) ^ k₁ ≤ |C₁| * ((max Bd 0) * ht h) ^ k₁ :=
        mul_le_mul (le_abs_self _) (pow_le_pow_left₀ (mul_nonneg hy0 h0) (mul_le_mul_of_nonneg_right hty h0) _)
          (pow_nonneg (mul_nonneg hy0 h0) _) (abs_nonneg _)
    _ = |C₁| * (max Bd 0) ^ k₁ * (ht h : ℝ) ^ k₁ := by rw [mul_pow]; ring

end GlobalTheory.ThetaSoSiegel
end
