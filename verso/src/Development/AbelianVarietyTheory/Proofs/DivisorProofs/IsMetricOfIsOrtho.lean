import Mathlib
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.UnifMetricScalar
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CuspFormValueLeSupNormAtOrthonormalFrame
import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.LinkFD

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT GlobalTheory.OrthoMetric

namespace GlobalTheory.SupFull

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c σ r U hσ hU k x W Wu hx`. Take `⟨hbij, hrt, -, -⟩` from `GlobalTheory.Relab.relab_good E H l c σ hσ`. Take `⟨hp0, hty⟩` from `hU.2.1 k`. Take `⟨f, hf⟩` from `GlobalTheory.FrameUnif.exists_letter_equiv (U.X k).Ψ (U.X k).cmType Dw.p Dw.q r hU.1 (relab c σ) hbij Dw.mult (fun τ h => by unfold Datum.mult; rw [if_pos ((hrt τ).1 ((hty _).1 h))]) (fun τ h => by unfold Datum.mult; rw [if_neg (fun h' => h ((hty _).2 ((hrt τ).2 h')))])`. Establish `hper : ∀ (v : Fin r → E) j, perFr (U.X k) x.1 v (relab c σ (W.e j).1) (W.e j).2 = if (((W.e.trans f) j).2 : ℕ) < (U.X k).p0 then FD.hermC ((W.e.trans f) j).1.1 (U.X k).Gm (FD.col (FD.mat x.1 ((W.e.trans f) j).1) ((W.e.trans f) j).2) (FD.Data.emb ((W.e.trans f) j).1.1 v) else ((FD …`.

Introduce `v j`. Establish `h` using `hf (W.e j)`. Rewrite using `[Equiv.trans_apply]`. Generalize the expression as in `f (W.e j) = t at h ⊢`. Take `⟨⟨τ, hτ⟩, ⟨n, hn⟩⟩` from `t`.

Generalize the expression as in `((W.e j).2 : ℕ) = i at h ⊢`. Simplify using `only at h ⊢`. Rewrite `h` using `[← hp0]`. Break down `h with ⟨a, rfl, rfl⟩ | ⟨a, rfl, rfl, d⟩` into its components or cases. Rewrite using `[if_neg (by omega)]`.

Unfold `perFr`. Rewrite using `[dif_pos a, dif_pos hn]`. Rewrite using `[if_pos (by omega)]`. Unfold `perFr`. Rewrite using `[dif_neg a, dif_pos (show conjEmb (relab c σ (W.e j).1) ∈ (U.X k).Ψ from hτ), dif_pos hn]`.

Both sides reduce to the same expression. Establish `hcc : FD.cc (-(U.X k).ξ0) = -(-(U.X k).ξ0)`. Establish `h` using `(U.X k).ξ0_im`. Unfold `FD.cc at h ⊢`. Rewrite using `[map_neg, h]`.

Establish `key : Wu.Hm = Matrix.diagonal fun j => ((2 * (((W.e.trans f) j).1.1 (-(U.X k).ξ0)).im : ℝ) : ℂ)`. Use `PullbackSections.UH.herm_eq_of_im W.Pm W.per.2.2.2.1 _ _ fun a b => ?_` and prove the remaining obligations. Rewrite using `[Wu.c1, OrthoHerm.im_diag_eq_trace (U.X k).p0 _ (U.X k).Gm (U.X k).Ψ (U.X k).cmType (W.e.trans f) hcc x.1 hx (W.φ k a) (W.φ k b) _ _ (fun j => (W.pm_eq a j).trans (hper _ j)) (fun j => (W.pm_eq b j).trans (hper _ j)), ← W.isom, Rat.cast_intCast]`. Establish `hd : ∀ j, (((W.e.trans f) j).1.1 (-(U.X k).ξ0)).im = ‖relab c σ (W.e j).1 (U.X k).ξ0‖`. Introduce `j`.

Establish `hn : ‖relab c σ (W.e j).1 (U.X k).ξ0‖ = ‖((W.e.trans f) j).1.1 (U.X k).ξ0‖`. Break down `hf (W.e j) with ⟨-, h, -⟩ | ⟨-, h, -⟩` into its components or cases. Rewrite using `[Equiv.trans_apply, h]`. Rewrite using `[Equiv.trans_apply, h]`. Conclude with `(Complex.norm_conj _).symm`.

Rewrite using `[hn]`. Use `clear hn`. Establish `hpos` using `Wu.pos (Pi.single j 1) (by simp)`. Rewrite `hpos` using `[key, hermForm, single_dotProduct, Matrix.mulVec_diagonal, Pi.star_apply, Pi.single_eq_same, star_one, _root_.one_mul, _root_.mul_one, Complex.ofReal_re]`. Generalize the expression as in `((W.e.trans f) j).1.1 = τ at hpos ⊢`.

Establish `hre : (τ (-(U.X k).ξ0)).re = 0`. Establish `h` using `congrArg τ hcc`. Rewrite `h` using `[FD.cc, IsCMField.complexEmbedding_complexConj, map_neg τ (-(U.X k).ξ0)]`. Use `congrArg Complex.re h` as an intermediate fact. Simplify using `only [Complex.conj_re, Complex.neg_re] at this`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hp : 0 < (τ (-(U.X k).ξ0)).im` using `by linarith`. Rewrite using `[← norm_neg, ← map_neg, ← Complex.abs_im_eq_norm.mpr hre, abs_of_pos hp]`. Rewrite using `[key]`. Simplify using `only [hd]`.
-/
theorem hm_eq_diagonal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → ∀ (k : U.Comp) (x : (U.X k).dom) (W : PullbackSections.UnfAt U k x) (Wu : PullbackSections.UnitAt W), (U.X k).IsOrtho x.1 → Wu.Hm = Matrix.diagonal fun j => ((2 * ‖relab c σ (W.e j).1 (U.X k).ξ0‖ : ℝ) : ℂ) := by
  intro E _ _ _ H Dw l Xo c σ r U hσ hU k x W Wu hx
  obtain ⟨hbij, hrt, -, -⟩ := GlobalTheory.Relab.relab_good E H l c σ hσ
  obtain ⟨hp0, hty⟩ := hU.2.1 k
  obtain ⟨f, hf⟩ := GlobalTheory.FrameUnif.exists_letter_equiv (U.X k).Ψ (U.X k).cmType Dw.p Dw.q r hU.1 (relab c σ) hbij
    Dw.mult
    (fun τ h => by unfold Datum.mult; rw [if_pos ((hrt τ).1 ((hty _).1 h))])
    (fun τ h => by unfold Datum.mult; rw [if_neg (fun h' => h ((hty _).2 ((hrt τ).2 h')))])
  have hper : ∀ (v : Fin r → E) j, perFr (U.X k) x.1 v (relab c σ (W.e j).1) (W.e j).2 =
      if (((W.e.trans f) j).2 : ℕ) < (U.X k).p0 then
        FD.hermC ((W.e.trans f) j).1.1 (U.X k).Gm
          (FD.col (FD.mat x.1 ((W.e.trans f) j).1) ((W.e.trans f) j).2) (FD.Data.emb ((W.e.trans f) j).1.1 v)
      else ((FD.mat x.1 ((W.e.trans f) j).1)⁻¹.mulVec (FD.Data.emb ((W.e.trans f) j).1.1 v))
        ((W.e.trans f) j).2 := by
    intro v j
    have h := hf (W.e j)
    rw [Equiv.trans_apply]
    generalize f (W.e j) = t at h ⊢
    obtain ⟨⟨τ, hτ⟩, ⟨n, hn⟩⟩ := t
    generalize ((W.e j).2 : ℕ) = i at h ⊢
    dsimp only at h ⊢
    rw [← hp0] at h
    rcases h with ⟨a, rfl, rfl⟩ | ⟨a, rfl, rfl, d⟩
    · rw [if_neg (by omega)]
      unfold perFr
      rw [dif_pos a, dif_pos hn]
    · rw [if_pos (by omega)]
      unfold perFr
      rw [dif_neg a, dif_pos (show conjEmb (relab c σ (W.e j).1) ∈ (U.X k).Ψ from hτ), dif_pos hn]
      rfl
  have hcc : FD.cc (-(U.X k).ξ0) = -(-(U.X k).ξ0) := by
    have h := (U.X k).ξ0_im
    unfold FD.cc at h ⊢
    rw [map_neg, h]
  have key : Wu.Hm = Matrix.diagonal fun j => ((2 * (((W.e.trans f) j).1.1 (-(U.X k).ξ0)).im : ℝ) : ℂ) := by
    refine PullbackSections.UH.herm_eq_of_im W.Pm W.per.2.2.2.1 _ _ fun a b => ?_
    rw [Wu.c1, OrthoHerm.im_diag_eq_trace (U.X k).p0 _ (U.X k).Gm (U.X k).Ψ (U.X k).cmType (W.e.trans f) hcc x.1 hx
      (W.φ k a) (W.φ k b) _ _ (fun j => (W.pm_eq a j).trans (hper _ j)) (fun j => (W.pm_eq b j).trans (hper _ j)),
      ← W.isom, Rat.cast_intCast]
  have hd : ∀ j, (((W.e.trans f) j).1.1 (-(U.X k).ξ0)).im = ‖relab c σ (W.e j).1 (U.X k).ξ0‖ := by
    intro j
    have hn : ‖relab c σ (W.e j).1 (U.X k).ξ0‖ = ‖((W.e.trans f) j).1.1 (U.X k).ξ0‖ := by
      rcases hf (W.e j) with ⟨-, h, -⟩ | ⟨-, h, -⟩
      · rw [Equiv.trans_apply, h]
      · rw [Equiv.trans_apply, h]
        exact (Complex.norm_conj _).symm
    rw [hn]
    clear hn
    have hpos := Wu.pos (Pi.single j 1) (by simp)
    rw [key, hermForm, single_dotProduct, Matrix.mulVec_diagonal, Pi.star_apply, Pi.single_eq_same, star_one,
      _root_.one_mul, _root_.mul_one, Complex.ofReal_re] at hpos
    generalize ((W.e.trans f) j).1.1 = τ at hpos ⊢
    have hre : (τ (-(U.X k).ξ0)).re = 0 := by
      have h := congrArg τ hcc
      rw [FD.cc, IsCMField.complexEmbedding_complexConj, map_neg τ (-(U.X k).ξ0)] at h
      have := congrArg Complex.re h
      simp only [Complex.conj_re, Complex.neg_re] at this
      linarith
    have hp : 0 < (τ (-(U.X k).ξ0)).im := by linarith
    rw [← norm_neg, ← map_neg, ← Complex.abs_im_eq_norm.mpr hre, abs_of_pos hp]
  rw [key]
  simp only [hd]

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c σ r U hσ hU hpq k x hx`. Take `⟨W⟩` from `PullbackSections.nonempty_unfAt hU k x`. Take `⟨Wu⟩` from `PullbackSections.nonempty_unitAt W (PullbackSections.PfSupAtUnit.dmin_ortho _ hx)`. Establish `hH` using `hm_eq_diagonal E H Dw l Xo c σ r U hσ hU k x W Wu hx`. Take `⟨Φ₀⟩` from `nonempty_fibKey E H Dw l Xo ℂ (U.un k x).x hpq`.

Take `⟨-, h₁, h₂⟩` from `SecTieEx.secTie_exists_unique E H Dw l Xo ℂ (U.un k x).x Φ₀.T.t Φ₀.m`. Take `⟨th, ht⟩` from `h₁ (U.un k x).s`. Establish `hne` using `(h₂ th _ ht).2.1 (secNZ_of_secGen lawsFieldsSeparately.2.1 E H Dw l Xo ℂ _ _ (U.un k x).gen)`. Set `Φ : FibKey Xo ℂ (U.un k x).x` to `{ Φ₀ with th := th, th_ne := hne }`. Take `⟨u, χ, hΛ, hA, hR, hF, hg, hD⟩` from `exists_unif W.F (W.ik k) W.per W.pt Φ ht Wu.herm Wu.pos Wu.c2 Wu.c3 Wu.c4 Wu.c5 Wu.c6 Wu.c7`.

Use `choose w hw using fun τ i => hD _ _ ((U.un k x).tan τ i) (W.der τ i)`. Establish `hFd : IsAddFundamentalDomain u.Λ Wu.Fd volume` using `hΛ ▸ Wu.c8`. Establish `hN` using `Wu.c9.symm`. Establish `hG : ∀ (b : E →+* ℂ) (i j : Fin (Dw.mult b)), (((2 * Real.pi * ‖relab c σ b (U.X k).ξ0‖ : ℝ) : ℂ) • (1 : Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) ℂ)) i j = Real.pi * hermForm Wu.Hm (Pi.single (W.e.symm ⟨b, j⟩) 1) (Pi.single (W.e.symm ⟨b, i⟩) 1)`. Introduce `b i j`.

Rewrite using `[hH]`. Simplify using `[hermForm, Matrix.mulVec_diagonal, Pi.single_apply, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp_all <;> ring`. Conclude with `isMetricAt_of Φ hg u Wu.Hm χ Wu.θ Wu.Fd w (fun b i => Pi.single (W.e.symm ⟨b, i⟩) 1) ⟨ht, hA, hR, hF, hFd, hN, hw, hG⟩`.
-/
theorem isMetric_of_isOrtho : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → 1 ≤ Dw.p + Dw.q → ∀ (k : U.Comp) (x : (U.X k).dom), (U.X k).IsOrtho x.1 → IsMetric (U.un k x) 1 (fun b => ((2 * Real.pi * ‖relab c σ b (U.X k).ξ0‖ : ℝ) : ℂ) • 1) := by
  intro E _ _ _ H Dw l Xo c σ r U hσ hU hpq k x hx
  obtain ⟨W⟩ := PullbackSections.nonempty_unfAt hU k x
  obtain ⟨Wu⟩ := PullbackSections.nonempty_unitAt W (PullbackSections.PfSupAtUnit.dmin_ortho _ hx)
  have hH := hm_eq_diagonal E H Dw l Xo c σ r U hσ hU k x W Wu hx
  obtain ⟨Φ₀⟩ := nonempty_fibKey E H Dw l Xo ℂ (U.un k x).x hpq
  obtain ⟨-, h₁, h₂⟩ := SecTieEx.secTie_exists_unique E H Dw l Xo ℂ (U.un k x).x Φ₀.T.t Φ₀.m
  obtain ⟨th, ht⟩ := h₁ (U.un k x).s
  have hne := (h₂ th _ ht).2.1 (secNZ_of_secGen lawsFieldsSeparately.2.1 E H Dw l Xo ℂ _ _ (U.un k x).gen)
  let Φ : FibKey Xo ℂ (U.un k x).x := { Φ₀ with th := th, th_ne := hne }
  obtain ⟨u, χ, hΛ, hA, hR, hF, hg, hD⟩ := exists_unif W.F (W.ik k) W.per W.pt Φ ht Wu.herm Wu.pos Wu.c2 Wu.c3 Wu.c4
    Wu.c5 Wu.c6 Wu.c7
  choose w hw using fun τ i => hD _ _ ((U.un k x).tan τ i) (W.der τ i)
  have hFd : IsAddFundamentalDomain u.Λ Wu.Fd volume := hΛ ▸ Wu.c8
  have hN := Wu.c9.symm
  have hG : ∀ (b : E →+* ℂ) (i j : Fin (Dw.mult b)),
      (((2 * Real.pi * ‖relab c σ b (U.X k).ξ0‖ : ℝ) : ℂ) • (1 : Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) ℂ)) i j =
        Real.pi * hermForm Wu.Hm (Pi.single (W.e.symm ⟨b, j⟩) 1) (Pi.single (W.e.symm ⟨b, i⟩) 1) := by
    intro b i j
    rw [hH]
    simp [hermForm, Matrix.mulVec_diagonal, Pi.single_apply, Matrix.one_apply]
    split_ifs <;> simp_all <;> ring
  exact isMetricAt_of Φ hg u Wu.Hm χ Wu.θ Wu.Fd w (fun b i => Pi.single (W.e.symm ⟨b, i⟩) 1)
    ⟨ht, hA, hR, hF, hFd, hN, hw, hG⟩

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c σ r U U' hσ hU hU' hpq a n hd f hf hb k'`. Establish `hB : Out.SecBaseChangeSt` using `GlobalTheory.lawsFieldsSeparately.2.1`. Take `⟨-, -, -, -, -, -, hwt⟩` from `GlobalTheory.Frames.algebraic_laws hB E H Dw l Xo c`. Establish `hs'` using `hU'.2.2.2.2.1 a n hd f hf k'`. Use `choose C hC using fun k => (hb k).2`.

Establish `hpos : ∀ (X : FD.Data E r) (b : E →+* ℂ), 0 < 2 * Real.pi * ‖relab c σ b X.ξ0‖` using `fun X b => mul_pos (by positivity) (norm_pos_iff.2 ((map_ne_zero _).2 X.ξ0_ne))`. Set `κ : U.Comp → (E →+* ℂ) → ℝ` to `fun k b => 2 * Real.pi * ‖relab c σ b (U.X k).ξ0‖ / (2 * Real.pi * ‖relab c σ b (U'.X k').ξ0‖)`. Set `B : U.Comp → ℝ` to `fun k => (∏ p : Σ τ : E →+* ℂ, Fin (Dw.mult τ), (Real.sqrt (κ k p.1))⁻¹ ^ a (p.1, p.2)) * |C k|`. Use `⟨hs', ∑ k, B k, fun x₁ hx₁ => ?_⟩` and prove the remaining obligations. Take `⟨b, hbB, ho⟩` from `(FD.orthonormalFlagTranslate_holds r (U'.X k')).1 x₁ hx₁`.

Establish `hx'` using `FD.OrthogonalFrameDomain.rmul_mem_dom (U'.X k') hx₁ hbB`. Rewrite using `[← (FD.orthonormalFlagTranslate_holds r (U'.X k')).2.1 _ _ hs'.2.1 x₁ hx₁ b hbB, PullbackSections.PfSupAtUnit.pnorm_unit _ _ _ (PullbackSections.PfSupAtUnit.dmin_ortho _ ho)]`. Establish `hN` using `isMetric_of_isOrtho E H Dw l Xo c σ r U' hσ hU' hpq k' ⟨_, hx'⟩ ho`. Establish `hrd' : ‖rdU U' f k' (FD.rmul x₁ b)‖ = cabs (evR Xo c f (U'.un k' ⟨_, hx'⟩))`. Establish `e : rdU U' f k' (FD.rmul x₁ b) = toC (evR Xo c f (U'.un k' ⟨_, hx'⟩))` using `dif_pos hx'`.

Rewrite using `[e]`. Both sides reduce to the same expression. Rewrite using `[hrd']`. Generalize the expression as in `U'.un k' ⟨_, hx'⟩ = y at hN ⊢`. Take `⟨k, x, t, hx, ht⟩` from `GlobalTheory.T.exists_orthonormalFrame_borelChange_complexFramedPoint E H Dw l Xo c σ r U hU y`.

Take `⟨g, hg0, hgd, hchg⟩` from `((GlobalTheory.Frames.frBor_calculus E H Dw l Xo c (CAt σ) (U.un k x) y y).1 t).1 ht`. Establish `hm0` using `isMetric_of_isOrtho E H Dw l Xo c σ r U hσ hU hpq k x hx`. Establish `hm1` using `GlobalTheory.T.metric_change_of_frame E H Dw l Xo c σ (U.un k x) y 1 _ (fun b => Matrix.transpose (show Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) ℂ from g b)) (show ℂ from (t none : CAt σ)) (Units.ne_zero (M₀ := ℂ) (t none)) hchg hm0`. Take `⟨hNN, hG⟩` from `GlobalTheory.T.metric_data_unique E H Dw l Xo c σ y _ _ _ _ hN hm1`. Establish `hnone : cabs (t none : CAt σ) = 1`.

Rewrite `hNN` using `[_root_.mul_one]`. Conclude with `(pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 hNN.symm`. Establish `hsome : ∀ p : Σ τ : E →+* ℂ, Fin (Dw.mult τ), cabs (t (some p) : CAt σ) = (Real.sqrt (κ k p.1))⁻¹`. Introduce and unpack `⟨τ, i⟩`. Rewrite using `[← hgd τ i]`.

Use `OrthoBound.norm_diag_of_triangular (Matrix.transpose (show Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ from g τ)) _ (div_pos (hpos _ _) (hpos _ _)) (fun i j hij => hg0 τ j i hij) ?_ i` and prove the remaining obligations. Establish `h1` using `(congrFun hG τ).symm`. Establish `h2 : ((2 * Real.pi * ‖relab c σ τ (U'.X k').ξ0‖ : ℝ) : ℂ) ≠ 0` using `Complex.ofReal_ne_zero.2 (hpos _ _).ne'`. Simplify using `only at h1`. Rewrite using `[Complex.ofReal_div, div_eq_inv_mul, mul_smul, Matrix.mul_smul, Matrix.smul_mul, h1, smul_smul, inv_mul_cancel₀ h2, one_smul]`.

Establish `hev` using `hwt (CAt σ) (GlobalTheory.FrameNorm.Comparison₂.isReduced_cAt σ) a n f hf t _ _ ht`. Establish `hw : cabs (wchar (ex Dw a n) t) = ∏ p : Σ τ : E →+* ℂ, Fin (Dw.mult τ), (Real.sqrt (κ k p.1))⁻¹ ^ a (p.1, p.2)`. Rewrite using `[GlobalTheory.FrameNorm.Comparison₂.cabs_wchar, Fintype.prod_option, hnone, one_pow, _root_.one_mul]`. Conclude with `Finset.prod_congr rfl fun p _ => by rw [hsome p]; rfl`. Establish `hrd : ‖rdU U f k x.1‖ = cabs (evR Xo c f (U.un k x))`.

Establish `e : rdU U f k x.1 = toC (evR Xo c f (U.un k x))` using `dif_pos x.2`. Rewrite using `[e]`. Both sides reduce to the same expression. Establish `hle` using `hC k x.1 x.2`. Rewrite `hle` using `[PullbackSections.PfSupAtUnit.pnorm_unit _ _ _ (PullbackSections.PfSupAtUnit.dmin_ortho _ hx), hrd]`.

Establish `hB0 : ∀ k, 0 ≤ B k` using `fun k => mul_nonneg (Finset.prod_nonneg fun p _ => by positivity) (abs_nonneg _)`. Rewrite using `[hev, GlobalTheory.FrameNorm.Comparison₂.cabs_mul, hw]`. Conclude with `(mul_le_mul_of_nonneg_left (hle.trans (le_abs_self _)) (Finset.prod_nonneg fun p _ => by positivity)).trans (Finset.single_le_sum (f := B) (fun k _ => hB0 k) (Finset.mem_univ k))`.
-/
theorem isBddSec_of_isUnf : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U U' : Unf Xo c σ r), GoodEmb c σ → IsUnf U → IsUnf U' → 1 ≤ Dw.p + Dw.q → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ f ∈ sec Xo c a n, (∀ k, (U.X k).IsBddSec (laU U a n k) (rdU U f k)) → ∀ k, (U'.X k).IsBddSec (laU U' a n k) (rdU U' f k) := by
  intro E _ _ _ H Dw l Xo c σ r U U' hσ hU hU' hpq a n hd f hf hb k'
  have hB : Out.SecBaseChangeSt := GlobalTheory.lawsFieldsSeparately.2.1
  obtain ⟨-, -, -, -, -, -, hwt⟩ := GlobalTheory.Frames.algebraic_laws hB E H Dw l Xo c
  have hs' := hU'.2.2.2.2.1 a n hd f hf k'
  choose C hC using fun k => (hb k).2
  have hpos : ∀ (X : FD.Data E r) (b : E →+* ℂ), 0 < 2 * Real.pi * ‖relab c σ b X.ξ0‖ := fun X b =>
    mul_pos (by positivity) (norm_pos_iff.2 ((map_ne_zero _).2 X.ξ0_ne))
  let κ : U.Comp → (E →+* ℂ) → ℝ := fun k b =>
    2 * Real.pi * ‖relab c σ b (U.X k).ξ0‖ / (2 * Real.pi * ‖relab c σ b (U'.X k').ξ0‖)
  let B : U.Comp → ℝ := fun k =>
    (∏ p : Σ τ : E →+* ℂ, Fin (Dw.mult τ), (Real.sqrt (κ k p.1))⁻¹ ^ a (p.1, p.2)) * |C k|
  refine ⟨hs', ∑ k, B k, fun x₁ hx₁ => ?_⟩
  obtain ⟨b, hbB, ho⟩ := (FD.orthonormalFlagTranslate_holds r (U'.X k')).1 x₁ hx₁
  have hx' := FD.OrthogonalFrameDomain.rmul_mem_dom (U'.X k') hx₁ hbB
  rw [← (FD.orthonormalFlagTranslate_holds r (U'.X k')).2.1 _ _ hs'.2.1 x₁ hx₁ b hbB,
    PullbackSections.PfSupAtUnit.pnorm_unit _ _ _ (PullbackSections.PfSupAtUnit.dmin_ortho _ ho)]
  have hN := isMetric_of_isOrtho E H Dw l Xo c σ r U' hσ hU' hpq k' ⟨_, hx'⟩ ho
  have hrd' : ‖rdU U' f k' (FD.rmul x₁ b)‖ = cabs (evR Xo c f (U'.un k' ⟨_, hx'⟩)) := by
    have e : rdU U' f k' (FD.rmul x₁ b) = toC (evR Xo c f (U'.un k' ⟨_, hx'⟩)) := dif_pos hx'
    rw [e]; rfl
  rw [hrd']
  generalize U'.un k' ⟨_, hx'⟩ = y at hN ⊢
  obtain ⟨k, x, t, hx, ht⟩ := GlobalTheory.T.exists_orthonormalFrame_borelChange_complexFramedPoint E H Dw l Xo c σ r U hU y
  obtain ⟨g, hg0, hgd, hchg⟩ :=
    ((GlobalTheory.Frames.frBor_calculus E H Dw l Xo c (CAt σ) (U.un k x) y y).1 t).1 ht
  have hm0 := isMetric_of_isOrtho E H Dw l Xo c σ r U hσ hU hpq k x hx
  have hm1 := GlobalTheory.T.metric_change_of_frame E H Dw l Xo c σ (U.un k x) y 1 _
    (fun b => Matrix.transpose (show Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) ℂ from g b))
    (show ℂ from (t none : CAt σ)) (Units.ne_zero (M₀ := ℂ) (t none)) hchg hm0
  obtain ⟨hNN, hG⟩ := GlobalTheory.T.metric_data_unique E H Dw l Xo c σ y _ _ _ _ hN hm1
  have hnone : cabs (t none : CAt σ) = 1 := by
    rw [_root_.mul_one] at hNN
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 hNN.symm
  have hsome : ∀ p : Σ τ : E →+* ℂ, Fin (Dw.mult τ), cabs (t (some p) : CAt σ) = (Real.sqrt (κ k p.1))⁻¹ := by
    rintro ⟨τ, i⟩
    rw [← hgd τ i]
    refine OrthoBound.norm_diag_of_triangular
      (Matrix.transpose (show Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ from g τ)) _
      (div_pos (hpos _ _) (hpos _ _)) (fun i j hij => hg0 τ j i hij) ?_ i
    have h1 := (congrFun hG τ).symm
    have h2 : ((2 * Real.pi * ‖relab c σ τ (U'.X k').ξ0‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (hpos _ _).ne'
    dsimp only at h1
    rw [Complex.ofReal_div, div_eq_inv_mul, mul_smul, Matrix.mul_smul, Matrix.smul_mul, h1, smul_smul,
      inv_mul_cancel₀ h2, one_smul]
  have hev := hwt (CAt σ) (GlobalTheory.FrameNorm.Comparison₂.isReduced_cAt σ) a n f hf t _ _ ht
  have hw : cabs (wchar (ex Dw a n) t) =
      ∏ p : Σ τ : E →+* ℂ, Fin (Dw.mult τ), (Real.sqrt (κ k p.1))⁻¹ ^ a (p.1, p.2) := by
    rw [GlobalTheory.FrameNorm.Comparison₂.cabs_wchar, Fintype.prod_option, hnone, one_pow, _root_.one_mul]
    exact Finset.prod_congr rfl fun p _ => by rw [hsome p]; rfl
  have hrd : ‖rdU U f k x.1‖ = cabs (evR Xo c f (U.un k x)) := by
    have e : rdU U f k x.1 = toC (evR Xo c f (U.un k x)) := dif_pos x.2
    rw [e]; rfl
  have hle := hC k x.1 x.2
  rw [PullbackSections.PfSupAtUnit.pnorm_unit _ _ _ (PullbackSections.PfSupAtUnit.dmin_ortho _ hx), hrd] at hle
  have hB0 : ∀ k, 0 ≤ B k := fun k => mul_nonneg (Finset.prod_nonneg fun p _ => by positivity) (abs_nonneg _)
  rw [hev, GlobalTheory.FrameNorm.Comparison₂.cabs_mul, hw]
  exact (mul_le_mul_of_nonneg_left (hle.trans (le_abs_self _)) (Finset.prod_nonneg fun p _ => by positivity)).trans
    (Finset.single_le_sum (f := B) (fun k _ => hB0 k) (Finset.mem_univ k))

end GlobalTheory.SupFull
