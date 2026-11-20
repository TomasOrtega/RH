import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.FinLocalCutAt
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsIntegralElemOfIsAlgebraicInt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FramedPointEvalNaturalWeightScalingStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcFramedPointValueIsHomogeneousLettersStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcLetterRingOverDVRPolynomialDenominatorsStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsEvalArcLetterRingOverDVRDiscStatement

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

noncomputable section

namespace GlobalTheory.ArcQ.FrameCut

/- English proof (translation)
Simplify using `only [GlobalTheory.ArcQ.lcoeffPoly, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]`. Rewrite using `[Finset.sum_ite_eq']`. Use `split_ifs with h`. Both sides reduce to the same expression. Rewrite using `[MvPolynomial.notMem_support_iff.mp h]`.

Both sides reduce to the same expression.
-/
theorem lcoeffPoly_coeff {ι K₁ : Type} [Field K₁] (P : MvPolynomial ι (LaurentSeries K₁)) (m : ℤ)
    (μ : ι →₀ ℕ) : (GlobalTheory.ArcQ.lcoeffPoly P m).coeff μ = (P.coeff μ).coeff m := by
  classical
  simp only [GlobalTheory.ArcQ.lcoeffPoly, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [MvPolynomial.notMem_support_iff.mp h]; rfl

/- English proof (translation)
Use extensionality with `μ`. Simplify using `only [lcoeffPoly_coeff, MvPolynomial.coeff_add, HahnSeries.coeff_add]`.
-/
theorem lcoeffPoly_add {ι K₁ : Type} [Field K₁] (P Q : MvPolynomial ι (LaurentSeries K₁)) (m : ℤ) :
    GlobalTheory.ArcQ.lcoeffPoly (P + Q) m = GlobalTheory.ArcQ.lcoeffPoly P m + GlobalTheory.ArcQ.lcoeffPoly Q m := by
  ext μ
  simp only [lcoeffPoly_coeff, MvPolynomial.coeff_add, HahnSeries.coeff_add]

/- English proof (translation)
Use extensionality with `ν`. Simplify using `only [lcoeffPoly_coeff, MvPolynomial.coeff_monomial]`. Use `split_ifs`. Both sides reduce to the same expression. Both sides reduce to the same expression.
-/
theorem lcoeffPoly_monomial {ι K₁ : Type} [Field K₁] (μ : ι →₀ ℕ) (f : LaurentSeries K₁) (m : ℤ) :
    GlobalTheory.ArcQ.lcoeffPoly (MvPolynomial.monomial μ f) m = MvPolynomial.monomial μ (f.coeff m) := by
  classical
  ext ν
  simp only [lcoeffPoly_coeff, MvPolynomial.coeff_monomial]
  split_ifs
  · rfl
  · rfl

/- English proof (translation)
Use extensionality with `ν`. Rewrite using `[lcoeffPoly_coeff, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map, mul_comm g, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul, mul_comm]`.
-/
theorem lcoeffPoly_C_mul_map {ι L : Type} [Field L] (g : LaurentSeries L) (Q : MvPolynomial ι L) (m : ℤ) :
    GlobalTheory.ArcQ.lcoeffPoly (MvPolynomial.C g * MvPolynomial.map (HahnSeries.C (Γ := ℤ)) Q) m =
      MvPolynomial.C (g.coeff m) * Q := by
  ext ν
  rw [lcoeffPoly_coeff, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map, mul_comm g,
    HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul, mul_comm]

/- English proof (translation)
Use extensionality with `ν`. Rewrite using `[lcoeffPoly_coeff, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_C_mul, lcoeffPoly_coeff, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul]`.
-/
theorem lcoeffPoly_const_mul {ι L : Type} [Field L] (x : L) (P : MvPolynomial ι (LaurentSeries L)) (m : ℤ) :
    GlobalTheory.ArcQ.lcoeffPoly (MvPolynomial.C (HahnSeries.C (Γ := ℤ) x) * P) m =
      MvPolynomial.C x * GlobalTheory.ArcQ.lcoeffPoly P m := by
  ext ν
  rw [lcoeffPoly_coeff, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_C_mul, lcoeffPoly_coeff,
    HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul]

/- English proof (translation)
Proceed by induction on `P using MvPolynomial.induction_on' with`. Consider the case `monomial μ f`. Take `⟨g, hg, hΦ⟩` from `hC f`. Use `⟨MvPolynomial.C g * MvPolynomial.map (HahnSeries.C (Γ := ℤ)) (μ.prod fun x e => q x ^ e), ?_, fun m => ?_⟩` and prove the remaining obligations. Rewrite using `[MvPolynomial.monomial_eq, map_mul, map_mul, hΦ]`.

Simplify using `only [Finsupp.prod, map_prod, map_pow, hX]`. Rewrite using `[lcoeffPoly_C_mul_map, lcoeffPoly_monomial, MvPolynomial.eval₂Hom_monomial, hg]`. Both sides reduce to the same expression. Consider the case `add P Q hP hQ`. Take `⟨P₁, h1, h2⟩` from `hP`.

Take `⟨Q₁, h3, h4⟩` from `hQ`. Conclude with `⟨P₁ + Q₁, by rw [map_add, map_add, h1, h3], fun m => by`. Rewrite using `[lcoeffPoly_add, lcoeffPoly_add, map_add, h2, h4]⟩`.
-/
theorem exists_subst {ι K₁ L S : Type} [Field K₁] [Field L] [CommRing S] (io : K₁ →+* L)
    (Φ : MvPolynomial ι (LaurentSeries K₁) →+* S) (j : MvPolynomial ι (LaurentSeries L) →+* S)
    (q : ι → MvPolynomial ι L)
    (hC : ∀ f : LaurentSeries K₁, ∃ g : LaurentSeries L, (∀ m, g.coeff m = io (f.coeff m)) ∧
      Φ (MvPolynomial.C f) = j (MvPolynomial.C g))
    (hX : ∀ x, Φ (MvPolynomial.X x) = j (MvPolynomial.map (HahnSeries.C (Γ := ℤ)) (q x)))
    (P : MvPolynomial ι (LaurentSeries K₁)) :
    ∃ P₁ : MvPolynomial ι (LaurentSeries L), j P₁ = Φ P ∧ ∀ m, GlobalTheory.ArcQ.lcoeffPoly P₁ m =
      MvPolynomial.eval₂Hom (MvPolynomial.C.comp io) q (GlobalTheory.ArcQ.lcoeffPoly P m) := by
  induction P using MvPolynomial.induction_on' with
  | monomial μ f =>
    obtain ⟨g, hg, hΦ⟩ := hC f
    refine ⟨MvPolynomial.C g * MvPolynomial.map (HahnSeries.C (Γ := ℤ)) (μ.prod fun x e => q x ^ e), ?_, fun m => ?_⟩
    · rw [MvPolynomial.monomial_eq, map_mul, map_mul, hΦ]
      simp only [Finsupp.prod, map_prod, map_pow, hX]
    · rw [lcoeffPoly_C_mul_map, lcoeffPoly_monomial, MvPolynomial.eval₂Hom_monomial, hg]
      rfl
  | add P Q hP hQ =>
    obtain ⟨P₁, h1, h2⟩ := hP
    obtain ⟨Q₁, h3, h4⟩ := hQ
    exact ⟨P₁ + Q₁, by rw [map_add, map_add, h1, h3], fun m => by
      rw [lcoeffPoly_add, lcoeffPoly_add, map_add, h2, h4]⟩

/- English proof (translation)
Proceed by induction on `R using MvPolynomial.induction_on with`. Consider the case `C a => simp`. Consider the case `add p q hp hq => simp only [map_add, hp, hq]`. Consider the case `mul_X p x hp => simp only [map_mul, hp, MvPolynomial.eval₂Hom_X', MvPolynomial.map_X, MvPolynomial.eval_X]`.
-/
theorem eval_subst {ι K₁ L K : Type} [Field K₁] [Field L] [Field K] (io : K₁ →+* L) (ιT : L →+* K)
    (q : ι → MvPolynomial ι L) (Y : ι → K) (R : MvPolynomial ι K₁) :
    MvPolynomial.eval Y (MvPolynomial.map ιT (MvPolynomial.eval₂Hom (MvPolynomial.C.comp io) q R)) =
      MvPolynomial.eval (fun x => MvPolynomial.eval Y (MvPolynomial.map ιT (q x)))
        (MvPolynomial.map (ιT.comp io) R) := by
  induction R using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p x hp => simp only [map_mul, hp, MvPolynomial.eval₂Hom_X', MvPolynomial.map_X, MvPolynomial.eval_X]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}

/- English proof (translation)
Establish `hs : ∃ Q, algebraMap (MvPolynomial (ArcLt Dw) (LaurentSeries K₁)) (ArcS Dw K₁) Q = algebraMap _ (ArcS Dw K₁) P` using `⟨P, rfl⟩`. Rewrite using `[arcNum, dif_pos hs]`. Conclude with `GlobalTheory.ArcConst.algebraMap_injective Dw K₁ hs.choose_spec`.
-/
theorem arcNum_of_poly {K₁ : Type} [Field K₁] (P : MvPolynomial (ArcLt Dw) (LaurentSeries K₁)) :
    arcNum (algebraMap _ (ArcS Dw K₁) P) = P := by
  have hs : ∃ Q, algebraMap (MvPolynomial (ArcLt Dw) (LaurentSeries K₁)) (ArcS Dw K₁) Q =
      algebraMap _ (ArcS Dw K₁) P := ⟨P, rfl⟩
  rw [arcNum, dif_pos hs]
  exact GlobalTheory.ArcConst.algebraMap_injective Dw K₁ hs.choose_spec

/- English proof (translation)
Rewrite using `[wchar, Fintype.prod_option]`. Simplify using `[h, ex]`.
-/
theorem wchar_gen {S : Type} [CommRing S] (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (t : Ix Dw → Sˣ)
    (h : ∀ x, t (some x) = 1) : wchar (ex Dw a n) t = (t none : S) ^ n := by
  rw [wchar, Fintype.prod_option]
  simp [h, ex]

set_option maxHeartbeats 1600000 in

/- English proof (translation)
Introduce `F hF t ht Y hY hdet`. Take `⟨φ, ψ, z₁, z₂, tγ, hφC, hφX, hψC, hψX, htγ, htγ', hm1, hm2, hb⟩` from `hBc`. Establish `hϖ : Dv.ϖ ≠ 0` using `Dv.ϖ_irr.ne_zero`. Take `⟨hdomR, -, -, -, hdiv⟩` from `GlobalTheory.T.arcLetterRingOverDVR_polynomial_denominators E H Dw Dv.Tv Dv.ϖ hϖ`. Establish `hdom1` using `GlobalTheory.ArcConst.isDomain Dw K₁`.

Establish `hdom2` using `GlobalTheory.ArcConst.isDomain Dw Dv.Tv.Fr`. Establish `hinj` using `GlobalTheory.ArcConst.algebraMap_injective Dw Dv.Tv.Fr`. Establish `hsec` using `hFs F hF`. Take `⟨P, hP, -⟩` from `GlobalTheory.T.arcFramedPoint_value_isHomogeneous_letters hL hL2 E H Dw l Xo c hev K₁ d a n F hsec`. Establish `e1` using `(GlobalTheory.T.framedPoint_eval_natural_weight_scaling E H Dw l Xo c hev a n F hsec (ArcS Dw K₁)).1 _ φ _ _ hm1`.

Establish `e2` using `(GlobalTheory.T.framedPoint_eval_natural_weight_scaling E H Dw l Xo c hev a n F hsec (ArcSR Dw Dv.Tv.V Dv.ϖ)).1 _ ψ _ _ hm2`. Establish `e3` using `((GlobalTheory.T.framedPoint_eval_natural_weight_scaling E H Dw l Xo c hev a n F hsec (ArcS Dw Dv.Tv.Fr)).2 hdom2).1 tγ _ _ hb`. Rewrite `e3` using `[wchar_gen a n tγ htγ', e1, e2, htγ, ← hP]`. Use `set f := evR Xo c F Dv.yR with hf`. Set `q : ArcLt Dw → MvPolynomial (ArcLt Dw) Dv.Tv.Fr` to `fun x => ∑ l : Fin (Dw.mult x.1), MvPolynomial.X ⟨x.1, x.2.1, l⟩ * MvPolynomial.C (Bm x.1 l x.2.2 * (lam x.1 x.2.2)⁻¹)`.

Take `⟨P₁, hP₁, hco⟩` from `exists_subst Dv.io (φ.toRingHom.comp (algebraMap _ (ArcS Dw K₁))) (algebraMap _ (ArcS Dw Dv.Tv.Fr)) q hφC (fun x => by`. Use `(hφX x).trans ?_` and prove the remaining obligations. Simplify using `only [q, map_sum, map_mul, MvPolynomial.map_X, MvPolynomial.map_C, arcX]) P`. Establish `hγn : γ ^ n ≠ 0` using `pow_ne_zero _ hγ`. Set `P₂ : MvPolynomial (ArcLt Dw) (LaurentSeries Dv.Tv.Fr)` to `MvPolynomial.C (HahnSeries.C (Γ := ℤ) (γ ^ n)⁻¹) * P₁`.

Establish `hP₂ : algebraMap _ (ArcS Dw Dv.Tv.Fr) P₂ = ψ.toRingHom f`. Establish `: algebraMap _ (ArcS Dw Dv.Tv.Fr) P₁ = _` using `hP₁.trans e3`. Simplify using `only [P₂]`. Rewrite using `[map_mul, this, ← mul_assoc, ← map_pow, ← map_mul, ← map_pow, ← map_mul, ← map_pow, ← map_mul, inv_mul_cancel₀ hγn, map_one, map_one, map_one, one_mul]`. Both sides reduce to the same expression.

Establish `hψι : ψ.toRingHom.comp (arcιR Dw Dv.Tv.V Dv.ϖ) = (arcι Dw Dv.Tv.Fr).comp (PowerSeries.map (algebraMap Dv.Tv.V Dv.Tv.Fr))` using `RingHom.ext fun p => hψC p`. Take `⟨N, G, hG⟩` from `hdiv ψ.toRingHom hψι hψX f ⟨P₂, hP₂⟩`. Establish `hψalg : ψ.toRingHom.comp (algebraMap (MvPolynomial (ArcLt Dw) (PowerSeries Dv.Tv.V)) _) = (algebraMap _ (ArcS Dw Dv.Tv.Fr)).comp (MvPolynomial.map ((HahnSeries.ofPowerSeries ℤ Dv.Tv.Fr).comp (PowerSeries.map (algebraMap Dv.Tv.V Dv.Tv.Fr))))`. Use `MvPolynomial.ringHom_ext (fun p => ?_) (fun x => ?_)` and prove the remaining obligations. Simplify using `only [RingHom.comp_apply, MvPolynomial.map_C]`.

Conclude with `hψC p`. Simplify using `only [RingHom.comp_apply, MvPolynomial.map_X]`. Conclude with `hψX x`. Establish `hPG : P₂ * MvPolynomial.C (HahnSeries.ofPowerSeries ℤ Dv.Tv.Fr (PowerSeries.C (R` using `Dv.Tv.Fr) (algebraMap Dv.Tv.V Dv.Tv.Fr Dv.ϖ) * PowerSeries.X)) ^ N = MvPolynomial.map ((HahnSeries.ofPowerSeries ℤ Dv.Tv.Fr).comp (PowerSeries.map (algebraMap Dv.Tv.V Dv.Tv.Fr))) G := by`. Apply `hinj` to reduce the goal to its premises.

Establish `h1` using `congrArg ψ.toRingHom hG`. Establish `h2` using `RingHom.congr_fun hψalg G`. Establish `h3` using `RingHom.congr_fun hψι (PowerSeries.C (R := Dv.Tv.V) Dv.ϖ * PowerSeries.X)`. Simplify using `only [RingHom.comp_apply] at h2 h3`. Rewrite `h1` using `[h2, map_mul, map_pow, h3, ← hP₂, map_mul (PowerSeries.map _), PowerSeries.map_C, PowerSeries.map_X]`.

Rewrite using `[← h1, map_mul, map_pow]`. Both sides reduce to the same expression. Establish `hdet0 : (∏ τ : E →+* ℂ, (Matrix.of fun i k : Fin (Dw.mult τ) => Y ⟨τ, i, k⟩).det) ≠ 0`. Introduce `h0`. Rewrite `hdet` using `[h0, norm_zero]`.

Conclude with `zero_ne_one hdet`. Take `⟨ev, hevC, hevX, hevf⟩` from `GlobalTheory.T.exists_eval_arcLetterRingOverDVR_disc E H Dw Dv.Tv Dv.ϖ Z.K Dv.ιT hϖ Dv.norm_le t Y (Z.S_disc t ht).1 (Z.S_disc t ht).2 hdet0`. Take `⟨hT, hS⟩` from `hevf f N G P₂ hG hPG`. Establish `hbd` using `hRec F hF t ht Y hY hdet ev hevC hevX`. Establish `hq : (fun x => MvPolynomial.eval Y (MvPolynomial.map Dv.ιT (q x))) = frameSub (fun τ => (Bm τ).map Dv.ιT) (fun τ k => Dv.ιT (lam τ k)) Y`.

Use function extensionality and compare the values at `x`. Simplify using `only [q, frameSub, map_sum, map_mul, MvPolynomial.map_X, MvPolynomial.map_C, MvPolynomial.eval_X, MvPolynomial.eval_C, Matrix.map_apply, map_inv₀, Finset.sum_mul, mul_assoc]`. Establish `hterm : ∀ k : ℤ, MvPolynomial.eval Y (MvPolynomial.map Dv.ιT (GlobalTheory.ArcQ.lcoeffPoly P₂ k)) * t ^ k = (Dv.ιT γ ^ n)⁻¹ * (MvPolynomial.eval (frameSub (fun τ => (Bm τ).map Dv.ιT) (fun τ k => Dv.ιT (lam τ k)) Y) (MvPolynomial.map Z.ι (GlobalTheory.ArcQ.lcoeffPoly P k)) * t ^ k …` using `fun k => by`. Simplify using `only [P₂]`. Rewrite using `[lcoeffPoly_const_mul, map_mul, map_mul, MvPolynomial.map_C, MvPolynomial.eval_C, hco, eval_subst, hq, Dv.ιT_io, map_inv₀, map_pow, mul_assoc]`.

Establish `hγK : Dv.ιT γ ^ n ≠ 0` using `pow_ne_zero _ ((map_ne_zero _).2 hγ)`. Rewrite using `[← hP, arcNum_of_poly]`. Simplify using `only [hterm] at hT hS`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `hT.const_mul ‖Dv.ιT γ ^ n‖` as an intermediate fact.

Rewrite `this` using `[mul_zero]`. Use `this.congr fun k => ?_` and prove the remaining obligations. Rewrite using `[← norm_mul, mul_inv_cancel_left₀ hγK]`. Rewrite `hS` using `[tsum_mul_left]`. Rewrite using `[← hS]`.

Conclude with `hbd`.
-/
theorem frameBound_of_cut (hL : Out.Laws) (hL2 : Out.Laws2) {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
    (hev : GlobalTheory.Reg.EvLaws Xo c) {K₁ : Type} [Field K₁] [NumberField K₁] [Algebra c.F K₁] {d : ArcDatum Xo c K₁}
    {w : HeightOneSpectrum (𝓞 K₁)} {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {Fs : Set (Rul Xo c)}
    (hFs : ∀ F ∈ Fs, F ∈ sec Xo c a n) (Z : FinSite K₁ w) (Dv : DvrFrame d w Z) (γ : Dv.Tv.Fr)
    (lam : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Dv.Tv.Fr)
    (Bm : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) Dv.Tv.Fr) (hγ : γ ≠ 0)
    (hBc : BcRigidAt Dv γ lam Bm) (hRec : RecordAt Dv Fs) :
    FrameBound Z (Dv.ιT γ) (fun τ k => Dv.ιT (lam τ k)) (fun τ => (Bm τ).map Dv.ιT) n d Fs := by
  intro F hF t ht Y hY hdet
  obtain ⟨φ, ψ, z₁, z₂, tγ, hφC, hφX, hψC, hψX, htγ, htγ', hm1, hm2, hb⟩ := hBc
  have hϖ : Dv.ϖ ≠ 0 := Dv.ϖ_irr.ne_zero
  obtain ⟨hdomR, -, -, -, hdiv⟩ := GlobalTheory.T.arcLetterRingOverDVR_polynomial_denominators E H Dw Dv.Tv Dv.ϖ hϖ
  have hdom1 := GlobalTheory.ArcConst.isDomain Dw K₁
  have hdom2 := GlobalTheory.ArcConst.isDomain Dw Dv.Tv.Fr
  have hinj := GlobalTheory.ArcConst.algebraMap_injective Dw Dv.Tv.Fr
  have hsec := hFs F hF
  obtain ⟨P, hP, -⟩ := GlobalTheory.T.arcFramedPoint_value_isHomogeneous_letters hL hL2 E H Dw l Xo c hev K₁ d a n F hsec
  have e1 := (GlobalTheory.T.framedPoint_eval_natural_weight_scaling E H Dw l Xo c hev a n F hsec (ArcS Dw K₁)).1 _ φ _ _ hm1
  have e2 := (GlobalTheory.T.framedPoint_eval_natural_weight_scaling E H Dw l Xo c hev a n F hsec (ArcSR Dw Dv.Tv.V Dv.ϖ)).1 _ ψ _ _ hm2
  have e3 := ((GlobalTheory.T.framedPoint_eval_natural_weight_scaling E H Dw l Xo c hev a n F hsec (ArcS Dw Dv.Tv.Fr)).2 hdom2).1 tγ _ _ hb
  rw [wchar_gen a n tγ htγ', e1, e2, htγ, ← hP] at e3
  set f := evR Xo c F Dv.yR with hf
  let q : ArcLt Dw → MvPolynomial (ArcLt Dw) Dv.Tv.Fr := fun x =>
    ∑ l : Fin (Dw.mult x.1), MvPolynomial.X ⟨x.1, x.2.1, l⟩ * MvPolynomial.C (Bm x.1 l x.2.2 * (lam x.1 x.2.2)⁻¹)
  obtain ⟨P₁, hP₁, hco⟩ := exists_subst Dv.io (φ.toRingHom.comp (algebraMap _ (ArcS Dw K₁)))
    (algebraMap _ (ArcS Dw Dv.Tv.Fr)) q hφC (fun x => by
      refine (hφX x).trans ?_
      simp only [q, map_sum, map_mul, MvPolynomial.map_X, MvPolynomial.map_C, arcX]) P
  have hγn : γ ^ n ≠ 0 := pow_ne_zero _ hγ
  let P₂ : MvPolynomial (ArcLt Dw) (LaurentSeries Dv.Tv.Fr) :=
    MvPolynomial.C (HahnSeries.C (Γ := ℤ) (γ ^ n)⁻¹) * P₁
  have hP₂ : algebraMap _ (ArcS Dw Dv.Tv.Fr) P₂ = ψ.toRingHom f := by
    have : algebraMap _ (ArcS Dw Dv.Tv.Fr) P₁ = _ := hP₁.trans e3
    simp only [P₂]
    rw [map_mul, this, ← mul_assoc, ← map_pow, ← map_mul, ← map_pow, ← map_mul, ← map_pow, ← map_mul,
      inv_mul_cancel₀ hγn, map_one, map_one, map_one, one_mul]
    rfl
  have hψι : ψ.toRingHom.comp (arcιR Dw Dv.Tv.V Dv.ϖ) =
      (arcι Dw Dv.Tv.Fr).comp (PowerSeries.map (algebraMap Dv.Tv.V Dv.Tv.Fr)) := RingHom.ext fun p => hψC p
  obtain ⟨N, G, hG⟩ := hdiv ψ.toRingHom hψι hψX f ⟨P₂, hP₂⟩
  have hψalg : ψ.toRingHom.comp (algebraMap (MvPolynomial (ArcLt Dw) (PowerSeries Dv.Tv.V)) _) =
      (algebraMap _ (ArcS Dw Dv.Tv.Fr)).comp (MvPolynomial.map ((HahnSeries.ofPowerSeries ℤ Dv.Tv.Fr).comp
        (PowerSeries.map (algebraMap Dv.Tv.V Dv.Tv.Fr)))) := by
    refine MvPolynomial.ringHom_ext (fun p => ?_) (fun x => ?_)
    · simp only [RingHom.comp_apply, MvPolynomial.map_C]
      exact hψC p
    · simp only [RingHom.comp_apply, MvPolynomial.map_X]
      exact hψX x
  have hPG : P₂ * MvPolynomial.C (HahnSeries.ofPowerSeries ℤ Dv.Tv.Fr (PowerSeries.C (R := Dv.Tv.Fr)
      (algebraMap Dv.Tv.V Dv.Tv.Fr Dv.ϖ) * PowerSeries.X)) ^ N =
      MvPolynomial.map ((HahnSeries.ofPowerSeries ℤ Dv.Tv.Fr).comp
        (PowerSeries.map (algebraMap Dv.Tv.V Dv.Tv.Fr))) G := by
    apply hinj
    have h1 := congrArg ψ.toRingHom hG
    have h2 := RingHom.congr_fun hψalg G
    have h3 := RingHom.congr_fun hψι (PowerSeries.C (R := Dv.Tv.V) Dv.ϖ * PowerSeries.X)
    simp only [RingHom.comp_apply] at h2 h3
    rw [h2, map_mul, map_pow, h3, ← hP₂, map_mul (PowerSeries.map _), PowerSeries.map_C, PowerSeries.map_X] at h1
    rw [← h1, map_mul, map_pow]
    rfl
  have hdet0 : (∏ τ : E →+* ℂ, (Matrix.of fun i k : Fin (Dw.mult τ) => Y ⟨τ, i, k⟩).det) ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hdet
    exact zero_ne_one hdet
  obtain ⟨ev, hevC, hevX, hevf⟩ := GlobalTheory.T.exists_eval_arcLetterRingOverDVR_disc E H Dw Dv.Tv Dv.ϖ Z.K Dv.ιT hϖ Dv.norm_le t Y
    (Z.S_disc t ht).1 (Z.S_disc t ht).2 hdet0
  obtain ⟨hT, hS⟩ := hevf f N G P₂ hG hPG
  have hbd := hRec F hF t ht Y hY hdet ev hevC hevX
  have hq : (fun x => MvPolynomial.eval Y (MvPolynomial.map Dv.ιT (q x))) =
      frameSub (fun τ => (Bm τ).map Dv.ιT) (fun τ k => Dv.ιT (lam τ k)) Y := by
    funext x
    simp only [q, frameSub, map_sum, map_mul, MvPolynomial.map_X, MvPolynomial.map_C, MvPolynomial.eval_X,
      MvPolynomial.eval_C, Matrix.map_apply, map_inv₀, Finset.sum_mul, mul_assoc]
  have hterm : ∀ k : ℤ, MvPolynomial.eval Y (MvPolynomial.map Dv.ιT (GlobalTheory.ArcQ.lcoeffPoly P₂ k)) * t ^ k =
      (Dv.ιT γ ^ n)⁻¹ * (MvPolynomial.eval (frameSub (fun τ => (Bm τ).map Dv.ιT) (fun τ k => Dv.ιT (lam τ k)) Y)
        (MvPolynomial.map Z.ι (GlobalTheory.ArcQ.lcoeffPoly P k)) * t ^ k) := fun k => by
    simp only [P₂]
    rw [lcoeffPoly_const_mul, map_mul, map_mul, MvPolynomial.map_C, MvPolynomial.eval_C, hco, eval_subst, hq,
      Dv.ιT_io, map_inv₀, map_pow, mul_assoc]
  have hγK : Dv.ιT γ ^ n ≠ 0 := pow_ne_zero _ ((map_ne_zero _).2 hγ)
  rw [← hP, arcNum_of_poly]
  simp only [hterm] at hT hS
  refine ⟨?_, ?_⟩
  · have := hT.const_mul ‖Dv.ιT γ ^ n‖
    rw [mul_zero] at this
    refine this.congr fun k => ?_
    rw [← norm_mul, mul_inv_cancel_left₀ hγK]
  · rw [tsum_mul_left] at hS
    rw [← hS]
    exact hbd

/- English proof (translation)
Introduce `hL hL2 E _ _ _ H Dw l Xo c hev K₁ _ _ _ d w a n Fs hFs`. Use `⟨fun Z Dv γ lam Bm hγ _ hBc hRec => frameBound_of_cut hL hL2 hev hFs Z Dv γ lam Bm hγ hBc hRec, ?_⟩` and prove the remaining obligations. Introduce and unpack `vth vη m ⟨Z, Dv, γ, lam, A, Bm, ⟨hγ, hγn⟩, hlam, ⟨hAB, hA⟩, hBc, hRec⟩`. Use `⟨Z, Dv.ιT γ, fun τ k => Dv.ιT (lam τ k), fun τ => (A τ).map Dv.ιT, fun τ => (Bm τ).map Dv.ιT, ⟨(map_ne_zero _).2 hγ, hγn⟩, fun τ k => ⟨(map_ne_zero _).2 (hlam τ k).1, (hlam τ k).2⟩, ⟨fun τ => ?_, fun τ k l => hA τ k l⟩, frameBound_of_cut hL hL2 hev hFs Z Dv γ lam Bm hγ hBc hRec⟩` and prove the remaining obligations. Use `beta_reduce`.

Rewrite using `[← Matrix.map_mul, hAB, Matrix.map_one _ (map_zero _) (map_one _)]`.
-/
theorem frame_of_cut : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), GlobalTheory.Reg.EvLaws Xo c → ∀ (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra c.F K₁] (d : ArcDatum Xo c K₁) (w : HeightOneSpectrum (𝓞 K₁)) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (Fs : Set (Rul Xo c)), (∀ F ∈ Fs, F ∈ sec Xo c a n) → (∀ (Z : FinSite K₁ w) (Dv : DvrFrame d w Z) (γ : Dv.Tv.Fr) (lam : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Dv.Tv.Fr) (Bm : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) Dv.Tv.Fr), γ ≠ 0 → (∀ τ k, lam τ k ≠ 0) → BcRigidAt Dv γ lam Bm → RecordAt Dv Fs → FrameBound Z (Dv.ιT γ) (fun τ k => Dv.ιT (lam τ k)) (fun τ => (Bm τ).map Dv.ιT) n d Fs) ∧ ∀ (vth : ℤ) (vη : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → ℤ) (m : ℕ), FinLocalCutAt d w vth vη m Fs → FinLocalAt d w n vth vη m Fs := by
  intro hL hL2 E _ _ _ H Dw l Xo c hev K₁ _ _ _ d w a n Fs hFs
  refine ⟨fun Z Dv γ lam Bm hγ _ hBc hRec => frameBound_of_cut hL hL2 hev hFs Z Dv γ lam Bm hγ hBc hRec, ?_⟩
  rintro vth vη m ⟨Z, Dv, γ, lam, A, Bm, ⟨hγ, hγn⟩, hlam, ⟨hAB, hA⟩, hBc, hRec⟩
  refine ⟨Z, Dv.ιT γ, fun τ k => Dv.ιT (lam τ k), fun τ => (A τ).map Dv.ιT, fun τ => (Bm τ).map Dv.ιT,
    ⟨(map_ne_zero _).2 hγ, hγn⟩, fun τ k => ⟨(map_ne_zero _).2 (hlam τ k).1, (hlam τ k).2⟩,
    ⟨fun τ => ?_, fun τ k l => hA τ k l⟩, frameBound_of_cut hL hL2 hev hFs Z Dv γ lam Bm hγ hBc hRec⟩
  beta_reduce
  rw [← Matrix.map_mul, hAB, Matrix.map_one _ (map_zero _) (map_one _)]

end GlobalTheory.ArcQ.FrameCut
