import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ReciprocityTheory.ChartRestriction.G

noncomputable section

namespace YPlusSmall

/- English proof (translation)
Simplify using `only [aeval_def, eval₂_eq', Finset.mul_sum]`. Use `Finset.sum_congr rfl fun m hm ↦ ?_` and prove the remaining obligations. Establish `h1 : ∏ p, (c p.1 * v p) ^ m p = (∏ p, c p.1 ^ m p) * ∏ p, v p ^ m p`. Rewrite using `[← Finset.prod_mul_distrib]`. Repeatedly rewrite using `[mul_pow]`.

Establish `h2 : ∏ p : Coord n', c p.1 ^ m p = ∏ k, c k ^ e k`. Rewrite using `[Fintype.prod_sigma]`. Use `Finset.prod_congr rfl fun k _ ↦ ?_` and prove the remaining obligations. Use `show ∏ i, c k ^ m ⟨k, i⟩ = _`. Rewrite using `[Finset.prod_pow_eq_pow_sum, hf m hm k]`.

Rewrite using `[h1, h2]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem aeval_blockScale {κ : Type} [Fintype κ] {n' : κ → ℕ} {A : Type*} [CommRing A]
    {f : MvPolynomial (Coord n') ℤ} {e : κ → ℕ} (hf : Geo.IsMultiHomog (ι := blockIdx n') f e)
    (c : κ → A) (v : Coord n' → A) :
    aeval (fun p ↦ c p.1 * v p) f = (∏ k, c k ^ e k) * aeval v f := by
  simp only [aeval_def, eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  have h1 : ∏ p, (c p.1 * v p) ^ m p = (∏ p, c p.1 ^ m p) * ∏ p, v p ^ m p := by
    rw [← Finset.prod_mul_distrib]
    simp_rw [mul_pow]
  have h2 : ∏ p : Coord n', c p.1 ^ m p = ∏ k, c k ^ e k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ ↦ ?_
    show ∏ i, c k ^ m ⟨k, i⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, hf m hm k]
  rw [h1, h2]
  ring

/- English proof (translation)
Use `congrArg (fun φ : MvPolynomial σ ℤ →ₐ[ℤ] MvPolynomial ι Ω ↦ φ F) (MvPolynomial.comp_aeval (R := ℤ) (f := v) (IsScalarTower.toAlgHom ℤ Ω (MvPolynomial ι Ω)))` as an intermediate fact. Simplify `this.symm` using `[MvPolynomial.algebraMap_eq]`.
-/
theorem aeval_C_comp {σ : Type*} {Ω : Type*} [Field Ω] {ι : Type*} (v : σ → Ω) (F : MvPolynomial σ ℤ) :
    aeval (fun p ↦ (C (v p) : MvPolynomial ι Ω)) F = C (aeval v F) := by
  have := congrArg (fun φ : MvPolynomial σ ℤ →ₐ[ℤ] MvPolynomial ι Ω ↦ φ F)
    (MvPolynomial.comp_aeval (R := ℤ) (f := v) (IsScalarTower.toAlgHom ℤ Ω (MvPolynomial ι Ω)))
  simpa [MvPolynomial.algebraMap_eq] using this.symm

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

/- English proof (translation)
Use `show aeval (fun p : Coord n ↦ (C (y p) * X p.1 : MvPolynomial ι Ω)) f = _`. Rewrite using `[show (fun p : Coord n ↦ (C (y p) * X p.1 : MvPolynomial ι Ω)) = fun p ↦ X p.1 * C (y p) from`. Use function extensionality and compare the values at `fun _ ↦ mul_comm _ _]`. Use `(aeval_blockScale hf (fun k ↦ (X k : MvPolynomial ι Ω)) (fun p ↦ C (y p))).trans ?_` and prove the remaining obligations. Use `erw [aeval_C_comp]`.

Rewrite using `[mul_comm]`.
-/
theorem mConeMap_of_homog {Ω : Type} [Field Ω] {f : MvPolynomial (Coord n) ℤ} {e : ι → ℕ}
    (hf : Geo.IsMultiHomog (ι := blockIdx n) f e) (y : Coord n → Ω) :
    Geo.mConeMap (ι := blockIdx n) y f = C (aeval y f) * ∏ k, X k ^ e k := by
  show aeval (fun p : Coord n ↦ (C (y p) * X p.1 : MvPolynomial ι Ω)) f = _
  rw [show (fun p : Coord n ↦ (C (y p) * X p.1 : MvPolynomial ι Ω)) = fun p ↦ X p.1 * C (y p) from
    funext fun _ ↦ mul_comm _ _]
  refine (aeval_blockScale hf (fun k ↦ (X k : MvPolynomial ι Ω)) (fun p ↦ C (y p))).trans ?_
  erw [aeval_C_comp]
  rw [mul_comm]

/- English proof (translation)
Establish `hle : Submodule.span ℤ {s | ∃ g : MvPolynomial (Coord n') ℤ, Geo.IsMultiHomog (ι` using `blockIdx n') g e ∧ aeval y g = s} ≤ Submodule.map (aeval y : MvPolynomial (Coord n') ℤ →ₐ[ℤ] Ω).toLinearMap (weightedHomogeneousSubmodule ℤ (coordDeg n') e) := by`. Use `Submodule.span_le.mpr ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨g, hg, rfl⟩`. Conclude with `⟨g, (mem_weightedHomogeneousSubmodule _ _ _ _).mpr ((geoMultiHomog_iff g e).mp hg), rfl⟩`. Take `⟨f, hf, hfs⟩` from `hle hs`.

Conclude with `⟨f, (geoMultiHomog_iff f e).mpr ((mem_weightedHomogeneousSubmodule _ _ _ _).mp hf), hfs⟩`.
-/
theorem exists_of_mem_secM {κ : Type} [Fintype κ] [DecidableEq κ] {n' : κ → ℕ} {Ω : Type} [Field Ω]
    (y : Coord n' → Ω) (e : κ → ℕ) {s : Ω} (hs : s ∈ Geo.secM (ι := blockIdx n') y e) :
    ∃ f : MvPolynomial (Coord n') ℤ, Geo.IsMultiHomog (ι := blockIdx n') f e ∧ aeval y f = s := by
  have hle : Submodule.span ℤ {s | ∃ g : MvPolynomial (Coord n') ℤ,
      Geo.IsMultiHomog (ι := blockIdx n') g e ∧ aeval y g = s} ≤
      Submodule.map (aeval y : MvPolynomial (Coord n') ℤ →ₐ[ℤ] Ω).toLinearMap
        (weightedHomogeneousSubmodule ℤ (coordDeg n') e) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨g, hg, rfl⟩
    exact ⟨g, (mem_weightedHomogeneousSubmodule _ _ _ _).mpr ((geoMultiHomog_iff g e).mp hg), rfl⟩
  obtain ⟨f, hf, hfs⟩ := hle hs
  exact ⟨f, (geoMultiHomog_iff f e).mpr ((mem_weightedHomogeneousSubmodule _ _ _ _).mp hf), hfs⟩

/- English proof (translation)
Use `congrArg (fun φ : MvPolynomial σ ℤ →ₐ[ℤ] Ω ↦ φ F) (MvPolynomial.comp_aeval (R := ℤ) (f := fun p ↦ (⟨w p, hw p⟩ : S)) S.val)` as an intermediate fact. Simplify using `only [AlgHom.comp_apply, Subalgebra.coe_val] at this`. Rewrite using `[← this]`. Conclude with `SetLike.coe_mem _`.
-/
theorem aeval_mem_of_forall {σ : Type*} {Ω : Type*} [CommRing Ω] (S : Subalgebra ℤ Ω) (w : σ → Ω)
    (hw : ∀ p, w p ∈ S) (F : MvPolynomial σ ℤ) : aeval w F ∈ S := by
  have := congrArg (fun φ : MvPolynomial σ ℤ →ₐ[ℤ] Ω ↦ φ F)
    (MvPolynomial.comp_aeval (R := ℤ) (f := fun p ↦ (⟨w p, hw p⟩ : S)) S.val)
  simp only [AlgHom.comp_apply, Subalgebra.coe_val] at this
  rw [← this]
  exact SetLike.coe_mem _

/- English proof (translation)
Rewrite using `[eval_map, aeval_def, algebraMap_int_eq]`.
-/
theorem eval_map_int {σ : Type*} (z : σ → ℂ) (F : MvPolynomial σ ℤ) :
    eval z (map (Int.castRingHom ℂ) F) = aeval z F := by
  rw [eval_map, aeval_def, algebraMap_int_eq]

end YPlusSmall

open YPlusSmall in

/- English proof (translation)
Introduce `ι _ _ n P D Ω _ y x' N Ap τ s hR hNa hM hs hsup`. Take `⟨d, hd⟩` from `hForms ι n P D`. Take `⟨g, hg⟩` from `hd d le_rfl`. Use `set e : ι → ℕ := fun k ↦ ((d k : ℤ) + D.deg k).toNat with he_def`. Establish `he : ∀ k, (e k : ℤ) = d k + D.deg k` using `fun k ↦ Int.toNat_of_nonneg (hg.nonneg k)`.

Establish `hgh : ∀ c j, Geo.IsMultiHomog (ι` using `blockIdx n) (g c j) e := by`. Introduce `c j`. Take `⟨δ, hδ, hδe⟩` from `hg.homog c j`. Establish `hδ' : δ = e` using `funext fun k ↦ by have := hδe k; have := he k; omega`. Conclude with `(geoMultiHomog_iff _ _).mpr (hδ' ▸ hδ)`.

Establish `hmh : ∀ c, Geo.IsMultiHomog (ι` using `blockIdx n) (chartMonomial c d) d := fun c ↦ (geoMultiHomog_iff _ _).mpr (isWeightedHomogeneous_chartMonomial c d)`. Establish `hval : ∀ c, P.IsLive c → ∀ j, aeval y (g c j) = aeval y (chartMonomial c d) * x' j`. Introduce `c hc j`. Use `(hR.reads j (g c j) (chartMonomial c d) e d ((geoMultiHomog_iff _ _).mp (hgh c j)) (isWeightedHomogeneous_chartMonomial c d) he).mpr (by rw [hg.value c hc j, mul_comm])` as an intermediate fact. Rewrite using `[this, mul_comm]`.

Take `⟨f, hf, hfs⟩` from `exists_of_mem_secM _ _ hs`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `show ∀ c : (k : ι) → Fin (n k + 1), (∀ k, y ⟨k, c k⟩ ≠ 0) → _`. Introduce `c hc`. Establish `hlive : P.IsLive c`.

Introduce `k hk`. Rewrite `hk` using `[hR.ideal_eq, Geo.mCoordIdeal, RingHom.mem_ker, Geo.mConeMap, aeval_X]`. Conclude with `hc k (C_eq_zero.mp ((mul_eq_zero.mp hk).resolve_right (X_ne_zero _)))`. Rewrite using `[hNa]`. Use `set u : Ω := ∏ k, y ⟨k, c k⟩ ^ (-(D.deg k)) with hu_def`.

Establish `hu : ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * D.deg k)) = u ^ τ`. Rewrite using `[hu_def, ← Finset.prod_pow]`. Use `Finset.prod_congr rfl fun k _ ↦ ?_` and prove the remaining obligations. Rewrite using `[← zpow_natCast, ← zpow_mul]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Establish `hx : ∀ j, u * x' j ∈ Geo.chartRingZ (ι` using `blockIdx n) y c := by`. Introduce `j`. Establish `hmem : aeval (fun p : Coord n ↦ y p / y ⟨p.1, c p.1⟩) (g c j) ∈ Geo.chartRingZ (ι` using `blockIdx n) y c := by`. Rewrite using `[Geo.chartRingZ, Algebra.adjoin_range_eq_range_aeval]`.

Conclude with `⟨g c j, rfl⟩`. Establish `hsc` using `aeval_blockScale (hgh c j) (fun k ↦ (y ⟨k, c k⟩)⁻¹) y`. Rewrite using `[show (fun p : Coord n ↦ y p / y ⟨p.1, c p.1⟩) = fun p ↦ (y ⟨p.1, c p.1⟩)⁻¹ * y p from`. Use function extensionality and compare the values at `fun _ ↦ div_eq_inv_mul _ _, hsc, hval c hlive j] at hmem`. Establish `hm : aeval y (chartMonomial c d) = ∏ k, y ⟨k, c k⟩ ^ d k`.

Simplify using `[chartMonomial, map_prod]`. Establish `hue : u = (∏ k, (y ⟨k, c k⟩)⁻¹ ^ e k) * ∏ k, y ⟨k, c k⟩ ^ d k`. Rewrite using `[hu_def, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun k _ ↦ ?_` and prove the remaining obligations. Rewrite using `[inv_pow, ← zpow_natCast, ← zpow_natCast (y _) (d k), ← zpow_neg, ← zpow_add₀ (hc k)]`.

Use `congr 1`. Use `he k` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite using `[hue, ← hm, mul_assoc]`. Conclude with `hmem`.

Use `set c'' : Option ι → Ω := fun o ↦ o.elim u fun _ ↦ 0 with hc''`. Establish `hsc` using `aeval_blockScale hf c'' (D.plusCoord y x')`. Establish `hprod : ∏ o, c'' o ^ (Pi.single (none : Option ι) τ : Option ι → ℕ) o = u ^ τ`. Simplify using `[Fintype.prod_option, hc'']`. Rewrite `hsc` using `[hprod, hfs]`.

Rewrite using `[hu, mul_comm, ← hsc]`. Use `aeval_mem_of_forall _ _ (fun p ↦ ?_) f` and prove the remaining obligations. Break down `p with ⟨_ | k, i⟩` into its components or cases. Conclude with `hx i`. Use `show 0 * y ⟨k, i⟩ ∈ _`.

Rewrite using `[zero_mul]`. Conclude with `zero_mem _`. Introduce `dg dh G H z hG hH hdeg hGH hz`. Establish `hzP' : z ∈ Geo.mcPts (ι` using `blockIdx n) P.ideal := by rw [hR.ideal_eq]; exact hz`. Establish `hzP : unflatCone z ∈ P.points ℂ` using `(P.mem_mcPts_iff z).mp hzP'`.

Use `choose c hc using hz.1`. Establish `hlc : P.IsLive c` using `fun k hk ↦ hc k (by simpa using hzP'.2 _ hk)`. Use `set zc : Cone n ℂ := unflatCone z with hzc`. Establish `hE : ∀ F, evalCone zc F = eval z (map (Int.castRingHom ℂ) F)` using `fun F ↦ (eval_map_flatCone zc F).symm`. Establish `hmz : evalCone zc (chartMonomial c d) ≠ 0`.

Rewrite using `[evalCone_chartMonomial]`. Conclude with `Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (hc k)`. Establish `hw` using `hConv ι n P D d g hg zc hzP c hmz`. Use `set w := D.joinPt zc (fun j ↦ evalCone zc (g c j)) with hw_def`. Establish `hwm : flatCone w ∈ Geo.mcPts (ι` using `blockIdx D.extSizes) (Geo.mCoordIdeal (ι := blockIdx D.extSizes) (D.plusCoord y x')) := by`.

Rewrite using `[← hR.ext_eq]`. Conclude with `⟨(blockNonzero_unflatCone_iff _).mp hw.1, fun F hF ↦ by`. Rewrite using `[eval_map_flatCone]`. Conclude with `hw.2 F hF⟩`. Take `⟨j, hj⟩` from `Function.ne_iff.mp (hw.1 none)`.

Establish `hj' : eval z (map (Int.castRingHom ℂ) (g c j)) ≠ 0` using `by rw [← hE]; exact hj`. Establish `hind` using `hM j (g c j) (chartMonomial c d) e d (hgh c j) (hmh c) (fun k ↦ by rw [hNa]; exact he k) (hval c hlc j) (flatCone w) hwm`. Establish `hold : D.oldFlat (flatCone w) = z` using `rfl`. Rewrite `hind` using `[hold]`. Express the relevant statement in the definitionally equal form `‖evalCone zc (g c j)‖ * _ * _ = _ at hind`.

Rewrite `hind` using `[hE, mul_assoc]`. Establish `hAp : Ap.h (flatCone w) = ‖eval z (map (Int.castRingHom ℂ) (chartMonomial c d))‖ * N.h z` using `(mul_left_cancel₀ (norm_ne_zero_iff.mpr hj') hind).symm`. Use `set q : Coord D.extSizes → MvPolynomial (Coord n) ℤ := fun p ↦ match p with`. Consider the case `⟨none, j⟩ => g c j`. Consider the case `⟨some k, i⟩ => X ⟨k, i⟩ with hq`.

Establish `hFz : eval z (map (Int.castRingHom ℂ) (aeval q f)) = eval (flatCone w) (map (Int.castRingHom ℂ) f)`. Rewrite using `[eval_map_int, eval_map_int, ← AlgHom.comp_apply, MvPolynomial.comp_aeval]`. Establish `hfun : (fun p ↦ aeval z (q p)) = flatCone w`. Use function extensionality and compare the values at `p`. Break down `p with ⟨_ | k, i⟩` into its components or cases.

Use `show aeval z (g c i) = evalCone zc (g c i)`. Rewrite using `[hE, eval_map_int]`. Use `show aeval z (X ⟨k, i⟩) = z ⟨k, i⟩`. Rewrite using `[aeval_X]`. Rewrite using `[hfun]`.

Use `set m := chartMonomial c d with hm_def`. Establish `hΦ : m ^ τ * G - aeval q f * H ∈ Geo.mCoordIdeal (ι` using `blockIdx n) y := by`. Rewrite using `[Geo.mCoordIdeal, RingHom.mem_ker]`. Use `set c' : Option ι → MvPolynomial ι Ω := fun o ↦ o.elim (∏ k, X k ^ e k) X with hc'`. Establish `hq' : (fun p ↦ Geo.mConeMap (ι` using `blockIdx n) y (q p)) = fun p ↦ c' p.1 * C (D.plusCoord y (fun j ↦ aeval y m * x' j) p) := by`.

Use function extensionality and compare the values at `p`. Break down `p with ⟨_ | k, i⟩` into its components or cases. Use `show Geo.mConeMap (ι := blockIdx n) y (g c i) = (∏ k, X k ^ e k) * C (aeval y m * x' i)`. Rewrite using `[mConeMap_of_homog (hgh c i), hval c hlc i, mul_comm]`. Use `show Geo.mConeMap (ι := blockIdx n) y (X ⟨k, i⟩) = X k * C (y ⟨k, i⟩)`.

Rewrite using `[Geo.mConeMap, aeval_X, mul_comm]`. Establish `hF1 : Geo.mConeMap (ι` using `blockIdx n) y (aeval q f) = (∏ k, (X k : MvPolynomial ι Ω) ^ e k) ^ τ * C (aeval y m ^ τ * s) := by`. Rewrite using `[← AlgHom.comp_apply, MvPolynomial.comp_aeval, hq']`. Use `(aeval_blockScale hf c' (fun p ↦ C (D.plusCoord y (fun j ↦ aeval y m * x' j) p))).trans ?_` and prove the remaining obligations. Use `erw [aeval_C_comp]`.

Establish `hsc` using `aeval_blockScale hf (fun o : Option ι ↦ o.elim (aeval y m) fun _ ↦ (1 : Ω)) (D.plusCoord y x')`. Rewrite using `[show (fun p : Coord D.extSizes ↦ (fun o : Option ι ↦ o.elim (aeval y m) fun _ ↦ (1 : Ω)) p.1 * D.plusCoord y x' p) = D.plusCoord y (fun j ↦ aeval y m * x' j) from by`. Use function extensionality and compare the values at `p`. Break down `p with ⟨_ | k, i⟩` into its components or cases. Both sides reduce to the same expression.

Use `show 1 * y ⟨k, i⟩ = y ⟨k, i⟩`. Rewrite `hsc` using `[one_mul]]`. Rewrite using `[hsc, hfs]`. Use `congr 1`. Simplify using `[Fintype.prod_option, hc']`.

Use `congr 1`. Simplify using `[Fintype.prod_option]`. Establish `hT : (∏ k, (X k : MvPolynomial ι Ω) ^ d k) ^ τ * ∏ k, X k ^ dg k = (∏ k, (X k : MvPolynomial ι Ω) ^ e k) ^ τ * ∏ k, X k ^ dh k`. Simplify using `only [← Finset.prod_pow, ← Finset.prod_mul_distrib, ← pow_mul, ← pow_add]`. Use `Finset.prod_congr rfl fun k _ ↦ congrArg _ ?_` and prove the remaining obligations.

Establish `h1` using `hdeg k`. Establish `h2` using `he k`. Rewrite `h1` using `[hNa]`. Use `zify`. Take the linear combination `h1 - (τ : ℤ) * h2`.

Rewrite using `[map_sub, map_mul, map_mul, map_pow, hF1, mConeMap_of_homog (hmh c), mConeMap_of_homog hG, mConeMap_of_homog hH, hGH]`. Simplify using `only [map_mul, map_pow]`. Take the linear combination `(C (aeval y m) : MvPolynomial ι Ω) ^ τ * C s * C (aeval y H) * hT`. Establish `hzero` using `hz.2 _ hΦ`. Simplify using `only [map_sub, map_mul, map_pow] at hzero`.

Establish `hrel` using `sub_eq_zero.mp hzero`. Establish `hmz' : eval z (map (Int.castRingHom ℂ) m) ≠ 0` using `by rw [← hE]; exact hmz`. Establish `hF : ‖eval z (map (Int.castRingHom ℂ) (aeval q f))‖ ≤ (‖eval z (map (Int.castRingHom ℂ) m)‖ * N.h z) ^ τ`. Rewrite using `[hFz, ← hAp]`. Conclude with `hsup f hf hfs (flatCone w) hwm`.

Establish `hpos : 0 < ‖eval z (map (Int.castRingHom ℂ) m)‖ ^ τ` using `pow_pos (norm_pos_iff.mpr hmz') τ`. Use `le_of_mul_le_mul_right ?_ hpos` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[norm_mul, norm_pow, mul_comm]`. Use `_ = ‖eval z (map (Int.castRingHom ℂ) (aeval q f))‖ * ‖eval z (map (Int.castRingHom ℂ) H)‖ := by`.

Rewrite using `[hrel, norm_mul]`. Use `_ ≤ (‖eval z (map (Int.castRingHom ℂ) m)‖ * N.h z) ^ τ * ‖eval z (map (Int.castRingHom ℂ) H)‖ := mul_le_mul_of_nonneg_right hF (norm_nonneg _)`. Use `_ = ‖eval z (map (Int.castRingHom ℂ) H)‖ * N.h z ^ τ * ‖eval z (map (Int.castRingHom ℂ) m)‖ ^ τ := by`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem YPlusSmall.proof (hForms : ChartFormsAlt.Statement) (hConv : ConePointsConverse.Statement) :
    YPlusSmall.Statement := by
  intro ι _ _ n P D Ω _ y x' N Ap τ s hR hNa hM hs hsup
  obtain ⟨d, hd⟩ := hForms ι n P D
  obtain ⟨g, hg⟩ := hd d le_rfl
  set e : ι → ℕ := fun k ↦ ((d k : ℤ) + D.deg k).toNat with he_def
  have he : ∀ k, (e k : ℤ) = d k + D.deg k := fun k ↦ Int.toNat_of_nonneg (hg.nonneg k)
  have hgh : ∀ c j, Geo.IsMultiHomog (ι := blockIdx n) (g c j) e := by
    intro c j
    obtain ⟨δ, hδ, hδe⟩ := hg.homog c j
    have hδ' : δ = e := funext fun k ↦ by have := hδe k; have := he k; omega
    exact (geoMultiHomog_iff _ _).mpr (hδ' ▸ hδ)
  have hmh : ∀ c, Geo.IsMultiHomog (ι := blockIdx n) (chartMonomial c d) d := fun c ↦
    (geoMultiHomog_iff _ _).mpr (isWeightedHomogeneous_chartMonomial c d)
  have hval : ∀ c, P.IsLive c → ∀ j,
      aeval y (g c j) = aeval y (chartMonomial c d) * x' j := by
    intro c hc j
    have := (hR.reads j (g c j) (chartMonomial c d) e d ((geoMultiHomog_iff _ _).mp (hgh c j))
      (isWeightedHomogeneous_chartMonomial c d) he).mpr (by rw [hg.value c hc j, mul_comm])
    rw [this, mul_comm]
  obtain ⟨f, hf, hfs⟩ := exists_of_mem_secM _ _ hs
  refine ⟨?_, ?_⟩
  ·
    show ∀ c : (k : ι) → Fin (n k + 1), (∀ k, y ⟨k, c k⟩ ≠ 0) → _
    intro c hc
    have hlive : P.IsLive c := by
      intro k hk
      rw [hR.ideal_eq, Geo.mCoordIdeal, RingHom.mem_ker, Geo.mConeMap, aeval_X] at hk
      exact hc k (C_eq_zero.mp ((mul_eq_zero.mp hk).resolve_right (X_ne_zero _)))
    rw [hNa]
    set u : Ω := ∏ k, y ⟨k, c k⟩ ^ (-(D.deg k)) with hu_def
    have hu : ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * D.deg k)) = u ^ τ := by
      rw [hu_def, ← Finset.prod_pow]
      refine Finset.prod_congr rfl fun k _ ↦ ?_
      rw [← zpow_natCast, ← zpow_mul]
      congr 1
      ring
    have hx : ∀ j, u * x' j ∈ Geo.chartRingZ (ι := blockIdx n) y c := by
      intro j
      have hmem : aeval (fun p : Coord n ↦ y p / y ⟨p.1, c p.1⟩) (g c j) ∈
          Geo.chartRingZ (ι := blockIdx n) y c := by
        rw [Geo.chartRingZ, Algebra.adjoin_range_eq_range_aeval]
        exact ⟨g c j, rfl⟩
      have hsc := aeval_blockScale (hgh c j) (fun k ↦ (y ⟨k, c k⟩)⁻¹) y
      rw [show (fun p : Coord n ↦ y p / y ⟨p.1, c p.1⟩) = fun p ↦ (y ⟨p.1, c p.1⟩)⁻¹ * y p from
        funext fun _ ↦ div_eq_inv_mul _ _, hsc, hval c hlive j] at hmem
      have hm : aeval y (chartMonomial c d) = ∏ k, y ⟨k, c k⟩ ^ d k := by
        simp [chartMonomial, map_prod]
      have hue : u = (∏ k, (y ⟨k, c k⟩)⁻¹ ^ e k) * ∏ k, y ⟨k, c k⟩ ^ d k := by
        rw [hu_def, ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun k _ ↦ ?_
        rw [inv_pow, ← zpow_natCast, ← zpow_natCast (y _) (d k), ← zpow_neg, ← zpow_add₀ (hc k)]
        congr 1
        have := he k
        omega
      rw [hue, ← hm, mul_assoc]
      exact hmem
    set c'' : Option ι → Ω := fun o ↦ o.elim u fun _ ↦ 0 with hc''
    have hsc := aeval_blockScale hf c'' (D.plusCoord y x')
    have hprod : ∏ o, c'' o ^ (Pi.single (none : Option ι) τ : Option ι → ℕ) o = u ^ τ := by
      simp [Fintype.prod_option, hc'']
    rw [hprod, hfs] at hsc
    rw [hu, mul_comm, ← hsc]
    refine aeval_mem_of_forall _ _ (fun p ↦ ?_) f
    rcases p with ⟨_ | k, i⟩
    · exact hx i
    · show 0 * y ⟨k, i⟩ ∈ _
      rw [zero_mul]
      exact zero_mem _
  ·
    intro dg dh G H z hG hH hdeg hGH hz
    have hzP' : z ∈ Geo.mcPts (ι := blockIdx n) P.ideal := by rw [hR.ideal_eq]; exact hz
    have hzP : unflatCone z ∈ P.points ℂ := (P.mem_mcPts_iff z).mp hzP'
    choose c hc using hz.1
    have hlc : P.IsLive c := fun k hk ↦ hc k (by simpa using hzP'.2 _ hk)
    set zc : Cone n ℂ := unflatCone z with hzc
    have hE : ∀ F, evalCone zc F = eval z (map (Int.castRingHom ℂ) F) :=
      fun F ↦ (eval_map_flatCone zc F).symm
    have hmz : evalCone zc (chartMonomial c d) ≠ 0 := by
      rw [evalCone_chartMonomial]
      exact Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (hc k)
    have hw := hConv ι n P D d g hg zc hzP c hmz
    set w := D.joinPt zc (fun j ↦ evalCone zc (g c j)) with hw_def
    have hwm : flatCone w ∈ Geo.mcPts (ι := blockIdx D.extSizes)
        (Geo.mCoordIdeal (ι := blockIdx D.extSizes) (D.plusCoord y x')) := by
      rw [← hR.ext_eq]
      exact ⟨(blockNonzero_unflatCone_iff _).mp hw.1, fun F hF ↦ by
        rw [eval_map_flatCone]; exact hw.2 F hF⟩
    obtain ⟨j, hj⟩ := Function.ne_iff.mp (hw.1 none)
    have hj' : eval z (map (Int.castRingHom ℂ) (g c j)) ≠ 0 := by rw [← hE]; exact hj
    have hind := hM j (g c j) (chartMonomial c d) e d (hgh c j) (hmh c)
      (fun k ↦ by rw [hNa]; exact he k) (hval c hlc j) (flatCone w) hwm
    have hold : D.oldFlat (flatCone w) = z := rfl
    rw [hold] at hind
    change ‖evalCone zc (g c j)‖ * _ * _ = _ at hind
    rw [hE, mul_assoc] at hind
    have hAp : Ap.h (flatCone w) = ‖eval z (map (Int.castRingHom ℂ) (chartMonomial c d))‖ * N.h z :=
      (mul_left_cancel₀ (norm_ne_zero_iff.mpr hj') hind).symm

    set q : Coord D.extSizes → MvPolynomial (Coord n) ℤ := fun p ↦ match p with
      | ⟨none, j⟩ => g c j
      | ⟨some k, i⟩ => X ⟨k, i⟩ with hq
    have hFz : eval z (map (Int.castRingHom ℂ) (aeval q f)) =
        eval (flatCone w) (map (Int.castRingHom ℂ) f) := by
      rw [eval_map_int, eval_map_int, ← AlgHom.comp_apply, MvPolynomial.comp_aeval]
      have hfun : (fun p ↦ aeval z (q p)) = flatCone w := by
        funext p
        rcases p with ⟨_ | k, i⟩
        · show aeval z (g c i) = evalCone zc (g c i)
          rw [hE, eval_map_int]
        · show aeval z (X ⟨k, i⟩) = z ⟨k, i⟩
          rw [aeval_X]
      rw [hfun]

    set m := chartMonomial c d with hm_def
    have hΦ : m ^ τ * G - aeval q f * H ∈ Geo.mCoordIdeal (ι := blockIdx n) y := by
      rw [Geo.mCoordIdeal, RingHom.mem_ker]
      set c' : Option ι → MvPolynomial ι Ω := fun o ↦ o.elim (∏ k, X k ^ e k) X with hc'
      have hq' : (fun p ↦ Geo.mConeMap (ι := blockIdx n) y (q p)) =
          fun p ↦ c' p.1 * C (D.plusCoord y (fun j ↦ aeval y m * x' j) p) := by
        funext p
        rcases p with ⟨_ | k, i⟩
        · show Geo.mConeMap (ι := blockIdx n) y (g c i) = (∏ k, X k ^ e k) * C (aeval y m * x' i)
          rw [mConeMap_of_homog (hgh c i), hval c hlc i, mul_comm]
        · show Geo.mConeMap (ι := blockIdx n) y (X ⟨k, i⟩) = X k * C (y ⟨k, i⟩)
          rw [Geo.mConeMap, aeval_X, mul_comm]
      have hF1 : Geo.mConeMap (ι := blockIdx n) y (aeval q f) =
          (∏ k, (X k : MvPolynomial ι Ω) ^ e k) ^ τ * C (aeval y m ^ τ * s) := by
        rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval, hq']
        refine (aeval_blockScale hf c' (fun p ↦ C (D.plusCoord y (fun j ↦ aeval y m * x' j) p))).trans ?_
        erw [aeval_C_comp]
        have hsc := aeval_blockScale hf (fun o : Option ι ↦ o.elim (aeval y m) fun _ ↦ (1 : Ω))
          (D.plusCoord y x')
        rw [show (fun p : Coord D.extSizes ↦ (fun o : Option ι ↦ o.elim (aeval y m) fun _ ↦ (1 : Ω)) p.1 *
            D.plusCoord y x' p) = D.plusCoord y (fun j ↦ aeval y m * x' j) from by
          funext p; rcases p with ⟨_ | k, i⟩
          · rfl
          · show 1 * y ⟨k, i⟩ = y ⟨k, i⟩
            rw [one_mul]] at hsc
        rw [hsc, hfs]
        congr 1
        · simp [Fintype.prod_option, hc']
        · congr 1
          simp [Fintype.prod_option]
      have hT : (∏ k, (X k : MvPolynomial ι Ω) ^ d k) ^ τ * ∏ k, X k ^ dg k =
          (∏ k, (X k : MvPolynomial ι Ω) ^ e k) ^ τ * ∏ k, X k ^ dh k := by
        simp only [← Finset.prod_pow, ← Finset.prod_mul_distrib, ← pow_mul, ← pow_add]
        refine Finset.prod_congr rfl fun k _ ↦ congrArg _ ?_
        have h1 := hdeg k
        have h2 := he k
        rw [hNa] at h1
        zify
        linear_combination h1 - (τ : ℤ) * h2
      rw [map_sub, map_mul, map_mul, map_pow, hF1, mConeMap_of_homog (hmh c),
        mConeMap_of_homog hG, mConeMap_of_homog hH, hGH]
      simp only [map_mul, map_pow]
      linear_combination (C (aeval y m) : MvPolynomial ι Ω) ^ τ * C s * C (aeval y H) * hT
    have hzero := hz.2 _ hΦ
    simp only [map_sub, map_mul, map_pow] at hzero
    have hrel := sub_eq_zero.mp hzero
    have hmz' : eval z (map (Int.castRingHom ℂ) m) ≠ 0 := by rw [← hE]; exact hmz
    have hF : ‖eval z (map (Int.castRingHom ℂ) (aeval q f))‖ ≤
        (‖eval z (map (Int.castRingHom ℂ) m)‖ * N.h z) ^ τ := by
      rw [hFz, ← hAp]
      exact hsup f hf hfs (flatCone w) hwm
    have hpos : 0 < ‖eval z (map (Int.castRingHom ℂ) m)‖ ^ τ := pow_pos (norm_pos_iff.mpr hmz') τ
    refine le_of_mul_le_mul_right ?_ hpos
    calc ‖eval z (map (Int.castRingHom ℂ) G)‖ * ‖eval z (map (Int.castRingHom ℂ) m)‖ ^ τ
        = ‖eval z (map (Int.castRingHom ℂ) m) ^ τ * eval z (map (Int.castRingHom ℂ) G)‖ := by
          rw [norm_mul, norm_pow, mul_comm]
      _ = ‖eval z (map (Int.castRingHom ℂ) (aeval q f))‖ * ‖eval z (map (Int.castRingHom ℂ) H)‖ := by
          rw [hrel, norm_mul]
      _ ≤ (‖eval z (map (Int.castRingHom ℂ) m)‖ * N.h z) ^ τ * ‖eval z (map (Int.castRingHom ℂ) H)‖ :=
          mul_le_mul_of_nonneg_right hF (norm_nonneg _)
      _ = ‖eval z (map (Int.castRingHom ℂ) H)‖ * N.h z ^ τ * ‖eval z (map (Int.castRingHom ℂ) m)‖ ^ τ := by
          ring

end

end GroundTheory.Heights₂.Heights
