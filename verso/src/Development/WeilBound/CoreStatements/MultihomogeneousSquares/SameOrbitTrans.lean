import Development.WeilBound.CoreStatements.MultihomogeneousSquares.SingSt
import Development.WeilBound.CoreStatements.FlagImmersions.SumFundOnRoot
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MemAbLocusIff
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexPointsIffCentresStatement

noncomputable section

namespace SquareStatements.Sing

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB
open GroundTheory.Heights₂.Heights.LowerBoundFree (valAt)
open scoped ComplexOrder

/- English proof (translation)
Assemble the required witnesses or components as `⟨h, 1, map_one _, map_one _⟩`.
-/
theorem valAt_one {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    {z : Spec (CommRingCat.of ℂ) ⟶ X} (h : GlobalTheory.CompanionTheory.Ar.genPt ξ ⤳ centre z) : ValAt ξ z 1 (1 : ℂ) :=
  ⟨h, 1, map_one _, map_one _⟩

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using valAt_one h`. Consider the case `insert m s hm ih`. Rewrite using `[Finset.prod_insert hm, Finset.prod_insert hm]`. Conclude with `CoordModel.valAt_mul (hv m (Finset.mem_insert_self _ _)) (ih fun m' h' => hv m' (Finset.mem_insert_of_mem h'))`.
-/
theorem valAt_prod {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    {z : Spec (CommRingCat.of ℂ) ⟶ X} (h : GlobalTheory.CompanionTheory.Ar.genPt ξ ⤳ centre z) {I : Type} (s : Finset I) {a : I → Ω}
    {u : I → ℂ} (hv : ∀ m ∈ s, ValAt ξ z (a m) (u m)) : ValAt ξ z (∏ m ∈ s, a m) (∏ m ∈ s, u m) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using valAt_one h
  | insert m s hm ih =>
    rw [Finset.prod_insert hm, Finset.prod_insert hm]
    exact CoordModel.valAt_mul (hv m (Finset.mem_insert_self _ _)) (ih fun m' h' => hv m' (Finset.mem_insert_of_mem h'))

/- English proof (translation)
Take `⟨c, hc, rfl⟩` from `h`. Conclude with `⟨fun k => (c k)⁻¹, fun k => inv_ne_zero (hc k), funext fun p => (inv_mul_cancel_left₀ (hc p.1) _).symm⟩`.
-/
theorem sameOrbit_symm {K : Type} {ι : K → Type} {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') : SameOrbit z' z := by
  obtain ⟨c, hc, rfl⟩ := h
  exact ⟨fun k => (c k)⁻¹, fun k => inv_ne_zero (hc k), funext fun p => (inv_mul_cancel_left₀ (hc p.1) _).symm⟩

/- English proof (translation)
Take `⟨c, hc, rfl⟩` from `h`. Take `⟨c', hc', rfl⟩` from `h'`. Conclude with `⟨fun k => c k * c' k, fun k => mul_ne_zero (hc k) (hc' k), funext fun p => (mul_assoc _ _ _).symm⟩`.
-/
theorem sameOrbit_trans {K : Type} {ι : K → Type} {z z' z'' : (Σ k, ι k) → ℂ} (h : SameOrbit z z')
    (h' : SameOrbit z' z'') : SameOrbit z z'' := by
  obtain ⟨c, hc, rfl⟩ := h
  obtain ⟨c', hc', rfl⟩ := h'
  exact ⟨fun k => c k * c' k, fun k => mul_ne_zero (hc k) (hc' k), funext fun p => (mul_assoc _ _ _).symm⟩

/- English proof (translation)
Use `choose u hu hu' using fun m => (hs m).2.2 c hc`. Establish `hy : ∀ k, y ⟨k, c k⟩ ≠ 0` using `fun k => (hw.2 k (c k) (IsUnit.mk0 _ (hc k))).1`. Establish `hn : ∀ k, ‖w ⟨k, c k⟩‖ ≠ 0` using `fun k => norm_ne_zero_iff.2 (hc k)`. Establish `hA : ∀ m, 0 < (A m).h w` using `fun m => (A m).pos w fun k => ⟨c k, hc k⟩`. Establish `hP : ∀ a : K → ℤ, (∏ k, ‖w ⟨k, c k⟩‖ ^ a k) ≠ 0` using `fun a => Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hn k)`.

Establish `hu0 : ∀ m, ‖u m‖ ≠ 0` using `fun m h0 => by`. Use `hu' m` as an intermediate fact. Rewrite `this` using `[h0, zero_mul]`. Conclude with `(mul_pos (hμ m) (hA m)).ne' this`. Establish `hl : ∀ a : K → ℤ, Real.log (∏ k, ‖w ⟨k, c k⟩‖ ^ a k) = ∑ k, (a k : ℝ) * Real.log ‖w ⟨k, c k⟩‖` using `fun a => by`.

Rewrite using `[Real.log_prod fun k _ => zpow_ne_zero _ (hn k)]`. Simplify using `only [Real.log_zpow]`. Use `⟨∏ m ∈ s, u m, ?_, ?_⟩` and prove the remaining obligations. Use `valAt_prod hz s fun m _ => hu m using 1` and compare the differences between its conclusion and the goal. Rewrite using `[Finset.prod_div_distrib, Finset.prod_mul_distrib, Finset.prod_comm]`.

Establish `: ∀ k, ∏ m ∈ s, y ⟨k, c k⟩ ^ (A m).a k = (y ⟨k, c k⟩ ^ dy k)⁻¹` using `fun k => by`. Rewrite using `[Chg.prod_zpow_sum s (hy k), hdy, Pi.neg_apply, Finset.sum_apply, _root_.zpow_neg, inv_inv]`. Simplify using `only [this, Finset.prod_inv_distrib]`. Rewrite using `[div_eq_mul_inv, mul_inv, inv_inv]`. Expand and normalize the polynomial expressions, which then agree.

Establish `h1 : ∀ m, Real.log ((A m).h w) = Real.log ‖u m‖ + ∑ k, ((A m).a k : ℝ) * Real.log ‖w ⟨k, c k⟩‖ - Real.log (μ m)` using `fun m => by`. Use `congrArg Real.log (hu' m)` as an intermediate fact. Rewrite `this` using `[Real.log_mul (hμ m).ne' (hA m).ne', Real.log_mul (hu0 m) (hP _), hl]`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[norm_prod, Real.log_prod fun m _ => hu0 m, hl, hdy]`.

Simplify using `only [h1, Finset.sum_sub_distrib, Finset.sum_add_distrib, Pi.neg_apply, Finset.sum_apply, Int.cast_neg, Int.cast_sum, neg_mul, Finset.sum_neg_distrib, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm (s := s)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem prod_secNorm {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}
    {z : Spec (CommRingCat.of ℂ) ⟶ X} (hz : GlobalTheory.CompanionTheory.Ar.genPt ξ ⤳ centre z) {w : (Σ k, J k) → ℂ}
    (hw : CoordsAt ξ y z w) {I : Type} (s : Finset I) (A : I → HermLine J) (e t : I → Ω) (μ : I → ℝ) (dy : K → ℤ)
    (hs : ∀ m, SecNorm ξ y (A m) (e m) z w (t m) (μ m)) (hμ : ∀ m, 0 < μ m) (hdy : dy = -∑ m ∈ s, (A m).a)
    (c : ∀ k, J k) (hc : ∀ k, w ⟨k, c k⟩ ≠ 0) :
    ∃ U : ℂ, ValAt ξ z ((∏ m ∈ s, t m) * (∏ m ∈ s, e m)⁻¹ * ∏ k, y ⟨k, c k⟩ ^ dy k) U ∧
      -∑ m ∈ s, Real.log ((A m).h w) =
        ∑ m ∈ s, Real.log (μ m) - Real.log ‖U‖ + Real.log (∏ k, ‖w ⟨k, c k⟩‖ ^ dy k) := by
  choose u hu hu' using fun m => (hs m).2.2 c hc
  have hy : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => (hw.2 k (c k) (IsUnit.mk0 _ (hc k))).1
  have hn : ∀ k, ‖w ⟨k, c k⟩‖ ≠ 0 := fun k => norm_ne_zero_iff.2 (hc k)
  have hA : ∀ m, 0 < (A m).h w := fun m => (A m).pos w fun k => ⟨c k, hc k⟩
  have hP : ∀ a : K → ℤ, (∏ k, ‖w ⟨k, c k⟩‖ ^ a k) ≠ 0 := fun a =>
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hn k)
  have hu0 : ∀ m, ‖u m‖ ≠ 0 := fun m h0 => by
    have := hu' m
    rw [h0, zero_mul] at this
    exact (mul_pos (hμ m) (hA m)).ne' this
  have hl : ∀ a : K → ℤ, Real.log (∏ k, ‖w ⟨k, c k⟩‖ ^ a k) = ∑ k, (a k : ℝ) * Real.log ‖w ⟨k, c k⟩‖ := fun a => by
    rw [Real.log_prod fun k _ => zpow_ne_zero _ (hn k)]
    simp only [Real.log_zpow]
  refine ⟨∏ m ∈ s, u m, ?_, ?_⟩
  · convert valAt_prod hz s fun m _ => hu m using 1
    rw [Finset.prod_div_distrib, Finset.prod_mul_distrib, Finset.prod_comm]
    have : ∀ k, ∏ m ∈ s, y ⟨k, c k⟩ ^ (A m).a k = (y ⟨k, c k⟩ ^ dy k)⁻¹ := fun k => by
      rw [Chg.prod_zpow_sum s (hy k), hdy, Pi.neg_apply, Finset.sum_apply, _root_.zpow_neg, inv_inv]
    simp only [this, Finset.prod_inv_distrib]
    rw [div_eq_mul_inv, mul_inv, inv_inv]
    ring
  · have h1 : ∀ m, Real.log ((A m).h w) =
        Real.log ‖u m‖ + ∑ k, ((A m).a k : ℝ) * Real.log ‖w ⟨k, c k⟩‖ - Real.log (μ m) := fun m => by
      have := congrArg Real.log (hu' m)
      rw [Real.log_mul (hμ m).ne' (hA m).ne', Real.log_mul (hu0 m) (hP _), hl] at this
      linarith
    rw [norm_prod, Real.log_prod fun m _ => hu0 m, hl, hdy]
    simp only [h1, Finset.sum_sub_distrib, Finset.sum_add_distrib, Pi.neg_apply, Finset.sum_apply, Int.cast_neg,
      Int.cast_sum, neg_mul, Finset.sum_neg_distrib, Finset.sum_mul]
    rw [Finset.sum_comm (s := s)]
    ring

/- English proof (translation)
Rewrite using `[← Fintype.prod_subtype_mul_prod_subtype (fun k => ∀ p', M.blk p' ≠ some k), mul_comm]`. Use `congr 1`. Establish `h1 : ∀ k : {k // ¬ ∀ p', M.blk p' ≠ some k}, f k.1 ^ M.dy p k.1 = if M.blk p = some k.1 then f k.1 else 1` using `fun k => by`. Rewrite using `[FlagModel.dy, dif_neg k.2]`. Apply the tactic sequence `split_ifs <;> simp`.

Simplify using `only [h1]`. Break down `hb : M.blk p with _ | k₀` into its components or cases. Simplify using the standard rewrite rules. Rewrite using `[Finset.prod_eq_single (⟨k₀, fun h => h p hb⟩ : {k // ¬ ∀ p', M.blk p' ≠ some k})]`. Simplify using the standard rewrite rules.

Introduce `k _ hk`. Conclude with `if_neg fun e => hk (Subtype.ext (Option.some.inj e).symm)`. Simplify using the standard rewrite rules. Use `Finset.prod_congr (by ext; simp) fun k _ => ?_` and prove the remaining obligations. Rewrite using `[FlagModel.dy, dif_pos k.2]`.
-/
theorem prod_dy {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
    {Ψ : Type} {N j : ℕ} (M : FlagModel y Ψ N j) (p : Ψ × Fin N) {R : Type} [Field R] (f : K → R) :
    ∏ k, f k ^ M.dy p k = (M.blk p).elim 1 f * ∏ k' : NonPluckerBlocks M.blk, f k'.1 ^ (-M.b p k') := by
  classical
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun k => ∀ p', M.blk p' ≠ some k), mul_comm]
  congr 1
  · have h1 : ∀ k : {k // ¬ ∀ p', M.blk p' ≠ some k}, f k.1 ^ M.dy p k.1 = if M.blk p = some k.1 then f k.1 else 1 :=
      fun k => by
        rw [FlagModel.dy, dif_neg k.2]
        split_ifs <;> simp
    simp only [h1]
    rcases hb : M.blk p with _ | k₀
    · simp
    · rw [Finset.prod_eq_single (⟨k₀, fun h => h p hb⟩ : {k // ¬ ∀ p', M.blk p' ≠ some k})]
      · simp
      · intro k _ hk
        exact if_neg fun e => hk (Subtype.ext (Option.some.inj e).symm)
      · simp
  · refine Finset.prod_congr (by ext; simp) fun k _ => ?_
    rw [FlagModel.dy, dif_pos k.2]

/- English proof (translation)
Introduce `E _ _ _ H D l Xo c Y S _ K _ ι _ Φ _ y M 𝔐 tie n BM 𝔐' Fl xdeg e sing hBM htot hsd hho a w hw x hx horb`. Take `⟨τ, i⟩` from `a`. Take `⟨⟨pr, j, hov, -, hV, hbW, hbO⟩, -, hdy, he⟩` from `htot`. Establish `hT : Tot tie 𝔐' Fl pr j` using `⟨hov, hV, hbW, hbO⟩`. Take `⟨z, -, hz⟩` from `(GlobalTheory.T.complex_points_iff_centres 𝔐'.X Φ 𝔐'.ξ K ι y 𝔐'.tie w).1 hw`.

Take `⟨q, hq⟩` from `BM.O_cover x`. Establish `hF` using `BM.isFrame q`. Establish `hC0` using `fun w' hw' => h0 E H D l Xo c Y S K ι Φ y M 𝔐 𝔐' pr j z w' hov hw'`. Establish `hl : CoordsAt 𝔐.ξ M.x (z ≫ pr) (BM.Rb.lift x x)` using `Chg.coordsAt_orbit (hC0 w hz).1 (sameOrbit_symm horb)`. Establish `hgood : ∀ w', CoordsAt 𝔐'.ξ y z w' → M.GoodAt (BM.F q) (mCoordIdeal (basePart M.blk w'))` using `fun w' hw' => by`.

Rewrite using `[← ptIdeal_centre (hC0 w' hw').1 (𝔐.all _), ptIdeal_centre hl (𝔐.all _)]`. Conclude with `BM.good q x hq`. Establish `hint : 𝔐'.Interior z` using `(hC0 w hz).2.1.2 ((hBM.interior x _ hl).1 hx)`. Take `⟨hfW, hfO⟩` from `BM.frames_of_tie tie hq hl τ`. Take `⟨B, h, hA⟩` from `h1 E H D l Xo c Y S K ι Φ y M 𝔐 tie 𝔐' Fl pr j z (BM.F q) τ hT hF hfW hfO`.

Take `⟨hGb, hGp⟩` from `BM.G_pos q τ x ⟨hq, hx⟩`. Take `⟨hμ, hsum⟩` from `h4 D.p D.q _ h hGb hGp hA.2.2.2.1 hA.2.2.2.2.1`. Take `⟨hdF, hsum⟩` from `hsum i`. Establish `hsec : ∀ w', CoordsAt 𝔐'.ξ y z w' → ∀ m, SecNorm 𝔐'.ξ y (sing (τ, m)) (e (τ, m)) z w' (B (col D.p D.q m) (col D.p D.q m)) (mu D.p D.q (hᴴ * BM.G q τ x * h) m)` using `fun w' hw' m => by`. Use `hho (τ, m) z w' hw' hint` as an intermediate fact.

Distinguish the cases in `hm : (m : ℕ) < D.p`. Establish `e2 : HodgeCpt.rootIdx D (τ, m) = ⟨.inl τ, ⟨m, hm⟩⟩` using `dif_pos hm`. Establish `e3 : HodgeCpt.rootSgn D (τ, m) = 1` using `if_pos hm`. Rewrite `this` using `[e2, e3]`. Establish `h3` using `this _ _ (hW E H D l Xo c Y S K ι Φ y M 𝔐 tie 𝔐' Fl pr j z (BM.F q) τ B h _ hT hF hfW hA hGb hGp hint (hBM.gramW q τ x ⟨hq, hx⟩ _ hl) ⟨m, hm⟩)`.

Rewrite `h3` using `[zpow_one, zpow_one]`. Rewrite using `[col, mu, dif_pos hm, if_pos hm]`. Conclude with `h3`. Establish `hm2` using `m.2`. Establish `e2 : HodgeCpt.rootIdx D (τ, m) = ⟨.inr τ, ⟨D.p + D.q - 1 - m, by show _ < D.q; omega⟩⟩` using `dif_neg hm`.

Establish `e3 : HodgeCpt.rootSgn D (τ, m) = -1` using `if_neg hm`. Rewrite `this` using `[e2, e3]`. Establish `h3` using `this _ _ (hO E H D l Xo c Y S K ι Φ y M 𝔐 tie 𝔐' Fl pr j z (BM.F q) τ B h _ hT hF hfO hA hGb hGp hint (hBM.gramO q τ x ⟨hq, hx⟩ _ hl) ⟨D.p + D.q - 1 - m, by omega⟩)`. Rewrite `h3` using `[_root_.zpow_neg_one, _root_.zpow_neg_one, inv_inv]`. Establish `e4 : (⟨D.p + D.q - 1 - m, by omega⟩ : Fin D.q).rev = ⟨m - D.p, by omega⟩` using `Fin.ext (by simp only [Fin.val_rev]; omega)`.

Rewrite `h3` using `[e4]`. Rewrite using `[col, mu, dif_neg hm, if_neg hm]`. Conclude with `h3`. Establish `hdy' : M.dy (τ, i) = -∑ m ∈ Finset.Iic i, (sing (τ, m)).a` using `by simp only [hsd]; exact hdy τ i`. Establish `hdeg : (Top.combLine sing (Cmp.fundOnRoot (τ, i))).a = (BM.hom (τ, i)).a` using `by show ∑ r, _ • (sing r).a = _`.

Rewrite using `[RootFieldNumerics.Sq.sum_fundOnRoot, BM.hom_deg, hdy']`. Establish `hlog : ∀ w' : (Σ k, ι k) → ℂ, (∀ k, ∃ m, w' ⟨k, m⟩ ≠ 0) → Real.log ((Top.combLine sing (Cmp.fundOnRoot (τ, i))).h w') = -∑ m ∈ Finset.Iic i, Real.log ((sing (τ, m)).h w')` using `fun w' hw' => (RootFieldNumerics.Sq.log_combLine _ _ hw').trans (RootFieldNumerics.Sq.sum_fundOnRoot _ _)`. It suffices to establish `hs : ∃ w', SameOrbit w' w ∧ Real.log ((Top.combLine sing (Cmp.fundOnRoot (τ, i))).h w') = Real.log ((BM.hom (τ, i)).h w') by`. Take `⟨w', ho, h'⟩` from `hs`. Use `Chg.log_sub_orbit hdeg ho hw.1` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hw0 : ∀ k : NonPluckerBlocks M.blk, w ⟨k.1, (BM.F q).c k⟩ ≠ 0` using `fun k h' => (hgood w hz).1 k (by`. Rewrite using `[mCoordIdeal, RingHom.mem_ker, mConeMap, MvPolynomial.aeval_X]`. Use `show MvPolynomial.C (w ⟨k.1, (BM.F q).c k⟩) * _ = 0`. Rewrite using `[h', MvPolynomial.C_0, zero_mul])`.

Set `s₁ : K → ℂ` to `fun k => if hk : ∀ p, M.blk p ≠ some k then (w ⟨k, (BM.F q).c ⟨k, hk⟩⟩)⁻¹ else 1`. Establish `hs₁ : ∀ k, s₁ k ≠ 0` using `fun k => by`. Simplify using `only [s₁]`. Use `split_ifs with hk`. Conclude with `inv_ne_zero (hw0 ⟨k, hk⟩)`.

Conclude with `one_ne_zero`. Take `⟨w₁, ho₁, hn₁⟩ : ∃ w₁, SameOrbit w₁ w ∧ ∀ k, basePart M.blk w₁ ⟨k, (BM.F q).c k⟩ = 1` from `⟨fun p => s₁ p.1 * w p, ⟨s₁, hs₁, rfl⟩, fun k => by show s₁ k.1 * w ⟨k.1, (BM.F q).c k⟩ = 1`. Simplify using `only [s₁]`. Rewrite using `[dif_pos k.2]`. Conclude with `inv_mul_cancel₀ (hw0 k)⟩`.

Establish `hz₁` using `Chg.coordsAt_orbit hz ho₁`. Establish `hx0 : ∀ k, M.x ⟨k, (BM.F q).c k⟩ ≠ 0` using `fun k => ((hC0 w₁ hz₁).1.2 k _ (by rw [hn₁]; exact isUnit_one)).1`. Establish `main : ∀ w', CoordsAt 𝔐'.ξ y z w' → (∀ k, basePart M.blk w' ⟨k, (BM.F q).c k⟩ = 1) → ∃ cc : ∀ k, ι k, (∀ k, w' ⟨k, cc k⟩ ≠ 0) ∧ ∃ U : ℂ, ValAt 𝔐'.ξ z ((∏ a ∈ Finset.Iic i, B (col D.p D.q a) (col D.p D.q a)) * detFac D.p i (M.g τ) * ((M.blk (τ, i)).elim (algebraMap M.Ω Φ (M.lam (τ …` using `fun w' hw' hn => by choose c₀ hc₀ using hw'.1`. Set `cc : ∀ k, ι k` to `fun k => if hk : ∀ p, M.blk p ≠ some k then (BM.F q).c ⟨k, hk⟩ else c₀ k`. Establish `hcb : ∀ k : NonPluckerBlocks M.blk, cc k.1 = (BM.F q).c k` using `fun k => dif_pos k.2`.

Establish `hcc : ∀ k, w' ⟨k, cc k⟩ ≠ 0` using `fun k => by`. Distinguish the cases in `hk : ∀ p, M.blk p ≠ some k`. Rewrite using `[hcb ⟨k, hk⟩]`. Conclude with `(hn ⟨k, hk⟩).trans_ne one_ne_zero`. Rewrite using `[show cc k = c₀ k from dif_neg hk]`.

Conclude with `(hc₀ k).ne_zero`. Take `⟨U, hU, hU'⟩` from `prod_secNorm (𝔐'.all _) hw' (Finset.Iic i) (fun m => sing (τ, m)) (fun m => e (τ, m)) _ _ _ (hsec w' hw') hμ hdy' cc hcc`. Use `⟨cc, hcc, U, ?_, ?_⟩` and prove the remaining obligations. Use `hU using 1` and compare the differences between its conclusion and the goal. Rewrite using `[prod_dy M (τ, i) fun k => y ⟨k, cc k⟩, eq_inv_of_mul_eq_one_right ((mul_assoc _ _ _).symm.trans (he τ i)) |>.symm]`.

Establish `: ∀ k' : NonPluckerBlocks M.blk, y ⟨k'.1, cc k'.1⟩ = algebraMap M.Ω Φ (M.x ⟨k', (BM.F q).c k'⟩)` using `fun k' => by`. Rewrite using `[hcb]`. Conclude with `M.y_base ⟨k', _⟩`. Simplify using `only [this]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hlog w' fun k => ⟨cc k, hcc k⟩, hU', hsum, prod_dy M (τ, i) fun k => ‖w' ⟨k, cc k⟩‖]`. Establish `: ∀ k' : NonPluckerBlocks M.blk, ‖w' ⟨k'.1, cc k'.1⟩‖ = 1` using `fun k' => by`. Rewrite using `[hcb, show w' ⟨k'.1, (BM.F q).c k'⟩ = 1 from hn k', norm_one]`. Simplify using `only [this, _root_.one_zpow, Finset.prod_const_one, mul_one]`. Establish `hmem : ∀ w', CoordsAt 𝔐'.ξ y z w' → w' ∈ mcPts (mCoordIdeal y)` using `fun w' hw' => (GlobalTheory.T.complex_points_iff_centres 𝔐'.X Φ 𝔐'.ξ K ι y 𝔐'.tie w').2 ⟨z, 𝔐'.all _, hw'⟩`.

Establish `hbo : ∀ w', SameOrbit w' w → SameOrbit (basePart M.blk w') (BM.Rb.lift x x)` using `fun w' ho => by`. Use `sameOrbit_trans ?_ horb` and prove the remaining obligations. Take `⟨s, hs, rfl⟩` from `ho`. Conclude with `⟨fun k => s k.1, fun k => hs k.1, rfl⟩`. Establish `hC2` using `h2 E H D l Xo c Y S K ι Φ y M 𝔐' z (basePart M.blk w₁) (BM.F q) τ B h hF (hgood w₁ hz₁) (hC0 w₁ hz₁).2.2.2 hx0 hA i`.

Establish `hdn : ‖detFac D.p i h‖ ≠ 0` using `norm_ne_zero_iff.2 hdF`. Break down `hb : M.blk (τ, i) with _ | k₀` into its components or cases. Take `⟨cc, -, U, hU, hU'⟩` from `main w₁ hz₁ hn₁`. Take `⟨hυ, hv⟩` from `hC2.2 hb`. Rewrite `hU`, `hU'` using `[hb]`.

Simplify using `only [Option.elim_none, mul_one] at hU hU'`. Establish `eU` using `CoordModel.valAt_unique 𝔐'.tie.gen hU hv`. Use `⟨w₁, ho₁, ?_⟩` and prove the remaining obligations. Rewrite using `[hU', (BM.induced q x ⟨hq, hx⟩ (τ, i) w₁ (hmem _ hz₁) (hbo _ ho₁) hn₁ h hA.2.2.2.1 hA.2.2.2.2.1).2 hb, eU, norm_mul, Real.log_mul hdn (norm_ne_zero_iff.2 hυ), Real.log_one]`. Expand and normalize the polynomial expressions, which then agree.

Set `Pl : ι k₀ → ℂ` to `fun m => ∑ I, valAt M.x ((BM.F q).u ⟨k₀, m⟩ I) (basePart M.blk w₁) * minorIJ h I (stepCols (D.p + D.q) D.p i)`. Establish `hv` using `hC2.1 k₀ hb`. Take `⟨m₁, hm₁⟩` from `hz₁.1 k₀`. Take `⟨hy₁, hr⟩` from `hz₁.2 k₀ m₁ hm₁`. Establish `hP : ∀ m, ∃ r, w₁ ⟨k₀, m⟩ = r * w₁ ⟨k₀, m₁⟩ ∧ Pl m = r * Pl m₁` using `fun m => by`.

Take `⟨r, hr1, hr2⟩` from `hr m`. Use `⟨r, hr2, mul_left_cancel₀ hdF ?_⟩` and prove the remaining obligations. Establish `h3` using `CoordModel.valAt_mul hr1 (hv m₁)`. Establish `h6` using `hv m`. Rewrite `h6` using `[show (∏ a ∈ Finset.Iic i, B (col D.p D.q a) (col D.p D.q a)) * detFac D.p i (M.g τ) * y ⟨k₀, m⟩ * ∏ k', algebraMap M.Ω Φ (M.x ⟨k', (BM.F q).c k'⟩) ^ (-M.b (τ, i) k') = y ⟨k₀, m⟩ / y ⟨k₀, m₁⟩ * ((∏ a ∈ Finset.Iic i, B (col D.p D.q a) (col D.p D.q a)) * detFac D.p i (M.g τ) * y ⟨k …`.

Rewrite using `[CoordModel.valAt_unique 𝔐'.tie.gen h6 h3]`. Simplify using `only [Pl]`. Expand and normalize the polynomial expressions, which then agree. Establish `hbm : basePart M.blk w₁ ∈ mcPts (mCoordIdeal M.x)` using `(GlobalTheory.T.complex_points_iff_centres 𝔐.X M.Ω 𝔐.ξ _ _ M.x 𝔐.tie _).2 ⟨_, 𝔐.all _, (hC0 w₁ hz₁).1⟩`. Take `⟨m₀, hm₀⟩` from `h5 K ι Φ y _ _ _ M _ (BM.F q) h (τ, i) k₀ hbm hF (hgood w₁ hz₁) hA.2.2.2.1 hA.2.2.2.2.1 hb`.

Establish `hP₁ : Pl m₁ ≠ 0` using `fun h' => by`. Take `⟨r, -, hr2⟩` from `hP m₀`. Conclude with `hm₀ (hr2.trans (by rw [h', mul_zero]))`. Set `s₂ : K → ℂ` to `fun k => if k = k₀ then Pl m₁ / w₁ ⟨k₀, m₁⟩ else 1`. Establish `hs₂ : ∀ k, s₂ k ≠ 0` using `fun k => by`.

Simplify using `only [s₂]`. Use `split_ifs`. Conclude with `div_ne_zero hP₁ hm₁.ne_zero`. Conclude with `one_ne_zero`. Set `w₂ : (Σ k, ι k) → ℂ` to `fun p => s₂ p.1 * w₁ p`.

Establish `ho₂ : SameOrbit w₂ w` using `sameOrbit_trans ⟨s₂, hs₂, rfl⟩ ho₁`. Establish `hz₂` using `Chg.coordsAt_orbit hz ho₂`. Establish `eb : basePart M.blk w₂ = basePart M.blk w₁` using `funext fun p => by show s₂ p.1.1 * w₁ ⟨p.1.1, p.2⟩ = w₁ ⟨p.1.1, p.2⟩`. Rewrite using `[show s₂ p.1.1 = 1 from if_neg fun e' => p.1.2 (τ, i) (hb.trans (congrArg some e'.symm)), one_mul]`. Establish `hex : ∀ m, w₂ ⟨k₀, m⟩ = Pl m` using `fun m => by`.

Take `⟨r, hr1, hr2⟩` from `hP m`. Use `show s₂ k₀ * w₁ ⟨k₀, m⟩ = _`. Rewrite using `[show s₂ k₀ = Pl m₁ / w₁ ⟨k₀, m₁⟩ from if_pos rfl, hr1, hr2]`. Use `hm₁.ne_zero` as an intermediate fact. Clear the denominators using the available nonvanishing facts.

Establish `hn₂ : ∀ k, basePart M.blk w₂ ⟨k, (BM.F q).c k⟩ = 1` using `by rw [eb]; exact hn₁`. Take `⟨cc, hcc, U, hU, hU'⟩` from `main w₂ hz₂ hn₂`. Rewrite `hU`, `hU'` using `[hb]`. Simplify using `only [Option.elim_some, one_mul] at hU hU'`. Establish `eU` using `CoordModel.valAt_unique 𝔐'.tie.gen hU (hv (cc k₀))`.

Use `⟨w₂, ho₂, ?_⟩` and prove the remaining obligations. Establish `hne : ‖Pl (cc k₀)‖ ≠ 0` using `norm_ne_zero_iff.2 (hex _ ▸ hcc k₀)`. Rewrite using `[hU', (BM.induced q x ⟨hq, hx⟩ (τ, i) w₂ (hmem _ hz₂) (hbo _ ho₂) hn₂ h hA.2.2.2.1 hA.2.2.2.2.1).1 k₀ hb (by rw [eb]; exact hex), eU, norm_mul, hex]`. Rewrite using `[show ‖∑ I, valAt M.x ((BM.F q).u ⟨k₀, cc k₀⟩ I) (basePart M.blk w₁) * minorIJ h I (stepCols (D.p + D.q) D.p i)‖ = ‖Pl (cc k₀)‖ from rfl, Real.log_mul hdn hne]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem stSing_of (h0 : C0) (h1 : C1) (h2 : C2) (h5 : C5) (hW : GradedLineNormsW) (hO : GradedLineNormsDualOmega) (h4 : C4) : StSing := by
  intro E _ _ _ H D l Xo c Y S _ K _ ι _ Φ _ y M 𝔐 tie n BM 𝔐' Fl xdeg e sing hBM htot hsd hho a w hw x hx horb
  classical
  obtain ⟨τ, i⟩ := a
  obtain ⟨⟨pr, j, hov, -, hV, hbW, hbO⟩, -, hdy, he⟩ := htot
  have hT : Tot tie 𝔐' Fl pr j := ⟨hov, hV, hbW, hbO⟩
  obtain ⟨z, -, hz⟩ := (GlobalTheory.T.complex_points_iff_centres 𝔐'.X Φ 𝔐'.ξ K ι y 𝔐'.tie w).1 hw
  obtain ⟨q, hq⟩ := BM.O_cover x
  have hF := BM.isFrame q
  have hC0 := fun w' hw' => h0 E H D l Xo c Y S K ι Φ y M 𝔐 𝔐' pr j z w' hov hw'
  have hl : CoordsAt 𝔐.ξ M.x (z ≫ pr) (BM.Rb.lift x x) := Chg.coordsAt_orbit (hC0 w hz).1 (sameOrbit_symm horb)
  have hgood : ∀ w', CoordsAt 𝔐'.ξ y z w' → M.GoodAt (BM.F q) (mCoordIdeal (basePart M.blk w')) := fun w' hw' => by
    rw [← ptIdeal_centre (hC0 w' hw').1 (𝔐.all _), ptIdeal_centre hl (𝔐.all _)]
    exact BM.good q x hq
  have hint : 𝔐'.Interior z := (hC0 w hz).2.1.2 ((hBM.interior x _ hl).1 hx)
  obtain ⟨hfW, hfO⟩ := BM.frames_of_tie tie hq hl τ
  obtain ⟨B, h, hA⟩ := h1 E H D l Xo c Y S K ι Φ y M 𝔐 tie 𝔐' Fl pr j z (BM.F q) τ hT hF hfW hfO
  obtain ⟨hGb, hGp⟩ := BM.G_pos q τ x ⟨hq, hx⟩
  obtain ⟨hμ, hsum⟩ := h4 D.p D.q _ h hGb hGp hA.2.2.2.1 hA.2.2.2.2.1
  obtain ⟨hdF, hsum⟩ := hsum i
  have hsec : ∀ w', CoordsAt 𝔐'.ξ y z w' → ∀ m, SecNorm 𝔐'.ξ y (sing (τ, m)) (e (τ, m)) z w'
      (B (col D.p D.q m) (col D.p D.q m)) (mu D.p D.q (hᴴ * BM.G q τ x * h) m) := fun w' hw' m => by
    have := hho (τ, m) z w' hw' hint
    by_cases hm : (m : ℕ) < D.p
    · have e2 : HodgeCpt.rootIdx D (τ, m) = ⟨.inl τ, ⟨m, hm⟩⟩ := dif_pos hm
      have e3 : HodgeCpt.rootSgn D (τ, m) = 1 := if_pos hm
      rw [e2, e3] at this
      have h3 := this _ _ (hW E H D l Xo c Y S K ι Φ y M 𝔐 tie 𝔐' Fl pr j z (BM.F q) τ B h _ hT hF hfW hA hGb hGp hint
        (hBM.gramW q τ x ⟨hq, hx⟩ _ hl) ⟨m, hm⟩)
      rw [zpow_one, zpow_one] at h3
      rw [col, mu, dif_pos hm, if_pos hm]
      exact h3
    · have hm2 := m.2
      have e2 : HodgeCpt.rootIdx D (τ, m) = ⟨.inr τ, ⟨D.p + D.q - 1 - m, by show _ < D.q; omega⟩⟩ := dif_neg hm
      have e3 : HodgeCpt.rootSgn D (τ, m) = -1 := if_neg hm
      rw [e2, e3] at this
      have h3 := this _ _ (hO E H D l Xo c Y S K ι Φ y M 𝔐 tie 𝔐' Fl pr j z (BM.F q) τ B h _ hT hF hfO hA hGb hGp hint
        (hBM.gramO q τ x ⟨hq, hx⟩ _ hl) ⟨D.p + D.q - 1 - m, by omega⟩)
      rw [_root_.zpow_neg_one, _root_.zpow_neg_one, inv_inv] at h3
      have e4 : (⟨D.p + D.q - 1 - m, by omega⟩ : Fin D.q).rev = ⟨m - D.p, by omega⟩ :=
        Fin.ext (by simp only [Fin.val_rev]; omega)
      rw [e4] at h3
      rw [col, mu, dif_neg hm, if_neg hm]
      exact h3
  have hdy' : M.dy (τ, i) = -∑ m ∈ Finset.Iic i, (sing (τ, m)).a := by simp only [hsd]; exact hdy τ i
  have hdeg : (Top.combLine sing (Cmp.fundOnRoot (τ, i))).a = (BM.hom (τ, i)).a := by
    show ∑ r, _ • (sing r).a = _
    rw [RootFieldNumerics.Sq.sum_fundOnRoot, BM.hom_deg, hdy']
  have hlog : ∀ w' : (Σ k, ι k) → ℂ, (∀ k, ∃ m, w' ⟨k, m⟩ ≠ 0) →
      Real.log ((Top.combLine sing (Cmp.fundOnRoot (τ, i))).h w') =
        -∑ m ∈ Finset.Iic i, Real.log ((sing (τ, m)).h w') := fun w' hw' =>
    (RootFieldNumerics.Sq.log_combLine _ _ hw').trans (RootFieldNumerics.Sq.sum_fundOnRoot _ _)

  suffices hs : ∃ w', SameOrbit w' w ∧ Real.log ((Top.combLine sing (Cmp.fundOnRoot (τ, i))).h w') =
      Real.log ((BM.hom (τ, i)).h w') by
    obtain ⟨w', ho, h'⟩ := hs
    have := Chg.log_sub_orbit hdeg ho hw.1
    linarith

  have hw0 : ∀ k : NonPluckerBlocks M.blk, w ⟨k.1, (BM.F q).c k⟩ ≠ 0 := fun k h' => (hgood w hz).1 k (by
    rw [mCoordIdeal, RingHom.mem_ker, mConeMap, MvPolynomial.aeval_X]
    show MvPolynomial.C (w ⟨k.1, (BM.F q).c k⟩) * _ = 0
    rw [h', MvPolynomial.C_0, zero_mul])
  let s₁ : K → ℂ := fun k => if hk : ∀ p, M.blk p ≠ some k then (w ⟨k, (BM.F q).c ⟨k, hk⟩⟩)⁻¹ else 1
  have hs₁ : ∀ k, s₁ k ≠ 0 := fun k => by
    simp only [s₁]
    split_ifs with hk
    · exact inv_ne_zero (hw0 ⟨k, hk⟩)
    · exact one_ne_zero
  obtain ⟨w₁, ho₁, hn₁⟩ : ∃ w₁, SameOrbit w₁ w ∧ ∀ k, basePart M.blk w₁ ⟨k, (BM.F q).c k⟩ = 1 :=
    ⟨fun p => s₁ p.1 * w p, ⟨s₁, hs₁, rfl⟩, fun k => by
      show s₁ k.1 * w ⟨k.1, (BM.F q).c k⟩ = 1
      simp only [s₁]
      rw [dif_pos k.2]
      exact inv_mul_cancel₀ (hw0 k)⟩
  have hz₁ := Chg.coordsAt_orbit hz ho₁
  have hx0 : ∀ k, M.x ⟨k, (BM.F q).c k⟩ ≠ 0 := fun k =>
    ((hC0 w₁ hz₁).1.2 k _ (by rw [hn₁]; exact isUnit_one)).1

  have main : ∀ w', CoordsAt 𝔐'.ξ y z w' → (∀ k, basePart M.blk w' ⟨k, (BM.F q).c k⟩ = 1) →
      ∃ cc : ∀ k, ι k, (∀ k, w' ⟨k, cc k⟩ ≠ 0) ∧ ∃ U : ℂ,
        ValAt 𝔐'.ξ z ((∏ a ∈ Finset.Iic i, B (col D.p D.q a) (col D.p D.q a)) * detFac D.p i (M.g τ) *
          ((M.blk (τ, i)).elim (algebraMap M.Ω Φ (M.lam (τ, i))) (fun _ => 1) *
            (M.blk (τ, i)).elim 1 fun k => y ⟨k, cc k⟩) *
          ∏ k', algebraMap M.Ω Φ (M.x ⟨k', (BM.F q).c k'⟩) ^ (-M.b (τ, i) k')) U ∧
        Real.log ((Top.combLine sing (Cmp.fundOnRoot (τ, i))).h w') =
          blockPot D.p i (BM.G q τ x) h + Real.log ‖detFac D.p i h‖ - Real.log ‖U‖ +
            Real.log ((M.blk (τ, i)).elim 1 fun k => ‖w' ⟨k, cc k⟩‖) := fun w' hw' hn => by
    choose c₀ hc₀ using hw'.1
    let cc : ∀ k, ι k := fun k => if hk : ∀ p, M.blk p ≠ some k then (BM.F q).c ⟨k, hk⟩ else c₀ k
    have hcb : ∀ k : NonPluckerBlocks M.blk, cc k.1 = (BM.F q).c k := fun k => dif_pos k.2
    have hcc : ∀ k, w' ⟨k, cc k⟩ ≠ 0 := fun k => by
      by_cases hk : ∀ p, M.blk p ≠ some k
      · rw [hcb ⟨k, hk⟩]
        exact (hn ⟨k, hk⟩).trans_ne one_ne_zero
      · rw [show cc k = c₀ k from dif_neg hk]
        exact (hc₀ k).ne_zero
    obtain ⟨U, hU, hU'⟩ := prod_secNorm (𝔐'.all _) hw' (Finset.Iic i) (fun m => sing (τ, m)) (fun m => e (τ, m)) _ _ _
      (hsec w' hw') hμ hdy' cc hcc
    refine ⟨cc, hcc, U, ?_, ?_⟩
    · convert hU using 1
      rw [prod_dy M (τ, i) fun k => y ⟨k, cc k⟩, eq_inv_of_mul_eq_one_right ((mul_assoc _ _ _).symm.trans (he τ i)) |>.symm]
      have : ∀ k' : NonPluckerBlocks M.blk, y ⟨k'.1, cc k'.1⟩ = algebraMap M.Ω Φ (M.x ⟨k', (BM.F q).c k'⟩) := fun k' => by
        rw [hcb]; exact M.y_base ⟨k', _⟩
      simp only [this]
      ring
    · rw [hlog w' fun k => ⟨cc k, hcc k⟩, hU', hsum, prod_dy M (τ, i) fun k => ‖w' ⟨k, cc k⟩‖]
      have : ∀ k' : NonPluckerBlocks M.blk, ‖w' ⟨k'.1, cc k'.1⟩‖ = 1 := fun k' => by
        rw [hcb, show w' ⟨k'.1, (BM.F q).c k'⟩ = 1 from hn k', norm_one]
      simp only [this, _root_.one_zpow, Finset.prod_const_one, mul_one]
  have hmem : ∀ w', CoordsAt 𝔐'.ξ y z w' → w' ∈ mcPts (mCoordIdeal y) := fun w' hw' =>
    (GlobalTheory.T.complex_points_iff_centres 𝔐'.X Φ 𝔐'.ξ K ι y 𝔐'.tie w').2 ⟨z, 𝔐'.all _, hw'⟩
  have hbo : ∀ w', SameOrbit w' w → SameOrbit (basePart M.blk w') (BM.Rb.lift x x) := fun w' ho => by
    refine sameOrbit_trans ?_ horb
    obtain ⟨s, hs, rfl⟩ := ho
    exact ⟨fun k => s k.1, fun k => hs k.1, rfl⟩
  have hC2 := h2 E H D l Xo c Y S K ι Φ y M 𝔐' z (basePart M.blk w₁) (BM.F q) τ B h hF (hgood w₁ hz₁)
    (hC0 w₁ hz₁).2.2.2 hx0 hA i
  have hdn : ‖detFac D.p i h‖ ≠ 0 := norm_ne_zero_iff.2 hdF
  rcases hb : M.blk (τ, i) with _ | k₀
  · obtain ⟨cc, -, U, hU, hU'⟩ := main w₁ hz₁ hn₁
    obtain ⟨hυ, hv⟩ := hC2.2 hb
    rw [hb] at hU hU'
    simp only [Option.elim_none, mul_one] at hU hU'
    have eU := CoordModel.valAt_unique 𝔐'.tie.gen hU hv
    refine ⟨w₁, ho₁, ?_⟩
    rw [hU', (BM.induced q x ⟨hq, hx⟩ (τ, i) w₁ (hmem _ hz₁) (hbo _ ho₁) hn₁ h hA.2.2.2.1 hA.2.2.2.2.1).2 hb, eU,
      norm_mul, Real.log_mul hdn (norm_ne_zero_iff.2 hυ), Real.log_one]
    ring
  · let Pl : ι k₀ → ℂ := fun m => ∑ I, valAt M.x ((BM.F q).u ⟨k₀, m⟩ I) (basePart M.blk w₁) *
      minorIJ h I (stepCols (D.p + D.q) D.p i)
    have hv := hC2.1 k₀ hb
    obtain ⟨m₁, hm₁⟩ := hz₁.1 k₀
    obtain ⟨hy₁, hr⟩ := hz₁.2 k₀ m₁ hm₁
    have hP : ∀ m, ∃ r, w₁ ⟨k₀, m⟩ = r * w₁ ⟨k₀, m₁⟩ ∧ Pl m = r * Pl m₁ := fun m => by
      obtain ⟨r, hr1, hr2⟩ := hr m
      refine ⟨r, hr2, mul_left_cancel₀ hdF ?_⟩
      have h3 := CoordModel.valAt_mul hr1 (hv m₁)
      have h6 := hv m
      rw [show (∏ a ∈ Finset.Iic i, B (col D.p D.q a) (col D.p D.q a)) * detFac D.p i (M.g τ) * y ⟨k₀, m⟩ *
          ∏ k', algebraMap M.Ω Φ (M.x ⟨k', (BM.F q).c k'⟩) ^ (-M.b (τ, i) k') =
        y ⟨k₀, m⟩ / y ⟨k₀, m₁⟩ * ((∏ a ∈ Finset.Iic i, B (col D.p D.q a) (col D.p D.q a)) * detFac D.p i (M.g τ) *
          y ⟨k₀, m₁⟩ * ∏ k', algebraMap M.Ω Φ (M.x ⟨k', (BM.F q).c k'⟩) ^ (-M.b (τ, i) k')) by field_simp] at h6
      rw [CoordModel.valAt_unique 𝔐'.tie.gen h6 h3]
      simp only [Pl]
      ring
    have hbm : basePart M.blk w₁ ∈ mcPts (mCoordIdeal M.x) :=
      (GlobalTheory.T.complex_points_iff_centres 𝔐.X M.Ω 𝔐.ξ _ _ M.x 𝔐.tie _).2 ⟨_, 𝔐.all _, (hC0 w₁ hz₁).1⟩
    obtain ⟨m₀, hm₀⟩ := h5 K ι Φ y _ _ _ M _ (BM.F q) h (τ, i) k₀ hbm hF (hgood w₁ hz₁) hA.2.2.2.1 hA.2.2.2.2.1 hb
    have hP₁ : Pl m₁ ≠ 0 := fun h' => by
      obtain ⟨r, -, hr2⟩ := hP m₀
      exact hm₀ (hr2.trans (by rw [h', mul_zero]))
    let s₂ : K → ℂ := fun k => if k = k₀ then Pl m₁ / w₁ ⟨k₀, m₁⟩ else 1
    have hs₂ : ∀ k, s₂ k ≠ 0 := fun k => by
      simp only [s₂]
      split_ifs
      · exact div_ne_zero hP₁ hm₁.ne_zero
      · exact one_ne_zero
    let w₂ : (Σ k, ι k) → ℂ := fun p => s₂ p.1 * w₁ p
    have ho₂ : SameOrbit w₂ w := sameOrbit_trans ⟨s₂, hs₂, rfl⟩ ho₁
    have hz₂ := Chg.coordsAt_orbit hz ho₂
    have eb : basePart M.blk w₂ = basePart M.blk w₁ := funext fun p => by
      show s₂ p.1.1 * w₁ ⟨p.1.1, p.2⟩ = w₁ ⟨p.1.1, p.2⟩
      rw [show s₂ p.1.1 = 1 from if_neg fun e' => p.1.2 (τ, i) (hb.trans (congrArg some e'.symm)), one_mul]
    have hex : ∀ m, w₂ ⟨k₀, m⟩ = Pl m := fun m => by
      obtain ⟨r, hr1, hr2⟩ := hP m
      show s₂ k₀ * w₁ ⟨k₀, m⟩ = _
      rw [show s₂ k₀ = Pl m₁ / w₁ ⟨k₀, m₁⟩ from if_pos rfl, hr1, hr2]
      have := hm₁.ne_zero
      field_simp
    have hn₂ : ∀ k, basePart M.blk w₂ ⟨k, (BM.F q).c k⟩ = 1 := by rw [eb]; exact hn₁
    obtain ⟨cc, hcc, U, hU, hU'⟩ := main w₂ hz₂ hn₂
    rw [hb] at hU hU'
    simp only [Option.elim_some, one_mul] at hU hU'
    have eU := CoordModel.valAt_unique 𝔐'.tie.gen hU (hv (cc k₀))
    refine ⟨w₂, ho₂, ?_⟩
    have hne : ‖Pl (cc k₀)‖ ≠ 0 := norm_ne_zero_iff.2 (hex _ ▸ hcc k₀)
    rw [hU', (BM.induced q x ⟨hq, hx⟩ (τ, i) w₂ (hmem _ hz₂) (hbo _ ho₂) hn₂ h hA.2.2.2.1 hA.2.2.2.2.1).1 k₀ hb
      (by rw [eb]; exact hex), eU, norm_mul, hex]
    rw [show ‖∑ I, valAt M.x ((BM.F q).u ⟨k₀, cc k₀⟩ I) (basePart M.blk w₁) *
      minorIJ h I (stepCols (D.p + D.q) D.p i)‖ = ‖Pl (cc k₀)‖ from rfl, Real.log_mul hdn hne]
    ring

end SquareStatements.Sing
