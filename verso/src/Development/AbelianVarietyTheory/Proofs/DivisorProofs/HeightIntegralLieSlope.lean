import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdmissibleRepresentationFactorisation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointIntegralityStatementStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieSlopePointIntegralityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatHeightStatementStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FaltingsStatementOfFlatHeightStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightAdditiveInSymbolsStatement

open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts
open GlobalTheory.ShFam GlobalTheory.ShFam.Pad ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeightParts.IntLower

/- English proof (translation)
Establish `h` using `Finset.sum_range_by_parts u r N`. Simplify using `only [smul_eq_mul] at h`. Rewrite using `[h]`. Establish `key : ∑ i ∈ Finset.range (N - 1), (u i - u (i + 1)) * -(∑ l ∈ Finset.range (i + 1), r l) = ∑ i ∈ Finset.range (N - 1), (u (i + 1) - u i) * ∑ l ∈ Finset.range (i + 1), r l` using `Finset.sum_congr rfl fun _ _ => by ring`. Rewrite using `[key]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem abel_sum (N : ℕ) (u r : ℕ → ℝ) :
    -∑ i ∈ Finset.range N, u i * r i =
      ∑ i ∈ Finset.range (N - 1), (u i - u (i + 1)) * -(∑ l ∈ Finset.range (i + 1), r l) -
        u (N - 1) * ∑ l ∈ Finset.range N, r l := by
  have h := Finset.sum_range_by_parts u r N
  simp only [smul_eq_mul] at h
  rw [h]
  have key : ∑ i ∈ Finset.range (N - 1), (u i - u (i + 1)) * -(∑ l ∈ Finset.range (i + 1), r l) =
      ∑ i ∈ Finset.range (N - 1), (u (i + 1) - u i) * ∑ l ∈ Finset.range (i + 1), r l :=
    Finset.sum_congr rfl fun _ _ => by ring
  rw [key]; ring

/- English proof (translation)
Rewrite using `[← Finset.sum_range_add_sum_Ico _ h, Finset.sum_congr rfl (fun i hi => if_pos (Finset.mem_range.1 hi)), Finset.sum_eq_zero (fun i hi => if_neg (by rw [Finset.mem_Ico] at hi; omega)), add_zero]`.
-/
theorem sum_range_ite_lt' (f : ℕ → ℝ) {j N : ℕ} (h : j ≤ N) :
    ∑ i ∈ Finset.range N, (if i < j then f i else 0) = ∑ i ∈ Finset.range j, f i := by
  rw [← Finset.sum_range_add_sum_Ico _ h,
    Finset.sum_congr rfl (fun i hi => if_pos (Finset.mem_range.1 hi)),
    Finset.sum_eq_zero (fun i hi => if_neg (by rw [Finset.mem_Ico] at hi; omega)), add_zero]

end GlobalTheory.HeightParts.IntLower

namespace GlobalTheory.HeightParts

open IntLower in

/- English proof (translation)
Introduce `hP2 hPH hSW hLS D O hC hN A T H h`. Establish `hFl : FlatHt` using `GlobalTheory.T.flat_height_statement hP2 hPH hSW`. Take `⟨C0, hC0, hS⟩` from `GlobalTheory.T.lie_slope_point_integrality hLS (GlobalTheory.T.point_integrality_statement hP2 hPH) D O hC hN A T H h`. Take `⟨C1, hC1⟩` from `hFl D O hC hN A T H h`. Take `⟨C2, hC2⟩` from `GlobalTheory.T.faltings_statement_of_flat_height hP2 hPH hFl D O hC hN A T H h`.

Use `haveI : Nonempty D.what₂.Tau := ⟨D.eTau.symm (Classical.arbitrary _)⟩`. Establish `hj1 : 1 ≤ O.j` using `O.indef.1`. Establish `hjN : O.j < O.N` using `O.indef.2`. Establish `hp : O.S.Dw.p = O.j` using `O.S.p_eq`. Establish `hpq : O.S.Dw.p + O.S.Dw.q = O.N` using `O.S.rank_eq`.

Establish `hind0 : ArIn.ind ∅ = fun _ => false` using `by funext q; simp [ArIn.ind]`. Use `set nT : ℝ := (Fintype.card D.what₂.Tau : ℝ) with hnT`. Use `set C1' := max C1 0 with hC1'`. Use `set C2' := max C2 0 with hC2'`. Use `⟨(2 + 4 * nT * O.N) * C0 + 4 * C2' + nT * (4 * O.N + 2) * C1', fun u hu hu2 g hg hgap y hy => ?_⟩` and prove the remaining obligations.

Use `set c := compPt O.s y with hc`. Use `set z := basePt O.Φ y with hz`. Set `e : (D.host.E →+* ℂ) → ℕ → ℝ` to `fun σ i => (adlOf (O.Φ.C c) (O.met.hm c) (Finsupp.single ((fun _ => false), none, .inl (σ, i)) 1)).ht z`. Establish `hstep : ∀ σ k, stepHt O O.met.hm y σ k = -∑ i ∈ Finset.range k, e σ i`. Introduce `σ k`.

Unfold `stepHt`. Rewrite using `[hind0]`. Establish `hneg : ∀ a : Sym D.host.E, a.1 = (fun _ => false) → a.2.1 = none → (adlOf (O.Φ.C c) (O.met.hm c) (Finsupp.single a (-1))).ht z = -(adlOf (O.Φ.C c) (O.met.hm c) (Finsupp.single a 1)).ht z`. Introduce `a ha hb`. Use `GlobalTheory.T.height_additive_in_symbols D O hC A T H h c z (Finset.univ : Finset Unit) (fun _ => a) (fun _ => -1) (fun _ _ => ⟨ha, hb⟩)` as an intermediate fact.

Simplify using `using this`. Set `R : D.what₂.Tau → ℕ → ℝ` to `fun τ i => if hi : i < O.N then (O.rootH c (τ, ⟨i, hi⟩)).ht z else 0`. Establish `hroot : ∀ τ i, i < O.N → R τ i = if i < O.j then e (DV.tauEmb D τ) i else -e (conjEmb (DV.tauEmb D τ)) (O.N - 1 - i)`. Introduce `τ i hi`. Simplify using `only [R, dif_pos hi]`.

Express the relevant statement in the definitionally equal form `(adlOf (O.Φ.C c) (O.met.hm c) (rootSym O.S.Dw (ArIn.ind ∅) none (DV.tauEmb D τ) i)).ht z = _`. Rewrite using `[hind0]`. Unfold `rootSym`. Use `split_ifs with h1 h2 h2`. Both sides reduce to the same expression.

Use linear arithmetic over natural numbers and integers. Use linear arithmetic over natural numbers and integers. Rewrite using `[hneg _ rfl rfl]`. Establish `: O.S.Dw.p + O.S.Dw.q - 1 - i = O.N - 1 - i` using `by omega`. Rewrite using `[this]`.

Set `W : Wt O.Y → D.what₂.Tau → ℕ → ℝ` to `fun w τ i => if hi : i < O.N then w τ ⟨i, hi⟩ else 0`. Establish `hR : ∀ w : Wt O.Y, H.hH w y = -∑ τ, ∑ i ∈ Finset.range O.N, W w τ i * R τ i`. Introduce `w`. Rewrite using `[h.ht.hH _ y hy]`. Express the relevant statement in the definitionally equal form `-∑ x : DV.Rt D.what₂.Tau O.N, w x.1 x.2 * (O.rootH c x).ht z = _`.

Rewrite using `[Fintype.sum_prod_type]`. Use `congr 1`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_range]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Simplify using `only [W, R, dif_pos i.2]`. Both sides reduce to the same expression. Set `P : D.what₂.Tau → ℕ → ℝ` to `fun τ k => ∑ i ∈ Finset.range k, R τ i`. Establish `hPa : ∀ τ k, k ≤ O.j → -P τ k = stepHt O O.met.hm y (DV.tauEmb D τ) k`. Introduce `τ k hk`.

Rewrite using `[hstep, neg_inj]`. Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations. Use `Finset.mem_range.1 hi` as an intermediate fact. Rewrite using `[hroot τ i (by omega), if_pos (by omega)]`. Establish `hPb : ∀ τ k, O.j ≤ k → k ≤ O.N → -P τ k = -P τ O.N + stepHt O O.met.hm y (conjEmb (DV.tauEmb D τ)) (O.N - k)`.

Introduce `τ k hk hkN`. Establish `hsplit : P τ O.N = P τ k + ∑ i ∈ Finset.Ico k O.N, R τ i` using `(Finset.sum_range_add_sum_Ico _ hkN).symm`. Establish `hS : ∑ i ∈ Finset.Ico k O.N, R τ i = -∑ m ∈ Finset.range (O.N - k), e (conjEmb (DV.tauEmb D τ)) m`. Rewrite using `[Finset.sum_Ico_eq_sum_range, ← Finset.sum_range_reflect (fun m => e (conjEmb (DV.tauEmb D τ)) m) (O.N - k), ← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun m hm => ?_` and prove the remaining obligations.

Use `Finset.mem_range.1 hm` as an intermediate fact. Rewrite using `[hroot τ (k + m) (by omega), if_neg (by omega)]`. Use `congr 2`. Use linear arithmetic over natural numbers and integers. Rewrite using `[hstep, hsplit, hS]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hPc : ∀ τ (w : Wt O.Y), (∀ i, w τ i = 1) → (∀ τ', τ' ≠ τ → ∀ i, w τ' i = 0) → H.hH w y = -P τ O.N`. Introduce `τ w h1 h0`. Rewrite using `[hR, Finset.sum_eq_single τ]`. Use `congr 1`.

Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations. Simplify using `only [W, dif_pos (Finset.mem_range.1 hi), h1, one_mul]`. Introduce `b _ hb`. Use `Finset.sum_eq_zero fun i hi => ?_` and prove the remaining obligations. Simplify using `only [W, dif_pos (Finset.mem_range.1 hi), h0 b hb, zero_mul]`.

Simplify using the standard rewrite rules. Establish `hPd : H.hH (midWt O.Y) y = ∑ τ, -P τ O.j`. Rewrite using `[hR, ← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[neg_inj]`.

Use `show _ = ∑ i ∈ Finset.range O.j, R τ i`. Rewrite using `[← sum_range_ite_lt' (R τ) hjN.le]`. Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations. Simplify using `only [W, dif_pos (Finset.mem_range.1 hi)]`. Use `show (if i < O.j then (1 : ℝ) else 0) * R τ i = _`.

Apply the tactic sequence `split_ifs <;> simp`. Establish `hPe : ∀ τ, -∑ i ∈ Finset.range O.N, W u τ i * R τ i = ∑ i ∈ Finset.range (O.N - 1), (W u τ i - W u τ (i + 1)) * -P τ (i + 1) - W u τ (O.N - 1) * P τ O.N` using `fun τ => abel_sum O.N (W u τ) (R τ)`. Take `⟨hfneg, hst⟩` from `hS y hy`. Use `set L := Real.log (2 + max (H.falt y) 0) with hL`. Establish `hL0 : 0 ≤ L` using `Real.log_nonneg (by linarith [le_max_right (H.falt y) 0])`.

Establish `hC1'0 : 0 ≤ C1'` using `le_max_right _ _`. Establish `hC2'0 : 0 ≤ C2'` using `le_max_right _ _`. Establish `hC0L : 0 ≤ C0 * L` using `mul_nonneg hC0 hL0`. Use `set M := C0 * L + C1' with hM`. Establish `hM0 : 0 ≤ M` using `by linarith`.

Establish `hmt : ∀ τ, O.S.Dw.mult (DV.tauEmb D τ) = O.j` using `fun τ => (GlobalTheory.Harm.mult_of_mem O.S.Dw (Amb.cm O.A τ)).trans hp`. Establish `hmc : ∀ τ, O.S.Dw.mult (conjEmb (DV.tauEmb D τ)) = O.N - O.j` using `fun τ => by`. Rewrite using `[GlobalTheory.Harm.mult_conjEmb_of_mem O.S.Dw (Amb.cm O.A τ)]`. Use linear arithmetic over natural numbers and integers. Establish `hPN : ∀ τ, |P τ O.N| ≤ C1'`.

Introduce `τ`. Establish `h1` using `(hC1 τ y).2 hy`. Rewrite `h1` using `[hPc τ _ (fun i => if_pos rfl) (fun τ' hτ' i => if_neg hτ'), abs_neg]`. Conclude with `h1.trans (le_max_left _ _)`. Establish `hlow : ∀ τ k, k ≤ O.N → -M ≤ -P τ k`.

Introduce `τ k hk`. Break down `le_total k O.j with hkj | hkj` into its components or cases. Rewrite using `[hPa τ k hkj]`. Use `hst (DV.tauEmb D τ) k (by rw [hmt]; exact hkj)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Rewrite using `[hPb τ k hkj hk]`. Use `hst (conjEmb (DV.tauEmb D τ)) (O.N - k) (by rw [hmc]; omega)` as an intermediate fact. Use `(abs_le.mp (hPN τ)).2` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hWb : ∀ τ i, |W u τ i| ≤ 2`.

Introduce `τ i`. Simplify using `only [W]`. Use `split_ifs with hi`. Rewrite using `[← Real.norm_eq_abs]`. Conclude with `((norm_le_pi_norm (u τ) _).trans (norm_le_pi_norm u τ)).trans hu2`.

Simplify using the standard rewrite rules. Establish `hWd : ∀ τ i, i + 1 < O.N → 0 ≤ W u τ i - W u τ (i + 1)`. Introduce `τ i hi`. Simplify using `only [W, dif_pos hi, dif_pos (show i < O.N by omega)]`. Use `hu τ ⟨i, (show i < O.N by omega)⟩ ⟨i + 1, hi⟩ (Fin.mk_le_mk.2 (Nat.le_succ i))` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hgapW : ∀ τ, g ≤ W u τ (O.j - 1) - W u τ (O.j - 1 + 1)`. Introduce `τ`. Establish `e1 : O.j - 1 + 1 = O.j` using `by omega`. Rewrite using `[e1]`.

Simplify using `only [W, dif_pos (show O.j - 1 < O.N by omega), dif_pos hjN]`. Conclude with `hgap τ`. Establish `hterm : ∀ τ, ∀ i ∈ Finset.range (O.N - 1), (if i = O.j - 1 then g * -P τ O.j else 0) - 4 * M ≤ (W u τ i - W u τ (i + 1)) * -P τ (i + 1)`. Introduce `τ i hi`. Establish `hi'` using `Finset.mem_range.1 hi`.

Establish `hc0` using `hWd τ i (by omega)`. Establish `hc4 : W u τ i - W u τ (i + 1) ≤ 4`. Use `abs_le.mp (hWb τ i)` as an intermediate fact. Use `abs_le.mp (hWb τ (i + 1))` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hl` using `hlow τ (i + 1) (by omega)`. Use `split_ifs with hij`. Establish `e1 : i + 1 = O.j` using `by omega`. Establish `hg' : g ≤ W u τ i - W u τ (i + 1)` using `by have := hgapW τ; rwa [← hij] at this`. Rewrite using `[← e1]`.

Use polynomial arithmetic with `[mul_nonneg (sub_nonneg.2 hg') (show 0 ≤ -P τ (i + 1) + M by linarith), mul_nonneg hM0 (show 0 ≤ 4 - (W u τ i - W u τ (i + 1) - g) by linarith)]`. Use polynomial arithmetic with `[mul_nonneg hc0 (show 0 ≤ -P τ (i + 1) + M by linarith), mul_nonneg hM0 (show 0 ≤ 4 - (W u τ i - W u τ (i + 1)) by linarith)]`. Establish `hQ : ∀ τ, g * -P τ O.j - 4 * M * O.N - 2 * C1' ≤ ∑ i ∈ Finset.range (O.N - 1), (W u τ i - W u τ (i + 1)) * -P τ (i + 1) - W u τ (O.N - 1) * P τ O.N`. Introduce `τ`. Establish `hs` using `Finset.sum_le_sum (hterm τ)`.

Simplify using `only [Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_range, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hs`. Rewrite `hs` using `[if_pos (by omega)]`. Establish `hNc : ((O.N - 1 : ℕ) : ℝ) ≤ O.N` using `by exact_mod_cast Nat.sub_le _ _`. Establish `hlast : W u τ (O.N - 1) * P τ O.N ≤ 2 * C1'`. Establish `e` using `abs_mul (W u τ (O.N - 1)) (P τ O.N)`.

Use `mul_le_mul (hWb τ (O.N - 1)) (hPN τ) (abs_nonneg _) (by norm_num)` as an intermediate fact. Combine the linear relations using `[le_abs_self (W u τ (O.N - 1) * P τ O.N)]`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_right hNc (show 0 ≤ 4 * M by linarith)]`. Establish `hHu : H.hH u y = ∑ τ, (∑ i ∈ Finset.range (O.N - 1), (W u τ i - W u τ (i + 1)) * -P τ (i + 1) - W u τ (O.N - 1) * P τ O.N)`. Rewrite using `[hR, ← Finset.sum_neg_distrib]`.

Conclude with `Finset.sum_congr rfl fun τ _ => hPe τ`. Establish `hsum` using `Finset.sum_le_sum fun τ (_ : τ ∈ Finset.univ) => hQ τ`. Rewrite `hsum` using `[← hHu, Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← hPd, Finset.sum_const, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, nsmul_eq_mul]`. Establish `hmid` using `abs_le.mp (hC2 y hy)`. Take `⟨τ0⟩` from `‹Nonempty D.what₂.Tau›`.

Establish `hg4 : g ≤ 4`. Use `hgapW τ0` as an intermediate fact. Use `abs_le.mp (hWb τ0 (O.j - 1))` as an intermediate fact. Use `abs_le.mp (hWb τ0 (O.j - 1 + 1))` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hC2le : C2 ≤ C2'` using `le_max_left _ _`. Establish `h1 : g * (H.falt y / 2) - 4 * C2' ≤ g * H.hH (midWt O.Y) y`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left (show H.falt y / 2 - C2 ≤ H.hH (midWt O.Y) y by linarith) hg, mul_le_mul_of_nonneg_right hg4 hC2'0, mul_le_mul_of_nonneg_left hC2le hg]`. Establish `hmin : -(C0 * L) ≤ H.falt y - max (H.falt y) 0`. Break down `le_total (H.falt y) 0 with hf | hf` into its components or cases.

Rewrite using `[max_eq_right hf]`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[max_eq_left hf]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h2 : g / 2 * max (H.falt y) 0 - 2 * (C0 * L) ≤ g * (H.falt y / 2)`.

Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left hmin (show 0 ≤ g / 2 by linarith), mul_le_mul_of_nonneg_right (show g / 2 ≤ 2 by linarith) hC0L]`. Establish `hnT0 : 0 ≤ nT` using `Nat.cast_nonneg _`. Establish `hN0 : (0 : ℝ) ≤ O.N` using `Nat.cast_nonneg _`. Establish `hA : 0 ≤ (4 * C2' + nT * (4 * O.N + 2) * C1') * L` using `by positivity`. Establish `hB : 0 ≤ (2 + 4 * nT * O.N) * C0` using `by positivity`.

Use polynomial arithmetic with `[hA, hB, hsum, h1, h2]`.
-/
theorem htIntSt_of_hypotheses : Hypotheses2 → HypothesesH → GlobalTheory.Published.ScholzeWeinsteinB → LieSlope → HtIntSt := by
  intro hP2 hPH hSW hLS D O hC hN A T H h
  have hFl : FlatHt := GlobalTheory.T.flat_height_statement hP2 hPH hSW
  obtain ⟨C0, hC0, hS⟩ := GlobalTheory.T.lie_slope_point_integrality hLS (GlobalTheory.T.point_integrality_statement hP2 hPH) D O hC hN A T H h
  obtain ⟨C1, hC1⟩ := hFl D O hC hN A T H h
  obtain ⟨C2, hC2⟩ := GlobalTheory.T.faltings_statement_of_flat_height hP2 hPH hFl D O hC hN A T H h
  haveI : Nonempty D.what₂.Tau := ⟨D.eTau.symm (Classical.arbitrary _)⟩
  have hj1 : 1 ≤ O.j := O.indef.1
  have hjN : O.j < O.N := O.indef.2
  have hp : O.S.Dw.p = O.j := O.S.p_eq
  have hpq : O.S.Dw.p + O.S.Dw.q = O.N := O.S.rank_eq
  have hind0 : ArIn.ind ∅ = fun _ => false := by funext q; simp [ArIn.ind]
  set nT : ℝ := (Fintype.card D.what₂.Tau : ℝ) with hnT
  set C1' := max C1 0 with hC1'
  set C2' := max C2 0 with hC2'
  refine ⟨(2 + 4 * nT * O.N) * C0 + 4 * C2' + nT * (4 * O.N + 2) * C1',
    fun u hu hu2 g hg hgap y hy => ?_⟩
  set c := compPt O.s y with hc
  set z := basePt O.Φ y with hz
  let e : (D.host.E →+* ℂ) → ℕ → ℝ := fun σ i =>
    (adlOf (O.Φ.C c) (O.met.hm c) (Finsupp.single ((fun _ => false), none, .inl (σ, i)) 1)).ht z
  have hstep : ∀ σ k, stepHt O O.met.hm y σ k = -∑ i ∈ Finset.range k, e σ i := by
    intro σ k
    unfold stepHt
    rw [hind0]
  have hneg : ∀ a : Sym D.host.E, a.1 = (fun _ => false) → a.2.1 = none →
      (adlOf (O.Φ.C c) (O.met.hm c) (Finsupp.single a (-1))).ht z =
        -(adlOf (O.Φ.C c) (O.met.hm c) (Finsupp.single a 1)).ht z := by
    intro a ha hb
    have := GlobalTheory.T.height_additive_in_symbols D O hC A T H h c z (Finset.univ : Finset Unit) (fun _ => a) (fun _ => -1)
      (fun _ _ => ⟨ha, hb⟩)
    simpa using this
  let R : D.what₂.Tau → ℕ → ℝ := fun τ i => if hi : i < O.N then (O.rootH c (τ, ⟨i, hi⟩)).ht z else 0
  have hroot : ∀ τ i, i < O.N → R τ i =
      if i < O.j then e (DV.tauEmb D τ) i else -e (conjEmb (DV.tauEmb D τ)) (O.N - 1 - i) := by
    intro τ i hi
    simp only [R, dif_pos hi]
    change (adlOf (O.Φ.C c) (O.met.hm c) (rootSym O.S.Dw (ArIn.ind ∅) none (DV.tauEmb D τ) i)).ht z = _
    rw [hind0]
    unfold rootSym
    split_ifs with h1 h2 h2
    · rfl
    · omega
    · omega
    · rw [hneg _ rfl rfl]
      have : O.S.Dw.p + O.S.Dw.q - 1 - i = O.N - 1 - i := by omega
      rw [this]
  let W : Wt O.Y → D.what₂.Tau → ℕ → ℝ := fun w τ i => if hi : i < O.N then w τ ⟨i, hi⟩ else 0
  have hR : ∀ w : Wt O.Y, H.hH w y = -∑ τ, ∑ i ∈ Finset.range O.N, W w τ i * R τ i := by
    intro w
    rw [h.ht.hH _ y hy]
    change -∑ x : DV.Rt D.what₂.Tau O.N, w x.1 x.2 * (O.rootH c x).ht z = _
    rw [Fintype.sum_prod_type]
    congr 1
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Finset.sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [W, R, dif_pos i.2]
    rfl
  let P : D.what₂.Tau → ℕ → ℝ := fun τ k => ∑ i ∈ Finset.range k, R τ i
  have hPa : ∀ τ k, k ≤ O.j → -P τ k = stepHt O O.met.hm y (DV.tauEmb D τ) k := by
    intro τ k hk
    rw [hstep, neg_inj]
    refine Finset.sum_congr rfl fun i hi => ?_
    have := Finset.mem_range.1 hi
    rw [hroot τ i (by omega), if_pos (by omega)]
  have hPb : ∀ τ k, O.j ≤ k → k ≤ O.N →
      -P τ k = -P τ O.N + stepHt O O.met.hm y (conjEmb (DV.tauEmb D τ)) (O.N - k) := by
    intro τ k hk hkN
    have hsplit : P τ O.N = P τ k + ∑ i ∈ Finset.Ico k O.N, R τ i :=
      (Finset.sum_range_add_sum_Ico _ hkN).symm
    have hS : ∑ i ∈ Finset.Ico k O.N, R τ i = -∑ m ∈ Finset.range (O.N - k), e (conjEmb (DV.tauEmb D τ)) m := by
      rw [Finset.sum_Ico_eq_sum_range, ← Finset.sum_range_reflect (fun m => e (conjEmb (DV.tauEmb D τ)) m) (O.N - k),
        ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun m hm => ?_
      have := Finset.mem_range.1 hm
      rw [hroot τ (k + m) (by omega), if_neg (by omega)]
      congr 2
      omega
    rw [hstep, hsplit, hS]
    ring
  have hPc : ∀ τ (w : Wt O.Y), (∀ i, w τ i = 1) → (∀ τ', τ' ≠ τ → ∀ i, w τ' i = 0) → H.hH w y = -P τ O.N := by
    intro τ w h1 h0
    rw [hR, Finset.sum_eq_single τ]
    · congr 1
      refine Finset.sum_congr rfl fun i hi => ?_
      simp only [W, dif_pos (Finset.mem_range.1 hi), h1, one_mul]
    · intro b _ hb
      refine Finset.sum_eq_zero fun i hi => ?_
      simp only [W, dif_pos (Finset.mem_range.1 hi), h0 b hb, zero_mul]
    · simp
  have hPd : H.hH (midWt O.Y) y = ∑ τ, -P τ O.j := by
    rw [hR, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [neg_inj]
    show _ = ∑ i ∈ Finset.range O.j, R τ i
    rw [← sum_range_ite_lt' (R τ) hjN.le]
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [W, dif_pos (Finset.mem_range.1 hi)]
    show (if i < O.j then (1 : ℝ) else 0) * R τ i = _
    split_ifs <;> simp
  have hPe : ∀ τ, -∑ i ∈ Finset.range O.N, W u τ i * R τ i =
      ∑ i ∈ Finset.range (O.N - 1), (W u τ i - W u τ (i + 1)) * -P τ (i + 1) - W u τ (O.N - 1) * P τ O.N :=
    fun τ => abel_sum O.N (W u τ) (R τ)

  obtain ⟨hfneg, hst⟩ := hS y hy
  set L := Real.log (2 + max (H.falt y) 0) with hL
  have hL0 : 0 ≤ L := Real.log_nonneg (by linarith [le_max_right (H.falt y) 0])
  have hC1'0 : 0 ≤ C1' := le_max_right _ _
  have hC2'0 : 0 ≤ C2' := le_max_right _ _
  have hC0L : 0 ≤ C0 * L := mul_nonneg hC0 hL0
  set M := C0 * L + C1' with hM
  have hM0 : 0 ≤ M := by linarith
  have hmt : ∀ τ, O.S.Dw.mult (DV.tauEmb D τ) = O.j := fun τ =>
    (GlobalTheory.Harm.mult_of_mem O.S.Dw (Amb.cm O.A τ)).trans hp
  have hmc : ∀ τ, O.S.Dw.mult (conjEmb (DV.tauEmb D τ)) = O.N - O.j := fun τ => by
    rw [GlobalTheory.Harm.mult_conjEmb_of_mem O.S.Dw (Amb.cm O.A τ)]; omega
  have hPN : ∀ τ, |P τ O.N| ≤ C1' := by
    intro τ
    have h1 := (hC1 τ y).2 hy
    rw [hPc τ _ (fun i => if_pos rfl) (fun τ' hτ' i => if_neg hτ'), abs_neg] at h1
    exact h1.trans (le_max_left _ _)
  have hlow : ∀ τ k, k ≤ O.N → -M ≤ -P τ k := by
    intro τ k hk
    rcases le_total k O.j with hkj | hkj
    · rw [hPa τ k hkj]
      have := hst (DV.tauEmb D τ) k (by rw [hmt]; exact hkj)
      linarith
    · rw [hPb τ k hkj hk]
      have := hst (conjEmb (DV.tauEmb D τ)) (O.N - k) (by rw [hmc]; omega)
      have := (abs_le.mp (hPN τ)).2
      linarith
  have hWb : ∀ τ i, |W u τ i| ≤ 2 := by
    intro τ i
    simp only [W]
    split_ifs with hi
    · rw [← Real.norm_eq_abs]
      exact ((norm_le_pi_norm (u τ) _).trans (norm_le_pi_norm u τ)).trans hu2
    · simp
  have hWd : ∀ τ i, i + 1 < O.N → 0 ≤ W u τ i - W u τ (i + 1) := by
    intro τ i hi
    simp only [W, dif_pos hi, dif_pos (show i < O.N by omega)]
    have := hu τ ⟨i, (show i < O.N by omega)⟩ ⟨i + 1, hi⟩ (Fin.mk_le_mk.2 (Nat.le_succ i))
    linarith
  have hgapW : ∀ τ, g ≤ W u τ (O.j - 1) - W u τ (O.j - 1 + 1) := by
    intro τ
    have e1 : O.j - 1 + 1 = O.j := by omega
    rw [e1]
    simp only [W, dif_pos (show O.j - 1 < O.N by omega), dif_pos hjN]
    exact hgap τ
  have hterm : ∀ τ, ∀ i ∈ Finset.range (O.N - 1),
      (if i = O.j - 1 then g * -P τ O.j else 0) - 4 * M ≤ (W u τ i - W u τ (i + 1)) * -P τ (i + 1) := by
    intro τ i hi
    have hi' := Finset.mem_range.1 hi
    have hc0 := hWd τ i (by omega)
    have hc4 : W u τ i - W u τ (i + 1) ≤ 4 := by
      have := abs_le.mp (hWb τ i); have := abs_le.mp (hWb τ (i + 1)); linarith
    have hl := hlow τ (i + 1) (by omega)
    split_ifs with hij
    · have e1 : i + 1 = O.j := by omega
      have hg' : g ≤ W u τ i - W u τ (i + 1) := by have := hgapW τ; rwa [← hij] at this
      rw [← e1]
      nlinarith [mul_nonneg (sub_nonneg.2 hg') (show 0 ≤ -P τ (i + 1) + M by linarith),
        mul_nonneg hM0 (show 0 ≤ 4 - (W u τ i - W u τ (i + 1) - g) by linarith)]
    · nlinarith [mul_nonneg hc0 (show 0 ≤ -P τ (i + 1) + M by linarith),
        mul_nonneg hM0 (show 0 ≤ 4 - (W u τ i - W u τ (i + 1)) by linarith)]
  have hQ : ∀ τ, g * -P τ O.j - 4 * M * O.N - 2 * C1' ≤
      ∑ i ∈ Finset.range (O.N - 1), (W u τ i - W u τ (i + 1)) * -P τ (i + 1) - W u τ (O.N - 1) * P τ O.N := by
    intro τ
    have hs := Finset.sum_le_sum (hterm τ)
    simp only [Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_range, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul] at hs
    rw [if_pos (by omega)] at hs
    have hNc : ((O.N - 1 : ℕ) : ℝ) ≤ O.N := by exact_mod_cast Nat.sub_le _ _
    have hlast : W u τ (O.N - 1) * P τ O.N ≤ 2 * C1' := by
      have e := abs_mul (W u τ (O.N - 1)) (P τ O.N)
      have := mul_le_mul (hWb τ (O.N - 1)) (hPN τ) (abs_nonneg _) (by norm_num)
      linarith [le_abs_self (W u τ (O.N - 1) * P τ O.N)]
    nlinarith [mul_le_mul_of_nonneg_right hNc (show 0 ≤ 4 * M by linarith)]
  have hHu : H.hH u y = ∑ τ, (∑ i ∈ Finset.range (O.N - 1), (W u τ i - W u τ (i + 1)) * -P τ (i + 1) -
      W u τ (O.N - 1) * P τ O.N) := by
    rw [hR, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun τ _ => hPe τ
  have hsum := Finset.sum_le_sum fun τ (_ : τ ∈ Finset.univ) => hQ τ
  rw [← hHu, Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← hPd, Finset.sum_const,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, nsmul_eq_mul] at hsum
  have hmid := abs_le.mp (hC2 y hy)
  obtain ⟨τ0⟩ := ‹Nonempty D.what₂.Tau›
  have hg4 : g ≤ 4 := by
    have := hgapW τ0; have := abs_le.mp (hWb τ0 (O.j - 1)); have := abs_le.mp (hWb τ0 (O.j - 1 + 1)); linarith
  have hC2le : C2 ≤ C2' := le_max_left _ _
  have h1 : g * (H.falt y / 2) - 4 * C2' ≤ g * H.hH (midWt O.Y) y := by
    nlinarith [mul_le_mul_of_nonneg_left (show H.falt y / 2 - C2 ≤ H.hH (midWt O.Y) y by linarith) hg,
      mul_le_mul_of_nonneg_right hg4 hC2'0, mul_le_mul_of_nonneg_left hC2le hg]
  have hmin : -(C0 * L) ≤ H.falt y - max (H.falt y) 0 := by
    rcases le_total (H.falt y) 0 with hf | hf
    · rw [max_eq_right hf]; linarith
    · rw [max_eq_left hf]; linarith
  have h2 : g / 2 * max (H.falt y) 0 - 2 * (C0 * L) ≤ g * (H.falt y / 2) := by
    nlinarith [mul_le_mul_of_nonneg_left hmin (show 0 ≤ g / 2 by linarith),
      mul_le_mul_of_nonneg_right (show g / 2 ≤ 2 by linarith) hC0L]
  have hnT0 : 0 ≤ nT := Nat.cast_nonneg _
  have hN0 : (0 : ℝ) ≤ O.N := Nat.cast_nonneg _
  have hA : 0 ≤ (4 * C2' + nT * (4 * O.N + 2) * C1') * L := by positivity
  have hB : 0 ≤ (2 + 4 * nT * O.N) * C0 := by positivity
  nlinarith [hA, hB, hsum, h1, h2]

end GlobalTheory.HeightParts
