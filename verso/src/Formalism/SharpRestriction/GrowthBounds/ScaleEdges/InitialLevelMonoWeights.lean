import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.EdgeFamOf
import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.EdgePlane
import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.RankMulConductorDivLeOne
import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.ScaleZpowMono
import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.NumericProductInequality

noncomputable section

namespace Formalism.MainNotions.Pf14

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning MvPolynomial

/- English proof (translation)
Unfold `t0 tableLineDegreeFive.La`. Establish `hl : 0 ≤ Real.log a` using `Real.log_nonneg ha`. Establish `ha0 : 0 ≤ a` using `by linarith`. Check the signs of the components of the expression.
-/
theorem initial_level_nonneg {C Ct0 : ℝ} (hC : 0 ≤ C) (h0 : 0 ≤ Ct0) (p N N₁ L₁ G' k : ℕ) {a : ℝ} (ha : 1 ≤ a) :
    0 ≤ t0 C Ct0 p N N₁ L₁ G' k a := by
  unfold t0 tableLineDegreeFive.La
  have hl : 0 ≤ Real.log a := Real.log_nonneg ha
  have ha0 : 0 ≤ a := by linarith
  positivity

/- English proof (translation)
Unfold `t0 tableLineDegreeFive.La`. Establish `hl : 0 ≤ Real.log a` using `Real.log_nonneg ha`. Establish `ha0 : 0 ≤ a` using `by linarith`. Establish `hB : 0 ≤ C * (N₁ : ℝ) ^ 2 * Real.log a * a / (p * k) + a * (p : ℝ) ^ (-(L₁ : ℤ)) + k * (p : ℝ) ^ G'`. Check the signs of the components of the expression.

Establish `hN : (0 : ℝ) ≤ N` using `Nat.cast_nonneg _`. Conclude with `mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h hN) hB`.
-/
theorem initial_level_mono_weights {C Ct0 Ct0' : ℝ} (hC : 0 ≤ C) (h : Ct0 ≤ Ct0') (p N N₁ L₁ G' k : ℕ) {a : ℝ} (ha : 1 ≤ a) :
    t0 C Ct0 p N N₁ L₁ G' k a ≤ t0 C Ct0' p N N₁ L₁ G' k a := by
  unfold t0 tableLineDegreeFive.La
  have hl : 0 ≤ Real.log a := Real.log_nonneg ha
  have ha0 : 0 ≤ a := by linarith
  have hB : 0 ≤ C * (N₁ : ℝ) ^ 2 * Real.log a * a / (p * k) + a * (p : ℝ) ^ (-(L₁ : ℤ)) + k * (p : ℝ) ^ G' := by
    positivity
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h hN) hB

/- English proof (translation)
Establish `hInc : DualHeightInclusion` using `hA.2.2.1`. Establish `hBP : BePerfect` using `hA.2.2.2.1`. Establish `h26 : Formalism.MainNotions.SelectionLemmas.Conclusion2 D CLa Ck Crk Cdeg` using `hA.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1`. Establish `hWI : WittIdent` using `hA.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1`. Establish `hM : tableLineDegreeFive.LevelPrimesProviso D` using `hA.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2`.

Take `⟨Cg, hCg1, hg2⟩` from `symbol_space_at D CLa Ck Crk Cdeg h26`. Use `⟨max Ct0 |Cdeg|, CD1, max Crk 1, max Cg (max C₂ (max C₃ (max 2 (max |CLa| CD1)))), lt_of_lt_of_le h0 (le_max_left _ _), h1, lt_of_lt_of_le one_pos (le_max_right _ _), lt_of_lt_of_le (by linarith) (le_max_left _ _), ?_⟩` and prove the remaining obligations. Introduce `C hC`. Establish `c1 : Cg ≤ C` using `le_trans (le_max_left _ _) hC`. Establish `hC'` using `le_trans (le_max_right _ _) hC`.

Establish `c2 : C₂ ≤ C` using `le_trans (le_max_left _ _) hC'`. Establish `hC''` using `le_trans (le_max_right _ _) hC'`. Establish `c3 : C₃ ≤ C` using `le_trans (le_max_left _ _) hC''`. Establish `hC3` using `le_trans (le_max_right _ _) hC''`. Establish `c4 : 2 ≤ C` using `le_trans (le_max_left _ _) hC3`.

Establish `hC4` using `le_trans (le_max_right _ _) hC3`. Establish `c5 : |CLa| ≤ C` using `le_trans (le_max_left _ _) hC4`. Establish `c6 : CD1 ≤ C` using `le_trans (le_max_right _ _) hC4`. Introduce `p W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar hSet H e he htgt`. Establish `: Fact p.Prime` using `⟨hSet.1.prime⟩`.

Establish `: NeZero n'` using `⟨by have := hSet.1.two_le; omega⟩`. Establish `hB` using `hyps_basic (C := C) (by linarith) H`. Establish `hr2 : 2 ≤ r` using `H.2.1`. Establish `hkr : orbitWindowCount r de h x + 2 * r ≤ (m + 1) - r` using `H.2.2.2.2.2.2.2.1`. Establish `hcS : 8 * (Dp + 1) ≤ cStar` using `H.2.2.2.2.2.2.2.2.2.2.1`.

Establish `hdom : IsDominant lam0` using `H.2.2.2.2.1.2.1`. Take `⟨K, hk⟩ : ∃ K, m + 1 = r + K` from `⟨m + 1 - r, by omega⟩`. Establish `: NeZero r` using `⟨by omega⟩`. Establish `: NeZero K` using `⟨by omega⟩`. Establish `hrk : r ≤ m + 1` using `by omega`.

Establish `hw` using `w_ne_zero hSet.1`. Establish `ha1 : (1 : ℝ) ≤ a` using `by linarith [hB.two_le_a]`. Take `⟨φ, hφ⟩` from `hWI p n' W Qq O Kf ι σ j w hSet.1`. Take `⟨F, hF⟩` from `frames_of TT r L₁ L₂ de h x hSet.1.even hr2 hB.one_le_depth_alt H.2.2.1`. Establish `hTT` using `hF.1`.

Substitute `hTT` using the available equality. Set `_ : Algebra (WF p n') O` to `algOfIdent j φ`. Take `⟨E', hE', hL⟩` from `hL3 C c2 p W Qq O Kf ι σ j w n' m r F.TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar hSet H φ hφ K hk hrk F hF`. Establish `hG2` using `hg2 C c1 p W Qq O Kf ι σ j w n' m r F.TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar hSet H K hk F hF E' (fun t ht => (hE' t ht).1)`. Take `⟨⟨Sg, hle, hcompl, ⟨ιb, b, hb⟩, hrank, _⟩, hdeg⟩` from `hG2`.

Take `⟨B, hBgen, hBli, hBc⟩` from `basis_fin Sg b hcompl (fun P => P ∈ Gen O p K F (symbolSpaces CLa p n' O r K F (flatDeg lam0) L₁ (min (orbitWindowCount r de h x) (2 * F.TT.card)) (mStar p F (r + K) (orbitWindowCount r de h x) (p ^ goodG' r de h x) (cPrime n' r F.TT.card c0 cpp cStar)) a Y) (G2d F (flatDeg lam0) …`. Take `⟨hm, hhm, hsrc⟩` from `he.1`. Take `⟨hE1, _, _⟩` from `edgePlane p n' W Qq O Kf ι σ j w hSet.1 φ hφ m r hm hhm`. Take `⟨g, hg, hbasis⟩` from `hE1 e he hsrc`. Use `set X : ℝ := Cdeg * (F.TT.card : ℝ) * (CLa * ((min (orbitWindowCount r de h x) (2 * F.TT.card) : ℕ) : ℝ) ^ 2 * Real.log a * a / ((p : ℝ) * ((r + K : ℕ) : ℝ)) + a * (p : ℝ) ^ (-(L₁ : ℤ)) + ((r + K : ℕ) : ℝ) * (p : ℝ) ^ goodG' r de h x) with hX`.

Establish `hT : ∀ i, ∀ mm ∈ (B i).support, vsDeg mm ≤ ⌊X⌋₊` using `fun i mm hmm => Nat.le_floor (hdeg (B i) (Submodule.subset_span (hBgen i)) mm hmm)`. Use `choose Fs hFs1 hFs2 using fun i => hL g hg (B i) (hBgen i) ⌊X⌋₊ (hT i)`. Take `⟨Θ, hΘ, n2, oS, tT, D1, sh, hoS, htT, hD1, hsh, hcount, htests⟩` from `hCl C c3 p W Qq O Kf ι σ j w n' m r F.TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar hSet H φ hφ K hk hrk F hF E' hE' _ B hBgen hBli hBc e he htgt hm g hhm hg hbasis (fun i => ∑ o ∈ Finset.range (⌊X⌋₊ + 1), Fs i o) (by`. Introduce `i`. Rewrite using `[← hFs2 i, Submodule.coe_sum, map_sum])`.

Use `choose Fv hv1 hv2 hv3 using fun (i : Fin (Module.finrank O Sg)) (o : ℕ) => flatSrc edgePlane p n' W Qq O Kf ι σ j w hSet.1 φ hφ m r (dT F.TT lam0) hm hhm Θ hΘ g hg e hbasis (cPrime n' r F.TT.card c0 cpp cStar) o _ (Fs i o) (hFs1 i o).1 rfl (hFs1 i o).2.2`. Take `⟨_, _, hn3, _⟩` from `num C 1 CD1 1 one_pos h1 one_pos c4 (by linarith) c6 (by linarith) p n' m r F.TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar H`. Establish `hD1' : D1 ≤ Dp`. Establish `: (D1 : ℝ) ≤ Dp` using `le_trans hD1 hn3`. Conclude with `this` after adjusting the coercions.

Establish `hoS' : oS ≤ r * F.TT.card * c0 + 2 * r * n' * cpp`. Establish `: (oS : ℝ) ≤ ((r * F.TT.card * c0 + 2 * r * n' * cpp : ℕ) : ℝ)`. Use `le_trans hoS ?_` and prove the remaining obligations. Unfold `om`. Use `push_cast`.

Conclude with `le_refl _`. Conclude with `this` after adjusting the coercions. Establish `hfam` using `edgeFamOf D hM hBP hInc p n' W Qq O Kf ι σ j w hSet.1 m r (flW (dT F.TT lam0)) (restW F.TT lam0) lam0 (lambda_zero_eq_product F.TT lam0) (flW_dom _) (restW_dom (by have := hB.m_ge; omega) F.TT lam0 hdom) e he (Module.finrank O Sg) n2 ⌊X⌋₊ oS tT D1 cStar (cPrime n' r F.TT.card c0 …`. Introduce `i`. Use `Submodule.sum_mem _ fun o ho => ?_` and prove the remaining obligations.

Rewrite using `[hsrc]`. Conclude with `scale_neg_mono w hw (Nat.lt_succ_iff.1 (Finset.mem_range.1 ho)) _ (hv1 i o))`. Use the proof step `(by`. Introduce `i`. Rewrite using `[map_sum, ← Finset.sum_sub_distrib]`.

Conclude with `Submodule.sum_mem _ fun o _ => hv2 i o)`. Use the proof step `(by`. Introduce `i e' he' hs' hne`. Conclude with `Submodule.sum_mem _ fun o _ => hv3 i o e' he' (hs'.trans hsrc) hne)`. Use the proof step `(by`.

Introduce `i`. Rewrite using `[map_sum]`. Use `Submodule.sum_mem _ fun o _ => ?_` and prove the remaining obligations. Conclude with `scale_pos_le w 0 _ ((hΘ.2 g hg e hbasis (Fs i o) 0).1 (hFs1 i o).2.1))`. Use `hsh`.

Use the proof step `(fun c hc => htests _ (fun _ _ => rfl) c hc)`. Establish `hkR : ((r + K : ℕ) : ℝ) = ((m + 1 : ℕ) : ℝ)` using `by rw [hk]`. Establish `hXle : X ≤ t0 C (max Ct0 |Cdeg|) p F.TT.card (orbitWindowCount r de h x) L₁ (goodG' r de h x) (m + 1) a`. Rewrite using `[hX, hkR]`. Conclude with `level_lower_bound_terms Cdeg CLa C (max Ct0 |Cdeg|) (le_max_right _ _) c5 p F.TT.card (orbitWindowCount r de h x) (min (orbitWindowCount r de h x) (2 * F.TT.card)) L₁ (goodG' r de h x) (m + 1) (min_le_left _ _) (by have := H.1; omega) (by omega) a ha1`.

Establish `ht0` using `initial_level_nonneg (C := C) (Ct0 := max Ct0 |Cdeg|) (by linarith) (le_trans h0.le (le_max_left _ _)) p F.TT.card (orbitWindowCount r de h x) L₁ (goodG' r de h x) (m + 1) ha1`. Establish `hTle : ((⌊X⌋₊ : ℕ) : ℝ) ≤ t0 C (max Ct0 |Cdeg|) p F.TT.card (orbitWindowCount r de h x) L₁ (goodG' r de h x) (m + 1) a`. Break down `le_or_gt 0 X with hx0 | hx0` into its components or cases. Conclude with `le_trans (Nat.floor_le hx0) hXle`. Rewrite using `[Nat.floor_of_nonpos hx0.le]`.

Simplify using `using ht0`. Use `⟨Module.finrank O Sg * n2, ⌊X⌋₊ + oS, tT, D1, ?_, ?_, hD1, ?_, hfam⟩` and prove the remaining obligations. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Use `initial_level_mono_weights (C := C) (by linarith) (le_max_left Ct0 |Cdeg|) p F.TT.card (orbitWindowCount r de h x) L₁ (goodG' r de h x) (m + 1) ha1` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hK : m + 1 - r = K` using `by omega`. Establish `hp0 : (0 : ℝ) < p`. Establish `: 0 < p` using `by have := H.1; omega`. Conclude with `this` after adjusting the coercions.

Establish `hY : 0 < Y` using `by linarith [hB.two_le_Y]`. Establish `hu : 0 ≤ (1 - ((m + 1 : ℕ) : ℝ) * c0 / a) ^ F.TT.card` using `pow_nonneg (by linarith [rank_mul_conductor_div_le_one c4 H]) _`. Establish `hPi : ∏ t ∈ F.TT, ((Nat.choose (flatDeg lam0 t + (r + K) - 1) (r + K - 1) : ℕ) : ℝ) = ∏ t ∈ F.TT, ((Nat.choose (flatDeg lam0 t + (m + 1) - 1) (m + 1 - 1) : ℕ) : ℝ)` using `by rw [hk]`. Establish `hq : ((p : ℝ) ^ n') ^ (-((r * K : ℕ) : ℤ)) = ((p : ℝ) ^ (n' * (r * (m + 1 - r))))⁻¹`. Rewrite using `[zpow_neg, zpow_natCast, ← pow_mul, hK]`.

Rewrite `hrank` using `[hq, hPi, hkR]`. Use `norm_index_count_bound Crk (max Crk 1) ((F.TT.card : ℝ) * (r : ℝ) ^ 2 * ((m + 1 : ℕ) : ℝ) / Y) ((1 - ((m + 1 : ℕ) : ℝ) * c0 / a) ^ F.TT.card) (dimV Kf lam0 : ℝ) (∏ t ∈ F.TT, ((Nat.choose (flatDeg lam0 t + (m + 1) - 1) (m + 1 - 1) : ℕ) : ℝ)) ((p : ℝ) ^ (n' * (r * (m + 1 - r)))) (M …` as an intermediate fact. Use `le_trans (le_of_eq ?_) hrank` and prove the remaining obligations. Use the proof step `ring)`. Use `hcount`.

Use `le_trans (le_of_eq ?_) this` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem edgeStep_of (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) (hA : tableLineDegreeFive.admitted D CLa Ck Crk Cdeg)
    (Ct0 CD1 C₂ C₃ : ℝ) (h0 : 0 < Ct0) (h1 : 0 < CD1)
    (hL3 : ∀ C : ℝ, C₂ ≤ C → SymbolRealisableBound C CLa) (hCl : ∀ C : ℝ, C₃ ≤ C → CloudStep C Ct0 CD1 CLa) :
    ∃ Ct0' CD1' Cr C₁ : ℝ, 0 < Ct0' ∧ 0 < CD1' ∧ 0 < Cr ∧ 0 < C₁ ∧ ∀ C : ℝ, C₁ ≤ C → EdgeStep C Ct0' CD1' Cr := by
  have hInc : DualHeightInclusion := hA.2.2.1
  have hBP : BePerfect := hA.2.2.2.1
  have h26 : Formalism.MainNotions.SelectionLemmas.Conclusion2 D CLa Ck Crk Cdeg := hA.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hWI : WittIdent := hA.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hM : tableLineDegreeFive.LevelPrimesProviso D := hA.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨Cg, hCg1, hg2⟩ := symbol_space_at D CLa Ck Crk Cdeg h26
  refine ⟨max Ct0 |Cdeg|, CD1, max Crk 1, max Cg (max C₂ (max C₃ (max 2 (max |CLa| CD1)))),
    lt_of_lt_of_le h0 (le_max_left _ _), h1, lt_of_lt_of_le one_pos (le_max_right _ _),
    lt_of_lt_of_le (by linarith) (le_max_left _ _), ?_⟩
  intro C hC
  have c1 : Cg ≤ C := le_trans (le_max_left _ _) hC
  have hC' := le_trans (le_max_right _ _) hC
  have c2 : C₂ ≤ C := le_trans (le_max_left _ _) hC'
  have hC'' := le_trans (le_max_right _ _) hC'
  have c3 : C₃ ≤ C := le_trans (le_max_left _ _) hC''
  have hC3 := le_trans (le_max_right _ _) hC''
  have c4 : 2 ≤ C := le_trans (le_max_left _ _) hC3
  have hC4 := le_trans (le_max_right _ _) hC3
  have c5 : |CLa| ≤ C := le_trans (le_max_left _ _) hC4
  have c6 : CD1 ≤ C := le_trans (le_max_right _ _) hC4
  intro p W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar hSet H e he htgt
  have : Fact p.Prime := ⟨hSet.1.prime⟩
  have : NeZero n' := ⟨by have := hSet.1.two_le; omega⟩
  have hB := hyps_basic (C := C) (by linarith) H
  have hr2 : 2 ≤ r := H.2.1
  have hkr : orbitWindowCount r de h x + 2 * r ≤ (m + 1) - r := H.2.2.2.2.2.2.2.1
  have hcS : 8 * (Dp + 1) ≤ cStar := H.2.2.2.2.2.2.2.2.2.2.1
  have hdom : IsDominant lam0 := H.2.2.2.2.1.2.1
  obtain ⟨K, hk⟩ : ∃ K, m + 1 = r + K := ⟨m + 1 - r, by omega⟩
  have : NeZero r := ⟨by omega⟩
  have : NeZero K := ⟨by omega⟩
  have hrk : r ≤ m + 1 := by omega
  have hw := w_ne_zero hSet.1
  have ha1 : (1 : ℝ) ≤ a := by linarith [hB.two_le_a]
  obtain ⟨φ, hφ⟩ := hWI p n' W Qq O Kf ι σ j w hSet.1
  obtain ⟨F, hF⟩ := frames_of TT r L₁ L₂ de h x hSet.1.even hr2 hB.one_le_depth_alt H.2.2.1
  have hTT := hF.1
  subst hTT
  let _ : Algebra (WF p n') O := algOfIdent j φ
  obtain ⟨E', hE', hL⟩ := hL3 C c2 p W Qq O Kf ι σ j w n' m r F.TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar hSet H
    φ hφ K hk hrk F hF
  have hG2 := hg2 C c1 p W Qq O Kf ι σ j w n' m r F.TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar hSet H K hk F hF E'
    (fun t ht => (hE' t ht).1)
  obtain ⟨⟨Sg, hle, hcompl, ⟨ιb, b, hb⟩, hrank, _⟩, hdeg⟩ := hG2
  obtain ⟨B, hBgen, hBli, hBc⟩ := basis_fin Sg b hcompl
    (fun P => P ∈ Gen O p K F
      (symbolSpaces CLa p n' O r K F (flatDeg lam0) L₁ (min (orbitWindowCount r de h x) (2 * F.TT.card))
        (mStar p F (r + K) (orbitWindowCount r de h x) (p ^ goodG' r de h x) (cPrime n' r F.TT.card c0 cpp cStar)) a Y)
      (G2d F (flatDeg lam0) E')) hb
  obtain ⟨hm, hhm, hsrc⟩ := he.1
  obtain ⟨hE1, _, _⟩ := edgePlane p n' W Qq O Kf ι σ j w hSet.1 φ hφ m r hm hhm
  obtain ⟨g, hg, hbasis⟩ := hE1 e he hsrc
  set X : ℝ := Cdeg * (F.TT.card : ℝ) *
    (CLa * ((min (orbitWindowCount r de h x) (2 * F.TT.card) : ℕ) : ℝ) ^ 2 * Real.log a * a / ((p : ℝ) * ((r + K : ℕ) : ℝ)) +
      a * (p : ℝ) ^ (-(L₁ : ℤ)) + ((r + K : ℕ) : ℝ) * (p : ℝ) ^ goodG' r de h x) with hX
  have hT : ∀ i, ∀ mm ∈ (B i).support, vsDeg mm ≤ ⌊X⌋₊ := fun i mm hmm =>
    Nat.le_floor (hdeg (B i) (Submodule.subset_span (hBgen i)) mm hmm)
  choose Fs hFs1 hFs2 using fun i => hL g hg (B i) (hBgen i) ⌊X⌋₊ (hT i)
  obtain ⟨Θ, hΘ, n2, oS, tT, D1, sh, hoS, htT, hD1, hsh, hcount, htests⟩ :=
    hCl C c3 p W Qq O Kf ι σ j w n' m r F.TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar hSet H φ hφ K hk hrk F hF E' hE'
      _ B hBgen hBli hBc e he htgt hm g hhm hg hbasis (fun i => ∑ o ∈ Finset.range (⌊X⌋₊ + 1), Fs i o)
      (by
        intro i
        rw [← hFs2 i, Submodule.coe_sum, map_sum])
  choose Fv hv1 hv2 hv3 using fun (i : Fin (Module.finrank O Sg)) (o : ℕ) =>
    flatSrc edgePlane p n' W Qq O Kf ι σ j w hSet.1 φ hφ m r (dT F.TT lam0) hm hhm Θ hΘ g hg e hbasis
      (cPrime n' r F.TT.card c0 cpp cStar) o _ (Fs i o) (hFs1 i o).1 rfl (hFs1 i o).2.2
  obtain ⟨_, _, hn3, _⟩ := num C 1 CD1 1 one_pos h1 one_pos c4 (by linarith) c6 (by linarith) p n' m r F.TT L₁ L₂ de h x
    lam0 aT bT a Y cpp c0 Dp cStar H
  have hD1' : D1 ≤ Dp := by
    have : (D1 : ℝ) ≤ Dp := le_trans hD1 hn3
    exact_mod_cast this
  have hoS' : oS ≤ r * F.TT.card * c0 + 2 * r * n' * cpp := by
    have : (oS : ℝ) ≤ ((r * F.TT.card * c0 + 2 * r * n' * cpp : ℕ) : ℝ) := by
      refine le_trans hoS ?_
      unfold om
      push_cast
      exact le_refl _
    exact_mod_cast this
  have hfam := edgeFamOf D hM hBP hInc p n' W Qq O Kf ι σ j w hSet.1 m r (flW (dT F.TT lam0)) (restW F.TT lam0) lam0
    (lambda_zero_eq_product F.TT lam0) (flW_dom _) (restW_dom (by have := hB.m_ge; omega) F.TT lam0 hdom) e he
    (Module.finrank O Sg) n2 ⌊X⌋₊ oS tT D1 cStar (cPrime n' r F.TT.card c0 cpp cStar)
    (by unfold cPrime; omega) (by unfold cPrime; omega)
    (fun i => ∑ o ∈ Finset.range (⌊X⌋₊ + 1), Fv i o)
    (fun i => Θ (∑ o ∈ Finset.range (⌊X⌋₊ + 1), Fs i o)) sh
    (by
      intro i
      refine Submodule.sum_mem _ fun o ho => ?_
      rw [hsrc]
      exact scale_neg_mono w hw (Nat.lt_succ_iff.1 (Finset.mem_range.1 ho)) _ (hv1 i o))
    (by
      intro i
      rw [map_sum, ← Finset.sum_sub_distrib]
      exact Submodule.sum_mem _ fun o _ => hv2 i o)
    (by
      intro i e' he' hs' hne
      exact Submodule.sum_mem _ fun o _ => hv3 i o e' he' (hs'.trans hsrc) hne)
    (by
      intro i
      rw [map_sum]
      refine Submodule.sum_mem _ fun o _ => ?_
      exact scale_pos_le w 0 _ ((hΘ.2 g hg e hbasis (Fs i o) 0).1 (hFs1 i o).2.1))
    hsh
    (fun c hc => htests _ (fun _ _ => rfl) c hc)
  have hkR : ((r + K : ℕ) : ℝ) = ((m + 1 : ℕ) : ℝ) := by rw [hk]
  have hXle : X ≤ t0 C (max Ct0 |Cdeg|) p F.TT.card (orbitWindowCount r de h x) L₁ (goodG' r de h x) (m + 1) a := by
    rw [hX, hkR]
    exact level_lower_bound_terms Cdeg CLa C (max Ct0 |Cdeg|) (le_max_right _ _) c5
      p F.TT.card (orbitWindowCount r de h x) (min (orbitWindowCount r de h x) (2 * F.TT.card)) L₁ (goodG' r de h x) (m + 1)
      (min_le_left _ _) (by have := H.1; omega) (by omega) a ha1
  have ht0 := initial_level_nonneg (C := C) (Ct0 := max Ct0 |Cdeg|) (by linarith) (le_trans h0.le (le_max_left _ _)) p F.TT.card
    (orbitWindowCount r de h x) L₁ (goodG' r de h x) (m + 1) ha1
  have hTle : ((⌊X⌋₊ : ℕ) : ℝ) ≤ t0 C (max Ct0 |Cdeg|) p F.TT.card (orbitWindowCount r de h x) L₁ (goodG' r de h x) (m + 1) a := by
    rcases le_or_gt 0 X with hx0 | hx0
    · exact le_trans (Nat.floor_le hx0) hXle
    · rw [Nat.floor_of_nonpos hx0.le]
      simpa using ht0
  refine ⟨Module.finrank O Sg * n2, ⌊X⌋₊ + oS, tT, D1, ?_, ?_, hD1, ?_, hfam⟩
  · push_cast
    linarith
  · have := initial_level_mono_weights (C := C) (by linarith) (le_max_left Ct0 |Cdeg|) p F.TT.card (orbitWindowCount r de h x) L₁ (goodG' r de h x)
      (m + 1) ha1
    linarith
  · have hK : m + 1 - r = K := by omega
    have hp0 : (0 : ℝ) < p := by
      have : 0 < p := by have := H.1; omega
      exact_mod_cast this
    have hY : 0 < Y := by linarith [hB.two_le_Y]
    have hu : 0 ≤ (1 - ((m + 1 : ℕ) : ℝ) * c0 / a) ^ F.TT.card :=
      pow_nonneg (by linarith [rank_mul_conductor_div_le_one c4 H]) _
    have hPi : ∏ t ∈ F.TT, ((Nat.choose (flatDeg lam0 t + (r + K) - 1) (r + K - 1) : ℕ) : ℝ) =
        ∏ t ∈ F.TT, ((Nat.choose (flatDeg lam0 t + (m + 1) - 1) (m + 1 - 1) : ℕ) : ℝ) := by rw [hk]
    have hq : ((p : ℝ) ^ n') ^ (-((r * K : ℕ) : ℤ)) = ((p : ℝ) ^ (n' * (r * (m + 1 - r))))⁻¹ := by
      rw [zpow_neg, zpow_natCast, ← pow_mul, hK]
    rw [hq, hPi, hkR] at hrank
    have := norm_index_count_bound Crk (max Crk 1) ((F.TT.card : ℝ) * (r : ℝ) ^ 2 * ((m + 1 : ℕ) : ℝ) / Y)
      ((1 - ((m + 1 : ℕ) : ℝ) * c0 / a) ^ F.TT.card) (dimV Kf lam0 : ℝ)
      (∏ t ∈ F.TT, ((Nat.choose (flatDeg lam0 t + (m + 1) - 1) (m + 1 - 1) : ℕ) : ℝ))
      ((p : ℝ) ^ (n' * (r * (m + 1 - r)))) (Module.finrank O Sg) n2 (le_max_left _ _)
      (div_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _)) (Nat.cast_nonneg _)) hY.le) hu
      (Nat.cast_nonneg _) (Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _) (pow_pos hp0 _)
      (by
        refine le_trans (le_of_eq ?_) hrank
        ring)
      hcount
    refine le_trans (le_of_eq ?_) this
    ring

/- English proof (translation)
Introduce `hA h14a h14b`. Take `⟨C₂, _, hL3⟩` from `hR3 hA h14a`. Take `⟨Ct0, CD1, C₃, h0, h1, _, hCl⟩` from `hRC hA h14a h14b`. Conclude with `edgeStep_of D CLa Ck Crk Cdeg hA Ct0 CD1 C₂ C₃ h0 h1 hL3 hCl`.
-/
theorem restEdge_of (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18 : ℝ)
    (hR3 : SourcesRealisable D CLa Ck Crk Cdeg CLa' CD Csz)
    (hRC : RestCloud D CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18) :
    RestEdge D CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18 := by
  intro hA h14a h14b
  obtain ⟨C₂, _, hL3⟩ := hR3 hA h14a
  obtain ⟨Ct0, CD1, C₃, h0, h1, _, hCl⟩ := hRC hA h14a h14b
  exact edgeStep_of D CLa Ck Crk Cdeg hA Ct0 CD1 C₂ C₃ h0 h1 hL3 hCl

end Formalism.MainNotions.Pf14
