import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoices
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMean
import Formalism.SharpRestriction.Divisibility.LatticeTransfer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerSumDecompositionHomogeneousStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LimitsOfShiftFunctionalsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KappaIndependentOfEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RemainderSumConvergesStatement

open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.WeightThresholdDefs Filter Topology Classical GlobalTheory.FlagPoly GlobalTheory.FlagAr GlobalTheory.Mean4

namespace GlobalTheory.Mean4

/- English proof (translation)
Establish `hN : 2 ≤ Y.N` using `by have := Y.j_pos; have := Y.j_lt; omega`. Establish `hc : 1 ≤ Fintype.card D.what₂.Tau` using `Fintype.card_pos`. Establish `hd : Y.N ≤ dimY Y + 1`. Establish `h1 : Y.N - 1 ≤ Y.N * (Y.N - 1) / 2`. Rewrite using `[Nat.le_div_iff_mul_le (by norm_num), mul_comm]`.

Conclude with `Nat.mul_le_mul_right _ hN`. Establish `h2 : Y.N * (Y.N - 1) / 2 ≤ dimY Y`. Unfold `dimY dimFl`. Conclude with `Nat.le_mul_of_pos_left _ hc`. Use linear arithmetic over natural numbers and integers.

Unfold `comb`. Use `IsHomogeneous.sum _ _ _ (fun τ _ => IsHomogeneous.sum _ _ _ (fun k hk => ?_))` and prove the remaining obligations. Rewrite `hk` using `[Finset.mem_Icc]`. Establish `hp : (pSum τ k : Pol D.what₂.Tau Y.N).IsHomogeneous k`. Unfold `pSum`.

Use `IsHomogeneous.sum _ _ _ (fun i _ => ?_)` and prove the remaining obligations. Simplify using `using (isHomogeneous_X ℝ (τ, i)).pow k`. Use `hp.mul (hQ τ k hk.1 hk.2)` as an intermediate fact. Rewrite `this` using `[show k + (dimY Y + 1 - k) = dimY Y + 1 by omega]`. Then use the resulting hypothesis.
-/
theorem comb_isHomogeneous_of_cof {D : D7} (Y : ShimX D.what₂.Tau) [Nonempty D.what₂.Tau]
    (Q : D.what₂.Tau → ℕ → Pol D.what₂.Tau Y.N) (hQ : Cof Y Q) : (comb Y Q).IsHomogeneous (dimY Y + 1) := by
  have hN : 2 ≤ Y.N := by have := Y.j_pos; have := Y.j_lt; omega
  have hc : 1 ≤ Fintype.card D.what₂.Tau := Fintype.card_pos
  have hd : Y.N ≤ dimY Y + 1 := by
    have h1 : Y.N - 1 ≤ Y.N * (Y.N - 1) / 2 := by
      rw [Nat.le_div_iff_mul_le (by norm_num), mul_comm]
      exact Nat.mul_le_mul_right _ hN
    have h2 : Y.N * (Y.N - 1) / 2 ≤ dimY Y := by
      unfold dimY dimFl
      exact Nat.le_mul_of_pos_left _ hc
    omega
  unfold comb
  refine IsHomogeneous.sum _ _ _ (fun τ _ => IsHomogeneous.sum _ _ _ (fun k hk => ?_))
  rw [Finset.mem_Icc] at hk
  have hp : (pSum τ k : Pol D.what₂.Tau Y.N).IsHomogeneous k := by
    unfold pSum
    refine IsHomogeneous.sum _ _ _ (fun i _ => ?_)
    simpa using (isHomogeneous_X ℝ (τ, i)).pow k
  have := hp.mul (hQ τ k hk.1 hk.2)
  rwa [show k + (dimY Y + 1 - k) = dimY Y + 1 by omega] at this

/- English proof (translation)
Introduce `D Y Φ hh hvol hS hC B₀ hB₀`. Use `haveI hT : Nonempty D.what₂.Tau := Fintype.card_pos_iff.1 (by`. Rewrite using `[D.what₂.card_Tau]`. Unfold `Ranks.f Ranks.n`. Use the proof step `positivity)`.

Take `⟨τ₀⟩` from `id hT`. Take `⟨al, be, hE⟩` from `hS`. Use `set a : ℕ → ℝ := fun B => al B + ∑ p ∈ newPrimes Y B₀ B, Real.log p / ((p : ℝ) - 1) with ha`. Use `set b : ℕ → ℝ := fun B => be B - ∑ p ∈ newPrimes Y B₀ B, Real.log p / Y.N * kap Y p τ₀ with hb`. Establish `key : ∀ Q, Cof Y Q → ∀ᶠ B : ℕ in atTop, Φ B₀ (comb Y Q) = Y.vol * (hh (comb Y Q) - a B * shAll Y (comb Y Q) - b B * totAll Y (comb Y Q)) + (∑ p ∈ newPrimes Y B₀ B, restTerm Y p Q) + (Φ B (comb Y Q) - Y.vol * (hh (comb Y Q) - al B * shAll Y (comb Y Q) - be B * totAll Y (comb Y Q)) …`.

Introduce `Q hQ`. Use `filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop B₀] with B hB`. Rewrite using `[hC B₀ B hB₀ hB Q hQ]`. Establish `hk : ∀ p : ℕ, (∑ τ, kap Y p τ * totF τ (comb Y Q)) = kap Y p τ₀ * totAll Y (comb Y Q)`. Introduce `p`.

Unfold `totAll`. Rewrite using `[Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl (fun τ _ => by rw [GlobalTheory.T.kappa_independent_of_embedding D Y p τ τ₀])`. Simplify using `only [hk, ha, hb]`. Rewrite using `[Finset.sum_add_distrib, Finset.sum_add_distrib]`.

Establish `e1 : ∑ p ∈ newPrimes Y B₀ B, -(Real.log p / ((p : ℝ) - 1)) * Y.vol * shAll Y (comb Y Q) = -(∑ p ∈ newPrimes Y B₀ B, Real.log p / ((p : ℝ) - 1)) * Y.vol * shAll Y (comb Y Q)`. Rewrite using `[← Finset.sum_mul, ← Finset.sum_mul, Finset.sum_neg_distrib]`. Establish `e2 : ∑ p ∈ newPrimes Y B₀ B, Real.log p / Y.N * Y.vol * (kap Y p τ₀ * totAll Y (comb Y Q)) = (∑ p ∈ newPrimes Y B₀ B, Real.log p / Y.N * kap Y p τ₀) * (Y.vol * totAll Y (comb Y Q))`. Rewrite using `[Finset.sum_mul]`. Conclude with `Finset.sum_congr rfl (fun p _ => by ring)`.

Rewrite using `[e1, e2]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨A, b₀, hA, hb₀⟩` from `GlobalTheory.T.limits_of_shift_functionals D.what₂.Tau Y.N Y.j a b Y.j_pos Y.j_lt (by`. Introduce `F hF`. Take `⟨Q, hQ, hFQ⟩` from `GlobalTheory.T.power_sum_decomposition_homogeneous D.what₂.Tau Y.N F hF`.

Establish `hQ' : Cof Y Q` using `hQ`. Establish `hFQ' : F = comb Y Q` using `hFQ`. Take `⟨L, hL⟩` from `GlobalTheory.T.remainder_sum_converges D Y B₀ Q (by linarith)`. Establish `h0` using `hE F hF`. Use `⟨hh F - (Φ B₀ F - L - 0) / Y.vol, ?_⟩` and prove the remaining obligations.

Use `(tendsto_const_nhds.sub (((tendsto_const_nhds.sub hL).sub h0).div_const Y.vol)).congr' ?_` and prove the remaining obligations. Use `filter_upwards [key Q hQ'] with B hB`. Rewrite `hB` using `[← hFQ']`. Express the relevant statement in the definitionally equal form `_ = a B * shAll Y F + b B * totAll Y F`. Rewrite using `[hB]`.

Clear the denominators using the available nonvanishing facts. Use the proof step `ring)`. Use `⟨A, b₀, fun Q hQ => ?_⟩` and prove the remaining obligations. Establish `h0` using `hE _ (comb_isHomogeneous_of_cof Y Q hQ)`. Establish `h1` using `((tendsto_const_nhds (x := Φ B₀ (comb Y Q))).sub ((((tendsto_const_nhds (x := hh (comb Y Q))).sub (hA.mul_const (shAll Y (comb Y Q)))).sub (hb₀.mul_const (totAll Y (comb Y Q)))).const_mul Y.vol)).sub h0`.

Rewrite `h1` using `[sub_zero]`. Use `h1.congr' ?_` and prove the remaining obligations. Use `filter_upwards [key Q hQ] with B hB`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem exists_exactAt : ∀ (D : D7) (Y : ShimX D.what₂.Tau), ∀ (Φ : ℝ → Fn Y) (hh : Fn Y), 0 < Y.vol → ShapeF Φ hh → Change Φ → ∀ B₀ : ℝ, 2 ≤ B₀ → ∃ a b : ℝ, ExactAt Φ hh B₀ a b := by
  intro D Y Φ hh hvol hS hC B₀ hB₀
  haveI hT : Nonempty D.what₂.Tau := Fintype.card_pos_iff.1 (by
    rw [D.what₂.card_Tau]; unfold Ranks.f Ranks.n; positivity)
  obtain ⟨τ₀⟩ := id hT
  obtain ⟨al, be, hE⟩ := hS
  set a : ℕ → ℝ := fun B => al B + ∑ p ∈ newPrimes Y B₀ B, Real.log p / ((p : ℝ) - 1) with ha
  set b : ℕ → ℝ := fun B => be B - ∑ p ∈ newPrimes Y B₀ B, Real.log p / Y.N * kap Y p τ₀ with hb
  have key : ∀ Q, Cof Y Q → ∀ᶠ B : ℕ in atTop,
      Φ B₀ (comb Y Q) = Y.vol * (hh (comb Y Q) - a B * shAll Y (comb Y Q) - b B * totAll Y (comb Y Q)) +
        (∑ p ∈ newPrimes Y B₀ B, restTerm Y p Q) +
        (Φ B (comb Y Q) - Y.vol * (hh (comb Y Q) - al B * shAll Y (comb Y Q) - be B * totAll Y (comb Y Q))) := by
    intro Q hQ
    filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop B₀] with B hB
    rw [hC B₀ B hB₀ hB Q hQ]
    have hk : ∀ p : ℕ, (∑ τ, kap Y p τ * totF τ (comb Y Q)) = kap Y p τ₀ * totAll Y (comb Y Q) := by
      intro p
      unfold totAll
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun τ _ => by rw [GlobalTheory.T.kappa_independent_of_embedding D Y p τ τ₀])
    simp only [hk, ha, hb]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    have e1 : ∑ p ∈ newPrimes Y B₀ B, -(Real.log p / ((p : ℝ) - 1)) * Y.vol * shAll Y (comb Y Q) =
        -(∑ p ∈ newPrimes Y B₀ B, Real.log p / ((p : ℝ) - 1)) * Y.vol * shAll Y (comb Y Q) := by
      rw [← Finset.sum_mul, ← Finset.sum_mul, Finset.sum_neg_distrib]
    have e2 : ∑ p ∈ newPrimes Y B₀ B, Real.log p / Y.N * Y.vol * (kap Y p τ₀ * totAll Y (comb Y Q)) =
        (∑ p ∈ newPrimes Y B₀ B, Real.log p / Y.N * kap Y p τ₀) * (Y.vol * totAll Y (comb Y Q)) := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun p _ => by ring)
    rw [e1, e2]
    ring
  obtain ⟨A, b₀, hA, hb₀⟩ := GlobalTheory.T.limits_of_shift_functionals D.what₂.Tau Y.N Y.j a b Y.j_pos Y.j_lt (by
    intro F hF
    obtain ⟨Q, hQ, hFQ⟩ := GlobalTheory.T.power_sum_decomposition_homogeneous D.what₂.Tau Y.N F hF
    have hQ' : Cof Y Q := hQ
    have hFQ' : F = comb Y Q := hFQ
    obtain ⟨L, hL⟩ := GlobalTheory.T.remainder_sum_converges D Y B₀ Q (by linarith)
    have h0 := hE F hF
    refine ⟨hh F - (Φ B₀ F - L - 0) / Y.vol, ?_⟩
    refine (tendsto_const_nhds.sub (((tendsto_const_nhds.sub hL).sub h0).div_const Y.vol)).congr' ?_
    filter_upwards [key Q hQ'] with B hB
    rw [← hFQ'] at hB
    change _ = a B * shAll Y F + b B * totAll Y F
    rw [hB]
    field_simp
    ring)
  refine ⟨A, b₀, fun Q hQ => ?_⟩
  have h0 := hE _ (comb_isHomogeneous_of_cof Y Q hQ)
  have h1 := ((tendsto_const_nhds (x := Φ B₀ (comb Y Q))).sub
    ((((tendsto_const_nhds (x := hh (comb Y Q))).sub (hA.mul_const (shAll Y (comb Y Q)))).sub
      (hb₀.mul_const (totAll Y (comb Y Q)))).const_mul Y.vol)).sub h0
  rw [sub_zero] at h1
  refine h1.congr' ?_
  filter_upwards [key Q hQ] with B hB
  linarith

end GlobalTheory.Mean4
