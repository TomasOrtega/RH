import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFLeib
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdjointLeibnizExpansion

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/- English proof (translation)
Introduce `n x hx`. Establish `h` using `(Real.hasDerivAt_rpow_const (p := s) (Or.inl hx.ne')).const_mul (s ^ n)`. Establish `e : s ^ (n + 1) * x ^ s / x = s ^ n * (s * x ^ (s - 1))`. Rewrite using `[Real.rpow_sub_one hx.ne', pow_succ]`. Expand and normalize the polynomial expressions, which then agree.

Use `show HasDerivAt (fun y => s ^ n * y ^ s) (s ^ (n + 1) * x ^ s / x) x`. Rewrite using `[e]`. Conclude with `h`.
-/
theorem nfLeib_thChain_rpow (s : ℝ) : ThChain (fun n x => s ^ n * x ^ s) := by
  intro n x hx
  have h := (Real.hasDerivAt_rpow_const (p := s) (Or.inl hx.ne')).const_mul (s ^ n)
  have e : s ^ (n + 1) * x ^ s / x = s ^ n * (s * x ^ (s - 1)) := by
    rw [Real.rpow_sub_one hx.ne', pow_succ]
    ring
  show HasDerivAt (fun y => s ^ n * y ^ s) (s ^ (n + 1) * x ^ s / x) x
  rw [e]
  exact h

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => simpa using hφ`. Consider the case `succ n ih`. Rewrite using `[Function.iterate_succ_apply']`.

Unfold `xD`. Conclude with `contDiff_id.mul (contDiff_infty_iff_deriv.1 ih).2`.
-/
theorem nfLeib_xD_contDiff (φ : ℝ → ℝ) (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) :
    ∀ n : ℕ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (xD^[n] φ) := by
  intro n
  induction n with
  | zero => simpa using hφ
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    unfold xD
    exact contDiff_id.mul (contDiff_infty_iff_deriv.1 ih).2

/- English proof (translation)
Introduce `n x hx`. Establish `h` using `nfLeib_xD_contDiff φ hφ n`. Establish `hd` using `((contDiff_infty_iff_deriv.1 h).1 x).hasDerivAt`. Establish `hx0 : x ≠ 0` using `hx.ne'`. Establish `e : xD^[n + 1] φ x / x = deriv (xD^[n] φ) x`.

Rewrite using `[Function.iterate_succ_apply']`. Use `show x * deriv (xD^[n] φ) x / x = _`. Clear the denominators using the available nonvanishing facts. Use `show HasDerivAt (xD^[n] φ) (xD^[n + 1] φ x / x) x`. Rewrite using `[e]`.

Conclude with `hd`.
-/
theorem nfLeib_thChain_xD (φ : ℝ → ℝ) (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) :
    ThChain (fun n => xD^[n] φ) := by
  intro n x hx
  have h := nfLeib_xD_contDiff φ hφ n
  have hd := ((contDiff_infty_iff_deriv.1 h).1 x).hasDerivAt
  have hx0 : x ≠ 0 := hx.ne'
  have e : xD^[n + 1] φ x / x = deriv (xD^[n] φ) x := by
    rw [Function.iterate_succ_apply']
    show x * deriv (xD^[n] φ) x / x = _
    field_simp
  show HasDerivAt (xD^[n] φ) (xD^[n + 1] φ x / x) x
  rw [e]
  exact hd

section cont

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

/- English proof (translation)
Unfold `B.CkOn at h`. Introduce `g₀ hg₀`. Take `⟨U, f', hU, hgU, hc, he⟩` from `h g₀ hg₀`. Establish `hcont : ContinuousAt f' g₀` using `hc.continuousOn.continuousAt (hU.mem_nhds hgU)`. Establish `heq : f =ᶠ[𝓝[UU] g₀] f'` using `by filter_upwards [nhdsWithin_le_nhds (hU.mem_nhds hgU), self_mem_nhdsWithin] with g hgU' hgUU`.

Conclude with `he g hgU' (hUU hgUU)`. Conclude with `hcont.continuousWithinAt.congr_of_eventuallyEq heq (he g₀ hgU (hUU hg₀))`.
-/
theorem nfLeib_ckOn_contOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {m : ℕ∞} {UU : Set (B.Mat k r)}
    (hUU : UU ⊆ B.GV k r) {f : B.Mat k r → E} (h : B.CkOn m UU f) : ContinuousOn f UU := by
  unfold B.CkOn at h
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hc, he⟩ := h g₀ hg₀
  have hcont : ContinuousAt f' g₀ := hc.continuousOn.continuousAt (hU.mem_nhds hgU)
  have heq : f =ᶠ[𝓝[UU] g₀] f' := by
    filter_upwards [nhdsWithin_le_nhds (hU.mem_nhds hgU), self_mem_nhdsWithin] with g hgU' hgUU
    exact he g hgU' (hUU hgUU)
  exact hcont.continuousWithinAt.congr_of_eventuallyEq heq (he g₀ hgU (hUU hg₀))

/- English proof (translation)
Unfold `C6.domL B.GPos`. Use extensionality with `g`. Simplify using the standard rewrite rules.
-/
theorem nfLeib_domL_eq (Bs : B.RealPlaceData k r Wp Wq) : C6.domL Bs ∅ = B.GPos Bs := by
  unfold C6.domL B.GPos
  ext g
  simp

/- English proof (translation)
Proceed by induction on `L with`. Consider the case `nil`. Establish `e : B.opApply ([] : B.DiffOp k r Wp Wq) F = fun _ => 0` using `by funext g; simp [B.opApply]`. Rewrite using `[e]`. Conclude with `continuousOn_const`.

Consider the case `cons T L ih`. Establish `e : B.opApply (T :: L) F = fun g => T.coef g (B.Rw T.word F g) + B.opApply L F g`. Use function extensionality and compare the values at `g`. Simplify using `[B.opApply]`. Rewrite using `[e]`.

Use `ContinuousOn.add ?_ (ih fun T' hT' => hL T' (List.mem_cons_of_mem _ hT'))` and prove the remaining obligations. Establish `h1 : ContinuousOn T.coef (B.GPos Bs)`. Rewrite using `[← nfLeib_domL_eq Bs]`. Conclude with `nfLeib_ckOn_contOn (fun g hg => hg.1) (hL T List.mem_cons_self).1`. Establish `h2 : ContinuousOn (B.Rw T.word F) (B.GPos Bs)` using `(nfLeib_ckOn_contOn le_rfl (JFxI.ckOn_Rw_top' hF T.word T.word_lie)).mono fun g hg => hg.1`.

Conclude with `h1.clm_apply h2`.
-/
theorem nfLeib_opApply_contOn (Bs : B.RealPlaceData k r Wp Wq) (L : B.DiffOp k r Wp Wq)
    (hL : B.SmoothCoef (C6.domL Bs ∅) L) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (hF : B.CkOn ⊤ (B.GV k r) F) :
    ContinuousOn (B.opApply L F) (B.GPos Bs) := by
  induction L with
  | nil =>
    have e : B.opApply ([] : B.DiffOp k r Wp Wq) F = fun _ => 0 := by funext g; simp [B.opApply]
    rw [e]; exact continuousOn_const
  | cons T L ih =>
    have e : B.opApply (T :: L) F = fun g => T.coef g (B.Rw T.word F g) + B.opApply L F g := by
      funext g; simp [B.opApply]
    rw [e]
    refine ContinuousOn.add ?_ (ih fun T' hT' => hL T' (List.mem_cons_of_mem _ hT'))
    have h1 : ContinuousOn T.coef (B.GPos Bs) := by
      rw [← nfLeib_domL_eq Bs]
      exact nfLeib_ckOn_contOn (fun g hg => hg.1) (hL T List.mem_cons_self).1
    have h2 : ContinuousOn (B.Rw T.word F) (B.GPos Bs) :=
      (nfLeib_ckOn_contOn le_rfl (JFxI.ckOn_Rw_top' hF T.word T.word_lie)).mono fun g hg => hg.1
    exact h1.clm_apply h2

end cont

/- English proof (translation)
Establish `hM : Cb ≤ max Cb 0` using `le_max_left _ _`. Establish `hM0 : 0 ≤ max Cb 0` using `le_max_right _ _`. Establish `hc : c₃ ≤ max c₃ 0` using `le_max_left _ _`. Establish `hc0 : 0 ≤ max c₃ 0` using `le_max_right _ _`. Use `set M := max Cb 0 with hMd`.

Use `set c := max c₃ 0 with hcd`. Use `set T := 2 * R + Kk + 1 with hTd`. Use `clear_value M c T`. Establish `hTR : R + 1 ≤ T` using `by rw [hTd]; linarith`. Establish `hT1 : 1 ≤ T` using `by linarith`.

Establish `hT0 : 0 ≤ T` using `by linarith`. Establish `hR1 : 1 ≤ R + 1` using `by linarith`. Establish `hR0 : 0 ≤ R + 1` using `by linarith`. Establish `ho' : o ≤ M * W * T`. Establish `: Cb * W * T ≤ M * W * T` using `mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hM hW) hT0`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hκ' : κ ≤ M * (R + 1) * o` using `hκ.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hM hR0) ho0)`. Establish `hR2 : R + 1 ≤ (R + 1) ^ 2`. Use `mul_le_mul_of_nonneg_left hR1 hR0` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hR4 : (R + 1) ^ 2 ≤ (R + 1) ^ 4`. Establish `h1 : 1 ≤ (R + 1) ^ 2` using `by linarith`. Use `mul_le_mul_of_nonneg_left h1 (sq_nonneg (R + 1))` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hR14 : R + 1 ≤ (R + 1) ^ 4` using `hR2.trans hR4`.

Establish `hT2 : T ≤ T ^ 2`. Use `mul_le_mul_of_nonneg_left hT1 hT0` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hT3 : T ^ 2 ≤ T ^ 3`. Use `mul_le_mul_of_nonneg_left hT1 (sq_nonneg T)` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hRT : R * T + 1 ≤ T ^ 2`. Use `mul_le_mul_of_nonneg_right hTR hT0` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hRT0 : 0 ≤ R * T + 1`.

Use `mul_nonneg hR hT0` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hX0 : 0 ≤ (R + 1) ^ 2 * (R * T + 1)` using `mul_nonneg (sq_nonneg _) hRT0`. Establish `hXY : (R + 1) ^ 2 * (R * T + 1) ≤ (R + 1) ^ 4 * T ^ 3` using `mul_le_mul hR4 (hRT.trans hT3) hRT0 (by positivity)`. Establish `h1 : c₃ * (R + 1) ^ 2 * (R * T + 1) ≤ c * ((R + 1) ^ 4 * T ^ 3)`.

Establish `e1` using `mul_le_mul_of_nonneg_right hc hX0`. Establish `e2` using `mul_le_mul_of_nonneg_left hXY hc0`. Combine the equalities or inequalities in the displayed calculation. Establish `hMR : 0 ≤ (M + 5) * (R + 1)` using `mul_nonneg (by linarith) hR0`. Establish `h3` using `mul_le_mul_of_nonneg_left ho' hMR`.

Establish `hS : 0 ≤ M ^ 2 + 5 * M` using `add_nonneg (sq_nonneg M) (by linarith)`. Establish `hZ : 0 ≤ (M ^ 2 + 5 * M) * W` using `mul_nonneg hS hW`. Establish `hRT4 : (R + 1) * T ≤ (R + 1) ^ 4 * T ^ 2` using `mul_le_mul hR14 hT2 hT0 (by positivity)`. Establish `h4` using `mul_le_mul_of_nonneg_left hRT4 hZ`. Establish `h5 : 0 ≤ (M ^ 2 + 5 * M) * ((R + 1) ^ 4 * T ^ 3)` using `mul_nonneg hS (mul_nonneg (by positivity) (pow_nonneg hT0 3))`.

Establish `h6 : 0 ≤ c * ((R + 1) ^ 4 * (W * T ^ 2))` using `mul_nonneg hc0 (mul_nonneg (by positivity) (mul_nonneg hW (sq_nonneg T)))`. Combine the linear relations using `[h1, h3, h4, h5, h6, hA, hκ']`.
-/
theorem nfLeib_thr (Cb c₃ R Kk W o κ A : ℝ) (hR : 0 ≤ R) (hK : 0 ≤ Kk) (hW : 0 ≤ W) (ho0 : 0 ≤ o) (hκ0 : 0 ≤ κ)
    (ho : o ≤ Cb * W * (2 * R + Kk + 1)) (hκ : κ ≤ Cb * (R + 1) * o)
    (hA : (max Cb 0 ^ 2 + 5 * max Cb 0 + max c₃ 0) * (R + 1) ^ 4 *
      (W * (2 * R + Kk + 1) ^ 2 + (2 * R + Kk + 1) ^ 3) ≤ A) :
    c₃ * (R + 1) ^ 2 * (R * (2 * R + Kk + 1) + 1) ≤ A - (κ + 3 * (R + 1) * o + (2 * R + 2) * o) := by
  have hM : Cb ≤ max Cb 0 := le_max_left _ _
  have hM0 : 0 ≤ max Cb 0 := le_max_right _ _
  have hc : c₃ ≤ max c₃ 0 := le_max_left _ _
  have hc0 : 0 ≤ max c₃ 0 := le_max_right _ _
  set M := max Cb 0 with hMd
  set c := max c₃ 0 with hcd
  set T := 2 * R + Kk + 1 with hTd
  clear_value M c T
  have hTR : R + 1 ≤ T := by rw [hTd]; linarith
  have hT1 : 1 ≤ T := by linarith
  have hT0 : 0 ≤ T := by linarith
  have hR1 : 1 ≤ R + 1 := by linarith
  have hR0 : 0 ≤ R + 1 := by linarith
  have ho' : o ≤ M * W * T := by
    have : Cb * W * T ≤ M * W * T :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hM hW) hT0
    linarith
  have hκ' : κ ≤ M * (R + 1) * o :=
    hκ.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hM hR0) ho0)
  have hR2 : R + 1 ≤ (R + 1) ^ 2 := by
    have := mul_le_mul_of_nonneg_left hR1 hR0
    linarith
  have hR4 : (R + 1) ^ 2 ≤ (R + 1) ^ 4 := by
    have h1 : 1 ≤ (R + 1) ^ 2 := by linarith
    have := mul_le_mul_of_nonneg_left h1 (sq_nonneg (R + 1))
    linarith
  have hR14 : R + 1 ≤ (R + 1) ^ 4 := hR2.trans hR4
  have hT2 : T ≤ T ^ 2 := by
    have := mul_le_mul_of_nonneg_left hT1 hT0
    linarith
  have hT3 : T ^ 2 ≤ T ^ 3 := by
    have := mul_le_mul_of_nonneg_left hT1 (sq_nonneg T)
    linarith
  have hRT : R * T + 1 ≤ T ^ 2 := by
    have := mul_le_mul_of_nonneg_right hTR hT0
    linarith
  have hRT0 : 0 ≤ R * T + 1 := by
    have := mul_nonneg hR hT0
    linarith
  have hX0 : 0 ≤ (R + 1) ^ 2 * (R * T + 1) := mul_nonneg (sq_nonneg _) hRT0
  have hXY : (R + 1) ^ 2 * (R * T + 1) ≤ (R + 1) ^ 4 * T ^ 3 :=
    mul_le_mul hR4 (hRT.trans hT3) hRT0 (by positivity)
  have h1 : c₃ * (R + 1) ^ 2 * (R * T + 1) ≤ c * ((R + 1) ^ 4 * T ^ 3) := by
    have e1 := mul_le_mul_of_nonneg_right hc hX0
    have e2 := mul_le_mul_of_nonneg_left hXY hc0
    calc c₃ * (R + 1) ^ 2 * (R * T + 1) = c₃ * ((R + 1) ^ 2 * (R * T + 1)) := by ring
      _ ≤ c * ((R + 1) ^ 4 * T ^ 3) := e1.trans e2
  have hMR : 0 ≤ (M + 5) * (R + 1) := mul_nonneg (by linarith) hR0
  have h3 := mul_le_mul_of_nonneg_left ho' hMR
  have hS : 0 ≤ M ^ 2 + 5 * M := add_nonneg (sq_nonneg M) (by linarith)
  have hZ : 0 ≤ (M ^ 2 + 5 * M) * W := mul_nonneg hS hW
  have hRT4 : (R + 1) * T ≤ (R + 1) ^ 4 * T ^ 2 := mul_le_mul hR14 hT2 hT0 (by positivity)
  have h4 := mul_le_mul_of_nonneg_left hRT4 hZ
  have h5 : 0 ≤ (M ^ 2 + 5 * M) * ((R + 1) ^ 4 * T ^ 3) :=
    mul_nonneg hS (mul_nonneg (by positivity) (pow_nonneg hT0 3))
  have h6 : 0 ≤ c * ((R + 1) ^ 4 * (W * T ^ 2)) :=
    mul_nonneg hc0 (mul_nonneg (by positivity) (mul_nonneg hW (sq_nonneg T)))
  linarith [h1, h3, h4, h5, h6, hA, hκ']

/- English proof (translation)
Take `⟨c₃, hc₃⟩` from `hV`. Introduce `Cb`. Use `⟨max Cb 0 ^ 2 + 5 * max Cb 0 + max c₃ 0, ?_⟩` and prove the remaining obligations. Introduce `Wp Wq _ _ _ _ _ _ P p hInD w hw e`. Take `⟨nf, fib, o, κ, Dop, hfib, hIn, ho, hκ, hΘ⟩` from `hInD w hw e`.

Take `⟨Q, L, hsm, hterm, hexp⟩` from `hO P.k P.r Wp Wq p.T.base Dop hIn.1`. Use `⟨Q, L, hsm, ?_, ?_⟩` and prove the remaining obligations. Introduce `s F hF g hg`. Establish `hG : 0 < Gf P.k P.r p.T.base.z p.T.base.z' g` using `hg.2.1`. Establish `e1 : (fun g' => ((Gf P.k P.r p.T.base.z p.T.base.z' g' ^ s : ℝ) : ℂ) • F g') = fun y => (((fun (n : ℕ) (x : ℝ) => s ^ n * x ^ s) 0 (Gf P.k P.r p.T.base.z p.T.base.z' y) : ℝ) : ℂ) • F y`.

Use function extensionality and compare the values at `y`. Simplify using the standard rewrite rules. Rewrite using `[hΘ _ g hg, e1, hexp _ (nfLeib_thChain_rpow s) F hF g hg, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations. Rewrite using `[smul_smul]`.

Use `congr 1`. Rewrite using `[← Complex.ofReal_mul]`. Use `congr 1`. Establish `hp : 0 < Gf P.k P.r p.T.base.z p.T.base.z' g ^ s` using `Real.rpow_pos_of_pos hG s`. Rewrite using `[Real.rpow_neg hG.le]`.

Clear the denominators using the available nonvanishing facts. Introduce `φ hφ F A hF hdec hA γ hγ hGγ`. Take `⟨b, hb⟩` from `hdec o`. Use `set m : ℝ := (κ : ℝ) + 3 * ((P.r : ℝ) + 1) * o + (2 * (P.r : ℝ) + 2) * o with hm`. Establish `hdecq : ∀ q : Fin (Q + 1), ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ g ∈ B.GV P.k P.r, ε ≤ Gf P.k P.r p.T.base.z p.T.base.z' g → ‖B.opApply (L q) F g‖ ≤ C * B.gN g ^ (-(A - m))`.

Introduce `q ε hε`. Take `⟨K, -, hK⟩` from `hB P.k P.r Wp Wq p.T.base nf fib o κ Dop hfib hIn (L q) (hterm q) ε hε`. Use `⟨K * b, fun g hg hgε => ?_⟩` and prove the remaining obligations. Use `hK F A b hb g hg hgε` as an intermediate fact. Establish `ee : (κ : ℝ) + 3 * ((P.r : ℝ) + 1) * o + (2 * (P.r : ℝ) + 2) * o - A = -(A - m)` using `by rw [hm]; ring`.

Rewrite `this` using `[ee]`. Then use the resulting hypothesis. Establish `hthr : c₃ * ((P.r : ℝ) + 1) ^ 2 * ((P.r : ℝ) * ((2 * P.r + P.k + 1 : ℕ) : ℝ) + 1) ≤ A - m`. Establish `h0` using `nfLeib_thr Cb c₃ P.r P.k w.length o κ A (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by push_cast at ho; linarith) hκ (by linarith)`. Use `push_cast`. Rewrite using `[hm]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hsplit : ∀ g ∈ B.GPos p.T.base, p.Θ.Θ w e (fun g => ((φ (Gf P.k P.r p.T.base.z p.T.base.z' g) : ℝ) : ℂ) • F g) g = ∑ q : Fin (Q + 1), (fun (q : Fin (Q + 1)) (x : ℝ) => ((xD^[(q : ℕ)] φ x : ℝ) : ℂ)) q (Gf P.k P.r p.T.base.z p.T.base.z' g) • B.opApply (L q) F g`. Introduce `g hg`. Establish `hgd : g ∈ C6.domL p.T.base ∅` using `by rw [nfLeib_domL_eq]; exact hg`. Rewrite using `[hΘ _ g hgd]`.

Conclude with `hexp (fun n => xD^[n] φ) (nfLeib_thChain_xD φ hφ) F hF g hgd`. Conclude with `hc₃ P.k P.r Wp Wq p.T.base p.ν' p.m₀ Q (fun q x => ((xD^[(q : ℕ)] φ x : ℝ) : ℂ)) _ (fun q => B.opApply (L q) F) (A - m) hthr (fun q => nfLeib_opApply_contOn p.T.base (L q) (hsm q) F hF) hdecq hsplit γ hγ hGγ`.
-/
theorem nfLeibV_of (hO : NFLeibOps) (hB : NFLeibBd) (hV : NFVLin) : NFLeibV := by
  obtain ⟨c₃, hc₃⟩ := hV
  intro Cb
  refine ⟨max Cb 0 ^ 2 + 5 * max Cb 0 + max c₃ 0, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p hInD w hw e
  obtain ⟨nf, fib, o, κ, Dop, hfib, hIn, ho, hκ, hΘ⟩ := hInD w hw e
  obtain ⟨Q, L, hsm, hterm, hexp⟩ := hO P.k P.r Wp Wq p.T.base Dop hIn.1
  refine ⟨Q, L, hsm, ?_, ?_⟩
  · intro s F hF g hg
    have hG : 0 < Gf P.k P.r p.T.base.z p.T.base.z' g := hg.2.1
    have e1 : (fun g' => ((Gf P.k P.r p.T.base.z p.T.base.z' g' ^ s : ℝ) : ℂ) • F g') =
        fun y => (((fun (n : ℕ) (x : ℝ) => s ^ n * x ^ s) 0 (Gf P.k P.r p.T.base.z p.T.base.z' y) : ℝ) : ℂ) •
          F y := by
      funext y; simp
    rw [hΘ _ g hg, e1, hexp _ (nfLeib_thChain_rpow s) F hF g hg, Finset.smul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [smul_smul]
    congr 1
    rw [← Complex.ofReal_mul]
    congr 1
    have hp : 0 < Gf P.k P.r p.T.base.z p.T.base.z' g ^ s := Real.rpow_pos_of_pos hG s
    rw [Real.rpow_neg hG.le]
    field_simp
  · intro φ hφ F A hF hdec hA γ hγ hGγ
    obtain ⟨b, hb⟩ := hdec o
    set m : ℝ := (κ : ℝ) + 3 * ((P.r : ℝ) + 1) * o + (2 * (P.r : ℝ) + 2) * o with hm
    have hdecq : ∀ q : Fin (Q + 1), ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ g ∈ B.GV P.k P.r,
        ε ≤ Gf P.k P.r p.T.base.z p.T.base.z' g → ‖B.opApply (L q) F g‖ ≤ C * B.gN g ^ (-(A - m)) := by
      intro q ε hε
      obtain ⟨K, -, hK⟩ := hB P.k P.r Wp Wq p.T.base nf fib o κ Dop hfib hIn (L q) (hterm q) ε hε
      refine ⟨K * b, fun g hg hgε => ?_⟩
      have := hK F A b hb g hg hgε
      have ee : (κ : ℝ) + 3 * ((P.r : ℝ) + 1) * o + (2 * (P.r : ℝ) + 2) * o - A = -(A - m) := by rw [hm]; ring
      rwa [ee] at this
    have hthr : c₃ * ((P.r : ℝ) + 1) ^ 2 * ((P.r : ℝ) * ((2 * P.r + P.k + 1 : ℕ) : ℝ) + 1) ≤ A - m := by
      have h0 := nfLeib_thr Cb c₃ P.r P.k w.length o κ A (by positivity) (by positivity) (by positivity)
        (by positivity) (by positivity) (by push_cast at ho; linarith) hκ (by linarith)
      push_cast
      rw [hm]
      linarith
    have hsplit : ∀ g ∈ B.GPos p.T.base, p.Θ.Θ w e
        (fun g => ((φ (Gf P.k P.r p.T.base.z p.T.base.z' g) : ℝ) : ℂ) • F g) g =
        ∑ q : Fin (Q + 1), (fun (q : Fin (Q + 1)) (x : ℝ) => ((xD^[(q : ℕ)] φ x : ℝ) : ℂ)) q
          (Gf P.k P.r p.T.base.z p.T.base.z' g) • B.opApply (L q) F g := by
      intro g hg
      have hgd : g ∈ C6.domL p.T.base ∅ := by rw [nfLeib_domL_eq]; exact hg
      rw [hΘ _ g hgd]
      exact hexp (fun n => xD^[n] φ) (nfLeib_thChain_xD φ hφ) F hF g hgd
    exact hc₃ P.k P.r Wp Wq p.T.base p.ν' p.m₀ Q (fun q x => ((xD^[(q : ℕ)] φ x : ℝ) : ℂ)) _
      (fun q => B.opApply (L q) F) (A - m) hthr
      (fun q => nfLeib_opApply_contOn p.T.base (L q) (hsm q) F hF) hdecq hsplit γ hγ hGγ

end

end Formalism.FourierDecayAlt.P.CutBP
