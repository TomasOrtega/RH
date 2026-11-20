import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsTopNMixed
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PTopNPoly
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PVertFactorPos
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

namespace TopNMixedExpand

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

/- English proof (translation)
Rewrite using `[← Finset.prod_pow, ← Finset.prod_pow, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Establish `h0 : ‖c k‖ ≠ 0` using `norm_ne_zero_iff.mpr (hc k)`. Simplify using `only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]`. Rewrite using `[zpow_add₀ h0, show (q : ℤ) * a k = a k * q by ring, show (p : ℤ) * b k = b k * p by ring, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast]`.
-/
theorem prod_norm_zpow_comb {c : K → ℂ} (hc : ∀ k, c k ≠ 0) (a b : K → ℤ) (q p : ℕ) :
    (∏ k, ‖c k‖ ^ ((q : ℤ) • a + (p : ℤ) • b) k) = (∏ k, ‖c k‖ ^ a k) ^ q * (∏ k, ‖c k‖ ^ b k) ^ p := by
  rw [← Finset.prod_pow, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  have h0 : ‖c k‖ ≠ 0 := norm_ne_zero_iff.mpr (hc k)
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [zpow_add₀ h0, show (q : ℤ) * a k = a k * q by ring, show (p : ℤ) * b k = b k * p by ring,
    zpow_mul, zpow_mul, zpow_natCast, zpow_natCast]

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
  {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]
  {D : ComponentData II Ψ K ι Ω E} {O Lt : Type} [CommRing O] [AddCommGroup Lt] [Module O Lt]

omit [DecidableEq Ψ] in

/- English proof (translation)
Take `⟨c, hc, hzc⟩` from `exists_eq_smul_orbitRep z`. Establish `hz0` using `hz.1`. Establish `hw0` using `TopNPoly.orbitRep_blocks hz0`. Establish `hwP : orbitRep z ∈ mcPts (mCoordIdeal D.y)`. Establish `h` using `mcPts_smul D.arith.2.1.2.1 (fun k => (c k)⁻¹) (fun k => inv_ne_zero (hc k)) hz`.

Use `h using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `p`. Establish `hp : z p = c p.1 * orbitRep z p` using `congrFun hzc p`. Rewrite using `[hp, ← mul_assoc, inv_mul_cancel₀ (hc _), one_mul]`. Establish `hvf : 0 < ∏ p' ∈ D.SB B, D.vertFactor p' (orbitRep z)` using `Finset.prod_pos fun p' hp' => VertFactorPos.proof II Ψ K ι Ω E D p' (Finset.mem_filter.1 hp').1 _ hwP`.

Establish `hG0 : 0 < X.S.ref.h (orbitRep z) * Real.exp (X.S.regWeight t (X.M.proj (orbitRep z)))` using `mul_pos (X.S.ref.pos _ hw0) (Real.exp_pos _)`. Establish `hreg : (X.S.regLine t).h (orbitRep z) = X.S.ref.h (orbitRep z) * Real.exp (X.S.regWeight t (X.M.proj (orbitRep z)))` using `TopNPoly.hermOfFun_h_orbitRep hz0 hG0`. Establish `hM : (muReg X.H X.S B t).h z = (∏ k, ‖c k‖ ^ muTwDeg X.H B k) * ((X.S.regLine t).h (orbitRep z) * ∏ p' ∈ D.SB B, D.vertFactor p' (orbitRep z))`. Unfold `muReg`. Rewrite using `[smoothRep_h _ hz]`.

Conclude with `TopNPoly.hermOfFun_h_smul hc hzc hz0 (by rw [hreg]; exact mul_pos hG0 hvf)`. Establish `hN : (X.NbarQ B p q t).h z = (∏ k, ‖c k‖ ^ ((q : ℤ) • muTwDeg X.H B + (p : ℤ) • D.a') k) * ((X.S.ref.h (orbitRep z) * Real.exp (X.S.regWeight t (X.M.proj (orbitRep z)))) ^ q * (∏ p' ∈ D.SB B, D.vertFactor p' (orbitRep z)) ^ q * D.A'.h (orbitRep z) ^ p)`. Unfold `ComponentSetting.NbarQ`. Rewrite using `[smoothRep_h _ hz]`. Conclude with `TopNPoly.hermOfFun_h_smul hc hzc hz0 (mul_pos (mul_pos (pow_pos hG0 _) (pow_pos hvf _)) (pow_pos (D.A'.pos _ hw0) _))`.

Establish `hA : D.A'.h z = (∏ k, ‖c k‖ ^ D.a' k) * D.A'.h (orbitRep z)` using `by conv_lhs => rw [hzc]`. Conclude with `(D.A'.smul c (orbitRep z) hc).trans (by rw [D.A'_deg])`. Rewrite using `[hN, hM, hA, hreg, prod_norm_zpow_comb hc]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem NbarQ_h_eq (X : ComponentSetting D O Lt) (B p q : ℕ) (t : ℝ)
    {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal D.y)) :
    (X.NbarQ B p q t).h z = (muReg X.H X.S B t).h z ^ q * D.A'.h z ^ p := by
  obtain ⟨c, hc, hzc⟩ := exists_eq_smul_orbitRep z
  have hz0 := hz.1
  have hw0 := TopNPoly.orbitRep_blocks hz0
  have hwP : orbitRep z ∈ mcPts (mCoordIdeal D.y) := by
    have h := mcPts_smul D.arith.2.1.2.1 (fun k => (c k)⁻¹) (fun k => inv_ne_zero (hc k)) hz
    convert h using 1
    funext p
    have hp : z p = c p.1 * orbitRep z p := congrFun hzc p
    rw [hp, ← mul_assoc, inv_mul_cancel₀ (hc _), one_mul]
  have hvf : 0 < ∏ p' ∈ D.SB B, D.vertFactor p' (orbitRep z) :=
    Finset.prod_pos fun p' hp' => VertFactorPos.proof II Ψ K ι Ω E D p' (Finset.mem_filter.1 hp').1 _ hwP
  have hG0 : 0 < X.S.ref.h (orbitRep z) * Real.exp (X.S.regWeight t (X.M.proj (orbitRep z))) :=
    mul_pos (X.S.ref.pos _ hw0) (Real.exp_pos _)
  have hreg : (X.S.regLine t).h (orbitRep z) =
      X.S.ref.h (orbitRep z) * Real.exp (X.S.regWeight t (X.M.proj (orbitRep z))) :=
    TopNPoly.hermOfFun_h_orbitRep hz0 hG0
  have hM : (muReg X.H X.S B t).h z = (∏ k, ‖c k‖ ^ muTwDeg X.H B k) *
      ((X.S.regLine t).h (orbitRep z) * ∏ p' ∈ D.SB B, D.vertFactor p' (orbitRep z)) := by
    unfold muReg
    rw [smoothRep_h _ hz]
    exact TopNPoly.hermOfFun_h_smul hc hzc hz0 (by rw [hreg]; exact mul_pos hG0 hvf)
  have hN : (X.NbarQ B p q t).h z = (∏ k, ‖c k‖ ^ ((q : ℤ) • muTwDeg X.H B + (p : ℤ) • D.a') k) *
      ((X.S.ref.h (orbitRep z) * Real.exp (X.S.regWeight t (X.M.proj (orbitRep z)))) ^ q *
        (∏ p' ∈ D.SB B, D.vertFactor p' (orbitRep z)) ^ q * D.A'.h (orbitRep z) ^ p) := by
    unfold ComponentSetting.NbarQ
    rw [smoothRep_h _ hz]
    exact TopNPoly.hermOfFun_h_smul hc hzc hz0
      (mul_pos (mul_pos (pow_pos hG0 _) (pow_pos hvf _)) (pow_pos (D.A'.pos _ hw0) _))
  have hA : D.A'.h z = (∏ k, ‖c k‖ ^ D.a' k) * D.A'.h (orbitRep z) := by
    conv_lhs => rw [hzc]
    exact (D.A'.smul c (orbitRep z) hc).trans (by rw [D.A'_deg])
  rw [hN, hM, hA, hreg, prod_norm_zpow_comb hc]
  ring

end TopNMixedExpand

open TopNMixedExpand in

/- English proof (translation)
Introduce `II Ψ _ _ K _ ι _ Ω _ _ E _ _ D O Lt _ _ _ X B p q hII hp hpq`. Establish `hP : IsArithVar (mCoordIdeal D.y) (D.n + 1)` using `D.arith`. Establish `hA : IsSmoothHerm D.A'` using `D.A'_pos.1`. Use `filter_upwards [hS II Ψ K ι Ω E D O Lt X B] with t ht`. Establish `hq0 : (q : ℝ) ≠ 0` using `Nat.cast_ne_zero.2 (by omega)`.

Use `set Z := HilbertSamuel.HermLine.zcomb (muReg X.H X.S B t) D.A' (q : ℤ) (p : ℤ) with hZdef`. Establish `hZ : IsSmoothHerm Z` using `HilbertSamuel.ZCombLimit.isSmoothHerm_zcomb_int ht hA _ _`. Establish `hagree : ∀ z ∈ mcPts (mCoordIdeal D.y), Z.h z = (X.NbarQ B p q t).h z`. Introduce `z hz`. Rewrite using `[NbarQ_h_eq X B p q t hz]`.

Use `show (muReg X.H X.S B t).h z ^ (q : ℤ) * D.A'.h z ^ (p : ℤ) = _`. Simplify using the standard rewrite rules. Establish `hdeg : Z.a = (X.NbarQ B p q t).a`. Unfold `ComponentSetting.NbarQ`. Rewrite using `[smoothRep_a]`.

Use `show (q : ℤ) • (muReg X.H X.S B t).a + (p : ℤ) • D.A'.a = _`. Rewrite using `[muReg, smoothRep_a, D.A'_deg]`. Both sides reduce to the same expression. Establish `hN : IsSmoothHerm (X.NbarQ B p q t)`. Unfold `ComponentSetting.NbarQ`.

Use `TopNPoly.smoothRep_smooth_of (Z := Z) ?_ hZ fun z hz => ?_` and prove the remaining obligations. Rewrite using `[hdeg]`. Unfold `ComponentSetting.NbarQ`. Rewrite using `[smoothRep_a]`. Rewrite using `[hagree z hz]`.

Unfold `ComponentSetting.NbarQ`. Rewrite using `[smoothRep_h _ hz]`. Establish `hne : (1 : MRing ι) ∉ mCoordIdeal D.y` using `fun h => hP.2.1.1.ne_top ((Ideal.eq_top_iff_one _).2 h)`. Establish `hiso : ∀ j : Fin (D.n + 1), HilbertSamuel.IsIsometricOn (mCoordIdeal D.y) ((fun _ => X.NbarQ B p q t) j) ((fun _ => Z) j)` using `fun _ => ⟨1, 1, 0, 0, by simpa using isMultiHomog_C_zero (ι := ι) 1, by simpa using isMultiHomog_C_zero (ι := ι) 1, hne, hne, fun k => by simp [hdeg], rfl, fun z hz => by simp [hagree z hz]⟩`. Establish `hI` using `hIso K ι (II K ι) (hII K ι) (mCoordIdeal D.y) (D.n + 1) (fun _ => X.NbarQ B p q t) (fun _ => Z) hP (fun _ => hN) (fun _ => hZ) hiso`.

Establish `hE` using `(HilbertSamuel.ZCombExpand.proof K ι (II K ι) (hII K ι) (mCoordIdeal D.y) (D.n + 1) (muReg X.H X.S B t) D.A' q p hP ht hA).1`. Use `show II K ι (mCoordIdeal D.y) (D.n + 1) (fun _ => X.NbarQ B p q t) / (q : ℝ) ^ (D.n + 1) = _`. Rewrite using `[hI, hE, Finset.sum_div, ← Finset.sum_range_reflect]`. Use `Finset.sum_congr rfl fun k hk => ?_` and prove the remaining obligations. Establish `hk' : k ≤ D.n + 1` using `by have := Finset.mem_range.1 hk; omega`.

Establish `hi : D.n + 1 + 1 - 1 - k = D.n + 1 - k` using `by omega`. Rewrite using `[hi, Nat.sub_sub_self hk', Nat.choose_symm hk']`. Unfold `ComponentSetting.mixN`. Establish `hpow : (q : ℝ) ^ (D.n + 1) = (q : ℝ) ^ k * (q : ℝ) ^ (D.n + 1 - k)`. Rewrite using `[← pow_add, Nat.add_sub_cancel' hk']`.

Rewrite using `[div_pow, hpow]`. Clear the denominators using the available nonvanishing facts.
-/
theorem TopNMixedExpand.proof (hIso : HilbertSamuel.IsomInvariance.Statement) (hS : MuRegSmooth.Statement) :
    TopNMixedExpand.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D O Lt _ _ _ X B p q hII hp hpq
  have hP : IsArithVar (mCoordIdeal D.y) (D.n + 1) := D.arith
  have hA : IsSmoothHerm D.A' := D.A'_pos.1
  filter_upwards [hS II Ψ K ι Ω E D O Lt X B] with t ht
  have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  set Z := HilbertSamuel.HermLine.zcomb (muReg X.H X.S B t) D.A' (q : ℤ) (p : ℤ) with hZdef
  have hZ : IsSmoothHerm Z := HilbertSamuel.ZCombLimit.isSmoothHerm_zcomb_int ht hA _ _
  have hagree : ∀ z ∈ mcPts (mCoordIdeal D.y), Z.h z = (X.NbarQ B p q t).h z := by
    intro z hz
    rw [NbarQ_h_eq X B p q t hz]
    show (muReg X.H X.S B t).h z ^ (q : ℤ) * D.A'.h z ^ (p : ℤ) = _
    simp
  have hdeg : Z.a = (X.NbarQ B p q t).a := by
    unfold ComponentSetting.NbarQ
    rw [smoothRep_a]
    show (q : ℤ) • (muReg X.H X.S B t).a + (p : ℤ) • D.A'.a = _
    rw [muReg, smoothRep_a, D.A'_deg]
    rfl
  have hN : IsSmoothHerm (X.NbarQ B p q t) := by
    unfold ComponentSetting.NbarQ
    refine TopNPoly.smoothRep_smooth_of (Z := Z) ?_ hZ fun z hz => ?_
    · rw [hdeg]; unfold ComponentSetting.NbarQ; rw [smoothRep_a]
    · rw [hagree z hz]; unfold ComponentSetting.NbarQ; rw [smoothRep_h _ hz]
  have hne : (1 : MRing ι) ∉ mCoordIdeal D.y := fun h =>
    hP.2.1.1.ne_top ((Ideal.eq_top_iff_one _).2 h)
  have hiso : ∀ j : Fin (D.n + 1), HilbertSamuel.IsIsometricOn (mCoordIdeal D.y)
      ((fun _ => X.NbarQ B p q t) j) ((fun _ => Z) j) := fun _ =>
    ⟨1, 1, 0, 0, by simpa using isMultiHomog_C_zero (ι := ι) 1, by simpa using isMultiHomog_C_zero (ι := ι) 1,
      hne, hne, fun k => by simp [hdeg], rfl, fun z hz => by simp [hagree z hz]⟩
  have hI := hIso K ι (II K ι) (hII K ι) (mCoordIdeal D.y) (D.n + 1) (fun _ => X.NbarQ B p q t) (fun _ => Z) hP
    (fun _ => hN) (fun _ => hZ) hiso
  have hE := (HilbertSamuel.ZCombExpand.proof K ι (II K ι) (hII K ι) (mCoordIdeal D.y) (D.n + 1)
    (muReg X.H X.S B t) D.A' q p hP ht hA).1
  show II K ι (mCoordIdeal D.y) (D.n + 1) (fun _ => X.NbarQ B p q t) / (q : ℝ) ^ (D.n + 1) = _
  rw [hI, hE, Finset.sum_div, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ D.n + 1 := by have := Finset.mem_range.1 hk; omega
  have hi : D.n + 1 + 1 - 1 - k = D.n + 1 - k := by omega
  rw [hi, Nat.sub_sub_self hk', Nat.choose_symm hk']
  unfold ComponentSetting.mixN
  have hpow : (q : ℝ) ^ (D.n + 1) = (q : ℝ) ^ k * (q : ℝ) ^ (D.n + 1 - k) := by
    rw [← pow_add, Nat.add_sub_cancel' hk']
  rw [div_pow, hpow]
  field_simp

end GroundTheory.Heights₂.Heights.LowerBoundFree
