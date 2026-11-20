import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SndDualLiftAlgebraMap

open GlobalTheory.BK PowerSeries Filter Topology

namespace GlobalTheory.BK

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] (l e : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K]

/- English proof (translation)
Establish `h2 : (((l : S O K e) : K⟦X⟧)) = C (l : K)` using `by simp`. Establish `hl : 0 < ‖(l : K)‖ ^ n` using `pow_pos (norm_pos_iff.2 (l_ne_zero l)) n`. Rewrite using `[Ideal.span_singleton_pow, Ideal.mem_span_singleton]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨g, rfl⟩ m`.

Rewrite using `[Subalgebra.coe_mul, Subalgebra.coe_pow, h2, ← map_pow, coeff_C_mul, norm_mul, norm_pow, mul_assoc]`. Conclude with `mul_le_of_le_one_right hl.le ((mem_S.1 g.2).1 m)`. Introduce `h`. Establish `hc : ∀ m, ‖coeff m (C (((l : K) ^ n)⁻¹) * (f : K⟦X⟧))‖ * wS K e m = (‖(l : K)‖ ^ n)⁻¹ * (‖coeff m (f : K⟦X⟧)‖ * wS K e m)` using `fun m => by`. Rewrite using `[coeff_C_mul, norm_mul, norm_inv, norm_pow, mul_assoc]`.

Use `⟨⟨C (((l : K) ^ n)⁻¹) * (f : K⟦X⟧), mem_S.2 ⟨fun m => ?_, ?_⟩⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Rewrite using `[hc, inv_mul_le_iff₀ hl, mul_one]`. Conclude with `h m`. Simplify using `only [hc]`. Simplify using `using (mem_S.1 f.2).2.const_mul (‖(l : K)‖ ^ n)⁻¹`.

Rewrite using `[Subalgebra.coe_mul, Subalgebra.coe_pow, h2, ← map_pow, ← mul_assoc, ← map_mul, mul_inv_cancel₀ (pow_ne_zero _ (l_ne_zero l)), map_one, one_mul]`.
-/
theorem mem_span_l_pow_S_iff (n : ℕ) (f : S O K e) :
    f ∈ Ideal.span {(l : S O K e)} ^ n ↔
      ∀ m, ‖coeff m (f : K⟦X⟧)‖ * wS K e m ≤ ‖(l : K)‖ ^ n := by
  have h2 : (((l : S O K e) : K⟦X⟧)) = C (l : K) := by simp
  have hl : 0 < ‖(l : K)‖ ^ n := pow_pos (norm_pos_iff.2 (l_ne_zero l)) n
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨g, rfl⟩ m
    rw [Subalgebra.coe_mul, Subalgebra.coe_pow, h2, ← map_pow, coeff_C_mul, norm_mul, norm_pow,
      mul_assoc]
    exact mul_le_of_le_one_right hl.le ((mem_S.1 g.2).1 m)
  · intro h
    have hc : ∀ m, ‖coeff m (C (((l : K) ^ n)⁻¹) * (f : K⟦X⟧))‖ * wS K e m =
        (‖(l : K)‖ ^ n)⁻¹ * (‖coeff m (f : K⟦X⟧)‖ * wS K e m) := fun m => by
      rw [coeff_C_mul, norm_mul, norm_inv, norm_pow, mul_assoc]
    refine ⟨⟨C (((l : K) ^ n)⁻¹) * (f : K⟦X⟧), mem_S.2 ⟨fun m => ?_, ?_⟩⟩, Subtype.ext ?_⟩
    · rw [hc, inv_mul_le_iff₀ hl, mul_one]
      exact h m
    · simp only [hc]
      simpa using (mem_S.1 f.2).2.const_mul (‖(l : K)‖ ^ n)⁻¹
    · rw [Subalgebra.coe_mul, Subalgebra.coe_pow, h2, ← map_pow, ← mul_assoc, ← map_mul,
        mul_inv_cancel₀ (pow_ne_zero _ (l_ne_zero l)), map_one, one_mul]

/- English proof (translation)
Rewrite using `[SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, mem_span_l_pow_S_iff]`. Simplify using the standard rewrite rules.
-/
theorem smodEq_l_pow_S_iff (n : ℕ) (f g : S O K e) :
    f ≡ g [SMOD (Ideal.span {(l : S O K e)} ^ n • ⊤ : Submodule (S O K e) (S O K e))] ↔
      ∀ m, ‖coeff m (f : K⟦X⟧) - coeff m (g : K⟦X⟧)‖ * wS K e m ≤ ‖(l : K)‖ ^ n := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, mem_span_l_pow_S_iff]
  simp

omit [IsUltrametricDist K] in
include l in
/- English proof (translation)
The claim follows from `norm_pos_iff.2 (natCast_ne_zero' l (Nat.factorial_ne_zero _))`.
-/
theorem wS_pos_of_padic (m : ℕ) : 0 < wS K e m :=
  norm_pos_iff.2 (natCast_ne_zero' l (Nat.factorial_ne_zero _))

/- English proof (translation)
Use `⟨fun f hf => Subtype.ext ?_⟩` and prove the remaining obligations. Use extensionality with `m`. Establish `h` using `fun n => (smodEq_l_pow_S_iff l e n f 0).1 (hf n) m`. Establish `h0` using `ge_of_tendsto' (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) (norm_l_lt_one (K := K) l)) h`. Establish `h1` using `nonpos_of_mul_nonpos_left h0 (wS_pos_of_padic l e m)`.

Simplify using `using h1`.
-/
theorem isHausdorff_S : IsHausdorff (Ideal.span {(l : S O K e)}) (S O K e) := by
  refine ⟨fun f hf => Subtype.ext ?_⟩
  ext m
  have h := fun n => (smodEq_l_pow_S_iff l e n f 0).1 (hf n) m
  have h0 := ge_of_tendsto' (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _)
    (norm_l_lt_one (K := K) l)) h
  have h1 := nonpos_of_mul_nonpos_left h0 (wS_pos_of_padic l e m)
  simpa using h1

/- English proof (translation)
Use `⟨fun f hf => ?_⟩` and prove the remaining obligations. Establish `hf' : ∀ {a b : ℕ}, a ≤ b → ∀ m, ‖coeff m (f a : K⟦X⟧) - coeff m (f b : K⟦X⟧)‖ * wS K e m ≤ ‖(l : K)‖ ^ a` using `fun h => (smodEq_l_pow_S_iff l e _ _ _).1 (hf h)`. Establish `hl0` using `tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) (norm_l_lt_one (K := K) l)`. Establish `hcau : ∀ m, CauchySeq fun n => coeff m (f n : K⟦X⟧)` using `fun m => by`. Use `cauchySeq_of_le_tendsto_0' (fun n => ‖(l : K)‖ ^ n / wS K e m) (fun a b h => ?_) (by simpa using hl0.div_const (wS K e m))` and prove the remaining obligations.

Rewrite using `[dist_eq_norm, le_div_iff₀ (wS_pos_of_padic l e m)]`. Conclude with `hf' h m`. Use `choose c hc using fun m => cauchySeq_tendsto_of_complete (hcau m)`. Establish `hb : ∀ n m, ‖coeff m (f n : K⟦X⟧) - c m‖ * wS K e m ≤ ‖(l : K)‖ ^ n` using `fun n m => le_of_tendsto ((tendsto_const_nhds.sub (hc m)).norm.mul_const _) ((eventually_ge_atTop n).mono fun b h => hf' h m)`. Establish `hu : ∀ n m, ‖c m‖ * wS K e m ≤ max (‖coeff m (f n : K⟦X⟧)‖ * wS K e m) (‖(l : K)‖ ^ n)` using `fun n m => by`.

Use `le_trans ?_ (max_le_max le_rfl (hb n m))` and prove the remaining obligations. Rewrite using `[← max_mul_of_nonneg _ _ (wS_nonneg e m)]`. Use `mul_le_mul_of_nonneg_right ?_ (wS_nonneg e m)` and prove the remaining obligations. Use `IsUltrametricDist.norm_add_le_max (coeff m (f n : K⟦X⟧)) (-(coeff m (f n : K⟦X⟧) - c m))` as an intermediate fact. Rewrite `this` using `[norm_neg]`.

Simplify using `using this`. Establish `hmem : PowerSeries.mk c ∈ S O K e`. Use `mem_S.2 ⟨fun m => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[coeff_mk]`. Conclude with `(hu 0 m).trans (max_le ((mem_S.1 (f 0).2).1 m) (by simp))`.

Simplify using `only [coeff_mk]`. Use `tendsto_order.2 ⟨fun a ha => Eventually.of_forall fun m => ha.trans_le (mul_nonneg (norm_nonneg _) (wS_nonneg e m)), fun a ha => ?_⟩` and prove the remaining obligations. Take `⟨n, hn⟩` from `(hl0.eventually (gt_mem_nhds ha)).exists`. Use `filter_upwards [(mem_S.1 (f n).2).2.eventually (gt_mem_nhds ha)] with m hm`. Conclude with `(hu n m).trans_lt (max_lt hm hn)`.

Use `⟨⟨_, hmem⟩, fun n => (smodEq_l_pow_S_iff l e _ _ _).2 fun m => ?_⟩` and prove the remaining obligations. Simplify using `using hb n m`.
-/
theorem isPrecomplete_S [CompleteSpace K] :
    IsPrecomplete (Ideal.span {(l : S O K e)}) (S O K e) := by
  refine ⟨fun f hf => ?_⟩
  have hf' : ∀ {a b : ℕ}, a ≤ b → ∀ m, ‖coeff m (f a : K⟦X⟧) - coeff m (f b : K⟦X⟧)‖ * wS K e m ≤
      ‖(l : K)‖ ^ a := fun h => (smodEq_l_pow_S_iff l e _ _ _).1 (hf h)
  have hl0 := tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) (norm_l_lt_one (K := K) l)
  have hcau : ∀ m, CauchySeq fun n => coeff m (f n : K⟦X⟧) := fun m => by
    refine cauchySeq_of_le_tendsto_0' (fun n => ‖(l : K)‖ ^ n / wS K e m) (fun a b h => ?_)
      (by simpa using hl0.div_const (wS K e m))
    rw [dist_eq_norm, le_div_iff₀ (wS_pos_of_padic l e m)]
    exact hf' h m
  choose c hc using fun m => cauchySeq_tendsto_of_complete (hcau m)
  have hb : ∀ n m, ‖coeff m (f n : K⟦X⟧) - c m‖ * wS K e m ≤ ‖(l : K)‖ ^ n := fun n m =>
    le_of_tendsto ((tendsto_const_nhds.sub (hc m)).norm.mul_const _)
      ((eventually_ge_atTop n).mono fun b h => hf' h m)
  have hu : ∀ n m, ‖c m‖ * wS K e m ≤
      max (‖coeff m (f n : K⟦X⟧)‖ * wS K e m) (‖(l : K)‖ ^ n) := fun n m => by
    refine le_trans ?_ (max_le_max le_rfl (hb n m))
    rw [← max_mul_of_nonneg _ _ (wS_nonneg e m)]
    refine mul_le_mul_of_nonneg_right ?_ (wS_nonneg e m)
    have := IsUltrametricDist.norm_add_le_max (coeff m (f n : K⟦X⟧))
      (-(coeff m (f n : K⟦X⟧) - c m))
    rw [norm_neg] at this
    simpa using this
  have hmem : PowerSeries.mk c ∈ S O K e := by
    refine mem_S.2 ⟨fun m => ?_, ?_⟩
    · rw [coeff_mk]
      exact (hu 0 m).trans (max_le ((mem_S.1 (f 0).2).1 m) (by simp))
    · simp only [coeff_mk]
      refine tendsto_order.2 ⟨fun a ha => Eventually.of_forall fun m =>
        ha.trans_le (mul_nonneg (norm_nonneg _) (wS_nonneg e m)), fun a ha => ?_⟩
      obtain ⟨n, hn⟩ := (hl0.eventually (gt_mem_nhds ha)).exists
      filter_upwards [(mem_S.1 (f n).2).2.eventually (gt_mem_nhds ha)] with m hm
      exact (hu n m).trans_lt (max_lt hm hn)
  refine ⟨⟨_, hmem⟩, fun n => (smodEq_l_pow_S_iff l e _ _ _).2 fun m => ?_⟩
  simpa using hb n m

end GlobalTheory.BK

namespace GlobalTheory.BK

/- English proof (translation)
The claim follows from `{ toIsHausdorff := isHausdorff_S l e, toIsPrecomplete := isPrecomplete_S l e }`.
-/
theorem isAdicComplete_S (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] (l e : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e]
    [CompleteSpace K] : IsAdicComplete (Ideal.span {(l : S O K e)}) (S O K e) :=
  { toIsHausdorff := isHausdorff_S l e, toIsPrecomplete := isPrecomplete_S l e }

end GlobalTheory.BK
