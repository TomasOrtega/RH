import Mathlib
import Formalism.SharpRestriction.Divisibility.LocalQuadraticParts
import Formalism.SharpRestriction.GrowthBounds.WeilJacquetShalikaLaw
import Formalism.SharpRestriction.GlobalSchurBounds.MainIn
import Formalism.QuotientMetricDivisors.FinalW
import Formalism.QuotientMetricDivisors.SixthReductionExplicit
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.OneLeLetterBlockLength

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField Classical

noncomputable section

namespace GlobalTheory.ConjLoss

/- English proof (translation)
Take `⟨T, hT⟩` from `finite_places_over (K := D.what₂.LL) p hp`. Use `⟨(T.map D.plEq.symm.toEmbedding).filter (fun w => D.what₂.places.resChar w = p), fun w => ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.mem_filter, Finset.mem_map_equiv, Equiv.symm_symm, hT]`. Conclude with `⟨fun h => h.2, fun h => ⟨h ▸ resChar_mem D w, h⟩⟩`.
-/
theorem exists_over (D : D7) (p : ℕ) (hp : p.Prime) :
    ∃ S : Finset D.what₂.places.Pl, ∀ w, w ∈ S ↔ D.what₂.places.resChar w = p := by
  obtain ⟨T, hT⟩ := finite_places_over (K := D.what₂.LL) p hp
  refine ⟨(T.map D.plEq.symm.toEmbedding).filter (fun w => D.what₂.places.resChar w = p), fun w => ?_⟩
  rw [Finset.mem_filter, Finset.mem_map_equiv, Equiv.symm_symm, hT]
  exact ⟨fun h => h.2, fun h => ⟨h ▸ resChar_mem D w, h⟩⟩

/- English proof (translation)
The claim follows from `div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)`.
-/
theorem logWeight_nonneg {D : D7} (w : D.what₂.places.Pl) : 0 ≤ SizeData₂.lwP w :=
  div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)

/- English proof (translation)
Rewrite using `[← Finset.sum_fiberwise_of_maps_to (fun w hw => Finset.mem_image_of_mem D.what₂.places.resChar hw)]`. Use `Finset.sum_le_sum fun p hp => ?_` and prove the remaining obligations. Take `⟨w0, -, rfl⟩` from `Finset.mem_image.1 hp`. Establish `hpp` using `D.what₂.places.resChar_prime w0`. Take `⟨T, hT⟩` from `exists_over D _ hpp`.

Establish `h0 : ∀ w : D.what₂.places.Pl, 0 ≤ SizeData₂.lwP w * (D.what₂.places.ramIdx w : ℝ)` using `fun w => mul_nonneg (logWeight_nonneg w) (Nat.cast_nonneg _)`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl fun w hw => ?_` and prove the remaining obligations. Rewrite using `[(Finset.mem_filter.1 hw).2]`. Establish `e : SizeData₂.sz w (g (D.what₂.places.resChar w0)) = 2 * g (D.what₂.places.resChar w0) * (SizeData₂.lwP w * (D.what₂.places.ramIdx w : ℝ))`.

Unfold `SizeData₂.sz`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, abs_mul, abs_mul, abs_two, abs_of_nonneg (h0 w)]`. Use `_ ≤ ∑ w ∈ T, 2 * |g (D.what₂.places.resChar w0)| * (SizeData₂.lwP w * (D.what₂.places.ramIdx w : ℝ)) := by`. Use `Finset.sum_le_sum_of_subset_of_nonneg (fun w hw => (hT w).2 (Finset.mem_filter.1 hw).2) ?_` and prove the remaining obligations.

Introduce `w _ _`. Conclude with `mul_nonneg (by positivity) (h0 w)`. Use `_ = _ := by`. Rewrite using `[← Finset.mul_sum]`. Use `factEtaMean D _ hpp T hT` as an intermediate fact.

Unfold `SizeData₂.lwP`. Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sum_sz_le (D : D7) (S : Finset D.what₂.places.Pl) (g : ℕ → ℝ) :
    ∑ w ∈ S, |SizeData₂.sz w (g (D.what₂.places.resChar w))| ≤
      ∑ p ∈ S.image D.what₂.places.resChar, 2 * (Real.log p * |g p|) := by
  rw [← Finset.sum_fiberwise_of_maps_to (fun w hw => Finset.mem_image_of_mem D.what₂.places.resChar hw)]
  refine Finset.sum_le_sum fun p hp => ?_
  obtain ⟨w0, -, rfl⟩ := Finset.mem_image.1 hp
  have hpp := D.what₂.places.resChar_prime w0
  obtain ⟨T, hT⟩ := exists_over D _ hpp
  have h0 : ∀ w : D.what₂.places.Pl, 0 ≤ SizeData₂.lwP w * (D.what₂.places.ramIdx w : ℝ) :=
    fun w => mul_nonneg (logWeight_nonneg w) (Nat.cast_nonneg _)
  calc ∑ w ∈ S.filter (fun w => D.what₂.places.resChar w = D.what₂.places.resChar w0),
        |SizeData₂.sz w (g (D.what₂.places.resChar w))|
      = ∑ w ∈ S.filter (fun w => D.what₂.places.resChar w = D.what₂.places.resChar w0),
        2 * |g (D.what₂.places.resChar w0)| * (SizeData₂.lwP w * (D.what₂.places.ramIdx w : ℝ)) := by
        refine Finset.sum_congr rfl fun w hw => ?_
        rw [(Finset.mem_filter.1 hw).2]
        have e : SizeData₂.sz w (g (D.what₂.places.resChar w0)) =
          2 * g (D.what₂.places.resChar w0) * (SizeData₂.lwP w * (D.what₂.places.ramIdx w : ℝ)) := by
          unfold SizeData₂.sz; ring
        rw [e, abs_mul, abs_mul, abs_two, abs_of_nonneg (h0 w)]
    _ ≤ ∑ w ∈ T, 2 * |g (D.what₂.places.resChar w0)| * (SizeData₂.lwP w * (D.what₂.places.ramIdx w : ℝ)) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (fun w hw => (hT w).2 (Finset.mem_filter.1 hw).2) ?_
        intro w _ _
        exact mul_nonneg (by positivity) (h0 w)
    _ = _ := by
        rw [← Finset.mul_sum]
        have := factEtaMean D _ hpp T hT
        unfold SizeData₂.lwP
        rw [this]
        ring

/- English proof (translation)
Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases. Simplify using the standard rewrite rules. Establish `hd : ∏ p ∈ P, p ^ padicValNat p n ∣ n`. Use `Finset.prod_dvd_of_isRelPrime ?_ fun p _ => pow_padicValNat_dvd` and prove the remaining obligations. Introduce `p hp q hq hpq`.

Conclude with `Nat.coprime_iff_isRelPrime.1 (Nat.Coprime.pow _ _ ((Nat.coprime_primes (hP p hp) (hP q hq)).2 hpq))`. Establish `h1 : ∑ p ∈ P, Real.log p * (padicValNat p n : ℝ) = Real.log (∏ p ∈ P, (p : ℝ) ^ padicValNat p n)`. Rewrite using `[Real.log_prod]`. Conclude with `Finset.sum_congr rfl fun p _ => by rw [Real.log_pow, mul_comm]`. Introduce `p hp`.

Establish `: (0 : ℝ) < p` using `by exact_mod_cast (hP p hp).pos`. Check the signs of the components of the expression. Rewrite using `[h1]`. Apply `Real.log_le_log` to reduce the goal to its premises. Use `Finset.prod_pos fun p hp => ?_` and prove the remaining obligations.

Establish `: (0 : ℝ) < p` using `by exact_mod_cast (hP p hp).pos`. Check the signs of the components of the expression. Conclude with `Nat.le_of_dvd hn hd` after adjusting the coercions.
-/
theorem sum_padic_log_le (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (n : ℕ) :
    ∑ p ∈ P, Real.log p * (padicValNat p n : ℝ) ≤ Real.log n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hd : ∏ p ∈ P, p ^ padicValNat p n ∣ n := by
      refine Finset.prod_dvd_of_isRelPrime ?_ fun p _ => pow_padicValNat_dvd
      intro p hp q hq hpq
      exact Nat.coprime_iff_isRelPrime.1
        (Nat.Coprime.pow _ _ ((Nat.coprime_primes (hP p hp) (hP q hq)).2 hpq))
    have h1 : ∑ p ∈ P, Real.log p * (padicValNat p n : ℝ) =
        Real.log (∏ p ∈ P, (p : ℝ) ^ padicValNat p n) := by
      rw [Real.log_prod]
      · exact Finset.sum_congr rfl fun p _ => by rw [Real.log_pow, mul_comm]
      · intro p hp
        have : (0 : ℝ) < p := by exact_mod_cast (hP p hp).pos
        positivity
    rw [h1]
    apply Real.log_le_log
    · refine Finset.prod_pos fun p hp => ?_
      have : (0 : ℝ) < p := by exact_mod_cast (hP p hp).pos
      positivity
    · exact_mod_cast Nat.le_of_dvd hn hd

/- English proof (translation)
Establish `hla : 0 ≤ Real.log a` using `Real.log_nonneg ha`. Establish `h1 : ∀ p ∈ P, Real.log p * |(padicValNat p n : ℝ) + (if (p : ℝ) ≤ X then A * Real.logb p a + W / ((p : ℝ) ^ 2 - 1) else 0)| ≤ Real.log p * (padicValNat p n : ℝ) + (if (p : ℝ) ≤ X then A * Real.log a + 2 * (W * Real.log a) * ((p : ℝ) ^ 2)⁻¹ else 0)`. Introduce `p hp`. Establish `h2 : (2 : ℝ) ≤ p` using `by exact_mod_cast (hP p hp).two_le`. Establish `hl : 0 < Real.log p` using `Real.log_pos (by linarith)`.

Establish `hq : 0 < (p : ℝ) ^ 2 - 1` using `by nlinarith`. Use `split_ifs with h`. Establish `hb : 0 ≤ Real.logb p a` using `Real.logb_nonneg (by linarith) ha`. Rewrite using `[abs_of_nonneg (by positivity), mul_add, mul_add]`. Establish `e1 : Real.log p * (A * Real.logb p a) = A * Real.log a`.

Unfold `Real.logb`. Clear the denominators using the available nonvanishing facts. Establish `e2 : Real.log p ≤ Real.log a` using `Real.log_le_log (by linarith) (h.trans hXa)`. Establish `e3 : W / ((p : ℝ) ^ 2 - 1) ≤ 2 * W * ((p : ℝ) ^ 2)⁻¹`. Rewrite using `[← div_eq_mul_inv, div_le_div_iff₀ hq (by positivity)]`.

Establish `: 0 ≤ (p : ℝ) ^ 2 - 2` using `by nlinarith`. Use polynomial arithmetic with `[mul_nonneg hW this]`. Establish `e4` using `mul_le_mul e2 e3 (by positivity) hla`. Rewrite using `[e1]`. Use the polynomial consequences of the given equalities and inequalities.

Rewrite using `[add_zero, add_zero, abs_of_nonneg (Nat.cast_nonneg _)]`. Use `(Finset.sum_le_sum h1).trans ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_add_distrib, ← Finset.sum_filter, add_assoc]`. Use `add_le_add (sum_padic_log_le P hP n) ?_` and prove the remaining obligations. Establish `hsub : P.filter (fun p : ℕ => (p : ℝ) ≤ X) ⊆ Finset.Ioo 1 (⌊X⌋₊ + 1)`.

Introduce `p hp`. Take `⟨a1, a2⟩` from `Finset.mem_filter.1 hp`. Conclude with `Finset.mem_Ioo.2 ⟨(hP p a1).one_lt, Nat.lt_succ_of_le (Nat.le_floor a2)⟩`. Use `(Finset.sum_le_sum_of_subset_of_nonneg hsub fun p _ _ => by positivity).trans ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_add_distrib, Finset.sum_const, ← Finset.mul_sum, nsmul_eq_mul]`.

Establish `c1 : ((Finset.Ioo 1 (⌊X⌋₊ + 1)).card : ℝ) ≤ X`. Use `le_trans ?_ (Nat.floor_le hX)` and prove the remaining obligations. Rewrite using `[Nat.card_Ioo]`. Conclude with `(by omega : ⌊X⌋₊ + 1 - 1 - 1 ≤ ⌊X⌋₊)` after adjusting the coercions. Establish `c2 : ∑ p ∈ Finset.Ioo 1 (⌊X⌋₊ + 1), ((p : ℝ) ^ 2)⁻¹ ≤ 1`.

Use `sum_Ioo_inv_sq_le (α := ℝ) 1 (⌊X⌋₊ + 1)` as an intermediate fact. Evaluate the numerical expressions using `at this ⊢`. Conclude with `this`. Conclude with `add_le_add (mul_le_mul_of_nonneg_right c1 (by positivity)) (mul_le_of_le_one_right (by positivity) c2)`.
-/
theorem sum_primes_le (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (n : ℕ) (X a A W : ℝ) (hX : 0 ≤ X) (hXa : X ≤ a)
    (ha : 1 ≤ a) (hA : 0 ≤ A) (hW : 0 ≤ W) :
    ∑ p ∈ P, Real.log p * |(padicValNat p n : ℝ) +
      (if (p : ℝ) ≤ X then A * Real.logb p a + W / ((p : ℝ) ^ 2 - 1) else 0)| ≤
      Real.log n + X * (A * Real.log a) + 2 * (W * Real.log a) := by
  have hla : 0 ≤ Real.log a := Real.log_nonneg ha
  have h1 : ∀ p ∈ P, Real.log p * |(padicValNat p n : ℝ) +
      (if (p : ℝ) ≤ X then A * Real.logb p a + W / ((p : ℝ) ^ 2 - 1) else 0)| ≤
      Real.log p * (padicValNat p n : ℝ) +
      (if (p : ℝ) ≤ X then A * Real.log a + 2 * (W * Real.log a) * ((p : ℝ) ^ 2)⁻¹ else 0) := by
    intro p hp
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (hP p hp).two_le
    have hl : 0 < Real.log p := Real.log_pos (by linarith)
    have hq : 0 < (p : ℝ) ^ 2 - 1 := by nlinarith
    split_ifs with h
    · have hb : 0 ≤ Real.logb p a := Real.logb_nonneg (by linarith) ha
      rw [abs_of_nonneg (by positivity), mul_add, mul_add]
      have e1 : Real.log p * (A * Real.logb p a) = A * Real.log a := by
        unfold Real.logb; field_simp
      have e2 : Real.log p ≤ Real.log a := Real.log_le_log (by linarith) (h.trans hXa)
      have e3 : W / ((p : ℝ) ^ 2 - 1) ≤ 2 * W * ((p : ℝ) ^ 2)⁻¹ := by
        rw [← div_eq_mul_inv, div_le_div_iff₀ hq (by positivity)]
        have : 0 ≤ (p : ℝ) ^ 2 - 2 := by nlinarith
        nlinarith [mul_nonneg hW this]
      have e4 := mul_le_mul e2 e3 (by positivity) hla
      rw [e1]
      nlinarith
    · rw [add_zero, add_zero, abs_of_nonneg (Nat.cast_nonneg _)]
  refine (Finset.sum_le_sum h1).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.sum_filter, add_assoc]
  refine add_le_add (sum_padic_log_le P hP n) ?_
  have hsub : P.filter (fun p : ℕ => (p : ℝ) ≤ X) ⊆ Finset.Ioo 1 (⌊X⌋₊ + 1) := by
    intro p hp
    obtain ⟨a1, a2⟩ := Finset.mem_filter.1 hp
    exact Finset.mem_Ioo.2 ⟨(hP p a1).one_lt, Nat.lt_succ_of_le (Nat.le_floor a2)⟩
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun p _ _ => by positivity).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_const, ← Finset.mul_sum, nsmul_eq_mul]
  have c1 : ((Finset.Ioo 1 (⌊X⌋₊ + 1)).card : ℝ) ≤ X := by
    refine le_trans ?_ (Nat.floor_le hX)
    rw [Nat.card_Ioo]
    exact_mod_cast (by omega : ⌊X⌋₊ + 1 - 1 - 1 ≤ ⌊X⌋₊)
  have c2 : ∑ p ∈ Finset.Ioo 1 (⌊X⌋₊ + 1), ((p : ℝ) ^ 2)⁻¹ ≤ 1 := by
    have := sum_Ioo_inv_sq_le (α := ℝ) 1 (⌊X⌋₊ + 1)
    norm_num at this ⊢
    exact this
  exact add_le_add (mul_le_mul_of_nonneg_right c1 (by positivity))
    (mul_le_of_le_one_right (by positivity) c2)

/- English proof (translation)
Use `set g : ℕ → ℝ := fun p => (padicValNat p (D.mem u).C.DGam : ℝ) + (if (p : ℝ) ≤ L.sc.X'' D.R.n then 3 * (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) ^ 2 * Real.logb p L.sc.a + (∑ τ : D.what₂.Tau, wj D j τ) / ((p : ℝ) ^ 2 - 1) else 0) with hg`. Establish `hEg : ∀ w ∈ S, L.E u j w = g (D.what₂.places.resChar w)`. Introduce `w hw`. Take `⟨a1, a2, a3, a4, a5⟩` from `hSp w hw`. Establish `b0 : D.what₂.places.resChar w ≠ D.host.g 0` using `fun h => a3 (by simp [SizeData₂.gTypes, h])`.

Establish `b1 : D.what₂.places.resChar w ≠ D.host.g 1` using `fun h => a3 (by simp [SizeData₂.gTypes, h])`. Establish `b2 : D.host.cls (D.what₂.places.resChar w) ≠ PrimeClass.ramD` using `fun h => a1 (cls_ramD h)`. Rewrite using `[hE u j hj w, hg]`. Unfold `Eval`. Simplify using `only [if_neg a2, if_neg b0, if_neg b1, if_neg b2]`.

Distinguish the cases in `h : ((D.what₂.places.resChar w : ℕ) : ℝ) ≤ L.sc.X'' D.R.n`. Rewrite using `[if_pos ⟨Or.inl a4, h⟩, if_pos ⟨a4, a5⟩, if_pos h]`. Unfold `EatC Formalism.MainNotions.G.Nm`. Rewrite using `[hc]`. Rewrite using `[if_neg (fun h' => h h'.2), if_neg h]`.

Rewrite using `[Finset.sum_congr rfl fun w hw => by rw [hEg w hw]]`. Use `(sum_sz_le D S g).trans ?_` and prove the remaining obligations. Rewrite using `[← Finset.mul_sum, mul_assoc]`. Use `mul_le_mul_of_nonneg_left ?_ (by norm_num)` and prove the remaining obligations. Establish `hL` using `HCEntries.one_le_scL L`.

Establish `hb` using `HCEntries.one_le_b L`. Establish `hk` using `HCEntries.one_le_k D`. Establish `ht` using `HCEntries.one_le_letterBlockLength D`. Establish `hmn` using `D.R.two_le_m`. Establish `hkn` using `D.R.m_add_three_le_k`.

Establish `hmfn : D.R.m ≤ D.R.f` using `D.R.m_le_f`. Establish `hm : (1 : ℝ) ≤ D.R.m` using `by exact_mod_cast (by omega : 1 ≤ D.R.m)`. Establish `hf : (1 : ℝ) ≤ D.R.f` using `by exact_mod_cast (by omega : 1 ≤ D.R.f)`. Establish `hN : (1 : ℝ) ≤ D.R.N D.R.m`. Conclude with `(by unfold Ranks.N; omega : 1 ≤ D.R.N D.R.m)` after adjusting the coercions.

Establish `hη0` using `L.etaSz_pos.le`. Establish `hNη : (D.R.N D.R.m : ℝ) ^ 2 ≤ L.etaSz`. Establish `a1` using `P.h0_ge.2.2.2.2.1`. Establish `a2 : LevelStarExponents.h0 L ≤ L.etaSz` using `div_le_self hη0 hm`. Establish `a3 : (D.R.N D.R.m : ℝ) ^ 2 ≤ (D.R.N D.R.m : ℝ) ^ 3` using `pow_le_pow_right₀ hN (by norm_num)`.

Establish `a4 : 0 ≤ (D.R.N D.R.m : ℝ) ^ 3` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hfη : (D.R.f : ℝ) * L.etaSz ≤ L.sc.b`. Establish `a1` using `P.eta_le`. Rewrite `a1` using `[le_div_iff₀ (by positivity)]`.

Establish `a2 : (1 : ℝ) ≤ (D.R.t : ℝ) ^ 3 * (D.R.k : ℝ) ^ 3` using `one_le_mul_of_one_le_of_one_le (one_le_pow₀ ht) (one_le_pow₀ hk)`. Establish `a3 : (D.R.f : ℝ) * L.etaSz ≤ (D.R.f : ℝ) * L.etaSz * ((D.R.t : ℝ) ^ 3 * (D.R.k : ℝ) ^ 3)` using `le_mul_of_one_le_right (by positivity) a2`. Combine the equalities or inequalities in the displayed calculation. Establish `hx0 : 0 < L.sc.x` using `by linarith`. Establish `ha : L.sc.a = L.sc.x * L.sc.b` using `rfl`.

Establish `ha1 : 1 ≤ L.sc.a` using `by rw [ha]; exact one_le_mul_of_one_le_of_one_le (by linarith) hb`. Establish `hN2 : (1 : ℝ) ≤ (D.R.N D.R.m : ℝ) ^ 2` using `one_le_pow₀ hN`. Establish `hw : (D.R.N D.R.m : ℝ) ^ 2 * L.sc.x ≤ L.sc.w'' D.R.n`. Establish `a1` using `P.teta`. Rewrite `a1` using `[le_div_iff₀ hx0]`.

Conclude with `(mul_le_mul_of_nonneg_right (hNη.trans (le_mul_of_one_le_left hη0 ht)) hx0.le).trans a1`. Establish `hw1 : 1 ≤ L.sc.w'' D.R.n` using `(one_le_mul_of_one_le_of_one_le hN2 (by linarith)).trans hw`. Establish `hX0 : 0 ≤ L.sc.X'' D.R.n` using `by unfold Scale.X''; positivity`. Establish `hXa : L.sc.X'' D.R.n ≤ L.sc.a` using `div_le_self (by linarith) hw1`. Establish `hXN : L.sc.X'' D.R.n * (D.R.N D.R.m : ℝ) ^ 2 ≤ L.sc.b`.

Unfold `Scale.X''`. Rewrite using `[div_mul_eq_mul_div, div_le_iff₀ (by linarith), ha]`. Use `mul_le_mul_of_nonneg_left hw (by linarith : 0 ≤ L.sc.b)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨hj1, hjm⟩` from `Finset.mem_Icc.1 hj`.

Establish `hwj` using `HCEntries.wj_bounds hS hx j hj1 hjm`. Establish `hW0 : 0 ≤ ∑ τ : D.what₂.Tau, wj D j τ` using `Finset.sum_nonneg fun τ _ => (hwj τ).1`. Establish `hcard : Fintype.card D.what₂.Tau = D.R.f`. Take `⟨T, hT⟩` from `exists_over D 2 Nat.prime_two`. Establish `hne : T.Nonempty`.

Assume the negation of the conclusion as `hn`. Use `factEtaMean D 2 Nat.prime_two T hT` as an intermediate fact. Rewrite `this` using `[Finset.not_nonempty_iff_eq_empty.1 hn, Finset.sum_empty]`. Conclude with `(Real.log_pos (by norm_num)).ne this`. Take `⟨w, -⟩` from `hne`.

Conclude with `(Fintype.card_congr ((D.fm u).tauOf w)).symm.trans (D.mem u).A.card_vT`. Establish `hW : ∑ τ : D.what₂.Tau, wj D j τ ≤ D.R.f * (3 * L.sc.b)`. Use `Finset.sum_le_card_nsmul Finset.univ (fun τ : D.what₂.Tau => wj D j τ) _ fun τ _ => (hwj τ).2` as an intermediate fact. Rewrite `this` using `[Finset.card_univ, hcard, nsmul_eq_mul]`. Then use the resulting hypothesis. Establish `hla0 : 0 ≤ Real.log L.sc.a` using `Real.log_nonneg ha1`.

Establish `he` using `L.sc.eps_pos`. Establish `hla : Real.log L.sc.a ≤ (1 / L.sc.eps + 1) * L.sc.L`. Rewrite using `[ha, Real.log_mul hx0.ne' (by linarith)]`. Establish `a1 : Real.log L.sc.b = L.sc.L` using `Real.log_exp _`. Establish `a2 : Real.log L.sc.x ≤ L.sc.L / L.sc.eps` using `Real.log_le_rpow_div hx0.le he`.

Rewrite using `[a1]`. Combine the equalities or inequalities in the displayed calculation. Establish `hB : L.B0 = D.R.f * D.R.m * L.sc.b * L.sc.L` using `rfl`. Establish `hfb : 0 ≤ (D.R.f : ℝ) * L.sc.b` using `by positivity`. Establish `hB1 : D.R.f * L.sc.b * L.sc.L ≤ L.B0`.

Establish `: L.B0 = D.R.m * (D.R.f * L.sc.b * L.sc.L)` using `by rw [hB]; ring`. Rewrite using `[this]`. Conclude with `le_mul_of_one_le_left (by positivity) hm`. Establish `hB2 : D.R.f * L.sc.b ≤ L.B0` using `le_trans (le_mul_of_one_le_right hfb hL) hB1`. Establish `hfl : D.R.f * L.sc.b * Real.log L.sc.a ≤ (1 / L.sc.eps + 1) * L.B0`.

Combine the equalities or inequalities in the displayed calculation. Establish `t1 : Real.log ((D.mem u).C.DGam : ℝ) ≤ |C₂| * L.B0`. Establish `hfN : (1 : ℝ) ≤ D.R.f * D.R.N D.R.m` using `one_le_mul_of_one_le_of_one_le hf hN`. Establish `l0` using `Real.log_nonneg hfN`. Establish `l1 : Real.log ((D.R.f : ℝ) * D.R.N D.R.m) ≤ D.R.f * D.R.N D.R.m` using `(Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)`.

Establish `h1 : (D.R.f : ℝ) * D.R.N D.R.m * Real.log ((D.R.f : ℝ) * D.R.N D.R.m) ≤ L.B0`. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation. Establish `t2 : L.sc.X'' D.R.n * (3 * (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) ^ 2 * Real.log L.sc.a) ≤ 3 * (D.R.f * L.sc.b * Real.log L.sc.a)`. Combine the equalities or inequalities in the displayed calculation.

Establish `t3 : (∑ τ : D.what₂.Tau, wj D j τ) * Real.log L.sc.a ≤ 3 * (D.R.f * L.sc.b * Real.log L.sc.a)`. Combine the equalities or inequalities in the displayed calculation. Establish `key` using `sum_primes_le (S.image D.what₂.places.resChar) (fun p hp => by`. Take `⟨w, -, rfl⟩` from `Finset.mem_image.1 hp`. Conclude with `D.what₂.places.resChar_prime w)`.

Use the proof step `(D.mem u).C.DGam (L.sc.X'' D.R.n) L.sc.a (3 * (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) ^ 2)`. Use the proof step `(∑ τ : D.what₂.Tau, wj D j τ) hX0 hXa ha1 (by positivity) hW0`. Use `key.trans ?_` and prove the remaining obligations. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem bound_one {D : D7} {L : SizeData₂ D} {X : ErrX D} {K : Formalism.MainNotions.G.Consts} {c : ErrC} (hE : L.EDef X K c)
    (hc : c.dig = 3) (P : ParameterChoice' D L) (hS : SizesAt L) (hx : 2 ≤ L.sc.x) (u : D.what₂.Word) (j : ℕ)
    (hj : j ∈ SizeData₂.lifts D) (C₂ : ℝ) (h2 : FactDGam D C₂) (S : Finset D.what₂.places.Pl)
    (hSp : ∀ w ∈ S, D.what₂.places.resChar w ≠ D.host.d ∧ D.what₂.places.resChar w ≠ (D.mem u).A.T ∧
      D.what₂.places.resChar w ∉ L.gTypes ∧ G.IsResidueClassZero D (D.what₂.places.resChar w) ∧
      G.hP D (D.what₂.places.resChar w) = 0) :
    ∑ w ∈ S, |SizeData₂.sz w (L.E u j w)| ≤ 2 * (|C₂| + 9 * (1 / L.sc.eps + 1)) * L.B0 := by
  set g : ℕ → ℝ := fun p => (padicValNat p (D.mem u).C.DGam : ℝ) +
    (if (p : ℝ) ≤ L.sc.X'' D.R.n then 3 * (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) ^ 2 * Real.logb p L.sc.a +
      (∑ τ : D.what₂.Tau, wj D j τ) / ((p : ℝ) ^ 2 - 1) else 0) with hg
  have hEg : ∀ w ∈ S, L.E u j w = g (D.what₂.places.resChar w) := by
    intro w hw
    obtain ⟨a1, a2, a3, a4, a5⟩ := hSp w hw
    have b0 : D.what₂.places.resChar w ≠ D.host.g 0 := fun h => a3 (by simp [SizeData₂.gTypes, h])
    have b1 : D.what₂.places.resChar w ≠ D.host.g 1 := fun h => a3 (by simp [SizeData₂.gTypes, h])
    have b2 : D.host.cls (D.what₂.places.resChar w) ≠ PrimeClass.ramD := fun h => a1 (cls_ramD h)
    rw [hE u j hj w, hg]
    unfold Eval
    simp only [if_neg a2, if_neg b0, if_neg b1, if_neg b2]
    by_cases h : ((D.what₂.places.resChar w : ℕ) : ℝ) ≤ L.sc.X'' D.R.n
    · rw [if_pos ⟨Or.inl a4, h⟩, if_pos ⟨a4, a5⟩, if_pos h]
      unfold EatC Formalism.MainNotions.G.Nm
      rw [hc]
    · rw [if_neg (fun h' => h h'.2), if_neg h]
  rw [Finset.sum_congr rfl fun w hw => by rw [hEg w hw]]
  refine (sum_sz_le D S g).trans ?_
  rw [← Finset.mul_sum, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  have hL := HCEntries.one_le_scL L
  have hb := HCEntries.one_le_b L
  have hk := HCEntries.one_le_k D
  have ht := HCEntries.one_le_letterBlockLength D
  have hmn := D.R.two_le_m
  have hkn := D.R.m_add_three_le_k
  have hmfn : D.R.m ≤ D.R.f := D.R.m_le_f
  have hm : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (by omega : 1 ≤ D.R.m)
  have hf : (1 : ℝ) ≤ D.R.f := by exact_mod_cast (by omega : 1 ≤ D.R.f)
  have hN : (1 : ℝ) ≤ D.R.N D.R.m := by
    exact_mod_cast (by unfold Ranks.N; omega : 1 ≤ D.R.N D.R.m)
  have hη0 := L.etaSz_pos.le
  have hNη : (D.R.N D.R.m : ℝ) ^ 2 ≤ L.etaSz := by
    have a1 := P.h0_ge.2.2.2.2.1
    have a2 : LevelStarExponents.h0 L ≤ L.etaSz := div_le_self hη0 hm
    have a3 : (D.R.N D.R.m : ℝ) ^ 2 ≤ (D.R.N D.R.m : ℝ) ^ 3 := pow_le_pow_right₀ hN (by norm_num)
    have a4 : 0 ≤ (D.R.N D.R.m : ℝ) ^ 3 := by positivity
    linarith
  have hfη : (D.R.f : ℝ) * L.etaSz ≤ L.sc.b := by
    have a1 := P.eta_le
    rw [le_div_iff₀ (by positivity)] at a1
    have a2 : (1 : ℝ) ≤ (D.R.t : ℝ) ^ 3 * (D.R.k : ℝ) ^ 3 :=
      one_le_mul_of_one_le_of_one_le (one_le_pow₀ ht) (one_le_pow₀ hk)
    have a3 : (D.R.f : ℝ) * L.etaSz ≤ (D.R.f : ℝ) * L.etaSz * ((D.R.t : ℝ) ^ 3 * (D.R.k : ℝ) ^ 3) :=
      le_mul_of_one_le_right (by positivity) a2
    calc _ ≤ _ := a3
      _ = L.etaSz * ((D.R.t : ℝ) ^ 3 * D.R.f * (D.R.k : ℝ) ^ 3) := by ring
      _ ≤ _ := a1
  have hx0 : 0 < L.sc.x := by linarith
  have ha : L.sc.a = L.sc.x * L.sc.b := rfl
  have ha1 : 1 ≤ L.sc.a := by rw [ha]; exact one_le_mul_of_one_le_of_one_le (by linarith) hb
  have hN2 : (1 : ℝ) ≤ (D.R.N D.R.m : ℝ) ^ 2 := one_le_pow₀ hN
  have hw : (D.R.N D.R.m : ℝ) ^ 2 * L.sc.x ≤ L.sc.w'' D.R.n := by
    have a1 := P.teta
    rw [le_div_iff₀ hx0] at a1
    exact (mul_le_mul_of_nonneg_right (hNη.trans (le_mul_of_one_le_left hη0 ht)) hx0.le).trans a1
  have hw1 : 1 ≤ L.sc.w'' D.R.n := (one_le_mul_of_one_le_of_one_le hN2 (by linarith)).trans hw
  have hX0 : 0 ≤ L.sc.X'' D.R.n := by unfold Scale.X''; positivity
  have hXa : L.sc.X'' D.R.n ≤ L.sc.a := div_le_self (by linarith) hw1
  have hXN : L.sc.X'' D.R.n * (D.R.N D.R.m : ℝ) ^ 2 ≤ L.sc.b := by
    unfold Scale.X''
    rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith), ha]
    have := mul_le_mul_of_nonneg_left hw (by linarith : 0 ≤ L.sc.b)
    linarith
  obtain ⟨hj1, hjm⟩ := Finset.mem_Icc.1 hj
  have hwj := HCEntries.wj_bounds hS hx j hj1 hjm
  have hW0 : 0 ≤ ∑ τ : D.what₂.Tau, wj D j τ := Finset.sum_nonneg fun τ _ => (hwj τ).1
  have hcard : Fintype.card D.what₂.Tau = D.R.f := by
    obtain ⟨T, hT⟩ := exists_over D 2 Nat.prime_two
    have hne : T.Nonempty := by
      by_contra hn
      have := factEtaMean D 2 Nat.prime_two T hT
      rw [Finset.not_nonempty_iff_eq_empty.1 hn, Finset.sum_empty] at this
      exact (Real.log_pos (by norm_num)).ne this
    obtain ⟨w, -⟩ := hne
    exact (Fintype.card_congr ((D.fm u).tauOf w)).symm.trans (D.mem u).A.card_vT
  have hW : ∑ τ : D.what₂.Tau, wj D j τ ≤ D.R.f * (3 * L.sc.b) := by
    have := Finset.sum_le_card_nsmul Finset.univ (fun τ : D.what₂.Tau => wj D j τ) _ fun τ _ => (hwj τ).2
    rwa [Finset.card_univ, hcard, nsmul_eq_mul] at this
  have hla0 : 0 ≤ Real.log L.sc.a := Real.log_nonneg ha1
  have he := L.sc.eps_pos
  have hla : Real.log L.sc.a ≤ (1 / L.sc.eps + 1) * L.sc.L := by
    rw [ha, Real.log_mul hx0.ne' (by linarith)]
    have a1 : Real.log L.sc.b = L.sc.L := Real.log_exp _
    have a2 : Real.log L.sc.x ≤ L.sc.L / L.sc.eps := Real.log_le_rpow_div hx0.le he
    rw [a1]
    calc _ ≤ L.sc.L / L.sc.eps + L.sc.L := by linarith
      _ = _ := by ring
  have hB : L.B0 = D.R.f * D.R.m * L.sc.b * L.sc.L := rfl
  have hfb : 0 ≤ (D.R.f : ℝ) * L.sc.b := by positivity
  have hB1 : D.R.f * L.sc.b * L.sc.L ≤ L.B0 := by
    have : L.B0 = D.R.m * (D.R.f * L.sc.b * L.sc.L) := by rw [hB]; ring
    rw [this]
    exact le_mul_of_one_le_left (by positivity) hm
  have hB2 : D.R.f * L.sc.b ≤ L.B0 := le_trans (le_mul_of_one_le_right hfb hL) hB1
  have hfl : D.R.f * L.sc.b * Real.log L.sc.a ≤ (1 / L.sc.eps + 1) * L.B0 := by
    calc _ ≤ D.R.f * L.sc.b * ((1 / L.sc.eps + 1) * L.sc.L) := mul_le_mul_of_nonneg_left hla hfb
      _ = (1 / L.sc.eps + 1) * (D.R.f * L.sc.b * L.sc.L) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hB1 (by positivity)
  have t1 : Real.log ((D.mem u).C.DGam : ℝ) ≤ |C₂| * L.B0 := by
    have hfN : (1 : ℝ) ≤ D.R.f * D.R.N D.R.m := one_le_mul_of_one_le_of_one_le hf hN
    have l0 := Real.log_nonneg hfN
    have l1 : Real.log ((D.R.f : ℝ) * D.R.N D.R.m) ≤ D.R.f * D.R.N D.R.m :=
      (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
    have h1 : (D.R.f : ℝ) * D.R.N D.R.m * Real.log ((D.R.f : ℝ) * D.R.N D.R.m) ≤ L.B0 := by
      calc _ ≤ (D.R.f : ℝ) * D.R.N D.R.m * (D.R.f * D.R.N D.R.m) := mul_le_mul_of_nonneg_left l1 (by linarith)
        _ = D.R.f * (D.R.f * (D.R.N D.R.m : ℝ) ^ 2) := by ring
        _ ≤ D.R.f * L.sc.b :=
          mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_left hNη (by linarith)).trans hfη) (by linarith)
        _ ≤ _ := hB2
    calc _ ≤ _ := h2 u
      _ = C₂ * ((D.R.f : ℝ) * D.R.N D.R.m * Real.log ((D.R.f : ℝ) * D.R.N D.R.m)) := by ring
      _ ≤ |C₂| * ((D.R.f : ℝ) * D.R.N D.R.m * Real.log ((D.R.f : ℝ) * D.R.N D.R.m)) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (mul_nonneg (by linarith) l0)
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
  have t2 : L.sc.X'' D.R.n * (3 * (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) ^ 2 * Real.log L.sc.a) ≤
      3 * (D.R.f * L.sc.b * Real.log L.sc.a) := by
    calc _ = 3 * (D.R.f * (L.sc.X'' D.R.n * (D.R.N D.R.m : ℝ) ^ 2) * Real.log L.sc.a) := by ring
      _ ≤ _ := by gcongr
  have t3 : (∑ τ : D.what₂.Tau, wj D j τ) * Real.log L.sc.a ≤ 3 * (D.R.f * L.sc.b * Real.log L.sc.a) := by
    calc _ ≤ D.R.f * (3 * L.sc.b) * Real.log L.sc.a := mul_le_mul_of_nonneg_right hW hla0
      _ = _ := by ring
  have key := sum_primes_le (S.image D.what₂.places.resChar)
    (fun p hp => by
      obtain ⟨w, -, rfl⟩ := Finset.mem_image.1 hp
      exact D.what₂.places.resChar_prime w)
    (D.mem u).C.DGam (L.sc.X'' D.R.n) L.sc.a (3 * (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) ^ 2)
    (∑ τ : D.what₂.Tau, wj D j τ) hX0 hXa ha1 (by positivity) hW0
  refine key.trans ?_
  linarith

end GlobalTheory.ConjLoss

end
