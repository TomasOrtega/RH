import Mathlib
import Formalism.HermitianLattices.StatementMass

noncomputable section

namespace Formalism.MainNotions.MassRatioZetaBound

open NumberField

variable {K : Type*} [Field K] [NumberField K]

/- English proof (translation)
Establish `hpos : 0 < 1 - x` using `by linarith`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[inv_le_iff_one_le_mul₀ hpos]`. Use the polynomial consequences of the given equalities and inequalities. Use `_ ≤ Real.exp (2 * x) := by linarith [Real.add_one_le_exp (2 * x)]`.
-/
theorem inv_one_sub_le_exp {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1 / 2) : (1 - x)⁻¹ ≤ Real.exp (2 * x) := by
  have hpos : 0 < 1 - x := by linarith
  calc (1 - x)⁻¹ ≤ 1 + 2 * x := by
        rw [inv_le_iff_one_le_mul₀ hpos]; nlinarith
    _ ≤ Real.exp (2 * x) := by linarith [Real.add_one_le_exp (2 * x)]

/- English proof (translation)
Establish `hQ : (P.under ℤ).IsMaximal` using `Ideal.IsMaximal.under ℤ P`. Establish `hQ0 : P.under ℤ ≠ ⊥`. Introduce `h`. Rewrite `hQ` using `[h]`. Conclude with `Int.not_isField (Ring.isField_iff_maximal_bot.2 hQ)`.

Take `⟨p, hp, hpp⟩` from `Ideal.IsPrime.exists_mem_prime_of_ne_bot hQ.isPrime hQ0`. Use `⟨p.natAbs, Int.prime_iff_natAbs_prime.1 hpp, ?_⟩` and prove the remaining obligations. Establish `hmem : algebraMap ℤ (𝓞 K) p ∈ P` using `hp`. Break down `Int.natAbs_eq p with h | h` into its components or cases. Rewrite `hmem` using `[h]`.

Simplify using `using hmem`. Rewrite `hmem` using `[h]`. Use `P.neg_mem hmem` as an intermediate fact. Simplify using `using this`.
-/
theorem exists_prime_mem (P : Ideal (𝓞 K)) [hP : P.IsMaximal] : ∃ l : ℕ, l.Prime ∧ (l : 𝓞 K) ∈ P := by
  have hQ : (P.under ℤ).IsMaximal := Ideal.IsMaximal.under ℤ P
  have hQ0 : P.under ℤ ≠ ⊥ := by
    intro h
    rw [h] at hQ
    exact Int.not_isField (Ring.isField_iff_maximal_bot.2 hQ)
  obtain ⟨p, hp, hpp⟩ := Ideal.IsPrime.exists_mem_prime_of_ne_bot hQ.isPrime hQ0
  refine ⟨p.natAbs, Int.prime_iff_natAbs_prime.1 hpp, ?_⟩
  have hmem : algebraMap ℤ (𝓞 K) p ∈ P := hp
  rcases Int.natAbs_eq p with h | h
  · rw [h] at hmem; simpa using hmem
  · rw [h] at hmem
    have := P.neg_mem hmem
    simpa using this

/- English proof (translation)
Rewrite using `[Ideal.absNorm_span_singleton]`. Establish `: ((l : 𝓞 K)) = algebraMap ℤ (𝓞 K) (l : ℤ)` using `by simp`. Rewrite using `[this, Algebra.norm_algebraMap, RingOfIntegers.rank]`. Simplify using the standard rewrite rules.
-/
theorem absNorm_nat (l : ℕ) : Ideal.absNorm (Ideal.span {(l : 𝓞 K)}) = l ^ Module.finrank ℚ K := by
  rw [Ideal.absNorm_span_singleton]
  have : ((l : 𝓞 K)) = algebraMap ℤ (𝓞 K) (l : ℤ) := by simp
  rw [this, Algebra.norm_algebraMap, RingOfIntegers.rank]
  simp

/- English proof (translation)
Establish `hle : Ideal.span {(l : 𝓞 K)} ≤ P` using `by rw [Ideal.span_le, Set.singleton_subset_iff]; exact hlP`. Establish `hd : Ideal.absNorm P ∣ l ^ Module.finrank ℚ K`. Rewrite using `[← absNorm_nat]`. Conclude with `Ideal.absNorm_dvd_absNorm_of_le hle`. Use `⟨hd, ?_⟩` and prove the remaining obligations.

Take `⟨k, -, hk⟩` from `(Nat.dvd_prime_pow hl).1 hd`. Establish `h1 : Ideal.absNorm P ≠ 1`. Rewrite using `[Ne, Ideal.absNorm_eq_one_iff]`. Conclude with `hP.ne_top`. Rewrite `h1`, the goal using `[hk]`.

Break down `k with _ | k` into its components or cases. Simplify using `at h1`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem absNorm_ge (P : Ideal (𝓞 K)) [hP : P.IsMaximal] {l : ℕ} (hl : l.Prime) (hlP : (l : 𝓞 K) ∈ P) :
    Ideal.absNorm P ∣ l ^ Module.finrank ℚ K ∧ l ≤ Ideal.absNorm P := by
  have hle : Ideal.span {(l : 𝓞 K)} ≤ P := by rw [Ideal.span_le, Set.singleton_subset_iff]; exact hlP
  have hd : Ideal.absNorm P ∣ l ^ Module.finrank ℚ K := by
    rw [← absNorm_nat]; exact Ideal.absNorm_dvd_absNorm_of_le hle
  refine ⟨hd, ?_⟩
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hl).1 hd
  have h1 : Ideal.absNorm P ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]; exact hP.ne_top
  rw [hk] at h1 ⊢
  rcases k with _ | k
  · simp at h1
  · calc l = l ^ 1 := (pow_one l).symm
      _ ≤ l ^ (k + 1) := Nat.pow_le_pow_right hl.pos (by omega)

/- English proof (translation)
Establish `hcop : (S : Set (Ideal (𝓞 K))).Pairwise (fun P Q => IsCoprime P Q)`. Introduce `P hPS Q hQS hPQ`. Rewrite using `[Ideal.isCoprime_iff_sup_eq]`. Establish `hPm` using `(hS P hPS).1`. Establish `hQm` using `(hS Q hQS).1`.

Assume the negation of the conclusion as `h`. Establish `h1 : P ⊔ Q = P` using `(hPm.eq_of_le h le_sup_left).symm`. Establish `h2 : Q ≤ P` using `h1 ▸ le_sup_right`. Conclude with `hPQ (hQm.eq_of_le hPm.ne_top h2).symm`. Establish `hdvd : ∏ P ∈ S, P ∣ Ideal.span {(l : 𝓞 K)}`.

Use `Finset.prod_dvd_of_coprime hcop fun P hP => ?_` and prove the remaining obligations. Rewrite using `[Ideal.dvd_iff_le, Ideal.span_le, Set.singleton_subset_iff]`. Conclude with `(hS P hP).2`. Establish `hN : ∏ P ∈ S, Ideal.absNorm P ∣ l ^ Module.finrank ℚ K`. Rewrite using `[← map_prod, ← absNorm_nat]`.

Conclude with `map_dvd Ideal.absNorm hdvd`. Establish `hN' : ∏ P ∈ S, Ideal.absNorm P ≤ l ^ Module.finrank ℚ K` using `Nat.le_of_dvd (pow_pos hl.pos _) hN`. Establish `hge : l ^ S.card ≤ ∏ P ∈ S, Ideal.absNorm P`. Rewrite using `[← Finset.prod_const]`. Use `Finset.prod_le_prod' fun P hP => ?_` and prove the remaining obligations.

Use `(hS P hP).1` as an intermediate fact. Conclude with `(absNorm_ge P hl (hS P hP).2).2`. Conclude with `(Nat.pow_le_pow_iff_right hl.two_le).1 (hge.trans hN')`.
-/
theorem card_over_le {l : ℕ} (hl : l.Prime) (S : Finset (Ideal (𝓞 K))) (hS : ∀ P ∈ S, P.IsMaximal ∧ (l : 𝓞 K) ∈ P) :
    S.card ≤ Module.finrank ℚ K := by
  classical
  have hcop : (S : Set (Ideal (𝓞 K))).Pairwise (fun P Q => IsCoprime P Q) := by
    intro P hPS Q hQS hPQ
    rw [Ideal.isCoprime_iff_sup_eq]
    have hPm := (hS P hPS).1
    have hQm := (hS Q hQS).1
    by_contra h
    have h1 : P ⊔ Q = P := (hPm.eq_of_le h le_sup_left).symm
    have h2 : Q ≤ P := h1 ▸ le_sup_right
    exact hPQ (hQm.eq_of_le hPm.ne_top h2).symm
  have hdvd : ∏ P ∈ S, P ∣ Ideal.span {(l : 𝓞 K)} := by
    refine Finset.prod_dvd_of_coprime hcop fun P hP => ?_
    rw [Ideal.dvd_iff_le, Ideal.span_le, Set.singleton_subset_iff]
    exact (hS P hP).2
  have hN : ∏ P ∈ S, Ideal.absNorm P ∣ l ^ Module.finrank ℚ K := by
    rw [← map_prod, ← absNorm_nat]
    exact map_dvd Ideal.absNorm hdvd
  have hN' : ∏ P ∈ S, Ideal.absNorm P ≤ l ^ Module.finrank ℚ K :=
    Nat.le_of_dvd (pow_pos hl.pos _) hN
  have hge : l ^ S.card ≤ ∏ P ∈ S, Ideal.absNorm P := by
    rw [← Finset.prod_const]
    refine Finset.prod_le_prod' fun P hP => ?_
    have := (hS P hP).1
    exact (absNorm_ge P hl (hS P hP).2).2
  exact (Nat.pow_le_pow_iff_right hl.two_le).1 (hge.trans hN')

def zetaGL3GL2 : ℝ := ∑' m : ℕ, 1 / (m : ℝ) ^ ((3 : ℝ) / 2)

/- English proof (translation)
The claim follows from `Real.summable_one_div_nat_rpow.2 (by norm_num)`.
-/
theorem summable_Z : Summable fun m : ℕ => 1 / (m : ℝ) ^ ((3 : ℝ) / 2) :=
  Real.summable_one_div_nat_rpow.2 (by norm_num)

/- English proof (translation)
Establish `hex : ∀ P ∈ S, ∃ l : ℕ, l.Prime ∧ (l : 𝓞 K) ∈ P` using `fun P hP => by haveI := hS P hP; exact exists_prime_mem P`. Use `choose! lp hlp hlpP using hex`. Establish `hterm : ∀ P ∈ S, 1 / ((Ideal.absNorm P : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ 1 / ((lp P : ℕ) : ℝ) ^ ((3 : ℝ) / 2)`. Introduce `P hP`. Use `haveI := hS P hP`.

Establish `hge` using `(absNorm_ge P (hlp P hP) (hlpP P hP)).2`. Establish `hl0 : (0 : ℝ) < (lp P : ℝ)` using `by exact_mod_cast (hlp P hP).pos`. Apply `one_div_le_one_div_of_le (Real.rpow_pos_of_pos hl0 _)` to reduce the goal to its premises. Conclude with `Real.rpow_le_rpow hl0.le (by exact_mod_cast hge) (by norm_num)`. Combine the equalities or inequalities in the displayed calculation.

Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_congr rfl (fun P hP => by rw [(Finset.mem_filter.1 hP).2]), Finset.sum_const, nsmul_eq_mul]`. Use `_ ≤ ∑ l ∈ S.image lp, (Module.finrank ℚ K : ℝ) * (1 / (l : ℝ) ^ ((3 : ℝ) / 2)) := by`. Use `Finset.sum_le_sum fun l hl => ?_` and prove the remaining obligations. Take `⟨P0, hP0, rfl⟩` from `Finset.mem_image.1 hl`.

Use `mul_le_mul_of_nonneg_right ?_ (by positivity)` and prove the remaining obligations. Conclude with `card_over_le (hlp P0 hP0) _ fun P hP => ⟨hS P (Finset.mem_filter.1 hP).1, by` after adjusting the coercions. Use `hlpP P (Finset.mem_filter.1 hP).1` as an intermediate fact. Rewrite using `[(Finset.mem_filter.1 hP).2] at this⟩` and apply the resulting hypothesis. Use `_ = (Module.finrank ℚ K : ℝ) * ∑ l ∈ S.image lp, 1 / (l : ℝ) ^ ((3 : ℝ) / 2) := by rw [Finset.mul_sum]`.

Use `_ ≤ (Module.finrank ℚ K : ℝ) * zetaGL3GL2 := by`. Use `mul_le_mul_of_nonneg_left ?_ (by positivity)` and prove the remaining obligations. Conclude with `summable_Z.sum_le_tsum _ (fun m _ => by positivity)`.
-/
theorem sum_norm_le (S : Finset (Ideal (𝓞 K))) (hS : ∀ P ∈ S, P.IsMaximal) :
    ∑ P ∈ S, 1 / ((Ideal.absNorm P : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ (Module.finrank ℚ K : ℝ) * zetaGL3GL2 := by
  classical
  have hex : ∀ P ∈ S, ∃ l : ℕ, l.Prime ∧ (l : 𝓞 K) ∈ P := fun P hP => by
    haveI := hS P hP; exact exists_prime_mem P
  choose! lp hlp hlpP using hex
  have hterm : ∀ P ∈ S, 1 / ((Ideal.absNorm P : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ 1 / ((lp P : ℕ) : ℝ) ^ ((3 : ℝ) / 2) := by
    intro P hP
    haveI := hS P hP
    have hge := (absNorm_ge P (hlp P hP) (hlpP P hP)).2
    have hl0 : (0 : ℝ) < (lp P : ℝ) := by exact_mod_cast (hlp P hP).pos
    apply one_div_le_one_div_of_le (Real.rpow_pos_of_pos hl0 _)
    exact Real.rpow_le_rpow hl0.le (by exact_mod_cast hge) (by norm_num)
  calc ∑ P ∈ S, 1 / ((Ideal.absNorm P : ℕ) : ℝ) ^ ((3 : ℝ) / 2)
      ≤ ∑ P ∈ S, 1 / ((lp P : ℕ) : ℝ) ^ ((3 : ℝ) / 2) := Finset.sum_le_sum hterm
    _ = ∑ l ∈ S.image lp, ∑ P ∈ S with lp P = l, 1 / ((lp P : ℕ) : ℝ) ^ ((3 : ℝ) / 2) :=
        (Finset.sum_fiberwise_of_maps_to (fun P hP => Finset.mem_image_of_mem lp hP) _).symm
    _ = ∑ l ∈ S.image lp, ((S.filter (fun P => lp P = l)).card : ℝ) * (1 / (l : ℝ) ^ ((3 : ℝ) / 2)) := by
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [Finset.sum_congr rfl (fun P hP => by rw [(Finset.mem_filter.1 hP).2]), Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ l ∈ S.image lp, (Module.finrank ℚ K : ℝ) * (1 / (l : ℝ) ^ ((3 : ℝ) / 2)) := by
        refine Finset.sum_le_sum fun l hl => ?_
        obtain ⟨P0, hP0, rfl⟩ := Finset.mem_image.1 hl
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact_mod_cast card_over_le (hlp P0 hP0) _ fun P hP => ⟨hS P (Finset.mem_filter.1 hP).1, by
          have := hlpP P (Finset.mem_filter.1 hP).1; rwa [(Finset.mem_filter.1 hP).2] at this⟩
    _ = (Module.finrank ℚ K : ℝ) * ∑ l ∈ S.image lp, 1 / (l : ℝ) ^ ((3 : ℝ) / 2) := by rw [Finset.mul_sum]
    _ ≤ (Module.finrank ℚ K : ℝ) * zetaGL3GL2 := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact summable_Z.sum_le_tsum _ (fun m _ => by positivity)

/- English proof (translation)
Take `⟨l, hl, hlP⟩` from `exists_prime_mem P`. Conclude with `hl.two_le.trans (absNorm_ge P hl hlP).2`.
-/
theorem two_le_absNorm (P : Ideal (𝓞 K)) [P.IsMaximal] : 2 ≤ Ideal.absNorm P := by
  obtain ⟨l, hl, hlP⟩ := exists_prime_mem P
  exact hl.two_le.trans (absNorm_ge P hl hlP).2

/- English proof (translation)
Establish `hN1 : 1 ≤ N` using `by linarith`. Establish `hN0 : 0 < N` using `by linarith`. Prove the components needed by the constructor for the conclusion. Rewrite using `[one_div, ← Real.rpow_neg hN0.le]`. Apply `Real.rpow_le_rpow_of_exponent_le hN1` to reduce the goal to its premises.

Establish `: (3 : ℝ) ≤ M` using `by exact_mod_cast hM`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h2 : (2 : ℝ) ≤ N ^ ((3 : ℝ) / 2)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[div_le_div_iff₀ (by positivity) (by norm_num)]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem rpow_bounds {N : ℝ} (hN : 2 ≤ N) {M : ℕ} (hM : 3 ≤ M) :
    N ^ (-(M : ℝ) / 2) ≤ 1 / N ^ ((3 : ℝ) / 2) ∧ 1 / N ^ ((3 : ℝ) / 2) ≤ 1 / 2 := by
  have hN1 : 1 ≤ N := by linarith
  have hN0 : 0 < N := by linarith
  constructor
  · rw [one_div, ← Real.rpow_neg hN0.le]
    apply Real.rpow_le_rpow_of_exponent_le hN1
    have : (3 : ℝ) ≤ M := by exact_mod_cast hM
    linarith
  · have h2 : (2 : ℝ) ≤ N ^ ((3 : ℝ) / 2) := by
      calc (2 : ℝ) ≤ N := hN
        _ = N ^ (1 : ℝ) := (Real.rpow_one N).symm
        _ ≤ N ^ ((3 : ℝ) / 2) := Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith

/- English proof (translation)
Use `set N : ℝ := ((Ideal.absNorm P : ℕ) : ℝ) with hNdef`. Establish `hN2 : (2 : ℝ) ≤ N` using `by rw [hNdef]; exact_mod_cast hN`. Establish `hN0 : 0 < N` using `by linarith`. Take `⟨hb1, hb2⟩` from `rpow_bounds hN2 hM`. Use `set y : ℝ := 1 / N ^ ((3 : ℝ) / 2) with hy`.

Establish `hy0 : 0 ≤ y` using `by positivity`. Unfold `Formalism.HermitianLatticesTheory.eulerFac`. Use `split_ifs with hc`. Establish `hx : Real.sqrt N ^ (-(M : ℤ)) = N ^ (-(M : ℝ) / 2)`. Rewrite using `[Real.sqrt_eq_rpow, ← Real.rpow_intCast, ← Real.rpow_mul hN0.le]`.

Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← hNdef, hx]`. Use `set x : ℝ := N ^ (-(M : ℝ) / 2) with hxdef`.

Establish `hx0 : 0 < x` using `Real.rpow_pos_of_pos hN0 _`. Break down `Nat.even_or_odd M with he | ho` into its components or cases. Rewrite using `[he.neg_one_pow, one_mul]`. Establish `h1 : x ≤ 1 / 2` using `hb1.trans hb2`. Use `⟨inv_pos.2 (by linarith), ?_⟩` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[ho.neg_one_pow, neg_one_mul, sub_neg_eq_add]`. Use `⟨inv_pos.2 (by linarith), ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← hNdef]`.

Use `set z : ℝ := N ^ (-(M : ℤ)) with hz`. Establish `hz0 : 0 < z` using `zpow_pos hN0 _`. Establish `hzx : z ≤ N ^ (-(M : ℝ) / 2)`. Rewrite using `[hz, ← Real.rpow_intCast]`. Apply `Real.rpow_le_rpow_of_exponent_le (by linarith)` to reduce the goal to its premises.

Use `push_cast`. Establish `: (0 : ℝ) ≤ M` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hz1 : z ≤ 1 / 2` using `hzx.trans (hb1.trans hb2)`. Establish `hpos : 0 < 1 - z` using `by linarith`.

Use `⟨Real.rpow_pos_of_pos hpos _, ?_⟩` and prove the remaining obligations. Establish `e : (1 - z) ^ ((-1 : ℝ) / 2) = ((1 - z)⁻¹) ^ ((1 : ℝ) / 2)`. Rewrite using `[Real.inv_rpow hpos.le, ← Real.rpow_neg hpos.le]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e]`. Establish `hge1 : 1 ≤ (1 - z)⁻¹` using `one_le_inv₀ hpos |>.2 (by linarith)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem eulerFac_le [StarRing K] {M : ℕ} (hM : 3 ≤ M) (P : Ideal (𝓞 K)) (hN : 2 ≤ Ideal.absNorm P) :
    0 < Formalism.HermitianLatticesTheory.eulerFac K M P ∧
      Formalism.HermitianLatticesTheory.eulerFac K M P ≤ Real.exp (2 * (1 / ((Ideal.absNorm P : ℕ) : ℝ) ^ ((3 : ℝ) / 2))) := by
  set N : ℝ := ((Ideal.absNorm P : ℕ) : ℝ) with hNdef
  have hN2 : (2 : ℝ) ≤ N := by rw [hNdef]; exact_mod_cast hN
  have hN0 : 0 < N := by linarith
  obtain ⟨hb1, hb2⟩ := rpow_bounds hN2 hM
  set y : ℝ := 1 / N ^ ((3 : ℝ) / 2) with hy
  have hy0 : 0 ≤ y := by positivity
  unfold Formalism.HermitianLatticesTheory.eulerFac
  split_ifs with hc
  ·
    have hx : Real.sqrt N ^ (-(M : ℤ)) = N ^ (-(M : ℝ) / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_intCast, ← Real.rpow_mul hN0.le]
      congr 1; push_cast; ring
    rw [← hNdef, hx]
    set x : ℝ := N ^ (-(M : ℝ) / 2) with hxdef
    have hx0 : 0 < x := Real.rpow_pos_of_pos hN0 _
    rcases Nat.even_or_odd M with he | ho
    · rw [he.neg_one_pow, one_mul]
      have h1 : x ≤ 1 / 2 := hb1.trans hb2
      refine ⟨inv_pos.2 (by linarith), ?_⟩
      calc (1 - x)⁻¹ ≤ Real.exp (2 * x) := inv_one_sub_le_exp hx0.le h1
        _ ≤ Real.exp (2 * y) := Real.exp_le_exp.2 (by linarith)
    · rw [ho.neg_one_pow, neg_one_mul, sub_neg_eq_add]
      refine ⟨inv_pos.2 (by linarith), ?_⟩
      calc (1 + x)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
        _ ≤ Real.exp (2 * y) := Real.one_le_exp (by positivity)
  ·
    rw [← hNdef]
    set z : ℝ := N ^ (-(M : ℤ)) with hz
    have hz0 : 0 < z := zpow_pos hN0 _
    have hzx : z ≤ N ^ (-(M : ℝ) / 2) := by
      rw [hz, ← Real.rpow_intCast]
      apply Real.rpow_le_rpow_of_exponent_le (by linarith)
      push_cast
      have : (0 : ℝ) ≤ M := by positivity
      linarith
    have hz1 : z ≤ 1 / 2 := hzx.trans (hb1.trans hb2)
    have hpos : 0 < 1 - z := by linarith
    refine ⟨Real.rpow_pos_of_pos hpos _, ?_⟩
    have e : (1 - z) ^ ((-1 : ℝ) / 2) = ((1 - z)⁻¹) ^ ((1 : ℝ) / 2) := by
      rw [Real.inv_rpow hpos.le, ← Real.rpow_neg hpos.le]; congr 1; ring
    rw [e]
    have hge1 : 1 ≤ (1 - z)⁻¹ := one_le_inv₀ hpos |>.2 (by linarith)
    calc ((1 - z)⁻¹) ^ ((1 : ℝ) / 2) ≤ ((1 - z)⁻¹) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hge1 (by norm_num)
      _ = (1 - z)⁻¹ := Real.rpow_one _
      _ ≤ Real.exp (2 * z) := inv_one_sub_le_exp hz0.le hz1
      _ ≤ Real.exp (2 * y) := Real.exp_le_exp.2 (by linarith [hzx.trans hb1])

/- English proof (translation)
Unfold `Formalism.HermitianLatticesTheory.lValEta`. Distinguish the cases in `hm : Multipliable (fun P : {P : Ideal (𝓞 K) // P.IsMaximal} => Formalism.HermitianLatticesTheory.eulerFac K M P.1)`. Use `hm.tprod_le_of_prod_le fun s => ?_` and prove the remaining obligations. Establish `hN : ∀ P : {P : Ideal (𝓞 K) // P.IsMaximal}, 2 ≤ Ideal.absNorm P.1` using `fun P => by haveI := P.2; exact two_le_absNorm P.1`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[← Real.exp_sum, Finset.mul_sum]`. Use `_ ≤ Real.exp (2 * ((Module.finrank ℚ K : ℝ) * zetaGL3GL2)) := by`. Use `Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ?_ (by norm_num))` and prove the remaining obligations. Establish `e : ∑ P ∈ s, 1 / ((Ideal.absNorm P.1 : ℕ) : ℝ) ^ ((3 : ℝ) / 2) = ∑ Q ∈ s.map (Function.Embedding.subtype _), 1 / ((Ideal.absNorm Q : ℕ) : ℝ) ^ ((3 : ℝ) / 2)`. Rewrite using `[Finset.sum_map]`.

Both sides reduce to the same expression. Rewrite using `[e]`. Use `sum_norm_le _ fun Q hQ => ?_` and prove the remaining obligations. Take `⟨P, -, rfl⟩` from `Finset.mem_map.1 hQ`. Conclude with `P.2`.

Rewrite using `[tprod_eq_one_of_not_multipliable hm]`. Establish `hZ : 0 ≤ zetaGL3GL2` using `tsum_nonneg fun m => by positivity`. Conclude with `Real.one_le_exp (by positivity)`.
-/
theorem lValEta_le [StarRing K] {M : ℕ} (hM : 3 ≤ M) :
    Formalism.HermitianLatticesTheory.lValEta K M ≤ Real.exp (2 * ((Module.finrank ℚ K : ℝ) * zetaGL3GL2)) := by
  classical
  unfold Formalism.HermitianLatticesTheory.lValEta
  by_cases hm : Multipliable (fun P : {P : Ideal (𝓞 K) // P.IsMaximal} => Formalism.HermitianLatticesTheory.eulerFac K M P.1)
  · refine hm.tprod_le_of_prod_le fun s => ?_
    have hN : ∀ P : {P : Ideal (𝓞 K) // P.IsMaximal}, 2 ≤ Ideal.absNorm P.1 := fun P => by
      haveI := P.2; exact two_le_absNorm P.1
    calc ∏ P ∈ s, Formalism.HermitianLatticesTheory.eulerFac K M P.1
        ≤ ∏ P ∈ s, Real.exp (2 * (1 / ((Ideal.absNorm P.1 : ℕ) : ℝ) ^ ((3 : ℝ) / 2))) :=
          Finset.prod_le_prod (fun P _ => (eulerFac_le hM P.1 (hN P)).1.le) (fun P _ => (eulerFac_le hM P.1 (hN P)).2)
      _ = Real.exp (2 * ∑ P ∈ s, 1 / ((Ideal.absNorm P.1 : ℕ) : ℝ) ^ ((3 : ℝ) / 2)) := by
          rw [← Real.exp_sum, Finset.mul_sum]
      _ ≤ Real.exp (2 * ((Module.finrank ℚ K : ℝ) * zetaGL3GL2)) := by
          refine Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ?_ (by norm_num))
          have e : ∑ P ∈ s, 1 / ((Ideal.absNorm P.1 : ℕ) : ℝ) ^ ((3 : ℝ) / 2) =
              ∑ Q ∈ s.map (Function.Embedding.subtype _), 1 / ((Ideal.absNorm Q : ℕ) : ℝ) ^ ((3 : ℝ) / 2) := by
            rw [Finset.sum_map]; rfl
          rw [e]
          refine sum_norm_le _ fun Q hQ => ?_
          obtain ⟨P, -, rfl⟩ := Finset.mem_map.1 hQ
          exact P.2
  · rw [tprod_eq_one_of_not_multipliable hm]
    have hZ : 0 ≤ zetaGL3GL2 := tsum_nonneg fun m => by positivity
    exact Real.one_le_exp (by positivity)

/- English proof (translation)
Unfold `Formalism.HermitianLatticesTheory.vInv`. Establish `hd : (1 : ℝ) ≤ |(discr K : ℝ)|` using `by exact_mod_cast Int.one_le_abs (discr_ne_zero K)`. Establish `h` using `Real.one_le_rpow hd (by positivity : (0 : ℝ) ≤ 1 / (2 * (Formalism.HermitianLatticesTheory.fDeg K : ℝ)))`. Establish `e : 2 * (|(discr K : ℝ)| ^ ((1 : ℝ) / (2 * (Formalism.HermitianLatticesTheory.fDeg K : ℝ))) / 2) = |(discr K : ℝ)| ^ ((1 : ℝ) / (2 * (Formalism.HermitianLatticesTheory.fDeg K : ℝ)))` using `by ring`. Rewrite using `[e]`.

Conclude with `h`.
-/
theorem one_le_two_vInv : 1 ≤ 2 * Formalism.HermitianLatticesTheory.vInv K := by
  unfold Formalism.HermitianLatticesTheory.vInv
  have hd : (1 : ℝ) ≤ |(discr K : ℝ)| := by exact_mod_cast Int.one_le_abs (discr_ne_zero K)
  have h := Real.one_le_rpow hd (by positivity : (0 : ℝ) ≤ 1 / (2 * (Formalism.HermitianLatticesTheory.fDeg K : ℝ)))
  have e : 2 * (|(discr K : ℝ)| ^ ((1 : ℝ) / (2 * (Formalism.HermitianLatticesTheory.fDeg K : ℝ))) / 2) =
      |(discr K : ℝ)| ^ ((1 : ℝ) / (2 * (Formalism.HermitianLatticesTheory.fDeg K : ℝ))) := by ring
  rw [e]; exact h

/- English proof (translation)
Unfold `Formalism.HermitianLatticesTheory.massRatioRightSide`. Establish `hv : 0 ≤ Formalism.HermitianLatticesTheory.vInv K`. Use `one_le_two_vInv (K := K)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Use `set a : ℝ := ((((M - 1).factorial : ℕ) : ℝ) * (Formalism.HermitianLatticesTheory.vInv K / Real.pi) ^ M) ^ Formalism.HermitianLatticesTheory.fDeg K with ha`.

Establish `ha0 : 0 ≤ a` using `by positivity`. Use `set b : ℝ := Real.sqrt ((2 * Formalism.HermitianLatticesTheory.vInv K) ^ Formalism.HermitianLatticesTheory.fDeg K) with hb`. Establish `hb1 : 1 ≤ b` using `Real.one_le_sqrt.2 (one_le_pow₀ one_le_two_vInv)`. Establish `hB0 : 0 ≤ Real.exp (2 * ((Module.finrank ℚ K : ℝ) * zetaGL3GL2))` using `(Real.exp_pos _).le`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem mass_ratio_rhs_le_factorial [StarRing K] {M : ℕ} (hM : 3 ≤ M) :
    Formalism.HermitianLatticesTheory.massRatioRightSide K M ≤
      ((((M - 1).factorial : ℕ) : ℝ) * (Formalism.HermitianLatticesTheory.vInv K / Real.pi) ^ M) ^ Formalism.HermitianLatticesTheory.fDeg K *
        Real.exp (2 * ((Module.finrank ℚ K : ℝ) * zetaGL3GL2)) := by
  unfold Formalism.HermitianLatticesTheory.massRatioRightSide
  have hv : 0 ≤ Formalism.HermitianLatticesTheory.vInv K := by
    have := one_le_two_vInv (K := K); linarith
  set a : ℝ := ((((M - 1).factorial : ℕ) : ℝ) * (Formalism.HermitianLatticesTheory.vInv K / Real.pi) ^ M) ^ Formalism.HermitianLatticesTheory.fDeg K with ha
  have ha0 : 0 ≤ a := by positivity
  set b : ℝ := Real.sqrt ((2 * Formalism.HermitianLatticesTheory.vInv K) ^ Formalism.HermitianLatticesTheory.fDeg K) with hb
  have hb1 : 1 ≤ b := Real.one_le_sqrt.2 (one_le_pow₀ one_le_two_vInv)
  have hB0 : 0 ≤ Real.exp (2 * ((Module.finrank ℚ K : ℝ) * zetaGL3GL2)) := (Real.exp_pos _).le
  calc a / b * Formalism.HermitianLatticesTheory.lValEta K M ≤ a / b * Real.exp (2 * ((Module.finrank ℚ K : ℝ) * zetaGL3GL2)) :=
        mul_le_mul_of_nonneg_left (lValEta_le hM) (div_nonneg ha0 (by linarith))
    _ ≤ a * Real.exp (2 * ((Module.finrank ℚ K : ℝ) * zetaGL3GL2)) :=
        mul_le_mul_of_nonneg_right (div_le_self ha0 hb1) hB0

end Formalism.MainNotions.MassRatioZetaBound

end
