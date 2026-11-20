import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPart
open NumberField ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.LieHt GlobalTheory.LieRead

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.StdScaleLat

/- English proof (translation)
Take `⟨q, hq, hqe⟩` from `h`. Assume the negation of the conclusion as `hlt`. Rewrite `hlt` using `[not_le]`. Rewrite `hqe` using `[Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hq.coeff_natDegree, map_one, one_mul]`. Establish `h1 : δ ^ q.natDegree = - ∑ i ∈ Finset.range q.natDegree, algebraMap ℤ C (q.coeff i) * δ ^ i` using `eq_neg_of_add_eq_zero_right hqe`.

Establish `hpos : 0 < ‖δ‖` using `lt_trans zero_lt_one hlt`. Establish `h2 : ‖∑ i ∈ Finset.range q.natDegree, algebraMap ℤ C (q.coeff i) * δ ^ i‖ ≤ ‖δ‖ ^ q.natDegree / ‖δ‖`. Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun i hi => ?_` and prove the remaining obligations. Rewrite using `[norm_mul, norm_pow, le_div_iff₀ hpos]`. Establish `hi' : i + 1 ≤ q.natDegree` using `Finset.mem_range.mp hi`.

Establish `hR : ‖algebraMap ℤ C (q.coeff i)‖ ≤ 1`. Rewrite using `[eq_intCast (algebraMap ℤ C)]`. Conclude with `IsUltrametricDist.norm_intCast_le_one C (q.coeff i)`. Combine the equalities or inequalities in the displayed calculation. Establish `h3 : ‖δ‖ ^ q.natDegree / ‖δ‖ < ‖δ‖ ^ q.natDegree` using `div_lt_self (by positivity) hlt`.

Establish `h4 : ‖δ ^ q.natDegree‖ = ‖δ‖ ^ q.natDegree` using `norm_pow _ _`. Rewrite `h4` using `[h1, norm_neg]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem norm_le_one_of_isIntegral_int {C : Type} [NormedField C] [IsUltrametricDist C] [Algebra ℤ C] (δ : C)
    (h : IsIntegral ℤ δ) : ‖δ‖ ≤ 1 := by
  obtain ⟨q, hq, hqe⟩ := h
  by_contra hlt
  rw [not_le] at hlt
  rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hq.coeff_natDegree, map_one, one_mul] at hqe
  have h1 : δ ^ q.natDegree = - ∑ i ∈ Finset.range q.natDegree, algebraMap ℤ C (q.coeff i) * δ ^ i :=
    eq_neg_of_add_eq_zero_right hqe
  have hpos : 0 < ‖δ‖ := lt_trans zero_lt_one hlt
  have h2 : ‖∑ i ∈ Finset.range q.natDegree, algebraMap ℤ C (q.coeff i) * δ ^ i‖
      ≤ ‖δ‖ ^ q.natDegree / ‖δ‖ := by
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun i hi => ?_
    rw [norm_mul, norm_pow, le_div_iff₀ hpos]
    have hi' : i + 1 ≤ q.natDegree := Finset.mem_range.mp hi
    have hR : ‖algebraMap ℤ C (q.coeff i)‖ ≤ 1 := by
      rw [eq_intCast (algebraMap ℤ C)]; exact IsUltrametricDist.norm_intCast_le_one C (q.coeff i)
    calc ‖algebraMap ℤ C (q.coeff i)‖ * ‖δ‖ ^ i * ‖δ‖ ≤ 1 * ‖δ‖ ^ i * ‖δ‖ := by gcongr
      _ = ‖δ‖ ^ (i + 1) := by rw [one_mul, pow_succ]
      _ ≤ ‖δ‖ ^ q.natDegree := pow_le_pow_right₀ hlt.le hi'
  have h3 : ‖δ‖ ^ q.natDegree / ‖δ‖ < ‖δ‖ ^ q.natDegree := div_lt_self (by positivity) hlt
  have h4 : ‖δ ^ q.natDegree‖ = ‖δ‖ ^ q.natDegree := norm_pow _ _
  rw [h1, norm_neg] at h4
  linarith

/- English proof (translation)
Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨i0, rfl⟩` from `hx`. Introduce `i`. Distinguish the cases in `h : i = i0`.

Substitute `h; exact ⟨1, by simp⟩` using the available equality. Conclude with `⟨0, by simp [Pi.single_apply, h]⟩`. Consider the case `zero => intro i; exact ⟨0, by simp⟩`. Consider the case `add x y _ _ hx hy`. Introduce `i`.

Take `⟨a, ha⟩` from `hx i`. Take `⟨b, hb⟩` from `hy i`. Conclude with `⟨a + b, by simp [ha, hb, mul_add]⟩`. Consider the case `smul r x _ hx`. Introduce `i`.

Take `⟨a, ha⟩` from `hx i`. Conclude with `⟨r * a, by simp [ha, Algebra.smul_def]; ring⟩`.
-/
theorem mem_span_scaled {K : Type} [Field K] [NumberField K] {g : ℕ} (D : ℕ) (v : Fin g → K)
    (hv : v ∈ Submodule.span (𝓞 K) (Set.range fun i : Fin g => (D : K) • (Pi.single i 1 : Fin g → K))) :
    ∀ i, ∃ x : 𝓞 K, v i = (D : K) * (x : K) := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i0, rfl⟩ := hx
    intro i
    by_cases h : i = i0
    · subst h; exact ⟨1, by simp⟩
    · exact ⟨0, by simp [Pi.single_apply, h]⟩
  | zero => intro i; exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    intro i
    obtain ⟨a, ha⟩ := hx i
    obtain ⟨b, hb⟩ := hy i
    exact ⟨a + b, by simp [ha, hb, mul_add]⟩
  | smul r x _ hx =>
    intro i
    obtain ⟨a, ha⟩ := hx i
    exact ⟨r * a, by simp [ha, Algebra.smul_def]; ring⟩

/- English proof (translation)
Establish `hpp : p.Prime` using `Fact.out`. Establish `e1 : ‖(D : ℂ_[p])‖ = ‖(D : ℚ_[p])‖`. Rewrite using `[← PadicComplex.norm_extends' p (D : ℚ_[p])]`. Use `congr 1`. Simplify using the standard rewrite rules.

Take `⟨e, n, hn, rfl⟩` from `Nat.exists_eq_pow_mul_and_not_dvd hD.ne' p hpp.ne_one`. Establish `hn0 : n ≠ 0` using `by rintro rfl; exact hn (dvd_zero p)`. Establish `hv : padicValNat p (p ^ e * n) = e`. Rewrite using `[padicValNat.mul (pow_ne_zero _ hpp.ne_zero) hn0, padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hn, add_zero]`. Establish `hnorm : ‖((p ^ e * n : ℕ) : ℚ_[p])‖ = ((p : ℝ)⁻¹) ^ e`.

Rewrite using `[Nat.cast_mul, Nat.cast_pow, norm_mul, norm_pow, Padic.norm_p, Padic.norm_natCast_eq_one_iff.2 ((hpp.coprime_iff_not_dvd).2 hn), mul_one]`. Rewrite using `[e1, hnorm, hv, inv_pow, inv_inv, Real.log_pow]`.
-/
theorem log_inv_norm_natCast (p : ℕ) [Fact p.Prime] (D : ℕ) (hD : 0 < D) :
    Real.log ‖(D : ℂ_[p])‖⁻¹ = (padicValNat p D : ℝ) * Real.log p := by
  have hpp : p.Prime := Fact.out
  have e1 : ‖(D : ℂ_[p])‖ = ‖(D : ℚ_[p])‖ := by
    rw [← PadicComplex.norm_extends' p (D : ℚ_[p])]; congr 1; simp
  obtain ⟨e, n, hn, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hD.ne' p hpp.ne_one
  have hn0 : n ≠ 0 := by rintro rfl; exact hn (dvd_zero p)
  have hv : padicValNat p (p ^ e * n) = e := by
    rw [padicValNat.mul (pow_ne_zero _ hpp.ne_zero) hn0, padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd hn, add_zero]
  have hnorm : ‖((p ^ e * n : ℕ) : ℚ_[p])‖ = ((p : ℝ)⁻¹) ^ e := by
    rw [Nat.cast_mul, Nat.cast_pow, norm_mul, norm_pow, Padic.norm_p,
      Padic.norm_natCast_eq_one_iff.2 ((hpp.coprime_iff_not_dvd).2 hn), mul_one]
  rw [e1, hnorm, hv, inv_pow, inv_inv, Real.log_pow]

/- English proof (translation)
Rewrite using `[← log_inv_norm_natCast p D hD]`. Unfold `lnGrP`. Use `congr 1`. Establish `hD0 : (D : ℂ_[p]) ≠ 0` using `Nat.cast_ne_zero.2 hD.ne'`. Apply `IsLeast.csInf_eq` to reduce the goal to its premises.

Prove the components needed by the constructor for the conclusion. Use `⟨fun i => j (((D : K) • (Pi.single k 1 : Fin g → K)) i), ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Simplify using `using hD0`. Introduce `i hi`. Simplify using `[Pi.single_apply, (ne_of_gt hi)]`.

Use `⟨1, fun _ => 1, fun _ => (D : K) • (Pi.single k 1 : Fin g → K), fun _ => by simp, fun _ => Submodule.subset_span ⟨k, rfl⟩, ?_⟩` and prove the remaining obligations. Use extensionality with `i`. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Introduce and unpack `r ⟨c, hck, -, ⟨n, a, v, ha, hv, rfl⟩, rfl⟩`.

Establish `hle : ‖(∑ m, a m • fun i => j (v m i)) k‖ ≤ ‖(D : ℂ_[p])‖`. Rewrite using `[Finset.sum_apply]`. Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun m _ => ?_` and prove the remaining obligations. Take `⟨x, hx⟩` from `mem_span_scaled D (v m) (hv m) k`. Establish `hjx : ‖j (x : K)‖ ≤ 1` using `@norm_le_one_of_isIntegral_int ℂ_[p] _ _ (Ring.toIntAlgebra _) _ (map_isIntegral_int j x.isIntegral_coe)`.

Simplify using `only [Pi.smul_apply, smul_eq_mul, hx, map_mul, map_natCast, norm_mul]`. Combine the equalities or inequalities in the displayed calculation. Conclude with `ha m`. Use `_ = ‖(D : ℂ_[p])‖ := by ring`. Conclude with `inv_anti₀ (norm_pos_iff.2 hck) hle`.
-/
theorem lnGrP_scaled (K : Type) [Field K] [NumberField K] (g p : ℕ) [Fact p.Prime] (D : ℕ) (hD : 0 < D)
    (j : K →+* ℂ_[p]) (k : Fin g) :
    lnGrP p j (Submodule.span (𝓞 K) (Set.range fun i : Fin g => (D : K) • (Pi.single i 1 : Fin g → K))) k =
      (padicValNat p D : ℝ) * Real.log p := by
  rw [← log_inv_norm_natCast p D hD]
  unfold lnGrP
  congr 1
  have hD0 : (D : ℂ_[p]) ≠ 0 := Nat.cast_ne_zero.2 hD.ne'
  apply IsLeast.csInf_eq
  constructor
  · refine ⟨fun i => j (((D : K) • (Pi.single k 1 : Fin g → K)) i), ?_, ?_, ?_, ?_⟩
    · simpa using hD0
    · intro i hi
      simp [Pi.single_apply, (ne_of_gt hi)]
    · refine ⟨1, fun _ => 1, fun _ => (D : K) • (Pi.single k 1 : Fin g → K), fun _ => by simp,
        fun _ => Submodule.subset_span ⟨k, rfl⟩, ?_⟩
      ext i; simp
    · simp
  · rintro r ⟨c, hck, -, ⟨n, a, v, ha, hv, rfl⟩, rfl⟩
    have hle : ‖(∑ m, a m • fun i => j (v m i)) k‖ ≤ ‖(D : ℂ_[p])‖ := by
      rw [Finset.sum_apply]
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun m _ => ?_
      obtain ⟨x, hx⟩ := mem_span_scaled D (v m) (hv m) k
      have hjx : ‖j (x : K)‖ ≤ 1 :=
        @norm_le_one_of_isIntegral_int ℂ_[p] _ _ (Ring.toIntAlgebra _) _ (map_isIntegral_int j x.isIntegral_coe)
      simp only [Pi.smul_apply, smul_eq_mul, hx, map_mul, map_natCast, norm_mul]
      calc ‖a m‖ * (‖(D : ℂ_[p])‖ * ‖j (x : K)‖) ≤ 1 * (‖(D : ℂ_[p])‖ * 1) := by
            gcongr
            · exact ha m
      _ = ‖(D : ℂ_[p])‖ := by ring
    exact inv_anti₀ (norm_pos_iff.2 hck) hle

/- English proof (translation)
Introduce `K _ _ g p _ D hD`. Repeatedly rewrite using `[lnGrP_scaled K g p D hD]`. Rewrite using `[finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, NumberField.Embeddings.card, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, nsmul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sum_lnGrP_scaled : ∀ (K : Type) [Field K] [NumberField K] (g p : ℕ) [Fact p.Prime] (D : ℕ), 0 < D → ∑ᶠ j : K →+* ℂ_[p], ∑ k : Fin g, lnGrP p j (Submodule.span (𝓞 K) (Set.range fun i : Fin g => (D : K) • (Pi.single i 1 : Fin g → K))) k = g * Module.finrank ℚ K * ((padicValNat p D : ℝ) * Real.log p) := by
  intro K _ _ g p _ D hD
  simp_rw [lnGrP_scaled K g p D hD]
  rw [finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, NumberField.Embeddings.card,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, nsmul_eq_mul]
  ring

end GlobalTheory.StdScaleLat
