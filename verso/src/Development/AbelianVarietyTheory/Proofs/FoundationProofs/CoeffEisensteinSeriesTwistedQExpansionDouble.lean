import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

/- English proof (translation)
Establish `hCa : 0 ≤ Ca` using `(norm_nonneg _).trans (ha 0)`. Establish `hCb : 0 ≤ Cb` using `(norm_nonneg _).trans (hb 0)`. Simplify using `only [eis, if_neg hn]`. Use `(norm_sum_le _ _).trans ?_` and prove the remaining obligations. Establish `hcard : n.divisorsAntidiagonal.card = n.divisors.card`.

Rewrite using `[← Nat.map_div_right_divisors, Finset.card_map]`. Establish `key : ∀ p ∈ n.divisorsAntidiagonal, ‖a p.1 * (p.1 : ℂ) ^ (j - 1) * b p.2‖ ≤ Ca * Cb * (n : ℝ) ^ (j - 1)`. Introduce `p hp`. Establish `hle : p.1 ≤ n` using `Nat.divisor_le (Nat.fst_mem_divisors_of_mem_antidiagonal hp)`. Rewrite using `[norm_mul, norm_mul, norm_pow, Complex.norm_natCast]`.

Establish `h1 : (p.1 : ℝ) ^ (j - 1) ≤ (n : ℝ) ^ (j - 1)` using `pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hle) _`. Combine the equalities or inequalities in the displayed calculation. Use `(Finset.sum_le_sum key).trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[Finset.sum_const, hcard, nsmul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem eis_norm_le (j : ℕ) (c : ℂ) (a b : ℤ → ℂ) (Ca Cb : ℝ) (ha : ∀ x, ‖a x‖ ≤ Ca)
    (hb : ∀ x, ‖b x‖ ≤ Cb) (n : ℕ) (hn : n ≠ 0) :
    ‖eis j c a b n‖ ≤ Ca * Cb * n.divisors.card * (n : ℝ) ^ (j - 1) := by
  have hCa : 0 ≤ Ca := (norm_nonneg _).trans (ha 0)
  have hCb : 0 ≤ Cb := (norm_nonneg _).trans (hb 0)
  simp only [eis, if_neg hn]
  refine (norm_sum_le _ _).trans ?_
  have hcard : n.divisorsAntidiagonal.card = n.divisors.card := by
    rw [← Nat.map_div_right_divisors, Finset.card_map]
  have key : ∀ p ∈ n.divisorsAntidiagonal,
      ‖a p.1 * (p.1 : ℂ) ^ (j - 1) * b p.2‖ ≤ Ca * Cb * (n : ℝ) ^ (j - 1) := by
    intro p hp
    have hle : p.1 ≤ n := Nat.divisor_le (Nat.fst_mem_divisors_of_mem_antidiagonal hp)
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_natCast]
    have h1 : (p.1 : ℝ) ^ (j - 1) ≤ (n : ℝ) ^ (j - 1) :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hle) _
    calc ‖a p.1‖ * (p.1 : ℝ) ^ (j - 1) * ‖b p.2‖ ≤ Ca * (n : ℝ) ^ (j - 1) * Cb :=
          mul_le_mul (mul_le_mul (ha _) h1 (by positivity) hCa) (hb _) (norm_nonneg _) (by positivity)
      _ = Ca * Cb * (n : ℝ) ^ (j - 1) := by ring
  refine (Finset.sum_le_sum key).trans (le_of_eq ?_)
  rw [Finset.sum_const, hcard, nsmul_eq_mul]
  ring

/- English proof (translation)
Introduce `j c a b ⟨Ca, ha⟩ ⟨Cb, hb⟩`. Establish `hCa : 0 ≤ Ca` using `(norm_nonneg _).trans (ha 0)`. Establish `hCb : 0 ≤ Cb` using `(norm_nonneg _).trans (hb 0)`. Establish `hB` using `eis_norm_le j c a b Ca Cb ha hb`. Use `⟨?_, ⟨Ca * Cb, hB⟩, ?_⟩` and prove the remaining obligations.

Use `⟨max ‖c‖ (Ca * Cb), j + 1, fun n => ?_⟩` and prove the remaining obligations. Break down `eq_or_ne n 0 with rfl | hn` into its components or cases. Simplify using `[eis]`. Use `(hB n hn).trans ?_` and prove the remaining obligations. Establish `hn0 : (0 : ℝ) ≤ n` using `Nat.cast_nonneg n`.

Establish `h1 : (n.divisors.card : ℝ) ≤ (n : ℝ) + 1`. Use `Nat.card_divisors_le_self n` as an intermediate fact. Establish `: (n.divisors.card : ℝ) ≤ n` using `by exact_mod_cast this`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h2 : (n : ℝ) ^ (j - 1) ≤ ((n : ℝ) + 1) ^ j` using `(pow_le_pow_left₀ hn0 (by linarith) _).trans (pow_le_pow_right₀ (by linarith) (Nat.sub_le j 1))`.

Establish `h3 : Ca * Cb ≤ max ‖c‖ (Ca * Cb)` using `le_max_right _ _`. Establish `h4 : 0 ≤ Ca * Cb` using `mul_nonneg hCa hCb`. Combine the equalities or inequalities in the displayed calculation. Apply `mul_le_mul (mul_le_mul h3 h1 (by positivity) (by positivity)) h2 (by positivity) (by positivity)` to reduce the goal to its premises. Use `_ = max ‖c‖ (Ca * Cb) * ((n : ℝ) + 1) ^ (j + 1) := by ring`.

Introduce `τ set q : ℂ := cexp (2 * π * Complex.I * τ) with hqdef`. Establish `hq : ‖q‖ < 1` using `UpperHalfPlane.norm_exp_two_pi_I_lt_one τ`. Establish `hE : ∀ m : ℕ, cexp (2 * π * Complex.I * m * τ) = q ^ m` using `fun m => by`. Rewrite using `[hqdef, ← Complex.exp_nat_mul]`. Put the polynomial expressions in normal form.

Establish `hE2 : ∀ m l : ℕ, cexp (2 * π * Complex.I * (m : ℂ) * ((l : ℂ) * τ)) = q ^ (m * l)` using `fun m l => by`. Rewrite using `[hqdef, ← Complex.exp_nat_mul]`. Use `push_cast`. Put the polynomial expressions in normal form. Use `set H : ℕ+ × ℕ+ → ℂ := fun d => a ((d.1 : ℕ) : ℤ) * (((d.1 : ℕ) : ℂ)) ^ (j - 1) * b ((d.2 : ℕ) : ℤ) * q ^ ((d.1 : ℕ) * (d.2 : ℕ)) with hHdef`.

Establish `hHs : Summable H`. Use `Summable.of_norm_bounded ((summable_prod_mul_pow (j - 1) hq).prod_symm.norm.mul_left (Ca * Cb)) fun d => ?_` and prove the remaining obligations. Simplify using `only [hHdef, norm_mul, norm_pow, Complex.norm_natCast, Prod.fst_swap, Prod.snd_swap]`. Rewrite using `[mul_comm ((d.2 : ℕ)) (d.1 : ℕ)]`. Use `(mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_right (ha _) (by positivity)) (hb _) (norm_nonneg _) (by positivity)) le_rfl (by positivity) (by positivity)).trans (le_of_eq ?_)` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree. Establish `h2` using `sigmaAntidiagonalEquivProd.hasSum_iff.2 hHs.hasSum`. Establish `h3 : HasSum (fun n : ℕ+ => eis j c a b n * q ^ (n : ℕ)) (∑' d, H d)`. Use `h2.sigma fun n => ?_` and prove the remaining obligations. Use `(congrArg (HasSum _) ?_).mpr (hasSum_fintype _)` and prove the remaining obligations.

Simplify using `only [Function.comp, sigmaAntidiagonalEquivProd, divisorsAntidiagonalFactors, PNat.mk_coe, Equiv.coe_fn_mk, Finset.univ_eq_attach, hHdef]`. Rewrite using `[(n : ℕ).divisorsAntidiagonal.sum_attach (fun y : ℕ × ℕ => a (y.1 : ℤ) * ((y.1 : ℕ) : ℂ) ^ (j - 1) * b (y.2 : ℤ) * q ^ (y.1 * y.2))]`. Simplify using `only [eis, if_neg n.ne_zero, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun p hp => ?_` and prove the remaining obligations. Rewrite using `[(Nat.mem_divisorsAntidiagonal.1 hp).1]`.

Establish `h4 : HasSum (fun n : ℕ => eis j c a b n * q ^ n) (c + ∑' d, H d)`. Establish `h5` using `(hasSum_pnat_iff_hasSum_succ (f := fun n : ℕ => eis j c a b n * q ^ n)).1 h3`. Establish `h6` using `HasSum.zero_add (f := fun n : ℕ => eis j c a b n * q ^ n) h5`. Establish `h7 : eis j c a b 0 * q ^ 0 = c` using `by simp [eis]`. Rewrite `h6` using `[h7]`.

Conclude with `h6`. Establish `hqs : qs (eis j c a b) τ = c + ∑' d, H d`. Unfold `qs`. Rewrite using `[← h4.tsum_eq]`. Conclude with `tsum_congr fun n => by rw [hE]`.

Rewrite using `[hqs, add_sub_cancel_left]`. Set `e : ℕ × ℕ ≃ ℕ+ × ℕ+` to `(Equiv.prodComm ℕ ℕ).trans (Equiv.pnatEquivNat.symm.prodCongr Equiv.pnatEquivNat.symm)`. Use `set F : ℕ × ℕ → ℂ := fun p => b (p.1 + 1 : ℕ) * (((p.2 + 1 : ℕ) : ℂ) ^ (j - 1) * a (p.2 + 1 : ℕ) * cexp (2 * π * Complex.I * (p.2 + 1 : ℕ) * ((p.1 + 1 : ℕ) * τ))) with hFdef`. Establish `hFe : F = H ∘ e`. Use function extensionality and compare the values at `p`.

Simplify using `only [hFdef, hHdef, Function.comp, e, Equiv.trans_apply, Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap, Equiv.prodCongr_apply, Prod.map, Equiv.pnatEquivNat_symm_apply, Nat.succPNat_coe, Nat.succ_eq_add_one]`. Rewrite using `[hE2, mul_comm (p.2 + 1) (p.1 + 1)]`. Expand and normalize the polynomial expressions, which then agree. Establish `hFs : Summable F` using `by rw [hFe]; exact e.summable_iff.2 hHs`. Establish `hF : HasSum F (∑' d, H d)` using `by rw [hFe]; exact e.hasSum_iff.2 hHs.hasSum`.

Use `hF.prod_fiberwise fun y => ?_` and prove the remaining obligations. Rewrite using `[← tsum_mul_left]`. Conclude with `(hFs.prod_factor y).hasSum`.
-/
theorem eis_qseries : ∀ (j : ℕ) (c : ℂ) (a b : ℤ → ℂ), (∃ C : ℝ, ∀ x, ‖a x‖ ≤ C) → (∃ C : ℝ, ∀ x, ‖b x‖ ≤ C) → PolyB (eis j c a b) ∧ (∃ C : ℝ, ∀ n, n ≠ 0 → ‖eis j c a b n‖ ≤ C * n.divisors.card * (n : ℝ) ^ (j - 1)) ∧ ∀ τ : ℍ, HasSum (fun y : ℕ => b (y + 1 : ℕ) * ∑' x : ℕ, ((x + 1 : ℕ) : ℂ) ^ (j - 1) * a (x + 1 : ℕ) * cexp (2 * π * Complex.I * (x + 1 : ℕ) * ((y + 1 : ℕ) * τ))) (qs (eis j c a b) τ - c) := by
  intro j c a b ⟨Ca, ha⟩ ⟨Cb, hb⟩
  have hCa : 0 ≤ Ca := (norm_nonneg _).trans (ha 0)
  have hCb : 0 ≤ Cb := (norm_nonneg _).trans (hb 0)
  have hB := eis_norm_le j c a b Ca Cb ha hb
  refine ⟨?_, ⟨Ca * Cb, hB⟩, ?_⟩
  · refine ⟨max ‖c‖ (Ca * Cb), j + 1, fun n => ?_⟩
    rcases eq_or_ne n 0 with rfl | hn
    · simp [eis]
    · refine (hB n hn).trans ?_
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have h1 : (n.divisors.card : ℝ) ≤ (n : ℝ) + 1 := by
        have := Nat.card_divisors_le_self n
        have : (n.divisors.card : ℝ) ≤ n := by exact_mod_cast this
        linarith
      have h2 : (n : ℝ) ^ (j - 1) ≤ ((n : ℝ) + 1) ^ j :=
        (pow_le_pow_left₀ hn0 (by linarith) _).trans (pow_le_pow_right₀ (by linarith) (Nat.sub_le j 1))
      have h3 : Ca * Cb ≤ max ‖c‖ (Ca * Cb) := le_max_right _ _
      have h4 : 0 ≤ Ca * Cb := mul_nonneg hCa hCb
      calc Ca * Cb * n.divisors.card * (n : ℝ) ^ (j - 1)
          ≤ max ‖c‖ (Ca * Cb) * ((n : ℝ) + 1) * ((n : ℝ) + 1) ^ j := by
            apply mul_le_mul (mul_le_mul h3 h1 (by positivity) (by positivity)) h2 (by positivity) (by positivity)
        _ = max ‖c‖ (Ca * Cb) * ((n : ℝ) + 1) ^ (j + 1) := by ring
  · intro τ
    set q : ℂ := cexp (2 * π * Complex.I * τ) with hqdef
    have hq : ‖q‖ < 1 := UpperHalfPlane.norm_exp_two_pi_I_lt_one τ
    have hE : ∀ m : ℕ, cexp (2 * π * Complex.I * m * τ) = q ^ m := fun m => by
      rw [hqdef, ← Complex.exp_nat_mul]; ring_nf
    have hE2 : ∀ m l : ℕ, cexp (2 * π * Complex.I * (m : ℂ) * ((l : ℂ) * τ)) = q ^ (m * l) := fun m l => by
      rw [hqdef, ← Complex.exp_nat_mul]; push_cast; ring_nf
    set H : ℕ+ × ℕ+ → ℂ := fun d => a ((d.1 : ℕ) : ℤ) * (((d.1 : ℕ) : ℂ)) ^ (j - 1) * b ((d.2 : ℕ) : ℤ) *
      q ^ ((d.1 : ℕ) * (d.2 : ℕ)) with hHdef
    have hHs : Summable H := by
      refine Summable.of_norm_bounded ((summable_prod_mul_pow (j - 1) hq).prod_symm.norm.mul_left (Ca * Cb)) fun d => ?_
      simp only [hHdef, norm_mul, norm_pow, Complex.norm_natCast, Prod.fst_swap, Prod.snd_swap]
      rw [mul_comm ((d.2 : ℕ)) (d.1 : ℕ)]
      refine (mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_right (ha _) (by positivity)) (hb _)
        (norm_nonneg _) (by positivity)) le_rfl (by positivity) (by positivity)).trans (le_of_eq ?_)
      ring
    have h2 := sigmaAntidiagonalEquivProd.hasSum_iff.2 hHs.hasSum
    have h3 : HasSum (fun n : ℕ+ => eis j c a b n * q ^ (n : ℕ)) (∑' d, H d) := by
      refine h2.sigma fun n => ?_
      refine (congrArg (HasSum _) ?_).mpr (hasSum_fintype _)
      simp only [Function.comp, sigmaAntidiagonalEquivProd, divisorsAntidiagonalFactors, PNat.mk_coe,
        Equiv.coe_fn_mk, Finset.univ_eq_attach, hHdef]
      rw [(n : ℕ).divisorsAntidiagonal.sum_attach (fun y : ℕ × ℕ => a (y.1 : ℤ) * ((y.1 : ℕ) : ℂ) ^ (j - 1) * b (y.2 : ℤ) * q ^ (y.1 * y.2))]
      simp only [eis, if_neg n.ne_zero, Finset.sum_mul]
      refine Finset.sum_congr rfl fun p hp => ?_
      rw [(Nat.mem_divisorsAntidiagonal.1 hp).1]
    have h4 : HasSum (fun n : ℕ => eis j c a b n * q ^ n) (c + ∑' d, H d) := by
      have h5 := (hasSum_pnat_iff_hasSum_succ (f := fun n : ℕ => eis j c a b n * q ^ n)).1 h3
      have h6 := HasSum.zero_add (f := fun n : ℕ => eis j c a b n * q ^ n) h5
      have h7 : eis j c a b 0 * q ^ 0 = c := by simp [eis]
      rw [h7] at h6
      exact h6
    have hqs : qs (eis j c a b) τ = c + ∑' d, H d := by
      unfold qs
      rw [← h4.tsum_eq]
      exact tsum_congr fun n => by rw [hE]
    rw [hqs, add_sub_cancel_left]
    let e : ℕ × ℕ ≃ ℕ+ × ℕ+ := (Equiv.prodComm ℕ ℕ).trans (Equiv.pnatEquivNat.symm.prodCongr Equiv.pnatEquivNat.symm)
    set F : ℕ × ℕ → ℂ := fun p => b (p.1 + 1 : ℕ) * (((p.2 + 1 : ℕ) : ℂ) ^ (j - 1) * a (p.2 + 1 : ℕ) *
      cexp (2 * π * Complex.I * (p.2 + 1 : ℕ) * ((p.1 + 1 : ℕ) * τ))) with hFdef
    have hFe : F = H ∘ e := by
      funext p
      simp only [hFdef, hHdef, Function.comp, e, Equiv.trans_apply, Equiv.prodComm_apply, Prod.fst_swap,
        Prod.snd_swap, Equiv.prodCongr_apply, Prod.map, Equiv.pnatEquivNat_symm_apply, Nat.succPNat_coe, Nat.succ_eq_add_one]
      rw [hE2, mul_comm (p.2 + 1) (p.1 + 1)]
      ring
    have hFs : Summable F := by rw [hFe]; exact e.summable_iff.2 hHs
    have hF : HasSum F (∑' d, H d) := by rw [hFe]; exact e.hasSum_iff.2 hHs.hasSum
    refine hF.prod_fiberwise fun y => ?_
    rw [← tsum_mul_left]
    exact (hFs.prod_factor y).hasSum

end GlobalTheory.EisM
