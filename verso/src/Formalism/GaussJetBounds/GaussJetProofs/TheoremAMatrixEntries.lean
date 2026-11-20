import Formalism.GaussJetBounds.StatementV
import Formalism.GaussJetBounds.GaussJetProofs.CoefficientBoundMembership
import Formalism.GaussJetBounds.ThmAGauss

noncomputable section
open scoped BigOperators

namespace Formalism.DworkPowerSeriesWeights

open Formalism.IncomingBounds

/- English proof (translation)
The claim follows from `norm_pos_iff.2 (Nat.cast_ne_zero.2 hl.out.ne_zero)`.
-/
lemma norm_l_pos (l : ℕ) [hl : Fact l.Prime] : 0 < ‖(l : ℂ_[l])‖ :=
  norm_pos_iff.2 (Nat.cast_ne_zero.2 hl.out.ne_zero)

/- English proof (translation)
Establish `h : ‖(((l : ℚ_[l]) : ℚ_[l]) : ℂ_[l])‖ = ‖(l : ℚ_[l])‖` using `PadicComplex.norm_extends' l _`. Establish `h2 : (((l : ℚ_[l]) : ℚ_[l]) : ℂ_[l]) = (l : ℂ_[l])`. Simplify using the standard rewrite rules. Rewrite `h` using `[h2]`. Rewrite using `[h]`.

Conclude with `Padic.norm_p_lt_one`.
-/
lemma norm_l_lt_one (l : ℕ) [hl : Fact l.Prime] : ‖(l : ℂ_[l])‖ < 1 := by
  have h : ‖(((l : ℚ_[l]) : ℚ_[l]) : ℂ_[l])‖ = ‖(l : ℚ_[l])‖ := PadicComplex.norm_extends' l _
  have h2 : (((l : ℚ_[l]) : ℚ_[l]) : ℂ_[l]) = (l : ℂ_[l]) := by
    simp
  rw [h2] at h
  rw [h]
  exact Padic.norm_p_lt_one

/- English proof (translation)
Take `⟨c, hc⟩` from `IsAlgClosed.exists_pow_nat_eq ((l : ℂ_[l]) ^ q.num) q.pos`. Use `⟨c, ?_⟩` and prove the remaining obligations. Establish `hπ` using `norm_l_pos l`. Establish `h1 : ‖c‖ ^ q.den = ‖(l : ℂ_[l])‖ ^ q.num`. Rewrite using `[← norm_pow, hc, norm_zpow]`.

Establish `hden : (q.den : ℝ) ≠ 0` using `Nat.cast_ne_zero.2 q.den_nz`. Establish `h2 : (‖(l : ℂ_[l])‖ ^ (q : ℝ)) ^ q.den = ‖(l : ℂ_[l])‖ ^ q.num`. Rewrite using `[← Real.rpow_natCast, ← Real.rpow_mul hπ.le, ← Real.rpow_intCast]`. Use `congr 1`. Establish `: (q : ℝ) = (q.num : ℝ) / (q.den : ℝ)`.

Conclude with `(Rat.num_div_den q).symm` after adjusting the coercions. Rewrite using `[this]`. Clear the denominators using the available nonvanishing facts. Conclude with `(pow_left_inj₀ (norm_nonneg c) (Real.rpow_nonneg hπ.le _) q.den_nz).1 (h1.trans h2.symm)`.
-/
lemma exists_norm_eq_rpow_rat (l : ℕ) [hl : Fact l.Prime] (q : ℚ) :
    ∃ c : ℂ_[l], ‖c‖ = ‖(l : ℂ_[l])‖ ^ (q : ℝ) := by
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq ((l : ℂ_[l]) ^ q.num) q.pos
  refine ⟨c, ?_⟩
  have hπ := norm_l_pos l
  have h1 : ‖c‖ ^ q.den = ‖(l : ℂ_[l])‖ ^ q.num := by
    rw [← norm_pow, hc, norm_zpow]
  have hden : (q.den : ℝ) ≠ 0 := Nat.cast_ne_zero.2 q.den_nz
  have h2 : (‖(l : ℂ_[l])‖ ^ (q : ℝ)) ^ q.den = ‖(l : ℂ_[l])‖ ^ q.num := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hπ.le, ← Real.rpow_intCast]
    congr 1
    have : (q : ℝ) = (q.num : ℝ) / (q.den : ℝ) := by
      exact_mod_cast (Rat.num_div_den q).symm
    rw [this]
    field_simp
  exact (pow_left_inj₀ (norm_nonneg c) (Real.rpow_nonneg hπ.le _) q.den_nz).1 (h1.trans h2.symm)

/- English proof (translation)
Establish `hπ` using `norm_l_pos l`. Establish `hπ1` using `norm_l_lt_one l`. Break down `hx.eq_or_lt with h0 | h0` into its components or cases. Rewrite using `[← h0]`. Conclude with `Real.rpow_nonneg hπ.le _`.

Assume the negation of the conclusion as `hlt`. Rewrite `hlt` using `[not_le]`. Use `set t : ℝ := Real.logb ‖(l : ℂ_[l])‖ x with ht`. Establish `hxt : ‖(l : ℂ_[l])‖ ^ t = x` using `Real.rpow_logb hπ hπ1.ne h0`. Rewrite `hlt` using `[← hxt]`.

Establish `htb : t < b` using `(Real.rpow_lt_rpow_left_iff_of_base_lt_one hπ hπ1).1 hlt`. Take `⟨q, hq1, hq2⟩` from `exists_rat_btwn htb`. Take `⟨c, hc⟩` from `exists_norm_eq_rpow_rat l q`. Establish `h1 : x ≤ ‖c‖` using `h c (by`. Rewrite using `[hc]`.

Conclude with `Real.rpow_le_rpow_of_exponent_ge hπ hπ1.le hq2.le)`. Rewrite `h1` using `[hc, ← hxt]`. Conclude with `absurd h1 (not_le.2 ((Real.rpow_lt_rpow_left_iff_of_base_lt_one hπ hπ1).2 hq1))`.
-/
lemma le_rpow_of_forall_norm (l : ℕ) [hl : Fact l.Prime] (b x : ℝ) (hx : 0 ≤ x)
    (h : ∀ c : ℂ_[l], ‖(l : ℂ_[l])‖ ^ b ≤ ‖c‖ → x ≤ ‖c‖) : x ≤ ‖(l : ℂ_[l])‖ ^ b := by
  have hπ := norm_l_pos l
  have hπ1 := norm_l_lt_one l
  rcases hx.eq_or_lt with h0 | h0
  · rw [← h0]; exact Real.rpow_nonneg hπ.le _
  by_contra hlt
  rw [not_le] at hlt
  set t : ℝ := Real.logb ‖(l : ℂ_[l])‖ x with ht
  have hxt : ‖(l : ℂ_[l])‖ ^ t = x := Real.rpow_logb hπ hπ1.ne h0
  rw [← hxt] at hlt
  have htb : t < b := (Real.rpow_lt_rpow_left_iff_of_base_lt_one hπ hπ1).1 hlt
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn htb
  obtain ⟨c, hc⟩ := exists_norm_eq_rpow_rat l q
  have h1 : x ≤ ‖c‖ := h c (by
    rw [hc]; exact Real.rpow_le_rpow_of_exponent_ge hπ hπ1.le hq2.le)
  rw [hc, ← hxt] at h1
  exact absurd h1 (not_le.2 ((Real.rpow_lt_rpow_left_iff_of_base_lt_one hπ hπ1).2 hq1))

/- English proof (translation)
Introduce `l _ d N0 N1 _ hl hd hev K0 hK0 ζ hζ be hbe g hg0 hg U hU ε hε TT colN p hp hp1 I nu1 nu2 size hnu1 hnu2 hsize a ha hsa hN0 hsat δ hδ`. Use `le_rpow_of_forall_norm l _ _ (norm_nonneg _) fun c hc => ?_` and prove the remaining obligations. Establish `hmem` using `hW l d N0 N1 hl hd hev K0 hK0 ζ hζ be hbe g hg0 hg U hU ε hε TT colN p hp hp1 I nu1 nu2 size hnu1 hnu2 hsize a ha hsa hN0 hsat c hc`. Establish `hcpos : 0 < ‖c‖` using `lt_of_lt_of_le (Real.rpow_pos_of_pos (norm_l_pos l) _) hc`. Establish `h1` using `hδ _ hmem`.

Rewrite `h1` using `[map_smul, norm_smul, norm_inv]`. Rewrite `h1` using `[inv_mul_le_iff₀ hcpos, mul_one]`. Then use the resulting hypothesis.
-/
theorem thmAEntry_of (hW : ThmAWeyl) : ThmAEntry := by
  intro l _ d N0 N1 _ hl hd hev K0 hK0 ζ hζ be hbe g hg0 hg U hU ε hε TT colN p hp hp1 I nu1 nu2 size
    hnu1 hnu2 hsize a ha hsa hN0 hsat δ hδ
  refine le_rpow_of_forall_norm l _ _ (norm_nonneg _) fun c hc => ?_
  have hmem := hW l d N0 N1 hl hd hev K0 hK0 ζ hζ be hbe g hg0 hg U hU ε hε TT colN p hp hp1 I nu1 nu2
    size hnu1 hnu2 hsize a ha hsa hN0 hsat c hc
  have hcpos : 0 < ‖c‖ := lt_of_lt_of_le (Real.rpow_pos_of_pos (norm_l_pos l) _) hc
  have h1 := hδ _ hmem
  rw [map_smul, norm_smul, norm_inv] at h1
  rwa [inv_mul_le_iff₀ hcpos, mul_one] at h1

/- English proof (translation)
The claim follows from `thmAEntry_of (thmAWeyl_of thmAGauss)`.
-/
theorem theorem_A_matrix_entries : ThmAEntry := thmAEntry_of (thmAWeyl_of thmAGauss)

end Formalism.DworkPowerSeriesWeights
