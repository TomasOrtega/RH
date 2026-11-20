import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SummableCardDivisorsSqDivOneAddRpowStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RegularizedEisensteinLatticeSumEqTsumOfKillsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitStripIntegralQExpansionEqLSeriesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RankinMeanSquareCuspFormStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EisensteinLatticeSumGcdFactorOutStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegrableOnStripUnfoldedRankinIntegrandStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralCoprimeSumUnfoldToUnitStripStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.QExpansionPolyGrowthSummableContinuousStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section
namespace GlobalTheory.EisM

def rkPsi (k : ℕ) (s : ℝ) (h b : ℕ → ℂ) (τ : ℍ) : ℂ :=
  conj (qs h τ) * qs b τ * ((τ.im ^ ((k : ℝ) + s) : ℝ) : ℂ)

/- English proof (translation)
Use `set j : ℂ := ((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ) with hjdef`. Establish `hdenom : UpperHalfPlane.denom γ τ = j` using `ModularGroup.denom_apply γ τ`. Establish `hj : j ≠ 0` using `by rw [← hdenom]; exact UpperHalfPlane.denom_ne_zero _ τ`. Establish `him : (γ • τ).im = τ.im / Complex.normSq j` using `by rw [ModularGroup.im_smul_eq_div_normSq, hdenom]`. Establish `hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1`.

Use `γ.2` as an intermediate fact. Rewrite `this` using `[Matrix.det_fin_two]`. Conclude with `this`. Take `⟨m, hm⟩` from `hγ`. Establish `hcop : IsCoprime (γ 1 1) (L : ℤ)` using `⟨γ 0 0, -(γ 0 1 * m), by rw [hm] at hdet; linear_combination hdet⟩`.

Establish `hunit : IsUnit ((γ 1 1 : ℤ) : ZMod N)`. Take `⟨n, hn⟩` from `hNL`. Establish `h1 : ((γ 1 1 * γ 0 0 + (-(γ 0 1 * m * n)) * (N : ℤ) : ℤ) : ZMod N) = 1`. Rewrite `hdet` using `[hm, hn]`. Move the coercions through the operations in `at hdet`.

Establish `: γ 1 1 * γ 0 0 + (-(γ 0 1 * m * n)) * (N : ℤ) = 1` using `by linear_combination hdet`. Rewrite using `[this]`. Simplify using the standard rewrite rules. Move the coercions through the operations in `at h1`. Simplify using `only [mul_neg, neg_mul, ZMod.natCast_self, mul_zero, neg_zero, add_zero] at h1`.

Conclude with `⟨⟨_, ((γ 0 0 : ℤ) : ZMod N), h1, by rw [mul_comm]; exact h1⟩, rfl⟩`. Establish `hεε : conj (ch ε (γ 1 1)) * ch ε (γ 1 1) = 1`. Establish `hn : ‖ch ε (γ 1 1)‖ = 1`. Unfold `ch`. Rewrite using `[← hunit.unit_spec]`.

Conclude with `DirichletCharacter.unit_norm_eq_one ε hunit.unit`. Rewrite using `[mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]`. Simplify using the standard rewrite rules. Establish `hH` using `hh.1.2 γ ⟨m, hm⟩ τ`. Establish `hB` using `hb.2 γ ⟨m, hm⟩ τ`.

Rewrite `hB` using `[hχ _ hcop]`. Rewrite `hH`, `hB` using `[← hjdef]`. Establish `hNpos : 0 < Complex.normSq j` using `Complex.normSq_pos.2 hj`. Establish `hy` using `τ.im_pos`. Unfold `rkPsi trm`.

Rewrite using `[hH, hB, him, Real.div_rpow hy.le hNpos.le, Real.rpow_add hNpos, Real.rpow_natCast]`. Establish `hn2 : ‖j‖ ^ (-2 * s) = (Complex.normSq j ^ s)⁻¹`. Rewrite using `[Complex.normSq_eq_norm_sq, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _), ← Real.rpow_neg (norm_nonneg _)]`. Use `congr 1`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hn2]`. Establish `hP : (Complex.normSq j ^ s) ≠ 0` using `(Real.rpow_pos_of_pos hNpos s).ne'`. Establish `hcj : conj j ≠ 0` using `by simpa using hj`. Establish `hNc : ((Complex.normSq j : ℝ) : ℂ) = j * conj j` using `(Complex.mul_conj j).symm`.

Simplify using `only [ch] at hεε ⊢`. Establish `hε0 : ε ((γ 1 1 : ℤ) : ZMod N) ≠ 0` using `by intro h0; rw [h0, mul_zero] at hεε; exact zero_ne_one hεε`. Establish `hεc : conj (ε ((γ 1 1 : ℤ) : ZMod N)) = (ε ((γ 1 1 : ℤ) : ZMod N))⁻¹` using `eq_inv_of_mul_eq_one_left hεε`. Use `push_cast`. Rewrite using `[hNc]`.

Simplify using `only [map_mul, map_pow, hεc]`. Clear the denominators using the available nonvanishing facts. Put the polynomial expressions in normal form.
-/
theorem rankin_transf (e L N : ℕ) (ε : DirichletCharacter ℂ N) (φ : DirichletCharacter ℂ L) (χ : ℤ → ℂ)
    (h b : ℕ → ℂ) (s : ℝ) (hNL : N ∣ L) (hh : CF (2 * e + 1) L (ch ε) h) (hb : MF e L χ b)
    (hχ : ∀ d : ℤ, IsCoprime d L → χ d = ch φ d * ch ε d) (γ : SL(2, ℤ)) (hγ : (L : ℤ) ∣ γ 1 0) (τ : ℍ) :
    rkPsi (2 * e + 1) s h b (γ • τ) =
      φ ((γ 1 1 : ℤ) : ZMod L) * trm (e + 1) s (((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ)) * rkPsi (2 * e + 1) s h b τ := by
  set j : ℂ := ((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ) with hjdef
  have hdenom : UpperHalfPlane.denom γ τ = j := ModularGroup.denom_apply γ τ
  have hj : j ≠ 0 := by rw [← hdenom]; exact UpperHalfPlane.denom_ne_zero _ τ
  have him : (γ • τ).im = τ.im / Complex.normSq j := by rw [ModularGroup.im_smul_eq_div_normSq, hdenom]
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.2; rw [Matrix.det_fin_two] at this; exact this
  obtain ⟨m, hm⟩ := hγ
  have hcop : IsCoprime (γ 1 1) (L : ℤ) := ⟨γ 0 0, -(γ 0 1 * m), by rw [hm] at hdet; linear_combination hdet⟩
  have hunit : IsUnit ((γ 1 1 : ℤ) : ZMod N) := by
    obtain ⟨n, hn⟩ := hNL
    have h1 : ((γ 1 1 * γ 0 0 + (-(γ 0 1 * m * n)) * (N : ℤ) : ℤ) : ZMod N) = 1 := by
      rw [hm, hn] at hdet; push_cast at hdet
      have : γ 1 1 * γ 0 0 + (-(γ 0 1 * m * n)) * (N : ℤ) = 1 := by linear_combination hdet
      rw [this]; simp
    push_cast at h1; simp only [mul_neg, neg_mul, ZMod.natCast_self, mul_zero, neg_zero, add_zero] at h1
    exact ⟨⟨_, ((γ 0 0 : ℤ) : ZMod N), h1, by rw [mul_comm]; exact h1⟩, rfl⟩
  have hεε : conj (ch ε (γ 1 1)) * ch ε (γ 1 1) = 1 := by
    have hn : ‖ch ε (γ 1 1)‖ = 1 := by
      unfold ch; rw [← hunit.unit_spec]; exact DirichletCharacter.unit_norm_eq_one ε hunit.unit
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]; simp
  have hH := hh.1.2 γ ⟨m, hm⟩ τ
  have hB := hb.2 γ ⟨m, hm⟩ τ
  rw [hχ _ hcop] at hB
  rw [← hjdef] at hH hB
  have hNpos : 0 < Complex.normSq j := Complex.normSq_pos.2 hj
  have hy := τ.im_pos
  unfold rkPsi trm
  rw [hH, hB, him, Real.div_rpow hy.le hNpos.le, Real.rpow_add hNpos, Real.rpow_natCast]
  have hn2 : ‖j‖ ^ (-2 * s) = (Complex.normSq j ^ s)⁻¹ := by
    rw [Complex.normSq_eq_norm_sq, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _), ← Real.rpow_neg (norm_nonneg _)]
    congr 1; push_cast; ring
  rw [hn2]
  have hP : (Complex.normSq j ^ s) ≠ 0 := (Real.rpow_pos_of_pos hNpos s).ne'
  have hcj : conj j ≠ 0 := by simpa using hj
  have hNc : ((Complex.normSq j : ℝ) : ℂ) = j * conj j := (Complex.mul_conj j).symm
  simp only [ch] at hεε ⊢
  have hε0 : ε ((γ 1 1 : ℤ) : ZMod N) ≠ 0 := by intro h0; rw [h0, mul_zero] at hεε; exact zero_ne_one hεε
  have hεc : conj (ε ((γ 1 1 : ℤ) : ZMod N)) = (ε ((γ 1 1 : ℤ) : ZMod N))⁻¹ := eq_inv_of_mul_eq_one_left hεε
  push_cast
  rw [hNc]
  simp only [map_mul, map_pow, hεc]
  field_simp
  ring_nf

/- English proof (translation)
Introduce `x`. Break down `Nat.eq_zero_or_pos L with hL | hL` into its components or cases. Substitute `hL` using the available equality. Simplify using the standard rewrite rules. Take `⟨n, rfl⟩ : ∃ n, L = n + 1` from `⟨L - 1, by omega⟩`.

Establish `h0 : ∑ z : ZMod (n + 1), φ z = 0` using `MulChar.sum_eq_zero_of_ne_one hφ`. Unfold `latF`. Establish `e1 : ∀ r : ℕ, (x - (r : ℤ) • ((0 : ℤ), (1 : ℤ))).1 = x.1` using `by intro r; simp`. Distinguish the cases in `hx : ((n + 1 : ℕ) : ℤ) ∣ x.1`. Establish `e2 : ∀ r : ℕ, (x - (r : ℤ) • ((0 : ℤ), (1 : ℤ))).2 = x.2 - r` using `by intro r; simp`.

Simplify using `only [e1, e2, hx, if_true, one_mul]`. Rewrite using `[← h0]`. Use `Finset.sum_nbij' (fun r : ℕ => (((x.2 - r : ℤ)) : ZMod (n + 1))) (fun z => ((x.2 : ZMod (n + 1)) - z).val) (fun _ _ => Finset.mem_univ _) (fun z _ => Finset.mem_range.2 (ZMod.val_lt _)) ?_ ?_ (fun _ _ => rfl)` and prove the remaining obligations. Introduce `r hr`. Establish `hr' : r < n + 1` using `Finset.mem_range.1 hr`.

Simplify using `[ZMod.val_cast_of_lt hr']`. Introduce `z _`. Simplify using the standard rewrite rules. Simplify using `only [e1, hx, if_false, Finset.sum_const_zero]`.
-/
theorem latF_kills (L : ℕ) (φ : DirichletCharacter ℂ L) (hφ : φ ≠ 1) :
    Kills L (0, 1) (latF L (fun _ => 1) φ) := by
  intro x
  rcases Nat.eq_zero_or_pos L with hL | hL
  · subst hL; simp
  obtain ⟨n, rfl⟩ : ∃ n, L = n + 1 := ⟨L - 1, by omega⟩
  have h0 : ∑ z : ZMod (n + 1), φ z = 0 := MulChar.sum_eq_zero_of_ne_one hφ
  unfold latF
  have e1 : ∀ r : ℕ, (x - (r : ℤ) • ((0 : ℤ), (1 : ℤ))).1 = x.1 := by intro r; simp
  by_cases hx : ((n + 1 : ℕ) : ℤ) ∣ x.1
  · have e2 : ∀ r : ℕ, (x - (r : ℤ) • ((0 : ℤ), (1 : ℤ))).2 = x.2 - r := by intro r; simp
    simp only [e1, e2, hx, if_true, one_mul]
    rw [← h0]
    refine Finset.sum_nbij' (fun r : ℕ => (((x.2 - r : ℤ)) : ZMod (n + 1)))
      (fun z => ((x.2 : ZMod (n + 1)) - z).val) (fun _ _ => Finset.mem_univ _)
      (fun z _ => Finset.mem_range.2 (ZMod.val_lt _)) ?_ ?_ (fun _ _ => rfl)
    · intro r hr
      have hr' : r < n + 1 := Finset.mem_range.1 hr
      simp [ZMod.val_cast_of_lt hr']
    · intro z _
      simp
  · simp only [e1, hx, if_false, Finset.sum_const_zero]

/- English proof (translation)
Take `⟨C, hC⟩` from `hb`. Establish `hb2 : Summable fun n : ℕ => ‖b n‖ ^ 2 / (n : ℝ) ^ (2 * (e : ℝ) - 1 + s)`. Use `Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) ((GlobalTheory.T.summable_card_divisors_sq_div_one_add_rpow s hs).mul_left (C ^ 2))` and prove the remaining obligations. Break down `Nat.eq_zero_or_pos n with hn | hn` into its components or cases. Substitute `hn` using the available equality.

Establish `: (2 * (e : ℝ) - 1 + s) ≠ 0`. Establish `: (1 : ℝ) ≤ e` using `by exact_mod_cast he`. Combine the linear equalities and inequalities to obtain the conclusion. Simplify using `[Real.zero_rpow this]`. Establish `hn0 : (0 : ℝ) < n` using `by exact_mod_cast hn`.

Establish `key : (n : ℝ) ^ (2 * (e : ℝ) - 1 + s) = ((n : ℝ) ^ (e - 1)) ^ 2 * (n : ℝ) ^ (1 + s)`. Rewrite using `[← pow_mul, ← Real.rpow_natCast, ← Real.rpow_add hn0]`. Use `congr 1`. Move the coercions through the operations in `[Nat.cast_sub he]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hA : 0 < (n : ℝ) ^ (e - 1)` using `by positivity`. Establish `hB : 0 < (n : ℝ) ^ (1 + s)` using `Real.rpow_pos_of_pos hn0 _`. Establish `hle` using `hC n hn.ne'`. Rewrite using `[key, div_le_iff₀ (by positivity)]`. Combine the equalities or inequalities in the displayed calculation.

Clear the denominators using the available nonvanishing facts. Use `⟨hb2, ?_⟩` and prove the remaining obligations. Unfold `LSeriesSummable`. Use `Summable.of_norm (Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) ((hh.add hb2).div_const 2))` and prove the remaining obligations. Rewrite using `[LSeries.norm_term_eq]`.

Use `split_ifs with hn`. Check the signs of the components of the expression. Establish `hn0 : (0 : ℝ) < n` using `by exact_mod_cast Nat.pos_of_ne_zero hn`. Simplify using `only [Complex.ofReal_re, norm_mul, Complex.norm_conj]`. Establish `e1 : (n : ℝ) ^ (((2 * e + 1 : ℕ) : ℝ) + s) = (n : ℝ) ^ (2 * (e : ℝ) - 1 + s) * n * n`.

Rewrite using `[← Real.rpow_add_one hn0.ne', ← Real.rpow_add_one hn0.ne']`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `e2 : (n : ℝ) ^ (2 * (e : ℝ) + s) = (n : ℝ) ^ (2 * (e : ℝ) - 1 + s) * n`.

Rewrite using `[← Real.rpow_add_one hn0.ne']`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1, e2]`. Establish `hu : 0 < (n : ℝ) ^ (2 * (e : ℝ) - 1 + s)` using `Real.rpow_pos_of_pos hn0 _`.

Use `set u := (n : ℝ) ^ (2 * (e : ℝ) - 1 + s)`. Use `set A := ‖h n‖`. Use `set B := ‖b n‖`. Establish `: (A ^ 2 / (u * n * n) + B ^ 2 / u) / 2 - A * B / (u * n) = (A - B * n) ^ 2 / (2 * u * n ^ 2)` using `by field_simp; ring`. Establish `h2 : 0 ≤ (A - B * n) ^ 2 / (2 * u * n ^ 2)` using `by positivity`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem rankin_summ (e : ℕ) (h b : ℕ → ℂ) (s : ℝ) (he : 1 ≤ e) (hs : 0 < s)
    (hb : ∃ C : ℝ, ∀ n, n ≠ 0 → ‖b n‖ ≤ C * n.divisors.card * (n : ℝ) ^ (e - 1))
    (hh : Summable fun n : ℕ => ‖h n‖ ^ 2 / (n : ℝ) ^ (((2 * e + 1 : ℕ) : ℝ) + s)) :
    (Summable fun n : ℕ => ‖b n‖ ^ 2 / (n : ℝ) ^ (2 * (e : ℝ) - 1 + s)) ∧
      LSeriesSummable (fun n => conj (h n) * b n) ((2 * (e : ℝ) + s : ℝ) : ℂ) := by
  obtain ⟨C, hC⟩ := hb
  have hb2 : Summable fun n : ℕ => ‖b n‖ ^ 2 / (n : ℝ) ^ (2 * (e : ℝ) - 1 + s) := by
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) ((GlobalTheory.T.summable_card_divisors_sq_div_one_add_rpow s hs).mul_left (C ^ 2))
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      have : (2 * (e : ℝ) - 1 + s) ≠ 0 := by
        have : (1 : ℝ) ≤ e := by exact_mod_cast he
        linarith
      simp [Real.zero_rpow this]
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have key : (n : ℝ) ^ (2 * (e : ℝ) - 1 + s) = ((n : ℝ) ^ (e - 1)) ^ 2 * (n : ℝ) ^ (1 + s) := by
      rw [← pow_mul, ← Real.rpow_natCast, ← Real.rpow_add hn0]
      congr 1; push_cast [Nat.cast_sub he]; ring
    have hA : 0 < (n : ℝ) ^ (e - 1) := by positivity
    have hB : 0 < (n : ℝ) ^ (1 + s) := Real.rpow_pos_of_pos hn0 _
    have hle := hC n hn.ne'
    rw [key, div_le_iff₀ (by positivity)]
    calc ‖b n‖ ^ 2 ≤ (C * n.divisors.card * (n : ℝ) ^ (e - 1)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hle 2
      _ = C ^ 2 * ((n.divisors.card : ℝ) ^ 2 / (n : ℝ) ^ (1 + s)) * (((n : ℝ) ^ (e - 1)) ^ 2 * (n : ℝ) ^ (1 + s)) := by
        field_simp
  refine ⟨hb2, ?_⟩
  unfold LSeriesSummable
  refine Summable.of_norm (Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) ((hh.add hb2).div_const 2))
  rw [LSeries.norm_term_eq]
  split_ifs with hn
  · positivity
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  simp only [Complex.ofReal_re, norm_mul, Complex.norm_conj]
  have e1 : (n : ℝ) ^ (((2 * e + 1 : ℕ) : ℝ) + s) = (n : ℝ) ^ (2 * (e : ℝ) - 1 + s) * n * n := by
    rw [← Real.rpow_add_one hn0.ne', ← Real.rpow_add_one hn0.ne']; congr 1; push_cast; ring
  have e2 : (n : ℝ) ^ (2 * (e : ℝ) + s) = (n : ℝ) ^ (2 * (e : ℝ) - 1 + s) * n := by
    rw [← Real.rpow_add_one hn0.ne']; congr 1; ring
  rw [e1, e2]
  have hu : 0 < (n : ℝ) ^ (2 * (e : ℝ) - 1 + s) := Real.rpow_pos_of_pos hn0 _
  set u := (n : ℝ) ^ (2 * (e : ℝ) - 1 + s)
  set A := ‖h n‖
  set B := ‖b n‖
  have : (A ^ 2 / (u * n * n) + B ^ 2 / u) / 2 - A * B / (u * n) = (A - B * n) ^ 2 / (2 * u * n ^ 2) := by
    field_simp; ring
  have h2 : 0 ≤ (A - B * n) ^ 2 / (2 * u * n ^ 2) := by positivity
  linarith

/- English proof (translation)
Introduce `e L N ε φ χ ρ h b s he hs hL hNL hρ hφ hh hb hχ hbC`. Establish `hcont` using `fun a (ha : PolyB a) => (GlobalTheory.T.qExpansion_polyGrowth_summable_continuous a ha).2`. Use `set Lφ := LSeries (fun n => φ n) ((e + 1 : ℕ) + 2 * s) with hLφ`. Establish `hlat : ∀ τ : ℍ, lat (e + 1) s L (0, 1) (latF L (fun _ => 1) φ) τ = Lφ * ∑' x : {x : ℤ × ℤ // IsCoprime x.1 x.2 ∧ (L : ℤ) ∣ x.1}, φ (x.1.2 : ZMod L) * trm (e + 1) s ((x.1.1 : ℂ) * τ + x.1.2)`. Introduce `τ`.

Establish `hb1 : ∃ C : ℝ, ∀ x, ‖latF L (fun _ => 1) φ x‖ ≤ C` using `⟨1, fun x => by`. Apply the tactic sequence `unfold latF; split_ifs <;> simp [DirichletCharacter.norm_le_one]⟩`. Rewrite using `[(GlobalTheory.T.regularizedEisensteinLatticeSum_eq_tsum_of_kills (e + 1) L s (0, 1) _ τ (by omega) hs hL hb1 (latF_kills L φ hφ)).2]`. Conclude with `GlobalTheory.T.eisenstein_lattice_sum_gcd_factor_out (e + 1) L s φ τ (by omega) hs hL`. Use `set Ψ := rkPsi (2 * e + 1) s h b with hΨ`.

Use `set W : ℤ × ℤ → ℍ → ℂ := fun x τ => φ (x.2 : ZMod L) * trm (e + 1) s ((x.1 : ℂ) * τ + x.2) * Ψ τ with hW`. Establish `hpt : ∀ τ : ℍ, (ρ τ : ℂ) * (conj (qs h τ) * (qs b τ * lat (e + 1) s L (0, 1) (latF L (fun _ => 1) φ) τ * ((τ.im ^ s : ℝ) : ℂ)) * (τ.im : ℂ) ^ (2 * e + 1)) = Lφ * ((ρ τ : ℂ) * ∑' x : {x : ℤ × ℤ // IsCoprime x.1 x.2 ∧ (L : ℤ) ∣ x.1}, W x.1 τ)`. Introduce `τ`. Rewrite using `[hlat τ]`. Simplify using `only [hW]`.

Rewrite using `[tsum_mul_right]`. Establish `hy : ((τ.im ^ (((2 * e + 1 : ℕ) : ℝ) + s) : ℝ) : ℂ) = (τ.im : ℂ) ^ (2 * e + 1) * ((τ.im ^ s : ℝ) : ℂ)`. Rewrite using `[Real.rpow_add τ.im_pos, Real.rpow_natCast]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `only [hΨ, rkPsi, hy]`. Expand and normalize the polynomial expressions, which then agree. Establish `hmsq` using `GlobalTheory.T.rankin_mean_square_cuspForm (2 * e + 1) L (ch ε) h (by omega) hh`. Take `⟨hbsq, hLS⟩` from `rankin_summ e h b s he hs hbC (by simpa using hmsq.2.2.1 s hs)`. Establish `hint : IntegrableOn Ψ strip`.

Conclude with `GlobalTheory.T.integrableOn_strip_unfolded_rankin_integrand (2 * e + 1) e L N ε h b s rfl he hs hL hNL hh hb.1 hbsq`. Establish `hmeas : AEStronglyMeasurable Ψ`. Use `Continuous.aestronglyMeasurable ?_` and prove the remaining obligations. Simplify using `only [hΨ, rkPsi]`. Use `((Complex.continuous_conj.comp (hcont h hh.1.1)).mul (hcont b hb.1)).mul (Complex.continuous_ofReal.comp ?_)` and prove the remaining obligations.

Conclude with `(UpperHalfPlane.continuous_im).rpow_const (fun τ => Or.inl τ.im_pos.ne')`. Establish `hunf` using `GlobalTheory.T.integral_coprime_sum_unfold_to_unitStrip L ρ Ψ W hρ hint hmeas (fun γ hγ τ => by`. Simplify `rankin_transf e L N ε φ χ h b s hNL hh hb hχ γ hγ τ)` using `[hW]`. Establish `hmel` using `GlobalTheory.T.unitStrip_integral_qExpansion_eq_LSeries h b (2 * (e : ℝ) + s) (by positivity) hh.1.1 hb.1 hmsq.1 hLS`. Establish `hΨeq : (fun τ : ℍ => conj (qs h τ) * qs b τ * ((τ.im ^ ((2 * (e : ℝ) + s) + 1) : ℝ) : ℂ)) = Ψ`.

Use function extensionality and compare the values at `τ`. Simplify using `only [hΨ, rkPsi]`. Use `congr 3`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite `hmel` using `[hΨeq]`. Unfold `pet`. Repeatedly rewrite using `[hpt]`. Rewrite using `[integral_const_mul, hunf, hmel hint]`.
-/
theorem rankin_unfold : ∀ (e L N : ℕ) (ε : DirichletCharacter ℂ N) (φ : DirichletCharacter ℂ L) (χ : ℤ → ℂ) (ρ : ℍ → ℝ) (h b : ℕ → ℂ) (s : ℝ), 1 ≤ e → 0 < s → 0 < L → N ∣ L → Wt L ρ → φ ≠ 1 → CF (2 * e + 1) L (ch ε) h → MF e L χ b → (∀ d : ℤ, IsCoprime d L → χ d = ch φ d * ch ε d) → (∃ C : ℝ, ∀ n, n ≠ 0 → ‖b n‖ ≤ C * n.divisors.card * (n : ℝ) ^ (e - 1)) → pet (2 * e + 1) ρ (qs h) (fun τ => qs b τ * lat (e + 1) s L (0, 1) (latF L (fun _ => 1) φ) τ * ((τ.im ^ s : ℝ) : ℂ)) = LSeries (fun n => φ n) ((e + 1 : ℕ) + 2 * s) * (((Real.Gamma (2 * (e : ℝ) + s) / (4 * π) ^ (2 * (e : ℝ) + s) : ℝ) : ℂ) * LSeries (fun n => conj (h n) * b n) ((2 * (e : ℝ) + s : ℝ) : ℂ)) := by
  intro e L N ε φ χ ρ h b s he hs hL hNL hρ hφ hh hb hχ hbC
  have hcont := fun a (ha : PolyB a) => (GlobalTheory.T.qExpansion_polyGrowth_summable_continuous a ha).2
  set Lφ := LSeries (fun n => φ n) ((e + 1 : ℕ) + 2 * s) with hLφ
  have hlat : ∀ τ : ℍ, lat (e + 1) s L (0, 1) (latF L (fun _ => 1) φ) τ = Lφ *
      ∑' x : {x : ℤ × ℤ // IsCoprime x.1 x.2 ∧ (L : ℤ) ∣ x.1}, φ (x.1.2 : ZMod L) * trm (e + 1) s ((x.1.1 : ℂ) * τ + x.1.2) := by
    intro τ
    have hb1 : ∃ C : ℝ, ∀ x, ‖latF L (fun _ => 1) φ x‖ ≤ C := ⟨1, fun x => by
      unfold latF; split_ifs <;> simp [DirichletCharacter.norm_le_one]⟩
    rw [(GlobalTheory.T.regularizedEisensteinLatticeSum_eq_tsum_of_kills (e + 1) L s (0, 1) _ τ (by omega) hs hL hb1 (latF_kills L φ hφ)).2]
    exact GlobalTheory.T.eisenstein_lattice_sum_gcd_factor_out (e + 1) L s φ τ (by omega) hs hL
  set Ψ := rkPsi (2 * e + 1) s h b with hΨ
  set W : ℤ × ℤ → ℍ → ℂ := fun x τ => φ (x.2 : ZMod L) * trm (e + 1) s ((x.1 : ℂ) * τ + x.2) * Ψ τ with hW
  have hpt : ∀ τ : ℍ, (ρ τ : ℂ) * (conj (qs h τ) * (qs b τ * lat (e + 1) s L (0, 1) (latF L (fun _ => 1) φ) τ * ((τ.im ^ s : ℝ) : ℂ)) * (τ.im : ℂ) ^ (2 * e + 1)) =
      Lφ * ((ρ τ : ℂ) * ∑' x : {x : ℤ × ℤ // IsCoprime x.1 x.2 ∧ (L : ℤ) ∣ x.1}, W x.1 τ) := by
    intro τ
    rw [hlat τ]
    simp only [hW]
    rw [tsum_mul_right]
    have hy : ((τ.im ^ (((2 * e + 1 : ℕ) : ℝ) + s) : ℝ) : ℂ) = (τ.im : ℂ) ^ (2 * e + 1) * ((τ.im ^ s : ℝ) : ℂ) := by
      rw [Real.rpow_add τ.im_pos, Real.rpow_natCast]; push_cast; ring
    simp only [hΨ, rkPsi, hy]
    ring
  have hmsq := GlobalTheory.T.rankin_mean_square_cuspForm (2 * e + 1) L (ch ε) h (by omega) hh
  obtain ⟨hbsq, hLS⟩ := rankin_summ e h b s he hs hbC (by simpa using hmsq.2.2.1 s hs)
  have hint : IntegrableOn Ψ strip := by
    exact GlobalTheory.T.integrableOn_strip_unfolded_rankin_integrand (2 * e + 1) e L N ε h b s rfl he hs hL hNL hh hb.1 hbsq
  have hmeas : AEStronglyMeasurable Ψ := by
    refine Continuous.aestronglyMeasurable ?_
    simp only [hΨ, rkPsi]
    refine ((Complex.continuous_conj.comp (hcont h hh.1.1)).mul (hcont b hb.1)).mul (Complex.continuous_ofReal.comp ?_)
    exact (UpperHalfPlane.continuous_im).rpow_const (fun τ => Or.inl τ.im_pos.ne')
  have hunf := GlobalTheory.T.integral_coprime_sum_unfold_to_unitStrip L ρ Ψ W hρ hint hmeas (fun γ hγ τ => by
    simpa [hW] using rankin_transf e L N ε φ χ h b s hNL hh hb hχ γ hγ τ)
  have hmel := GlobalTheory.T.unitStrip_integral_qExpansion_eq_LSeries h b (2 * (e : ℝ) + s) (by positivity) hh.1.1 hb.1 hmsq.1 hLS
  have hΨeq : (fun τ : ℍ => conj (qs h τ) * qs b τ * ((τ.im ^ ((2 * (e : ℝ) + s) + 1) : ℝ) : ℂ)) = Ψ := by
    funext τ; simp only [hΨ, rkPsi]; congr 3; push_cast; ring
  rw [hΨeq] at hmel
  unfold pet
  simp_rw [hpt]
  rw [integral_const_mul, hunf, hmel hint]

end GlobalTheory.EisM
end
