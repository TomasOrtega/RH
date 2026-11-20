import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefiniteThetaPairTermsNormsIndependentRepresenta
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DerivationDenominatorsAndHostFieldSizes
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormLeOneOfValuationLeOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefiniteThetaPairNormPadicValuationBoundStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoordIntOfJets

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.NormSum.DenomBound

/- English proof (translation)
Rewrite using `[Real.log_nat_eq_sum_factorization, Finsupp.sum_of_support_subset _ (Finset.subset_union_right (s₁ := S)) _ (by simp)]`. Rewrite using `[← Finset.sum_congr rfl fun (l : ℕ) (hl : l ∈ S) => congrArg (fun t : ℕ => (t : ℝ) * Real.log l) (Nat.factorization_def n (hS l hl))]`. Conclude with `Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left fun l _ _ => mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)`.
-/
theorem sum_val_log_le (S : Finset ℕ) (hS : ∀ l ∈ S, l.Prime) (n : ℕ) :
    ∑ l ∈ S, (padicValNat l n : ℝ) * Real.log l ≤ Real.log n := by
  rw [Real.log_nat_eq_sum_factorization,
    Finsupp.sum_of_support_subset _ (Finset.subset_union_right (s₁ := S)) _ (by simp)]
  rw [← Finset.sum_congr rfl fun (l : ℕ) (hl : l ∈ S) =>
    congrArg (fun t : ℕ => (t : ℝ) * Real.log l) (Nat.factorization_def n (hS l hl))]
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left fun l _ _ =>
    mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)

/- English proof (translation)
Establish `h1 : 8 ^ (2 * x) ≤ x ^ (6 * x)`. Rewrite using `[show 6 * x = 3 * (2 * x) by ring, pow_mul x]`. Conclude with `Nat.pow_le_pow_left (by simpa using Nat.pow_le_pow_left hx 3) _`. Establish `h2 : (4 * x).factorial ≤ x ^ (12 * x)`. Use `(Nat.factorial_le_pow _).trans ?_` and prove the remaining obligations.

Rewrite using `[show 12 * x = 3 * (4 * x) by ring, pow_mul x]`. Use `Nat.pow_le_pow_left ?_ _` and prove the remaining obligations. Rewrite using `[pow_succ]`. Conclude with `Nat.mul_le_mul_right _ (by simpa using Nat.pow_le_pow_left hx 2)`. Establish `h3 : 8 ^ (2 * x) * (4 * x).factorial ≤ x ^ (18 * x)`.

Rewrite using `[show 18 * x = 6 * x + 12 * x by ring, pow_add]`. Conclude with `Nat.mul_le_mul h1 h2`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem log_order_le (x : ℕ) (hx : 2 ≤ x) :
    Real.log ((8 ^ (2 * x) * (4 * x).factorial : ℕ) : ℝ) ≤ 18 * x * Real.log x := by
  have h1 : 8 ^ (2 * x) ≤ x ^ (6 * x) := by
    rw [show 6 * x = 3 * (2 * x) by ring, pow_mul x]
    exact Nat.pow_le_pow_left (by simpa using Nat.pow_le_pow_left hx 3) _
  have h2 : (4 * x).factorial ≤ x ^ (12 * x) := by
    refine (Nat.factorial_le_pow _).trans ?_
    rw [show 12 * x = 3 * (4 * x) by ring, pow_mul x]
    refine Nat.pow_le_pow_left ?_ _
    rw [pow_succ]
    exact Nat.mul_le_mul_right _ (by simpa using Nat.pow_le_pow_left hx 2)
  have h3 : 8 ^ (2 * x) * (4 * x).factorial ≤ x ^ (18 * x) := by
    rw [show 18 * x = 6 * x + 12 * x by ring, pow_add]
    exact Nat.mul_le_mul h1 h2
  calc _ ≤ Real.log ((x ^ (18 * x) : ℕ) : ℝ) :=
        Real.log_le_log (by positivity) (by exact_mod_cast h3)
    _ = _ := by rw [Nat.cast_pow, Real.log_pow]; push_cast; ring

noncomputable def expo_vp (f N d Q : ℕ) (B : ℝ) (dl : ℕ → ℝ) (p : ℕ) : ℝ :=
  (padicValNat p (8 ^ (4 * f * N) * (8 * f * N).factorial) : ℝ) +
    4 * f * N * B * (dl p + (if p = d then 1 / 4 else 0) + (padicValNat p Q : ℝ)) +
    4 * (N : ℝ) ^ 2 * (padicValNat p Q : ℝ)

/- English proof (translation)
Use `set M : ℕ := 8 ^ (4 * f * N) * (8 * f * N).factorial with hM`. Establish `hM0 : M ≠ 0` using `by positivity`. Use `set S' : Finset ℕ := (M.primeFactors ∪ S ∪ {d} ∪ Q.primeFactors).filter Nat.Prime with hS'`. Establish `hP : ∀ l ∈ S', l.Prime` using `fun l hl => (Finset.mem_filter.1 hl).2`. Use `⟨S', hP, fun l => ?_, fun l hl => ?_, ?_⟩` and prove the remaining obligations.

Use `h0 l` as an intermediate fact. Establish `hB0 : 0 ≤ B` using `by linarith`. Unfold `expo_vp`. Simplify using `only`. Apply the tactic sequence `split_ifs <;> positivity`.

Simplify using `only split_ifs with hp`. Simplify using `only [hS', Finset.mem_filter, hp, and_true, Finset.mem_union, not_or, Finset.mem_singleton, Nat.mem_primeFactors, true_and, ne_eq, hM0, hQ.ne', not_false_eq_true] at hl`. Take `⟨⟨⟨a1, a2⟩, a3⟩, a4⟩` from `hl`. Unfold `expo_vp`. Rewrite using `[← hM, padicValNat.eq_zero_of_not_dvd a1, padicValNat.eq_zero_of_not_dvd a4, hz l a2, if_neg a3]`.

Simplify using the standard rewrite rules. Both sides reduce to the same expression. Establish `e1` using `sum_val_log_le S' hP M`. Establish `e2` using `sum_val_log_le S' hP Q`. Establish `e3 : ∑ l ∈ S', dl l * Real.log l ≤ L`.

Use `le_trans ?_ hs` and prove the remaining obligations. Rewrite using `[Finset.sum_subset (s₁ := S) (s₂ := S ∪ S') Finset.subset_union_left (fun l _ hl => by rw [hz l hl, zero_mul])]`. Conclude with `Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_right fun l _ _ => mul_nonneg (h0 l) (Real.log_natCast_nonneg _)`. Establish `e4 : ∑ l ∈ S', (if l = d then (1 / 4 : ℝ) else 0) * Real.log l ≤ L / 2`. Simplify using `only [ite_mul, zero_mul, Finset.sum_ite_eq']`.

Apply the tactic sequence `split_ifs <;> linarith`. Establish `e5 : Real.log M ≤ 18 * (f * (2 * N)) * Real.log (f * (2 * N))`. Use `log_order_le (f * (2 * N)) (by nlinarith)` as an intermediate fact. Rewrite `this` using `[show 2 * (f * (2 * N)) = 4 * f * N by ring, show 4 * (f * (2 * N)) = 8 * f * N by ring, ← hM]`. Move the coercions through the operations in `at this`.

Conclude with `this`. Establish `e6 : ∑ l ∈ S', (if l.Prime then expo_vp f N d Q B dl l else 0) * Real.log l = ∑ l ∈ S', (padicValNat l M : ℝ) * Real.log l + 4 * f * N * B * (∑ l ∈ S', dl l * Real.log l + ∑ l ∈ S', (if l = d then (1 / 4 : ℝ) else 0) * Real.log l + ∑ l ∈ S', (padicValNat l Q : ℝ) * Real.log l) + …`. Rewrite using `[← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun l hl => ?_` and prove the remaining obligations. Rewrite using `[if_pos (hP l hl), expo_vp, ← hM]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hfR : (1 : ℝ) ≤ f` using `by exact_mod_cast hf`. Establish `hNR : (1 : ℝ) ≤ N` using `by exact_mod_cast hN`. Establish `hq : 0 ≤ Real.log Q` using `Real.log_natCast_nonneg _`. Establish `hc : 0 ≤ 4 * (f : ℝ) * N * B` using `by positivity`.

Establish `hfB : 1 ≤ (f : ℝ) * B` using `by nlinarith`. Establish `g1` using `mul_le_mul_of_nonneg_left (add_le_add (add_le_add e3 e4) e2) hc`. Establish `g2` using `mul_le_mul_of_nonneg_left e2 (show 0 ≤ 4 * (N : ℝ) ^ 2 by positivity)`. Establish `g3 : (N : ℝ) * (f * N * B * Real.log Q) ≥ 1 * (f * N * B * Real.log Q)` using `mul_le_mul_of_nonneg_right hNR (by positivity)`. Establish `g4 : (f : ℝ) * B * (N ^ 2 * Real.log Q) ≥ 1 * (N ^ 2 * Real.log Q)` using `mul_le_mul_of_nonneg_right hfB (by positivity)`.

Establish `g5 : 0 ≤ (f : ℝ) * N * B * L` using `by positivity`. Establish `g6 : 0 ≤ (f : ℝ) * N ^ 2 * B * Real.log Q` using `by positivity`. Use `show ∑ l ∈ S', (if l.Prime then expo_vp f N d Q B dl l else 0) * Real.log l ≤ _`. Rewrite using `[e6, intBound]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem exists_exponents (f N d Q : ℕ) (B L : ℝ) (S : Finset ℕ) (dl : ℕ → ℝ) (hf : 1 ≤ f) (hN : 1 ≤ N) (hB : 1 ≤ B)
    (hL : 1 ≤ L) (hQ : 0 < Q) (h0 : ∀ l, 0 ≤ dl l) (hz : ∀ l, l ∉ S → dl l = 0)
    (hs : ∑ l ∈ S, dl l * Real.log l ≤ L) (hd : Real.log d ≤ 2 * L) :
    ∃ S' : Finset ℕ, Exponents S' (fun p => if p.Prime then expo_vp f N d Q B dl p else 0) (intBound 18 f N B L Q) := by
  set M : ℕ := 8 ^ (4 * f * N) * (8 * f * N).factorial with hM
  have hM0 : M ≠ 0 := by positivity
  set S' : Finset ℕ := (M.primeFactors ∪ S ∪ {d} ∪ Q.primeFactors).filter Nat.Prime with hS'
  have hP : ∀ l ∈ S', l.Prime := fun l hl => (Finset.mem_filter.1 hl).2
  refine ⟨S', hP, fun l => ?_, fun l hl => ?_, ?_⟩
  · have := h0 l
    have hB0 : 0 ≤ B := by linarith
    unfold expo_vp
    dsimp only
    split_ifs <;> positivity
  · dsimp only
    split_ifs with hp
    · simp only [hS', Finset.mem_filter, hp, and_true, Finset.mem_union, not_or, Finset.mem_singleton,
        Nat.mem_primeFactors, true_and, ne_eq, hM0, hQ.ne', not_false_eq_true] at hl
      obtain ⟨⟨⟨a1, a2⟩, a3⟩, a4⟩ := hl
      unfold expo_vp
      rw [← hM, padicValNat.eq_zero_of_not_dvd a1, padicValNat.eq_zero_of_not_dvd a4, hz l a2, if_neg a3]
      simp
    · rfl
  · have e1 := sum_val_log_le S' hP M
    have e2 := sum_val_log_le S' hP Q
    have e3 : ∑ l ∈ S', dl l * Real.log l ≤ L := by
      refine le_trans ?_ hs
      rw [Finset.sum_subset (s₁ := S) (s₂ := S ∪ S') Finset.subset_union_left (fun l _ hl => by rw [hz l hl, zero_mul])]
      exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_right fun l _ _ =>
        mul_nonneg (h0 l) (Real.log_natCast_nonneg _)
    have e4 : ∑ l ∈ S', (if l = d then (1 / 4 : ℝ) else 0) * Real.log l ≤ L / 2 := by
      simp only [ite_mul, zero_mul, Finset.sum_ite_eq']
      split_ifs <;> linarith
    have e5 : Real.log M ≤ 18 * (f * (2 * N)) * Real.log (f * (2 * N)) := by
      have := log_order_le (f * (2 * N)) (by nlinarith)
      rw [show 2 * (f * (2 * N)) = 4 * f * N by ring, show 4 * (f * (2 * N)) = 8 * f * N by ring, ← hM] at this
      push_cast at this
      exact this
    have e6 : ∑ l ∈ S', (if l.Prime then expo_vp f N d Q B dl l else 0) * Real.log l =
        ∑ l ∈ S', (padicValNat l M : ℝ) * Real.log l + 4 * f * N * B * (∑ l ∈ S', dl l * Real.log l +
          ∑ l ∈ S', (if l = d then (1 / 4 : ℝ) else 0) * Real.log l + ∑ l ∈ S', (padicValNat l Q : ℝ) * Real.log l) +
          4 * (N : ℝ) ^ 2 * ∑ l ∈ S', (padicValNat l Q : ℝ) * Real.log l := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun l hl => ?_
      rw [if_pos (hP l hl), expo_vp, ← hM]
      ring
    have hfR : (1 : ℝ) ≤ f := by exact_mod_cast hf
    have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hq : 0 ≤ Real.log Q := Real.log_natCast_nonneg _
    have hc : 0 ≤ 4 * (f : ℝ) * N * B := by positivity
    have hfB : 1 ≤ (f : ℝ) * B := by nlinarith
    have g1 := mul_le_mul_of_nonneg_left (add_le_add (add_le_add e3 e4) e2) hc
    have g2 := mul_le_mul_of_nonneg_left e2 (show 0 ≤ 4 * (N : ℝ) ^ 2 by positivity)
    have g3 : (N : ℝ) * (f * N * B * Real.log Q) ≥ 1 * (f * N * B * Real.log Q) :=
      mul_le_mul_of_nonneg_right hNR (by positivity)
    have g4 : (f : ℝ) * B * (N ^ 2 * Real.log Q) ≥ 1 * (N ^ 2 * Real.log Q) :=
      mul_le_mul_of_nonneg_right hfB (by positivity)
    have g5 : 0 ≤ (f : ℝ) * N * B * L := by positivity
    have g6 : 0 ≤ (f : ℝ) * N ^ 2 * B * Real.log Q := by positivity
    show ∑ l ∈ S', (if l.Prime then expo_vp f N d Q B dl l else 0) * Real.log l ≤ _
    rw [e6, intBound]
    nlinarith

/- English proof (translation)
Use `w.isMaximal` as an intermediate fact. Take `⟨p, n, -, h, hp, -⟩` from `Ideal.exists_prime_and_absNorm_eq_pow w.asIdeal`. Conclude with `⟨p, hp, h⟩`.
-/
theorem exists_prime_mem {K : Type} [Field K] [NumberField K] (w : Formalism.PairingDivisionLocalBalance.Pl K) :
    ∃ p : ℕ, p.Prime ∧ (p : 𝓞 K) ∈ w.asIdeal := by
  have := w.isMaximal
  obtain ⟨p, n, -, h, hp, -⟩ := Ideal.exists_prime_and_absNorm_eq_pow w.asIdeal
  exact ⟨p, hp, h⟩

/- English proof (translation)
Introduce `hI`. Use `⟨18, by norm_num, fun D Q N B L hQ hN hB hL hr => ?_⟩` and prove the remaining obligations. Take `⟨⟨S, dl, hLet⟩, hd, -, hf, -⟩` from `letters_and_sizes D (hI D).g1`. Take `⟨S', hE⟩` from `exists_exponents (fF D) N D.host.d Q B L S dl hf hN hB hL hQ.1 hLet.2.1 hLet.2.2.1 (hLet.2.2.2.1.trans hr) (by linarith)`. Use `⟨S', _, hE, ?_, ?_⟩` and prove the remaining obligations.

Introduce `δ t0 p hp Q' hQ' P hP`. Use `CoordBound.coordInt D (hI D) S dl hLet Q N B hQ (by linarith) δ t0 p Q' hQ' P hP` as an intermediate fact. Simplify using `only [if_pos hp.out]`. Conclude with `this`. Introduce `δ t0 K _ _ _ _ σ ι P P' zA zA' hs hc hn`.

Establish `ne : ∀ (R : Pair D ⊤ δ t0 Q) (z : K), (∃ h T, R.coord h T ≠ 0) → σ z = (R.norm : ℂ) → z ≠ 0`. Introduce and unpack `R z h1 h2 rfl`. Use `(RepInv.rep_indep D (hI D) ⊤ δ t0 Q R.crv R.pt0 R R.level_pos).2.2.2.2 h1` as an intermediate fact. Rewrite `h2` using `[map_zero]`. Conclude with `this.ne (by exact_mod_cast h2)`.

Establish `val : ∀ (R : Pair D ⊤ δ t0 Q) (z : K), R.Small N B → z ≠ 0 → σ z = (R.norm : ℂ) → ∀ w : Formalism.PairingDivisionLocalBalance.Pl K, -(3 * Formalism.PairingDivisionLocalBalance.wt S' (fun p => if p.Prime then expo_vp (fF D) N D.host.d Q B dl p else 0) w) ≤ (Formalism.DivisionValue …`. Introduce `R z h1 h2 h3 w`. Take `⟨p, hp, hw⟩` from `exists_prime_mem w`. Establish `: Fact p.Prime` using `⟨hp⟩`. Rewrite using `[hE.wt_eq hp w hw, if_pos hp, ← mul_assoc]`.

Use `GlobalTheory.PadicPlaceBound.neg_mul_vw_le_vw K σ z p w _ h2 hw fun lam => ?_` and prove the remaining obligations. Rewrite using `[h3]`. Conclude with `(GlobalTheory.T.definiteThetaPairNorm_padicValuation_bound D (hI D) S dl hLet δ t0 Q R.crv R.pt0 hQ R N B h1 p lam).2`. Use `⟨hE.wt_size.1, hE.wt_size.2, fun i => ?_⟩` and prove the remaining obligations. Establish `a1` using `ne _ _ (hc i).1 (hn i).1`.

Establish `a2` using `ne _ _ (hc i).2 (hn i).2`. Conclude with `⟨a1, a2, fun w => ⟨val _ _ (hs i).1 a1 (hn i).1 w, val _ _ (hs i).2 a2 (hn i).2 w⟩⟩`.
-/
theorem intSt_of_forall_inp : (∀ D, Inp D) → IntSt := by
  intro hI
  refine ⟨18, by norm_num, fun D Q N B L hQ hN hB hL hr => ?_⟩
  obtain ⟨⟨S, dl, hLet⟩, hd, -, hf, -⟩ := letters_and_sizes D (hI D).g1
  obtain ⟨S', hE⟩ := exists_exponents (fF D) N D.host.d Q B L S dl hf hN hB hL hQ.1 hLet.2.1 hLet.2.2.1
    (hLet.2.2.2.1.trans hr) (by linarith)
  refine ⟨S', _, hE, ?_, ?_⟩
  · intro δ t0 p hp Q' hQ' P hP
    have := CoordBound.coordInt D (hI D) S dl hLet Q N B hQ (by linarith) δ t0 p Q' hQ' P hP
    simp only [if_pos hp.out]
    exact this
  · intro δ t0 K _ _ _ _ σ ι P P' zA zA' hs hc hn
    have ne : ∀ (R : Pair D ⊤ δ t0 Q) (z : K), (∃ h T, R.coord h T ≠ 0) → σ z = (R.norm : ℂ) → z ≠ 0 := by
      rintro R z h1 h2 rfl
      have := (RepInv.rep_indep D (hI D) ⊤ δ t0 Q R.crv R.pt0 R R.level_pos).2.2.2.2 h1
      rw [map_zero] at h2
      exact this.ne (by exact_mod_cast h2)
    have val : ∀ (R : Pair D ⊤ δ t0 Q) (z : K), R.Small N B → z ≠ 0 → σ z = (R.norm : ℂ) → ∀ w : Formalism.PairingDivisionLocalBalance.Pl K,
        -(3 * Formalism.PairingDivisionLocalBalance.wt S' (fun p => if p.Prime then expo_vp (fF D) N D.host.d Q B dl p else 0) w) ≤
          (Formalism.DivisionValues.vw w z : ℝ) := by
      intro R z h1 h2 h3 w
      obtain ⟨p, hp, hw⟩ := exists_prime_mem w
      have : Fact p.Prime := ⟨hp⟩
      rw [hE.wt_eq hp w hw, if_pos hp, ← mul_assoc]
      refine GlobalTheory.PadicPlaceBound.neg_mul_vw_le_vw K σ z p w _ h2 hw fun lam => ?_
      rw [h3]
      exact (GlobalTheory.T.definiteThetaPairNorm_padicValuation_bound D (hI D) S dl hLet δ t0 Q R.crv R.pt0 hQ R N B h1 p lam).2
    refine ⟨hE.wt_size.1, hE.wt_size.2, fun i => ?_⟩
    have a1 := ne _ _ (hc i).1 (hn i).1
    have a2 := ne _ _ (hc i).2 (hn i).2
    exact ⟨a1, a2, fun w => ⟨val _ _ (hs i).1 a1 (hn i).1 w, val _ _ (hs i).2 a2 (hn i).2 w⟩⟩

end GlobalTheory.NormSum.DenomBound
