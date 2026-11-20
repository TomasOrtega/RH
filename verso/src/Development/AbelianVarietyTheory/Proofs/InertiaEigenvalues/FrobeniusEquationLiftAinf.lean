import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BoundedAndEventuallySubMemLatStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfMuFrobeniusEquationSolvableAndTendstoStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemDeRhamFiltrationOfForallAinfLatticeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TeichmullerEpsilonRootPowSubZetaExpMemFiltrationStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLiftsOfNormLeOneStatement

noncomputable section

namespace GlobalTheory.ExpImage.Tail

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} {K : FinExt l}

abbrev Fr (l : ℕ) [Fact l.Prime] (n : ℕ) : Ainf l →+* Ainf l :=
  (WittVector.frobenius : Ainf l →+* Ainf l) ^ n

/- English proof (translation)
Rewrite using `[Fr, pow_succ']`. Both sides reduce to the same expression.
-/
theorem Fr_succ (n : ℕ) (a : Ainf l) : Fr l (n + 1) a = WittVector.frobenius (Fr l n a) := by
  rw [Fr, pow_succ']; rfl

/- English proof (translation)
Rewrite using `[Fr, pow_succ]`. Both sides reduce to the same expression.
-/
theorem Fr_succ' (n : ℕ) (a : Ainf l) : Fr l (n + 1) a = Fr l n (WittVector.frobenius a) := by
  rw [Fr, pow_succ]; rfl

/- English proof (translation)
Rewrite using `[WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def, map_pow]`.
-/
theorem frob_teich (x : OCb l) :
    WittVector.frobenius (WittVector.teichmuller l x) = WittVector.teichmuller l x ^ l := by
  rw [WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def, map_pow]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp [Fr]`. Consider the case `succ n ih => rw [Fr_succ, ih, map_pow, frob_teich, ← pow_mul, pow_succ']`.
-/
theorem Fr_teich (n : ℕ) (x : OCb l) :
    Fr l n (WittVector.teichmuller l x) = WittVector.teichmuller l x ^ l ^ n := by
  induction n with
  | zero => simp [Fr]
  | succ n ih => rw [Fr_succ, ih, map_pow, frob_teich, ← pow_mul, pow_succ']

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simpa [Fr] using h`. Consider the case `succ n ih`. Rewrite using `[Fr_succ, pow_succ']`. Conclude with `ih.frob`.
-/
theorem lifts_Fr {w : Ainf l} {c : ↥(K0 K)} (h : Lifts AI K w c) (n : ℕ) :
    Lifts AI K (Fr l n w) ((frK P K ^ n) c) := by
  induction n with
  | zero => simpa [Fr] using h
  | succ n ih =>
    rw [Fr_succ, pow_succ']
    exact ih.frob

/- English proof (translation)
Unfold `Lifts at h ⊢`. Rewrite using `[map_sum, map_sum]`. Conclude with `Finset.sum_congr rfl h`.
-/
theorem lifts_sum {ι : Type} (T : Finset ι) (w : ι → Ainf l) (c : ι → ↥(K0 K))
    (h : ∀ i ∈ T, Lifts AI K (w i) (c i)) : Lifts AI K (∑ i ∈ T, w i) (∑ i ∈ T, c i) := by
  unfold Lifts at h ⊢
  rw [map_sum, map_sum]
  exact Finset.sum_congr rfl h

def oK (P : LocPrime l) (K : FinExt l) : ↥(K0 K) →+* P.R.BdR :=
  (oB P).comp (algebraMap ↥(K0 K) (Om l))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem oK_apply (c : ↥(K0 K)) : oK P K c = oB P (c : Om l) := rfl

def u (P : LocPrime l) (j : ℕ) : P.R.BdR := qB P ((j.factorial : ℚ_[l])⁻¹) * tD P ^ j

/- English proof (translation)
Use `qB_mul_mem _ (FilB_anti ?_ (FilB_pow tD_mem j))` and prove the remaining obligations. Simplify using the standard rewrite rules.
-/
theorem u_mem (j : ℕ) : u P j ∈ FilB P 0 := by
  refine qB_mul_mem _ (FilB_anti ?_ (FilB_pow tD_mem j))
  simp

/- English proof (translation)
Establish `h` using `GlobalTheory.T.teichmullerEpsilonRoot_pow_sub_zeta_exp_mem_filtration l P AI hT 0 m M`. Rewrite `h` using `[P.ζQ_zero, one_pow, map_one, one_mul]`. Use `h using 3 with j hj` and compare the differences between its conclusion and the goal. Both sides reduce to the same expression. Rewrite using `[pow_zero, div_one, div_eq_mul_inv, map_mul, map_pow, map_natCast, u, mul_assoc]`.
-/
theorem taylor0 (hT : LocTied l P AI) (m M : ℕ) :
    io AI (WittVector.teichmuller l AI.ε ^ m) - ∑ j ∈ Finset.range M, (m : P.R.BdR) ^ j * u P j ∈
      FilB P (M : ℤ) := by
  have h := GlobalTheory.T.teichmullerEpsilonRoot_pow_sub_zeta_exp_mem_filtration l P AI hT 0 m M
  rw [P.ζQ_zero, one_pow, map_one, one_mul] at h
  convert h using 3 with j hj
  · rfl
  · rw [pow_zero, div_one, div_eq_mul_inv, map_mul, map_pow, map_natCast, u, mul_assoc]

/- English proof (translation)
Take `⟨x, y, rfl⟩` from `Ideal.mem_span_pair.mp ha`. Use `⟨x, ?_⟩` and prove the remaining obligations. Establish `h` using `FilB_zero_mul (io_mem AI y) (FilB_pow (io_ξ_mem AI) M)`. Rewrite `h` using `[mul_one]`. Use `h using 1` and compare the differences between its conclusion and the goal.

Simplify using `only [map_add, map_mul, map_pow]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem span_mem_Lat {M n : ℕ} {a : Ainf l}
    (ha : a ∈ Ideal.span {((l : ℕ) : Ainf l) ^ n, AI.ξ ^ M}) : io AI a ∈ Lat AI M n := by
  obtain ⟨x, y, rfl⟩ := Ideal.mem_span_pair.mp ha
  refine ⟨x, ?_⟩
  have h := FilB_zero_mul (io_mem AI y) (FilB_pow (io_ξ_mem AI) M)
  rw [mul_one] at h
  convert h using 1
  simp only [map_add, map_mul, map_pow]
  ring

/- English proof (translation)
Establish `hD : ∀ j, ∃ D : Ainf l, j < M → Lifts AI K D (d j)`. Introduce `j`. Distinguish the cases in `hj : j < M`. Take `⟨D, hD⟩` from `GlobalTheory.T.exists_lifts_of_norm_le_one_alt l P AI hT K (d j) (hd j hj).1`. Conclude with `⟨D, fun _ => hD⟩`.

Conclude with `⟨0, fun h => absurd h hj⟩`. Use `choose D hD using hD`. Establish `h0 : D 0 - WittVector.frobenius (D 0) = ∑ i ∈ T, w i`. Establish `h1` using `(hD 0 hM).sub (hD 0 hM).frob`. Establish `h2` using `(hd 0 hM).2`.

Simplify using `only [pow_zero, one_mul, mul_one] at h2`. Rewrite `h1` using `[h2]`. Conclude with `h1.unique (lifts_sum T w c hw)`. Choose the witnesses or unpack the hypotheses as in `⟨q, hq⟩ : AI.μ ∣ ∑ i ∈ T, w i * (WittVector.teichmuller l AI.ε ^ m i - 1) := by`. Use `Finset.dvd_sum fun i _ => Dvd.dvd.mul_left ?_ _` and prove the remaining obligations.

Use `sub_dvd_pow_sub_pow (WittVector.teichmuller l AI.ε) 1 (m i)` as an intermediate fact. Rewrite `this` using `[one_pow]`. Then use the resulting hypothesis. Take `⟨hc1, hc2⟩` from `GlobalTheory.T.ainf_mu_frobenius_equation_solvable_and_tendsto l P AI`. Take `⟨y', hy'⟩` from `hc1 q`. Establish `hy : (D 0 + AI.μ * y') - WittVector.frobenius (D 0 + AI.μ * y') = ∑ i ∈ T, w i * WittVector.teichmuller l AI.ε ^ m i`.

Simplify using `only [mul_sub, mul_one, Finset.sum_sub_distrib] at hq`. Rewrite using `[map_add]`. Take the linear combination `h0 + hy' - hq`. Use `⟨D 0 + AI.μ * y', hy, ?_⟩` and prove the remaining obligations. Use `set y := D 0 + AI.μ * y' with hydef`.

Set `E : ℕ → P.R.BdR` to `fun n => io AI (Fr l n y) - ∑ j ∈ Finset.range M, (l : P.R.BdR) ^ (j * n) * oK P K ((frK P K ^ n) (d j)) * u P j`. Establish `hstep : ∀ n, E n - E (n + 1) ∈ FilB P (M : ℤ)`. Introduce `n`. Establish `h1 : io AI (Fr l n y) - io AI (Fr l (n + 1) y) = ∑ i ∈ T, oK P K ((frK P K ^ n) (c i)) * io AI (WittVector.teichmuller l AI.ε ^ (m i * l ^ n))`. Rewrite using `[Fr_succ', ← map_sub, ← map_sub, hy, map_sum, map_sum]`.

Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_mul, (lifts_Fr (hw i hi) n).io_eq, map_pow (Fr l n), Fr_teich, ← pow_mul, mul_comm (l ^ n), oK_apply]`. Establish `h2 : ∀ j ∈ Finset.range M, (l : P.R.BdR) ^ (j * n) * oK P K ((frK P K ^ n) (d j)) * u P j - (l : P.R.BdR) ^ (j * (n + 1)) * oK P K ((frK P K ^ (n + 1)) (d j)) * u P j = ∑ i ∈ T, oK P K ((frK P K ^ n) (c i)) * (((m i * l ^ n : ℕ) : P.R.BdR) ^ j * u P j)`. Introduce `j hj`. Establish `h3` using `congrArg (fun x => oK P K ((frK P K ^ n) x)) (hd j (Finset.mem_range.mp hj)).2`.

Simplify using `only [map_sub, map_mul, map_pow, map_natCast, map_sum] at h3`. Establish `h4 : (frK P K ^ (n + 1)) (d j) = (frK P K ^ n) (frK P K (d j))`. Rewrite using `[pow_succ]`. Both sides reduce to the same expression. Establish `h5 : ∑ i ∈ T, oK P K ((frK P K ^ n) (c i)) * (((m i * l ^ n : ℕ) : P.R.BdR) ^ j * u P j) = (l : P.R.BdR) ^ (j * n) * u P j * ∑ i ∈ T, oK P K ((frK P K ^ n) (c i)) * (m i : P.R.BdR) ^ j`.

Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h4, h5, ← h3]`.

Expand and normalize the polynomial expressions, which then agree. Establish `h6 : E n - E (n + 1) = ∑ i ∈ T, oK P K ((frK P K ^ n) (c i)) * (io AI (WittVector.teichmuller l AI.ε ^ (m i * l ^ n)) - ∑ j ∈ Finset.range M, ((m i * l ^ n : ℕ) : P.R.BdR) ^ j * u P j)`. Simplify using `only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]`. Rewrite using `[← h1, Finset.sum_comm, ← Finset.sum_congr rfl h2, Finset.sum_sub_distrib]`. Simplify using `only [E]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h6]`. Use `Submodule.sum_mem _ fun i hi => FilB_zero_mul ?_ (taylor0 hT _ _)` and prove the remaining obligations. Rewrite using `[oK_apply, ← (lifts_Fr (hw i hi) n).io_eq]`. Conclude with `io_mem AI _`.

Establish `htel : ∀ n, E 0 - E n ∈ FilB P (M : ℤ)`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`.

Use `add_mem ih (hstep n)` as an intermediate fact. Rewrite `this` using `[sub_add_sub_cancel]`. Then use the resulting hypothesis. Establish `hE0 : E 0 ∈ FilB P (M : ℤ)`. Use `GlobalTheory.T.mem_deRhamFiltration_of_forall_ainfLattice l P AI hT M _ fun r => ?_` and prove the remaining obligations. Take `⟨k₀, hk₀⟩` from `hc2 M r`.

Establish `hk : ∀ j, ∃ k : ℕ, (l : P.R.BdR) ^ k * u P j ∈ Lat AI M r` using `fun j => (GlobalTheory.T.bounded_and_eventually_sub_mem_Lat_alt l P AI hT _ (u_mem j) M r).1`. Use `choose k hk using hk`. Use `set n := k₀ + ∑ j ∈ Finset.range M, k j with hn`. Establish `hEn : E n ∈ Lat AI M r`. Take `⟨M', rfl⟩` from `Nat.exists_eq_add_of_le' hM`.

Establish `e0 : oK P K ((frK P K ^ n) (d 0)) = io AI (Fr l n (D 0))`. Rewrite using `[oK_apply, (lifts_Fr (hD 0 hM) n).io_eq]`. Establish `e1 : E n = io AI (Fr l n y') * io AI (Fr l n AI.μ) - ∑ j ∈ Finset.range M', (l : P.R.BdR) ^ ((j + 1) * n) * oK P K ((frK P K ^ n) (d (j + 1))) * u P (j + 1)`. Simplify using `only [E, hydef]`. Rewrite using `[Finset.sum_range_succ', e0]`.

Simplify using `only [map_add, map_mul, u, zero_mul, pow_zero, Nat.factorial_zero, Nat.cast_one, inv_one, map_one]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1]`. Use `sub_mem (io_mul_mem_Lat AI _ (span_mem_Lat ?_)) (sum_mem fun j hj => ?_)` and prove the remaining obligations. Use `hk₀ n (Nat.le_add_right _ _)` as an intermediate fact.

Rewrite `this` using `[← RingHom.coe_pow]`. Then use the resulting hypothesis. Establish `hj' : j + 1 < M' + 1` using `Nat.succ_lt_succ (Finset.mem_range.mp hj)`. Establish `hle : k (j + 1) ≤ (j + 1) * n`. Establish `a1 : k (j + 1) ≤ ∑ j ∈ Finset.range (M' + 1), k j` using `Finset.single_le_sum (f := k) (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hj')`. Establish `a2 : n ≤ (j + 1) * n` using `Nat.le_mul_of_pos_left _ (Nat.succ_pos j)`.

Use linear arithmetic over natural numbers and integers. Take `⟨e, he⟩` from `Nat.exists_eq_add_of_le hle`. Use `io_mul_mem_Lat AI (((l : ℕ) : Ainf l) ^ e * Fr l n (D (j + 1))) (hk (j + 1))` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Rewrite using `[he, oK_apply, ← (lifts_Fr (hD _ hj') n).io_eq, map_mul, map_pow, map_natCast]`.

Expand and normalize the polynomial expressions, which then agree. Use `add_mem (FilB_le_Lat AI (n := r) (htel n)) hEn` as an intermediate fact. Rewrite `this` using `[sub_add_cancel]`. Then use the resulting hypothesis. Use `hE0 using 1` and compare the differences between its conclusion and the goal. Simplify using `only [E, Fr, pow_zero, mul_zero, one_mul]`.

Use `congr 1`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[u, oK_apply, AlgHom.one_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem tail (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (hT : LocTied l P AI)
    (K : FinExt l) (ι : Type) (T : Finset ι) (w : ι → Ainf l) (c : ι → ↥(K0 K)) (m : ι → ℕ) (M : ℕ)
    (d : ℕ → ↥(K0 K)) (hM : 1 ≤ M) (hw : ∀ i ∈ T, Lifts AI K (w i) (c i))
    (hd : ∀ j < M, ‖(d j : Om l)‖ ≤ 1 ∧
      d j - (l : ↥(K0 K)) ^ j * frK P K (d j) = ∑ i ∈ T, c i * (m i : ↥(K0 K)) ^ j) :
    ∃ y : Ainf l, y - WittVector.frobenius y =
        ∑ i ∈ T, w i * WittVector.teichmuller l AI.ε ^ m i ∧
      io AI y - ∑ j ∈ Finset.range M,
        qB P ((j.factorial : ℚ_[l])⁻¹) * oB P (d j : Om l) * tD P ^ j ∈ FilB P (M : ℤ) := by
  have hD : ∀ j, ∃ D : Ainf l, j < M → Lifts AI K D (d j) := by
    intro j
    by_cases hj : j < M
    · obtain ⟨D, hD⟩ := GlobalTheory.T.exists_lifts_of_norm_le_one_alt l P AI hT K (d j) (hd j hj).1
      exact ⟨D, fun _ => hD⟩
    · exact ⟨0, fun h => absurd h hj⟩
  choose D hD using hD
  have h0 : D 0 - WittVector.frobenius (D 0) = ∑ i ∈ T, w i := by
    have h1 := (hD 0 hM).sub (hD 0 hM).frob
    have h2 := (hd 0 hM).2
    simp only [pow_zero, one_mul, mul_one] at h2
    rw [h2] at h1
    exact h1.unique (lifts_sum T w c hw)
  obtain ⟨q, hq⟩ : AI.μ ∣ ∑ i ∈ T, w i * (WittVector.teichmuller l AI.ε ^ m i - 1) := by
    refine Finset.dvd_sum fun i _ => Dvd.dvd.mul_left ?_ _
    have := sub_dvd_pow_sub_pow (WittVector.teichmuller l AI.ε) 1 (m i)
    rwa [one_pow] at this
  obtain ⟨hc1, hc2⟩ := GlobalTheory.T.ainf_mu_frobenius_equation_solvable_and_tendsto l P AI
  obtain ⟨y', hy'⟩ := hc1 q
  have hy : (D 0 + AI.μ * y') - WittVector.frobenius (D 0 + AI.μ * y') =
      ∑ i ∈ T, w i * WittVector.teichmuller l AI.ε ^ m i := by
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib] at hq
    rw [map_add]
    linear_combination h0 + hy' - hq
  refine ⟨D 0 + AI.μ * y', hy, ?_⟩
  set y := D 0 + AI.μ * y' with hydef
  let E : ℕ → P.R.BdR := fun n => io AI (Fr l n y) -
    ∑ j ∈ Finset.range M, (l : P.R.BdR) ^ (j * n) * oK P K ((frK P K ^ n) (d j)) * u P j
  have hstep : ∀ n, E n - E (n + 1) ∈ FilB P (M : ℤ) := by
    intro n
    have h1 : io AI (Fr l n y) - io AI (Fr l (n + 1) y) =
        ∑ i ∈ T, oK P K ((frK P K ^ n) (c i)) *
          io AI (WittVector.teichmuller l AI.ε ^ (m i * l ^ n)) := by
      rw [Fr_succ', ← map_sub, ← map_sub, hy, map_sum, map_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [map_mul, map_mul, (lifts_Fr (hw i hi) n).io_eq, map_pow (Fr l n), Fr_teich, ← pow_mul,
        mul_comm (l ^ n), oK_apply]
    have h2 : ∀ j ∈ Finset.range M,
        (l : P.R.BdR) ^ (j * n) * oK P K ((frK P K ^ n) (d j)) * u P j -
          (l : P.R.BdR) ^ (j * (n + 1)) * oK P K ((frK P K ^ (n + 1)) (d j)) * u P j =
        ∑ i ∈ T, oK P K ((frK P K ^ n) (c i)) * (((m i * l ^ n : ℕ) : P.R.BdR) ^ j * u P j) := by
      intro j hj
      have h3 := congrArg (fun x => oK P K ((frK P K ^ n) x)) (hd j (Finset.mem_range.mp hj)).2
      simp only [map_sub, map_mul, map_pow, map_natCast, map_sum] at h3
      have h4 : (frK P K ^ (n + 1)) (d j) = (frK P K ^ n) (frK P K (d j)) := by
        rw [pow_succ]; rfl
      have h5 : ∑ i ∈ T, oK P K ((frK P K ^ n) (c i)) * (((m i * l ^ n : ℕ) : P.R.BdR) ^ j * u P j)
          = (l : P.R.BdR) ^ (j * n) * u P j *
            ∑ i ∈ T, oK P K ((frK P K ^ n) (c i)) * (m i : P.R.BdR) ^ j := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        push_cast
        ring
      rw [h4, h5, ← h3]
      ring
    have h6 : E n - E (n + 1) = ∑ i ∈ T, oK P K ((frK P K ^ n) (c i)) *
        (io AI (WittVector.teichmuller l AI.ε ^ (m i * l ^ n)) -
          ∑ j ∈ Finset.range M, ((m i * l ^ n : ℕ) : P.R.BdR) ^ j * u P j) := by
      simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
      rw [← h1, Finset.sum_comm, ← Finset.sum_congr rfl h2, Finset.sum_sub_distrib]
      simp only [E]
      ring
    rw [h6]
    refine Submodule.sum_mem _ fun i hi => FilB_zero_mul ?_ (taylor0 hT _ _)
    rw [oK_apply, ← (lifts_Fr (hw i hi) n).io_eq]
    exact io_mem AI _
  have htel : ∀ n, E 0 - E n ∈ FilB P (M : ℤ) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have := add_mem ih (hstep n)
      rwa [sub_add_sub_cancel] at this
  have hE0 : E 0 ∈ FilB P (M : ℤ) := by
    refine GlobalTheory.T.mem_deRhamFiltration_of_forall_ainfLattice l P AI hT M _ fun r => ?_
    obtain ⟨k₀, hk₀⟩ := hc2 M r
    have hk : ∀ j, ∃ k : ℕ, (l : P.R.BdR) ^ k * u P j ∈ Lat AI M r := fun j =>
      (GlobalTheory.T.bounded_and_eventually_sub_mem_Lat_alt l P AI hT _ (u_mem j) M r).1
    choose k hk using hk
    set n := k₀ + ∑ j ∈ Finset.range M, k j with hn
    have hEn : E n ∈ Lat AI M r := by
      obtain ⟨M', rfl⟩ := Nat.exists_eq_add_of_le' hM
      have e0 : oK P K ((frK P K ^ n) (d 0)) = io AI (Fr l n (D 0)) := by
        rw [oK_apply, (lifts_Fr (hD 0 hM) n).io_eq]
      have e1 : E n = io AI (Fr l n y') * io AI (Fr l n AI.μ) - ∑ j ∈ Finset.range M',
          (l : P.R.BdR) ^ ((j + 1) * n) * oK P K ((frK P K ^ n) (d (j + 1))) * u P (j + 1) := by
        simp only [E, hydef]
        rw [Finset.sum_range_succ', e0]
        simp only [map_add, map_mul, u, zero_mul, pow_zero, Nat.factorial_zero, Nat.cast_one,
          inv_one, map_one]
        ring
      rw [e1]
      refine sub_mem (io_mul_mem_Lat AI _ (span_mem_Lat ?_)) (sum_mem fun j hj => ?_)
      · have := hk₀ n (Nat.le_add_right _ _)
        rwa [← RingHom.coe_pow] at this
      · have hj' : j + 1 < M' + 1 := Nat.succ_lt_succ (Finset.mem_range.mp hj)
        have hle : k (j + 1) ≤ (j + 1) * n := by
          have a1 : k (j + 1) ≤ ∑ j ∈ Finset.range (M' + 1), k j :=
            Finset.single_le_sum (f := k) (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hj')
          have a2 : n ≤ (j + 1) * n := Nat.le_mul_of_pos_left _ (Nat.succ_pos j)
          omega
        obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le hle
        have := io_mul_mem_Lat AI (((l : ℕ) : Ainf l) ^ e * Fr l n (D (j + 1))) (hk (j + 1))
        convert this using 1
        rw [he, oK_apply, ← (lifts_Fr (hD _ hj') n).io_eq, map_mul, map_pow, map_natCast]
        ring
    have := add_mem (FilB_le_Lat AI (n := r) (htel n)) hEn
    rwa [sub_add_cancel] at this
  convert hE0 using 1
  simp only [E, Fr, pow_zero, mul_zero, one_mul]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [u, oK_apply, AlgHom.one_apply]
  ring

end GlobalTheory.ExpImage.Tail
