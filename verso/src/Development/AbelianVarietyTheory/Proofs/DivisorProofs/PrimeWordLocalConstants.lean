import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FactorBounds
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeightedNormSquareRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OrthogonalNormSquareSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankEqTwoMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogNormConjVacuumEqRankProductMulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ErrorUnitExponentialEstimate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterSumLocalConstantTenthStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterSumLocalConstantEleventhStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterSumLocalConstantTwelfthStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeanLogMetricGeneratorEqMeanPeriodStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedFamilyStandardLatticesEqBaseVectorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelConstantExponentsFiniteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NumDatumNumbersEqHostOfCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FamIpAtNonneg
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColRows
open scoped ComplexOrder

namespace GlobalTheory.KernelHalf

open GlobalTheory.ColNorms GlobalTheory.ColNorms.NumMean

/- English proof (translation)
Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Establish `h2 : ∑ a, w a * (∑ b, w b * f b) < ∑ a, w a * f a`. Choose the witnesses or unpack the hypotheses as in `⟨a, ha⟩ : ∃ a, w a ≠ 0 := by`. Assume the negation of the conclusion as `h`.

Use `push_neg at h`. Simplify using `[h] at h1`. Use `Finset.sum_lt_sum (fun b _ => ?_) ⟨a, Finset.mem_univ _, ?_⟩` and prove the remaining obligations. Distinguish the cases in `hb : w b = 0`. Simplify using `[hb]`.

Conclude with `mul_le_mul_of_nonneg_left (hc b hb).le (h0 b)`. Conclude with `mul_lt_mul_of_pos_left (hc a ha) (lt_of_le_of_ne (h0 a) (Ne.symm ha))`. Rewrite `h2` using `[← Finset.sum_mul, h1, one_mul]`. Conclude with `lt_irrefl _ h2`.
-/
theorem exists_le_wtSum {α : Type} [Fintype α] (w f : α → ℝ) (h0 : ∀ a, 0 ≤ w a) (h1 : ∑ a, w a = 1) :
    ∃ a, w a ≠ 0 ∧ f a ≤ ∑ b, w b * f b := by
  by_contra hc
  push_neg at hc
  have h2 : ∑ a, w a * (∑ b, w b * f b) < ∑ a, w a * f a := by
    obtain ⟨a, ha⟩ : ∃ a, w a ≠ 0 := by
      by_contra h
      push_neg at h
      simp [h] at h1
    refine Finset.sum_lt_sum (fun b _ => ?_) ⟨a, Finset.mem_univ _, ?_⟩
    · by_cases hb : w b = 0
      · simp [hb]
      · exact mul_le_mul_of_nonneg_left (hc b hb).le (h0 b)
    · exact mul_lt_mul_of_pos_left (hc a ha) (lt_of_le_of_ne (h0 a) (Ne.symm ha))
  rw [← Finset.sum_mul, h1, one_mul] at h2
  exact lt_irrefl _ h2

/- English proof (translation)
Establish `h1 : ∑ a, w a * ∑ z, (p z - q z * o a z) = ∑ z, (p z - q z * ∑ a, w a * o a z)`. Simplify using `only [Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun z _ => ?_` and prove the remaining obligations. Establish `: ∑ a, w a * (p z - q z * o a z) = (∑ a, w a) * p z - ∑ a, q z * (w a * o a z)`.

Rewrite using `[Finset.sum_mul, ← Finset.sum_sub_distrib]`. Conclude with `Finset.sum_congr rfl fun a _ => by ring`. Rewrite using `[this, hw, one_mul]`. Simplify using `only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hw, one_mul, h1]`.
-/
theorem wt_affine {α Z : Type} [Fintype α] [Fintype Z] (w : α → ℝ) (hw : ∑ a, w a = 1) (p q : Z → ℝ) (o : α → Z → ℝ) (t : α → ℝ)
    (c₁ c₂ : ℝ) :
    ∑ a, w a * ((∑ z, (p z - q z * o a z)) + t a + c₁ + c₂) =
      (∑ z, (p z - q z * ∑ a, w a * o a z)) + (∑ a, w a * t a) + c₁ + c₂ := by
  have h1 : ∑ a, w a * ∑ z, (p z - q z * o a z) = ∑ z, (p z - q z * ∑ a, w a * o a z) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun z _ => ?_
    have : ∑ a, w a * (p z - q z * o a z) = (∑ a, w a) * p z - ∑ a, q z * (w a * o a z) := by
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun a _ => by ring
    rw [this, hw, one_mul]
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hw, one_mul, h1]

/- English proof (translation)
Unfold `kernelBound_sq`. Conclude with `wt_affine w hw _ _ lo lt _ _`.
-/
theorem kernelBound_wt (N : NumDatum) (δ : Code N) (T : ℕ) (CK : ℝ) (j : ℕ) {α : Type} [Fintype α] (w : α → ℝ) (hw : ∑ a, w a = 1)
    (lo : α → RPl N.R → ℝ) (lt : α → ℝ) (h h' n n' : ℕ) :
    ∑ a, w a * kernelBound_sq N δ T CK j (lo a) (lt a) h h' n n' =
      kernelBound_sq N δ T CK j (fun z => ∑ a, w a * lo a z) (∑ a, w a * lt a) h h' n n' := by
  unfold kernelBound_sq
  exact wt_affine w hw _ _ lo lt _ _

/- English proof (translation)
Rewrite using `[Finset.sum_comm, Finset.sum_div, Finset.sum_div]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_mul, mul_div_right_comm, h a]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem wt_mean {α Emb : Type} [Fintype α] [Fintype Emb] (wt : Emb → α → ℝ) (c d : ℝ) (h : ∀ a, (∑ v, wt v a) / c = 1 / d) (x : α → ℝ) :
    (∑ v, ∑ a, wt v a * x a) / c = (∑ a, x a) / d := by
  rw [Finset.sum_comm, Finset.sum_div, Finset.sum_div]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_mul, mul_div_right_comm, h a]
  ring

/- English proof (translation)
Establish `: Finset.univ.filter (fun l => (eJ l).1 = i) = {eJ.symm ⟨i, hi⟩}`. Use extensionality with `l`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Rewrite using `[Equiv.eq_symm_apply]`. Conclude with `Fin.ext h`. Introduce and unpack `rfl`. Simplify using the standard rewrite rules. Rewrite using `[this, Finset.sum_singleton]`.
-/
theorem sum_filter_eq {J : Type} [Fintype J] {m : ℕ} (eJ : J ≃ Fin m) (t : J → ℝ) {i : ℕ} (hi : i < m) :
    ∑ l ∈ Finset.univ.filter (fun l => (eJ l).1 = i), t l = t (eJ.symm ⟨i, hi⟩) := by
  have : Finset.univ.filter (fun l => (eJ l).1 = i) = {eJ.symm ⟨i, hi⟩} := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h
      rw [Equiv.eq_symm_apply]
      exact Fin.ext h
    · rintro rfl
      simp
  rw [this, Finset.sum_singleton]

/- English proof (translation)
Establish `hne : eJ.symm ⟨m - 2, by omega⟩ ≠ eJ.symm ⟨m - 1, by omega⟩`. Introduce `h`. Use `congrArg Fin.val (eJ.symm.injective h)` as an intermediate fact. Simplify using `only at this`. Use linear arithmetic over natural numbers and integers.

Establish `: Finset.univ.filter (fun l => m - 2 ≤ (eJ l).1) = {eJ.symm ⟨m - 2, by omega⟩, eJ.symm ⟨m - 1, by omega⟩}`. Use extensionality with `l`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Establish `h2` using `(eJ l).2`. Break down `(by omega : (eJ l).1 = m - 2 ∨ (eJ l).1 = m - 1) with h3 | h3` into its components or cases. Use `left`. Rewrite using `[Equiv.eq_symm_apply]`. Conclude with `Fin.ext h3`.

Use `right`. Rewrite using `[Equiv.eq_symm_apply]`. Conclude with `Fin.ext h3`. Apply the tactic sequence `rintro (rfl | rfl) <;> simp <;> omega`. Rewrite using `[this, Finset.sum_pair hne]`.
-/
theorem sum_filter_ge {J : Type} [Fintype J] {m : ℕ} (hm : 2 ≤ m) (eJ : J ≃ Fin m) (t : J → ℝ) :
    ∑ l ∈ Finset.univ.filter (fun l => m - 2 ≤ (eJ l).1), t l =
      t (eJ.symm ⟨m - 2, by omega⟩) + t (eJ.symm ⟨m - 1, by omega⟩) := by
  classical
  have hne : eJ.symm ⟨m - 2, by omega⟩ ≠ eJ.symm ⟨m - 1, by omega⟩ := by
    intro h
    have := congrArg Fin.val (eJ.symm.injective h)
    simp only at this
    omega
  have : Finset.univ.filter (fun l => m - 2 ≤ (eJ l).1) = {eJ.symm ⟨m - 2, by omega⟩, eJ.symm ⟨m - 1, by omega⟩} := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro h
      have h2 := (eJ l).2
      rcases (by omega : (eJ l).1 = m - 2 ∨ (eJ l).1 = m - 1) with h3 | h3
      · left
        rw [Equiv.eq_symm_apply]
        exact Fin.ext h3
      · right
        rw [Equiv.eq_symm_apply]
        exact Fin.ext h3
    · rintro (rfl | rfl) <;> simp <;> omega
  rw [this, Finset.sum_pair hne]

/- English proof (translation)
Use `⟨fun i hi v => ?_, fun v => ?_⟩` and prove the remaining obligations. Establish `hi' : i + 2 < m` using `by omega`. Establish `hi1 : i < m` using `by omega`. Rewrite using `[sum_filter_eq eJ (fun l => t l v) hi1, ht]`. Take `⟨a, ha, hle⟩` from `exists_le_wtSum (wt v) (fun a => lb a (i + 1)) (h0 v) (h1 v)`.

Establish `h2` using `hS a i hi'`. Rewrite `h2` using `[hup v a ha]`. Simplify using `only [Equiv.apply_symm_apply]`. Conclude with `h2.mono hle (hpos i v)`. Rewrite using `[hn, sum_filter_ge hm eJ (fun l => t l v), ht, ht]`.

Take `⟨a, ha, hle⟩` from `exists_le_wtSum (wt v) (fun a => lb a (m - 1) + lb a m) (h0 v) (h1 v)`. Establish `h2` using `hC a`. Rewrite `h2` using `[hup v a ha]`. Simplify using `only [Equiv.apply_symm_apply]`. Establish `e1 : m - 2 + 1 = m - 1` using `by omega`.

Establish `e2 : m - 1 + 1 = m` using `by omega`. Rewrite using `[e1, e2, ← Finset.sum_add_distrib]`. Simplify using `only [mul_add] at hle`. Introduce `φ`. Use `(h2 φ).trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 hle) (hpos _ v φ))` and prove the remaining obligations.
-/
theorem factorBounds_of_weights {K : Type} [Field K] [NumberField K] [StarRing K] (Q : KerChain K) {α J : Type} [Fintype α] [Fintype J]
    {m : ℕ} (hm : 2 ≤ m) (hn : Q.n = m - 2) (eJ : J ≃ Fin m) (pu : α → InfinitePlace K) (wt : InfinitePlace K → α → ℝ)
    (h0 : ∀ v a, 0 ≤ wt v a) (h1 : ∀ v, ∑ a, wt v a = 1) (hup : ∀ v a, wt v a ≠ 0 → pu a = v) (lb : α → ℕ → ℝ)
    (hpos : ∀ i v φ, 0 ≤ (famIpAt (Q.F i) (Q.hF i) v φ φ).re)
    (hS : ∀ a i, i + 2 < m → StepBound_sq Q i (pu a) (lb a (i + 1)))
    (hC : ∀ a, CplBound_sq Q (pu a) (lb a (m - 1) + lb a m))
    (t : J → InfinitePlace K → ℝ) (ht : ∀ l v, t l v = ∑ a, wt v a * lb a ((eJ l).1 + 1)) :
    FactorBounds Q (fun l => (eJ l).1) t := by
  refine ⟨fun i hi v => ?_, fun v => ?_⟩
  · have hi' : i + 2 < m := by omega
    have hi1 : i < m := by omega
    rw [sum_filter_eq eJ (fun l => t l v) hi1, ht]
    obtain ⟨a, ha, hle⟩ := exists_le_wtSum (wt v) (fun a => lb a (i + 1)) (h0 v) (h1 v)
    have h2 := hS a i hi'
    rw [hup v a ha] at h2
    simp only [Equiv.apply_symm_apply]
    exact h2.mono hle (hpos i v)
  · rw [hn, sum_filter_ge hm eJ (fun l => t l v), ht, ht]
    obtain ⟨a, ha, hle⟩ := exists_le_wtSum (wt v) (fun a => lb a (m - 1) + lb a m) (h0 v) (h1 v)
    have h2 := hC a
    rw [hup v a ha] at h2
    simp only [Equiv.apply_symm_apply]
    have e1 : m - 2 + 1 = m - 1 := by omega
    have e2 : m - 1 + 1 = m := by omega
    rw [e1, e2, ← Finset.sum_add_distrib]
    simp only [mul_add] at hle
    intro φ
    refine (h2 φ).trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 hle) (hpos _ v φ))

/- English proof (translation)
Establish `: 1 ≤ R.f`. Unfold `Ranks.f Ranks.n`. Use `And.intro (Nat.one_le_two_pow (n := R.e)) (show 0 < R.ord by positivity)` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Conclude with `this` after adjusting the coercions.
-/
theorem one_le_f (R : Ranks) : (1 : ℝ) ≤ R.f := by
  have : 1 ≤ R.f := by
    unfold Ranks.f Ranks.n
    have := And.intro (Nat.one_le_two_pow (n := R.e)) (show 0 < R.ord by positivity)
    omega
  exact_mod_cast this

/- English proof (translation)
Establish `: 1 ≤ N.Nm`. Unfold `NumDatum.Nm Ranks.N`. Use `N.R.m_add_three_le_k` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Conclude with `this` after adjusting the coercions.
-/
theorem one_le_Nm (N : NumDatum) : (1 : ℝ) ≤ N.Nm := by
  have : 1 ≤ N.Nm := by
    unfold NumDatum.Nm Ranks.N
    have := N.R.m_add_three_le_k
    omega
  exact_mod_cast this

/- English proof (translation)
Establish `hb` using `two_le_b N.sc`. Establish `hx` using `N.sc.one_lt_alt`. Establish `hrd` using `one_le_rd N`. Establish `h1 : N.sc.b ≤ N.sc.a`. Unfold `Scale.a`.

Conclude with `le_mul_of_one_le_left (by linarith) hx.le`. Establish `h2 : N.sc.a ≤ N.sc.a * N.rd` using `le_mul_of_one_le_right (by linarith) hrd`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem L_le_La (N : NumDatum) : N.sc.L ≤ N.La := by
  have hb := two_le_b N.sc
  have hx := N.sc.one_lt_alt
  have hrd := one_le_rd N
  have h1 : N.sc.b ≤ N.sc.a := by
    unfold Scale.a
    exact le_mul_of_one_le_left (by linarith) hx.le
  have h2 : N.sc.a ≤ N.sc.a * N.rd := le_mul_of_one_le_right (by linarith) hrd
  calc N.sc.L = Real.log (Real.exp N.sc.L) := (Real.log_exp _).symm
    _ ≤ Real.log (N.sc.a * N.rd) := Real.log_le_log (Real.exp_pos _) (h1.trans h2)
    _ = N.La := rfl

/- English proof (translation)
Take `⟨⟨hrd, -, -, hx4, -⟩, hg, hlT, hfN, hnu, -⟩` from `hS`. Establish `hA` using `N_le N (j := i) (by omega)`. Establish `hB` using `N_le N (j := i + 1) (by omega)`. Establish `hL` using `one_le_L N.sc`. Establish `hb` using `two_le_b N.sc`.

Establish `hx` using `N.sc.one_lt_alt`. Establish `hrd1` using `one_le_rd N`. Establish `hf` using `one_le_f N.R`. Establish `hNb : (N.Nm : ℝ) ≤ N.sc.b` using `le_trans (le_mul_of_one_le_left (by positivity) hf) hfN`. Establish `hAB : (N.R.N i : ℝ) * N.R.N (i + 1) ≤ (N.Nm : ℝ) ^ 2` using `by rw [sq]; gcongr`.

Establish `hgb : (N.R.f : ℝ) * ((N.R.N i : ℝ) * N.R.N (i + 1)) ≤ N.sc.b ^ 2`. Combine the equalities or inequalities in the displayed calculation. Establish `hrdb : N.rd ≤ N.sc.b` using `(Real.log_le_iff_le_exp (by linarith)).1 hrd`. Establish `hxb : 4 * N.sc.x ≤ N.sc.b` using `(Real.log_le_iff_le_exp (by linarith)).1 hx4`. Establish `hv0 : 0 ≤ N.v` using `by unfold NumDatum.v; linarith`.

Establish `hvb : N.v ≤ N.sc.b / 2` using `by unfold NumDatum.v; linarith`. Establish `hb3 : 8 ≤ N.sc.b ^ 3`. Combine the equalities or inequalities in the displayed calculation. Establish `hb5 : 32 ≤ N.sc.b ^ 5`. Combine the equalities or inequalities in the displayed calculation.

Use `log_le_mul N.sc (y := 8 + 32 * ((N.R.f : ℝ) * ((N.R.N i : ℝ) * N.R.N (i + 1))) * N.v) (by positivity) 8 (by` as an intermediate fact. Combine the equalities or inequalities in the displayed calculation. Simplify using `using this`.
-/
theorem log_eight_le (N : NumDatum) (δ : Code N) (T : ℕ) (hS : SizeRows N δ T) {i : ℕ} (hi : i < N.R.m) :
    Real.log (8 + 32 * ((N.R.f : ℝ) * ((N.R.N i : ℝ) * N.R.N (i + 1))) * N.v) ≤ 8 * N.sc.L := by
  obtain ⟨⟨hrd, -, -, hx4, -⟩, hg, hlT, hfN, hnu, -⟩ := hS
  have hA := N_le N (j := i) (by omega)
  have hB := N_le N (j := i + 1) (by omega)
  have hL := one_le_L N.sc
  have hb := two_le_b N.sc
  have hx := N.sc.one_lt_alt
  have hrd1 := one_le_rd N
  have hf := one_le_f N.R
  have hNb : (N.Nm : ℝ) ≤ N.sc.b := le_trans (le_mul_of_one_le_left (by positivity) hf) hfN
  have hAB : (N.R.N i : ℝ) * N.R.N (i + 1) ≤ (N.Nm : ℝ) ^ 2 := by rw [sq]; gcongr
  have hgb : (N.R.f : ℝ) * ((N.R.N i : ℝ) * N.R.N (i + 1)) ≤ N.sc.b ^ 2 := by
    calc _ ≤ (N.R.f : ℝ) * (N.Nm : ℝ) ^ 2 := by gcongr
      _ = ((N.R.f : ℝ) * N.Nm) * N.Nm := by ring
      _ ≤ N.sc.b * N.sc.b := by gcongr
      _ = _ := by ring
  have hrdb : N.rd ≤ N.sc.b := (Real.log_le_iff_le_exp (by linarith)).1 hrd
  have hxb : 4 * N.sc.x ≤ N.sc.b := (Real.log_le_iff_le_exp (by linarith)).1 hx4
  have hv0 : 0 ≤ N.v := by unfold NumDatum.v; linarith
  have hvb : N.v ≤ N.sc.b / 2 := by unfold NumDatum.v; linarith
  have hb3 : 8 ≤ N.sc.b ^ 3 := by
    calc (8 : ℝ) = 2 ^ 3 := by norm_num
      _ ≤ _ := by gcongr
  have hb5 : 32 ≤ N.sc.b ^ 5 := by
    calc (32 : ℝ) = 2 ^ 5 := by norm_num
      _ ≤ _ := by gcongr
  have := log_le_mul N.sc (y := 8 + 32 * ((N.R.f : ℝ) * ((N.R.N i : ℝ) * N.R.N (i + 1))) * N.v) (by positivity) 8 (by
    calc _ ≤ 8 + 32 * N.sc.b ^ 2 * (N.sc.b / 2) := by gcongr
      _ = 8 + 16 * N.sc.b ^ 3 := by ring
      _ ≤ 32 * N.sc.b ^ 3 := by linarith
      _ ≤ N.sc.b ^ 5 * N.sc.b ^ 3 := by gcongr
      _ = _ := by ring)
  simpa using this

/- English proof (translation)
Take `⟨⟨hrd, -, -, hx4, -⟩, hg, hlT, hfN, hnu, -⟩` from `hS`. Establish `hj : i + 1 ∈ N.lifts` using `Finset.mem_Icc.2 ⟨by omega, by omega⟩`. Establish `hA` using `N_le N (j := i) (by omega)`. Establish `hb` using `two_le_b N.sc`. Establish `hx` using `N.sc.one_lt_alt`.

Establish `hf` using `one_le_f N.R`. Establish `hNb : (N.Nm : ℝ) ≤ N.sc.b` using `le_trans (le_mul_of_one_le_left (by positivity) hf) hfN`. Establish `hxb : 4 * N.sc.x ≤ N.sc.b` using `(Real.log_le_iff_le_exp (by linarith)).1 hx4`. Establish `hb2 : 4 ≤ N.sc.b ^ 2`. Combine the equalities or inequalities in the displayed calculation.

Establish `hb3 : 8 ≤ N.sc.b ^ 3`. Combine the equalities or inequalities in the displayed calculation. Establish `h0 : (0 : ℝ) ≤ ((N.nuAbs δ (i + 1) z : ℚ) : ℝ)`. Establish `: 0 ≤ N.nuAbs δ (i + 1) z` using `Finset.sum_nonneg fun k hk => (hnu (i + 1) hj z k (Finset.mem_range.1 hk)).1`. Conclude with `this` after adjusting the coercions.

Establish `h1 : ((N.nuAbs δ (i + 1) z : ℚ) : ℝ) ≤ (N.R.N i : ℝ) * (3 * N.sc.a)`. Unfold `NumDatum.nuAbs`. Use `push_cast`. Use `Finset.sum_le_card_nsmul (Finset.range (N.R.N i)) (fun k => ((N.nu δ (i + 1) z k : ℚ) : ℝ)) (3 * N.sc.a) fun k hk => (hnu (i + 1) hj z k (Finset.mem_range.1 hk)).2` as an intermediate fact. Simplify using `using this`.

Establish `h2 : ((N.nuAbs δ (i + 1) z : ℚ) : ℝ) ≤ N.sc.b ^ 3`. Combine the equalities or inequalities in the displayed calculation. Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion. Use `_ = _ := by ring`.

Use `log_le_mul N.sc (y := 2 * ((N.nuAbs δ (i + 1) z : ℚ) : ℝ) + 2) (by positivity) 5 (by` as an intermediate fact. Combine the equalities or inequalities in the displayed calculation. Simplify using `using this`.
-/
theorem log_nu_le (N : NumDatum) (δ : Code N) (T : ℕ) (hS : SizeRows N δ T) {i : ℕ} (hi : i < N.R.m) (z : RPl N.R) :
    Real.log (2 * ((N.nuAbs δ (i + 1) z : ℚ) : ℝ) + 2) ≤ 5 * N.sc.L := by
  obtain ⟨⟨hrd, -, -, hx4, -⟩, hg, hlT, hfN, hnu, -⟩ := hS
  have hj : i + 1 ∈ N.lifts := Finset.mem_Icc.2 ⟨by omega, by omega⟩
  have hA := N_le N (j := i) (by omega)
  have hb := two_le_b N.sc
  have hx := N.sc.one_lt_alt
  have hf := one_le_f N.R
  have hNb : (N.Nm : ℝ) ≤ N.sc.b := le_trans (le_mul_of_one_le_left (by positivity) hf) hfN
  have hxb : 4 * N.sc.x ≤ N.sc.b := (Real.log_le_iff_le_exp (by linarith)).1 hx4
  have hb2 : 4 ≤ N.sc.b ^ 2 := by
    calc (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ _ := by gcongr
  have hb3 : 8 ≤ N.sc.b ^ 3 := by
    calc (8 : ℝ) = 2 ^ 3 := by norm_num
      _ ≤ _ := by gcongr
  have h0 : (0 : ℝ) ≤ ((N.nuAbs δ (i + 1) z : ℚ) : ℝ) := by
    have : 0 ≤ N.nuAbs δ (i + 1) z := Finset.sum_nonneg fun k hk => (hnu (i + 1) hj z k (Finset.mem_range.1 hk)).1
    exact_mod_cast this
  have h1 : ((N.nuAbs δ (i + 1) z : ℚ) : ℝ) ≤ (N.R.N i : ℝ) * (3 * N.sc.a) := by
    unfold NumDatum.nuAbs
    push_cast
    have := Finset.sum_le_card_nsmul (Finset.range (N.R.N i)) (fun k => ((N.nu δ (i + 1) z k : ℚ) : ℝ)) (3 * N.sc.a)
      fun k hk => (hnu (i + 1) hj z k (Finset.mem_range.1 hk)).2
    simpa using this
  have h2 : ((N.nuAbs δ (i + 1) z : ℚ) : ℝ) ≤ N.sc.b ^ 3 := by
    calc _ ≤ (N.R.N i : ℝ) * (3 * N.sc.a) := h1
      _ = (N.R.N i : ℝ) * (3 * N.sc.x) * N.sc.b := by unfold Scale.a; ring
      _ ≤ N.sc.b * N.sc.b * N.sc.b := by
          gcongr
          · linarith
          · linarith
      _ = _ := by ring
  have := log_le_mul N.sc (y := 2 * ((N.nuAbs δ (i + 1) z : ℚ) : ℝ) + 2) (by positivity) 5 (by
    calc _ ≤ 4 * N.sc.b ^ 3 := by linarith
      _ ≤ N.sc.b ^ 2 * N.sc.b ^ 3 := by gcongr
      _ = _ := by ring)
  simpa using this

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Take `⟨nL, na, nb, nLa, nm, nf, nk, nNn, nS, nη, nb', nlo⟩` from `hR.nums`. Establish `hL` using `one_le_L N.sc`. Establish `hf` using `one_le_f N.R`. Establish `hN` using `one_le_Nm N`. Establish `hLL` using `L_le_La N`.

Establish `hg0 : (1 : ℝ) ≤ N.g 0` using `by exact_mod_cast (N.g_prime 0).one_lt.le`. Establish `hg1 : (1 : ℝ) ≤ N.g 1` using `by exact_mod_cast (N.g_prime 1).one_lt.le`. Establish `hT1 : (1 : ℝ) ≤ T` using `by exact_mod_cast (by omega : 1 ≤ T)`. Establish `hlg0 : 0 ≤ Real.log ((N.g 0 : ℝ) * N.g 1)` using `Real.log_nonneg (one_le_mul_of_one_le_of_one_le hg0 hg1)`. Establish `hlT0 : 0 ≤ Real.log (T : ℝ)` using `Real.log_nonneg hT1`.

Establish `hlog : Real.log ((N.g 0 : ℝ) * N.g 1 * T) = Real.log ((N.g 0 : ℝ) * N.g 1) + Real.log (T : ℝ)` using `Real.log_mul (by positivity) (by positivity)`. Establish `hU0 : 0 ≤ errUnit N T`. Unfold `errUnit`. Rewrite using `[hlog]`. Check the signs of the components of the expression.

Use `set C : ℝ := CK + 2 * E + 2 * Ct + 20 with hC`. Establish `hC0 : 0 ≤ C` using `by positivity`. Establish `hX0 : 0 ≤ E * errUnit N T` using `mul_nonneg hE hU0`. Unfold `KerSide`. Use `⟨fun l => (N.R.N (eJ l).1 : ℝ) * (N.R.N ((eJ l).1 + 1) : ℝ), fun l _ => CK * N.R.f * (N.R.m : ℝ) ^ 2 * (N.Nm : ℝ) ^ 2 * Real.log ((N.g 0 : ℝ) * N.g 1 * T) + (1 / 2) * Real.log ((h (eJ l).1 : ℝ) * h ((eJ l).1 + 1)) + (1 / 2) * Real.log ((n (eJ l).1 : ℝ) * n ((eJ l).1 + 1)), fun z …` and prove the remaining obligations.

Introduce `τ`. Rewrite using `[wt_mean wt _ d hmean (fun a => lo a τ), hlo, nlo]`. Introduce `l _`. Establish `hl` using `(eJ l).2`. Establish `a1` using `log_mul_le hX0 (hh (eJ l).1 hl.le) (hh ((eJ l).1 + 1) hl)`.

Establish `a2` using `log_mul_le hX0 (hn (eJ l).1 hl.le) (hn ((eJ l).1 + 1) hl)`. Rewrite using `[nf, nm, nNn, hR.logT]`. Establish `e : CK * N.R.f * (N.R.m : ℝ) ^ 2 * (N.Nm : ℝ) ^ 2 * Real.log ((N.g 0 : ℝ) * N.g 1 * T) = CK * errUnit N T`. Unfold `errUnit`. Expand and normalize the polynomial expressions, which then agree.

Establish `e2 : C * N.R.f * (N.R.m : ℝ) ^ 2 * (N.Nm : ℝ) ^ 2 * (Real.log ((N.g 0 : ℝ) * N.g 1) + Real.log (T : ℝ)) = C * errUnit N T`. Unfold `errUnit`. Rewrite using `[hlog]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, e2]`.

Establish `h3 : (CK + 2 * E) * errUnit N T ≤ C * errUnit N T`. Use `mul_le_mul_of_nonneg_right ?_ hU0` and prove the remaining obligations. Rewrite using `[hC]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h4 : 0 ≤ C * N.R.f * (N.Nm : ℝ) ^ 2 * Real.log ((N.g 0 : ℝ) * N.g 1)` using `by positivity`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `e : (∑ v, (∑ a, wt v a * lt a) / (N.R.f : ℝ)) / (Fintype.card Emb : ℝ) = ((∑ a, lt a) / d) / N.R.f`. Rewrite using `[← Finset.sum_div, div_right_comm, wt_mean wt _ d hmean lt]`. Rewrite using `[e, nL]`. Establish `hf0 : (0 : ℝ) < N.R.f` using `by linarith`.

Rewrite using `[div_le_iff₀ hf0]`. Use `hlt.trans ?_` and prove the remaining obligations. Establish `: 2 * Ct ≤ C` using `by rw [hC]; linarith`. Establish `h5 : 2 * Ct * N.sc.L ≤ C * N.sc.L` using `mul_le_mul_of_nonneg_right this (by linarith)`. Establish `h7` using `mul_le_mul_of_nonneg_right h5 hf0.le`.

Combine the equalities or inequalities in the displayed calculation. Introduce `_`. Rewrite using `[nf, nNn, nL, hR.logT]`. Establish `: 0 ≤ N.sc.L` using `by linarith`. Check the signs of the components of the expression.

Introduce `_`. Rewrite using `[nf, nNn, nL, hR.logT]`. Establish `: 0 ≤ N.sc.L` using `by linarith`. Check the signs of the components of the expression. Introduce `l`.

Establish `hl` using `(eJ l).2`. Rewrite using `[nNn, sq]`. Use `⟨by positivity, ?_⟩` and prove the remaining obligations. Conclude with `mul_le_mul (N_le N hl.le) (N_le N hl) (by positivity) (by positivity)`. Introduce `l`.

Rewrite using `[card_RPl, nLa]`. Use `(log_eight_le N δ T hS (eJ l).2).trans ?_` and prove the remaining obligations. Establish `h6 : 8 ≤ C` using `by rw [hC]; linarith`. Combine the equalities or inequalities in the displayed calculation. Introduce `l τ`.

Rewrite using `[hR.sumNu, nLa]`. Use `(log_nu_le N δ T hS (eJ l).2 τ).trans ?_` and prove the remaining obligations. Establish `h6 : 5 ≤ C` using `by rw [hC]; linarith`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[nL, Real.log_mul (by positivity) (by positivity)]`.

Establish `b0` using `(hS.2.1 0).2`. Establish `b1` using `(hS.2.1 1).2`. Establish `h6 : 20 ≤ C` using `by rw [hC]; linarith`. Combine the equalities or inequalities in the displayed calculation. Use `hP _ fun l v => ?_` and prove the remaining obligations.

Rewrite using `[kernelBound_wt N δ T CK _ (wt v) (h1 v) lo _]`. Establish `hf0 : (N.R.f : ℝ) ≠ 0` using `by linarith`. Establish `e : (N.R.f : ℝ) * ((N.R.N (eJ l).1 : ℝ) * (N.R.N ((eJ l).1 + 1) : ℝ)) * ((∑ a, wt v a * lt a) / N.R.f) = ∑ a, wt v a * ((N.R.N (eJ l).1 : ℝ) * (N.R.N ((eJ l).1 + 1) : ℝ) * lt a)`. Simplify using `only [Finset.mul_sum, Finset.sum_div]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations.

Clear the denominators using the available nonvanishing facts. Unfold `Formalism.DimensionVariation.liftedMapLogSize kernelBound_sq`. Simplify using `only [hR.phNu, hR.sumNu, card_RPl, Nat.add_sub_cancel]`. Rewrite using `[e]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem kerSide_of_means {J Emb α : Type} [Fintype J] [Fintype Emb] [Fintype α] (N : NumDatum) (δ : Code N) (T : ℕ) (hT : 2 ≤ T)
    (hS : SizeRows N δ T) (eJ : J ≃ Fin N.R.m) (R : RecNums J (RPl N.R)) (hR : Reads N eJ δ T R)
    (CK E Ct d : ℝ) (hCK : 0 ≤ CK) (hE : 0 ≤ E) (hCt : 0 ≤ Ct)
    (wt : Emb → α → ℝ) (h1 : ∀ v, ∑ a, wt v a = 1) (hmean : ∀ a, (∑ v, wt v a) / (Fintype.card Emb : ℝ) = 1 / d)
    (lo : α → RPl N.R → ℝ) (lt : α → ℝ) (hlo : ∀ z, (∑ a, lo a z) / d = N.logOm)
    (hlt : (∑ a, lt a) / d ≤ Ct * N.R.f * (2 * N.sc.L))
    (h n : ℕ → ℕ) (hh : ∀ l ≤ N.R.m, (h l : ℝ) ≤ Real.exp (E * errUnit N T))
    (hn : ∀ l ≤ N.R.m, (n l : ℝ) ≤ Real.exp (E * errUnit N T))
    (P : (J → Emb → ℝ) → Prop)
    (hP : ∀ t : J → Emb → ℝ, (∀ l v, t l v = ∑ a, wt v a * kernelBound_sq N δ T CK ((eJ l).1 + 1) (lo a)
        ((N.R.N (eJ l).1 : ℝ) * (N.R.N ((eJ l).1 + 1) : ℝ) * lt a) (h (eJ l).1) (h ((eJ l).1 + 1)) (n (eJ l).1) (n ((eJ l).1 + 1))) → P t) :
    KerSide R Emb (CK + 2 * E + 2 * Ct + 20) P := by
  obtain ⟨nL, na, nb, nLa, nm, nf, nk, nNn, nS, nη, nb', nlo⟩ := hR.nums
  have hL := one_le_L N.sc
  have hf := one_le_f N.R
  have hN := one_le_Nm N
  have hLL := L_le_La N
  have hg0 : (1 : ℝ) ≤ N.g 0 := by exact_mod_cast (N.g_prime 0).one_lt.le
  have hg1 : (1 : ℝ) ≤ N.g 1 := by exact_mod_cast (N.g_prime 1).one_lt.le
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast (by omega : 1 ≤ T)
  have hlg0 : 0 ≤ Real.log ((N.g 0 : ℝ) * N.g 1) := Real.log_nonneg (one_le_mul_of_one_le_of_one_le hg0 hg1)
  have hlT0 : 0 ≤ Real.log (T : ℝ) := Real.log_nonneg hT1
  have hlog : Real.log ((N.g 0 : ℝ) * N.g 1 * T) = Real.log ((N.g 0 : ℝ) * N.g 1) + Real.log (T : ℝ) :=
    Real.log_mul (by positivity) (by positivity)
  have hU0 : 0 ≤ errUnit N T := by
    unfold errUnit
    rw [hlog]
    positivity
  set C : ℝ := CK + 2 * E + 2 * Ct + 20 with hC
  have hC0 : 0 ≤ C := by positivity
  have hX0 : 0 ≤ E * errUnit N T := mul_nonneg hE hU0
  unfold KerSide
  refine ⟨fun l => (N.R.N (eJ l).1 : ℝ) * (N.R.N ((eJ l).1 + 1) : ℝ),
    fun l _ => CK * N.R.f * (N.R.m : ℝ) ^ 2 * (N.Nm : ℝ) ^ 2 * Real.log ((N.g 0 : ℝ) * N.g 1 * T) +
      (1 / 2) * Real.log ((h (eJ l).1 : ℝ) * h ((eJ l).1 + 1)) + (1 / 2) * Real.log ((n (eJ l).1 : ℝ) * n ((eJ l).1 + 1)),
    fun z v => ∑ a, wt v a * lo a z, fun v => (∑ a, wt v a * lt a) / N.R.f, fun _ => 0, fun _ => 0, N.v,
    Real.log ((N.g 0 : ℝ) * N.g 1), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro τ
    rw [wt_mean wt _ d hmean (fun a => lo a τ), hlo, nlo]
  · intro l _
    have hl := (eJ l).2
    have a1 := log_mul_le hX0 (hh (eJ l).1 hl.le) (hh ((eJ l).1 + 1) hl)
    have a2 := log_mul_le hX0 (hn (eJ l).1 hl.le) (hn ((eJ l).1 + 1) hl)
    rw [nf, nm, nNn, hR.logT]
    have e : CK * N.R.f * (N.R.m : ℝ) ^ 2 * (N.Nm : ℝ) ^ 2 * Real.log ((N.g 0 : ℝ) * N.g 1 * T) = CK * errUnit N T := by
      unfold errUnit; ring
    have e2 : C * N.R.f * (N.R.m : ℝ) ^ 2 * (N.Nm : ℝ) ^ 2 * (Real.log ((N.g 0 : ℝ) * N.g 1) + Real.log (T : ℝ)) = C * errUnit N T := by
      unfold errUnit; rw [hlog]; ring
    rw [e, e2]
    have h3 : (CK + 2 * E) * errUnit N T ≤ C * errUnit N T := by
      refine mul_le_mul_of_nonneg_right ?_ hU0
      rw [hC]
      linarith
    have h4 : 0 ≤ C * N.R.f * (N.Nm : ℝ) ^ 2 * Real.log ((N.g 0 : ℝ) * N.g 1) := by positivity
    linarith
  · have e : (∑ v, (∑ a, wt v a * lt a) / (N.R.f : ℝ)) / (Fintype.card Emb : ℝ) = ((∑ a, lt a) / d) / N.R.f := by
      rw [← Finset.sum_div, div_right_comm, wt_mean wt _ d hmean lt]
    rw [e, nL]
    have hf0 : (0 : ℝ) < N.R.f := by linarith
    rw [div_le_iff₀ hf0]
    refine hlt.trans ?_
    have : 2 * Ct ≤ C := by rw [hC]; linarith
    have h5 : 2 * Ct * N.sc.L ≤ C * N.sc.L := mul_le_mul_of_nonneg_right this (by linarith)
    have h7 := mul_le_mul_of_nonneg_right h5 hf0.le
    calc _ = 2 * Ct * N.sc.L * (N.R.f : ℝ) := by ring
      _ ≤ _ := h7
  · intro _
    rw [nf, nNn, nL, hR.logT]
    have : 0 ≤ N.sc.L := by linarith
    positivity
  · intro _
    rw [nf, nNn, nL, hR.logT]
    have : 0 ≤ N.sc.L := by linarith
    positivity
  · intro l
    have hl := (eJ l).2
    rw [nNn, sq]
    refine ⟨by positivity, ?_⟩
    exact mul_le_mul (N_le N hl.le) (N_le N hl) (by positivity) (by positivity)
  · intro l
    rw [card_RPl, nLa]
    refine (log_eight_le N δ T hS (eJ l).2).trans ?_
    have h6 : 8 ≤ C := by rw [hC]; linarith
    calc 8 * N.sc.L ≤ 8 * N.La := by linarith
      _ ≤ C * N.La := mul_le_mul_of_nonneg_right h6 (by linarith)
  · intro l τ
    rw [hR.sumNu, nLa]
    refine (log_nu_le N δ T hS (eJ l).2 τ).trans ?_
    have h6 : 5 ≤ C := by rw [hC]; linarith
    calc 5 * N.sc.L ≤ 5 * N.La := by linarith
      _ ≤ C * N.La := mul_le_mul_of_nonneg_right h6 (by linarith)
  · rw [nL, Real.log_mul (by positivity) (by positivity)]
    have b0 := (hS.2.1 0).2
    have b1 := (hS.2.1 1).2
    have h6 : 20 ≤ C := by rw [hC]; linarith
    calc _ ≤ 20 * N.sc.L := by linarith
      _ ≤ C * N.sc.L := mul_le_mul_of_nonneg_right h6 (by linarith)
  · refine hP _ fun l v => ?_
    rw [kernelBound_wt N δ T CK _ (wt v) (h1 v) lo _]
    have hf0 : (N.R.f : ℝ) ≠ 0 := by linarith
    have e : (N.R.f : ℝ) * ((N.R.N (eJ l).1 : ℝ) * (N.R.N ((eJ l).1 + 1) : ℝ)) * ((∑ a, wt v a * lt a) / N.R.f) =
        ∑ a, wt v a * ((N.R.N (eJ l).1 : ℝ) * (N.R.N ((eJ l).1 + 1) : ℝ) * lt a) := by
      simp only [Finset.mul_sum, Finset.sum_div]
      refine Finset.sum_congr rfl fun a _ => ?_
      field_simp
    unfold Formalism.DimensionVariation.liftedMapLogSize kernelBound_sq
    simp only [hR.phNu, hR.sumNu, card_RPl, Nat.add_sub_cancel]
    rw [e]
    ring

set_option maxHeartbeats 2000000 in

/- English proof (translation)
Introduce `hCN hP hV hN`. Take `⟨CK, C', hCK, -, hcol⟩` from `hCN`. Take `⟨Cc, hCc, hcl⟩` from `GlobalTheory.T.character_sum_local_constant_tenth`. Take `⟨Ci, hCi, hidx⟩` from `GlobalTheory.T.character_sum_local_constant_eleventh`. Take `⟨Cy, hCy, hyb⟩` from `GlobalTheory.T.character_sum_local_constant_twelfth`.

Take `⟨Ct, hth⟩` from `hN`. Use `⟨CK + 2 * (Cc + Ci + Cy) + 2 * max Ct 0 + 20, by positivity, ?_⟩` and prove the remaining obligations. Introduce `D N X _ s Pr W Ch G sel Sg mu cst I dl B χ cD pl u δ b hY hK hF hE J _ eJ R h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 hR`. Establish `H : Hyp N s W Ch G sel mu cst I dl χ cD pl u δ` using `⟨h1, h2, h3, h4, h5, h6, h7, h9, h10⟩`. Take `⟨trd, tv, tL, tOm, tf, -, tE, -, tcc⟩` from `GlobalTheory.T.numDatum_numbers_eq_host_of_compatible D N X s Pr h1`.

Take `⟨-, -, -, -, hpsi, hadm, hX, hs, -, hPr, -, -, hg, -⟩` from `id h1`. Establish `hcrv : StandardLatticesGL3.Crv D D.host.ccK dl` using `⟨tcc, h4.1⟩`. Establish `hYf` using `GlobalTheory.T.kernelConstant_exponents_finite D B.γ₀ B.kc`. Establish `hVe : B.VecP χ` using `hV D _ dl B χ hadm hpsi tcc h4.1 h4.2.1 hYf`. Establish `hev : ∀ l, Even (N.R.N l)` using `fun l => by`.

Unfold `Ranks.N`. Conclude with `N.R.k_even.add ((N.R.t_odd.add_one).mul_left l)`. Establish `hm` using `N.R.two_le_m`. Establish `hU : 0 ≤ errUnit N (Pr.T u)`. Establish `h0 : (1 : ℝ) ≤ N.g 0` using `by exact_mod_cast (N.g_prime 0).one_lt.le`.

Establish `h1' : (1 : ℝ) ≤ N.g 1` using `by exact_mod_cast (N.g_prime 1).one_lt.le`. Establish `h2' : (1 : ℝ) ≤ Pr.T u` using `by exact_mod_cast (hPr.T_prime u).one_lt.le`. Establish `h3' : 0 ≤ Real.log ((N.g 0 : ℝ) * N.g 1 * Pr.T u)` using `Real.log_nonneg (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le h0 h1') h2')`. Unfold `errUnit`. Check the signs of the components of the expression.

Take `⟨hc1, -, hc3⟩` from `hcl D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H`. Establish `m1 : Real.exp (Cc * errUnit N (Pr.T u)) ≤ Real.exp ((Cc + Ci + Cy) * errUnit N (Pr.T u))` using `by gcongr; linarith`. Establish `m2 : Real.exp (Ci * errUnit N (Pr.T u)) ≤ Real.exp ((Cc + Ci + Cy) * errUnit N (Pr.T u))` using `by gcongr; linarith`. Establish `m3 : Real.exp (Cy * errUnit N (Pr.T u)) ≤ Real.exp ((Cc + Ci + Cy) * errUnit N (Pr.T u))` using `by gcongr; linarith`. Establish `hh : ∀ l ≤ N.R.m, (classNumberAt W Ch sel mu I u l : ℝ) ≤ Real.exp ((Cc + Ci + Cy) * errUnit N (Pr.T u))`.

Introduce `l hl`. Use `le_trans ?_ m1` and prove the remaining obligations. Unfold `classNumberAt`. Use `split_ifs with h`. Conclude with `hc3`.

Rewrite using `[← Nat.le_floor_iff (Real.exp_pos _).le]`. Conclude with `Finset.sup_le fun b _ => Nat.le_floor (hc1 l hl b)`. Establish `hn : ∀ l ≤ N.R.m, (indexCount sel mu cst I l : ℝ) ≤ Real.exp ((Cc + Ci + Cy) * errUnit N (Pr.T u))`. Introduce `l hl`. Unfold `indexCount`.

Use `split_ifs with h h'`. Rewrite using `[Nat.cast_one]`. Conclude with `Real.one_le_exp (by positivity)`. Use `le_trans (hyb D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H _ ?_).1 m3` and prove the remaining obligations. Unfold `NumDatum.Nm Ranks.N`.

Use `gcongr`. Conclude with `le_trans (hidx D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H l (by omega)) m2`. Take `⟨⟨M, hfd, hM⟩, hall⟩` from `(hcol D N X s Pr W Ch G sel Sg mu cst I dl B χ cD pl u δ b hY hK hF hE (mtildeOk W Ch sel mu hX.ok (rPsymF Ch)) h1 h2 h3 h4 h5 h6 h7 h8 h9 h10).1`. Use `haveI := hfd`. Take `⟨hfac, -⟩` from `hall M hM`.

Take `⟨wt, w0, w1, wup, wmean⟩` from `GlobalTheory.PlaceWeights.exists_weights X.K s.σ₀ M hM.1`. Use `choose lt hlt using GlobalTheory.T.log_norm_conj_vacuum_eq_rank_product_mul D dl B χ cD X.K s.σ₀ N.R M hadm hpsi tcc h4.1 h4.2.1 hVe hM`. Establish `hmean : (∑ ρ, lt ρ) / (Module.finrank ℚ M : ℝ) ≤ max Ct 0 * N.R.f * (2 * N.sc.L)`. Take `⟨hAdm, hbase⟩` from `GlobalTheory.T.normalisedFamily_standardLattices_eq_baseVector D _ dl B χ h4.2.1 hVe _ _ (hev 0) (hev 1)`. Establish `hco : TaylorLogMetric.CoefIn D (B.thZero (N.R.N 0) (N.R.N 1)) M` using `hM.2.2.2 0 (by omega)`.

Establish `hL0 : 0 ≤ N.sc.L` using `(Real.rpow_pos_of_pos (by linarith [N.sc.one_lt_alt]) _).le`. Establish `hLs : Real.log D.host.v + |TaylorLogMetric.logDerivativeAtOne D| ≤ 2 * N.sc.L`. Establish `g1` using `h10.1.1`. Establish `g2` using `h10.1.2.2.2.2`. Rewrite using `[← tv, ← tL]`.

Establish `g3 : 0 < N.rd` using `lt_of_lt_of_le one_pos (one_le_rd N)`. Establish `g4 : Real.log N.v ≤ Real.log N.rd` using `Real.log_le_log (by unfold NumDatum.v; positivity) (by unfold NumDatum.v; linarith)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h5'` using `(hth D _ dl B χ hadm hpsi tcc h4.1 h4.2.1 hYf).2.1 _ hLs _ _ _ _ hAdm M hM.2.1 (by rwa [hbase])`. Rewrite `h5'` using `[hbase, tf]`.

Establish `e : (∑ ρ : M →ₐ[ℚ] ℂ, logThAt B M ρ (N.R.N 0) (N.R.N 1)) / (Module.finrank ℚ M : ℝ) = ((N.R.N 0 : ℝ) * (N.R.N 1 : ℝ)) * ((∑ ρ, lt ρ) / (Module.finrank ℚ M : ℝ))`. Simplify using `only [fun ρ => hlt ρ 0 (by omega : 0 < N.R.m)]`. Rewrite using `[← Finset.mul_sum]`. Expand and normalize the polynomial expressions, which then agree. Establish `hpos : (0 : ℝ) < (N.R.N 0 : ℝ) * (N.R.N 1 : ℝ)`.

Establish `hk` using `N.R.m_add_three_le_k`. Establish `a0 : 0 < N.R.N 0` using `by unfold Ranks.N; omega`. Establish `a1 : 0 < N.R.N 1` using `by unfold Ranks.N; omega`. Check the signs of the components of the expression. Establish `h6 : ((N.R.N 0 : ℝ) * (N.R.N 1 : ℝ)) * ((∑ ρ, lt ρ) / (Module.finrank ℚ M : ℝ)) ≤ ((N.R.N 0 : ℝ) * (N.R.N 1 : ℝ)) * (max Ct 0 * N.R.f * (2 * N.sc.L))`.

Rewrite using `[← e]`. Use `le_trans h5' ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Conclude with `le_max_left _ _`. Use `_ = _ := by ring`.

Conclude with `le_of_mul_le_mul_left h6 hpos`. Use `kerSide_of_means N δ (Pr.T u) (hPr.T_prime u).two_le h10 eJ R hR CK (Cc + Ci + Cy) (max Ct 0) (Module.finrank ℚ M : ℝ) hCK (by positivity) (le_max_right _ _) wt w1 wmean (fun ρ z => logOmAt B cD M ρ (s.iT (pl z))) lt ?_ hmean (classNumberAt W Ch sel mu I u) (indexCount sel mu cst …` and prove the remaining obligations. Introduce `z`. Rewrite using `[tOm]`. Conclude with `(GlobalTheory.T.mean_logMetric_generator_eq_meanPeriod D _ dl cD hcrv (hP D _ dl tcc h4.1) h4.2.2).2 M hM.2.1 hM.2.2.1 _`.

Introduce `t ht`. Use `factorBounds_of_weights _ hm rfl eJ (fun ρ => placeUnder s.σ₀ hM.1 ρ) wt w0 w1 wup (fun ρ j => liftBound_sq N s W Ch sel mu cst I B cD pl u δ CK M ρ j) (fun i v φ => GlobalTheory.ColumnFamilyMetric.famIpAt_nonneg X Pr N.R W sel Sg mu I u i (hF i) v φ) (fun a i hi => (hfac a).1 i …` and prove the remaining obligations. Rewrite using `[ht]`. Use `Finset.sum_congr rfl fun ρ _ => ?_` and prove the remaining obligations. Unfold `liftBound_sq`.

Simplify using `only [Nat.add_sub_cancel]`. Rewrite using `[hlt ρ _ (eJ l).2]`.
-/
theorem kerSide_chain : ColumnNorms → GlobalTheory.IndefiniteRowSideFullHecke.MeanPeriodLogarithms.MeanPeriod → GlobalTheory.ColNorms.FamilyVectors → GlobalTheory.ColNorms.FamilyNorms → ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (N : NumDatum) (X : Fields) [IsTotallyComplex X.K] (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (B : Base D D.host.ccK dl) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N) (b : I.β (N.R.m - 2 + 1)) (hY : YbHyp (R := N.R) sel mu cst I u (N.R.m - 2) b) (hK : KerEquivC W Ch sel mu cst I (ambOf s B χ cD) u (N.R.m - 2) b hY (rPsymF Ch)) (hF : ∀ j, (chF W sel mu I u j).Ok) (hE : (evGSD W Ch sel mu (rPsymF Ch) u).Ok) (J : Type) [Fintype J] (eJ : J ≃ Fin N.R.m) (R : RecNums J (RPl N.R)), HostTie N s Pr → WeightTie N W pl u δ → CharTie N s W Ch G sel → AnalyticTie D dl χ cD → mu = 1 → cst.sharp = true → I.Ok Ch sel mu cst G (N.R.m - 2) → FieldOfDefinition W sel mu cst u (ambOf s B χ cD) → Sizes Pr W N.sc.a → SizeRows N δ (Pr.T u) → Reads N eJ δ (Pr.T u) R → KerSide R (InfinitePlace X.K) C (FactorBounds (KerChain.ofCol W Ch sel mu cst I (chKerC W Ch sel mu cst I (ambOf s B χ cD) u (N.R.m - 2) b hY (rPsymF Ch) hK) hF hE) fun l => (eJ l).1) := by
  intro hCN hP hV hN
  obtain ⟨CK, C', hCK, -, hcol⟩ := hCN
  obtain ⟨Cc, hCc, hcl⟩ := GlobalTheory.T.character_sum_local_constant_tenth
  obtain ⟨Ci, hCi, hidx⟩ := GlobalTheory.T.character_sum_local_constant_eleventh
  obtain ⟨Cy, hCy, hyb⟩ := GlobalTheory.T.character_sum_local_constant_twelfth
  obtain ⟨Ct, hth⟩ := hN
  refine ⟨CK + 2 * (Cc + Ci + Cy) + 2 * max Ct 0 + 20, by positivity, ?_⟩
  intro D N X _ s Pr W Ch G sel Sg mu cst I dl B χ cD pl u δ b hY hK hF hE J _ eJ R h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 hR
  have H : Hyp N s W Ch G sel mu cst I dl χ cD pl u δ := ⟨h1, h2, h3, h4, h5, h6, h7, h9, h10⟩
  obtain ⟨trd, tv, tL, tOm, tf, -, tE, -, tcc⟩ := GlobalTheory.T.numDatum_numbers_eq_host_of_compatible D N X s Pr h1
  obtain ⟨-, -, -, -, hpsi, hadm, hX, hs, -, hPr, -, -, hg, -⟩ := id h1
  have hcrv : StandardLatticesGL3.Crv D D.host.ccK dl := ⟨tcc, h4.1⟩
  have hYf := GlobalTheory.T.kernelConstant_exponents_finite D B.γ₀ B.kc
  have hVe : B.VecP χ := hV D _ dl B χ hadm hpsi tcc h4.1 h4.2.1 hYf
  have hev : ∀ l, Even (N.R.N l) := fun l => by
    unfold Ranks.N
    exact N.R.k_even.add ((N.R.t_odd.add_one).mul_left l)
  have hm := N.R.two_le_m
  have hU : 0 ≤ errUnit N (Pr.T u) := by
    have h0 : (1 : ℝ) ≤ N.g 0 := by exact_mod_cast (N.g_prime 0).one_lt.le
    have h1' : (1 : ℝ) ≤ N.g 1 := by exact_mod_cast (N.g_prime 1).one_lt.le
    have h2' : (1 : ℝ) ≤ Pr.T u := by exact_mod_cast (hPr.T_prime u).one_lt.le
    have h3' : 0 ≤ Real.log ((N.g 0 : ℝ) * N.g 1 * Pr.T u) :=
      Real.log_nonneg (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le h0 h1') h2')
    unfold errUnit
    positivity
  obtain ⟨hc1, -, hc3⟩ := hcl D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H
  have m1 : Real.exp (Cc * errUnit N (Pr.T u)) ≤ Real.exp ((Cc + Ci + Cy) * errUnit N (Pr.T u)) := by
    gcongr; linarith
  have m2 : Real.exp (Ci * errUnit N (Pr.T u)) ≤ Real.exp ((Cc + Ci + Cy) * errUnit N (Pr.T u)) := by
    gcongr; linarith
  have m3 : Real.exp (Cy * errUnit N (Pr.T u)) ≤ Real.exp ((Cc + Ci + Cy) * errUnit N (Pr.T u)) := by
    gcongr; linarith
  have hh : ∀ l ≤ N.R.m, (classNumberAt W Ch sel mu I u l : ℝ) ≤ Real.exp ((Cc + Ci + Cy) * errUnit N (Pr.T u)) := by
    intro l hl
    refine le_trans ?_ m1
    unfold classNumberAt
    split_ifs with h
    · exact hc3
    · rw [← Nat.le_floor_iff (Real.exp_pos _).le]
      exact Finset.sup_le fun b _ => Nat.le_floor (hc1 l hl b)
  have hn : ∀ l ≤ N.R.m, (indexCount sel mu cst I l : ℝ) ≤ Real.exp ((Cc + Ci + Cy) * errUnit N (Pr.T u)) := by
    intro l hl
    unfold indexCount
    split_ifs with h h'
    · rw [Nat.cast_one]
      exact Real.one_le_exp (by positivity)
    · refine le_trans (hyb D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H _ ?_).1 m3
      unfold NumDatum.Nm Ranks.N
      gcongr
    · exact le_trans (hidx D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H l (by omega)) m2
  obtain ⟨⟨M, hfd, hM⟩, hall⟩ := (hcol D N X s Pr W Ch G sel Sg mu cst I dl B χ cD pl u δ b hY hK hF hE
    (mtildeOk W Ch sel mu hX.ok (rPsymF Ch)) h1 h2 h3 h4 h5 h6 h7 h8 h9 h10).1
  haveI := hfd
  obtain ⟨hfac, -⟩ := hall M hM
  obtain ⟨wt, w0, w1, wup, wmean⟩ := GlobalTheory.PlaceWeights.exists_weights X.K s.σ₀ M hM.1
  choose lt hlt using GlobalTheory.T.log_norm_conj_vacuum_eq_rank_product_mul D dl B χ cD X.K s.σ₀ N.R M hadm hpsi tcc h4.1 h4.2.1 hVe hM
  have hmean : (∑ ρ, lt ρ) / (Module.finrank ℚ M : ℝ) ≤ max Ct 0 * N.R.f * (2 * N.sc.L) := by
    obtain ⟨hAdm, hbase⟩ := GlobalTheory.T.normalisedFamily_standardLattices_eq_baseVector D _ dl B χ h4.2.1 hVe _ _ (hev 0) (hev 1)
    have hco : TaylorLogMetric.CoefIn D (B.thZero (N.R.N 0) (N.R.N 1)) M := hM.2.2.2 0 (by omega)
    have hL0 : 0 ≤ N.sc.L := (Real.rpow_pos_of_pos (by linarith [N.sc.one_lt_alt]) _).le
    have hLs : Real.log D.host.v + |TaylorLogMetric.logDerivativeAtOne D| ≤ 2 * N.sc.L := by
      have g1 := h10.1.1
      have g2 := h10.1.2.2.2.2
      rw [← tv, ← tL]
      have g3 : 0 < N.rd := lt_of_lt_of_le one_pos (one_le_rd N)
      have g4 : Real.log N.v ≤ Real.log N.rd := Real.log_le_log (by unfold NumDatum.v; positivity) (by unfold NumDatum.v; linarith)
      linarith
    have h5' := (hth D _ dl B χ hadm hpsi tcc h4.1 h4.2.1 hYf).2.1 _ hLs _ _ _ _ hAdm M hM.2.1 (by rwa [hbase])
    rw [hbase, tf] at h5'
    have e : (∑ ρ : M →ₐ[ℚ] ℂ, logThAt B M ρ (N.R.N 0) (N.R.N 1)) / (Module.finrank ℚ M : ℝ) =
        ((N.R.N 0 : ℝ) * (N.R.N 1 : ℝ)) * ((∑ ρ, lt ρ) / (Module.finrank ℚ M : ℝ)) := by
      simp only [fun ρ => hlt ρ 0 (by omega : 0 < N.R.m)]
      rw [← Finset.mul_sum]
      ring
    have hpos : (0 : ℝ) < (N.R.N 0 : ℝ) * (N.R.N 1 : ℝ) := by
      have hk := N.R.m_add_three_le_k
      have a0 : 0 < N.R.N 0 := by unfold Ranks.N; omega
      have a1 : 0 < N.R.N 1 := by unfold Ranks.N; omega
      positivity
    have h6 : ((N.R.N 0 : ℝ) * (N.R.N 1 : ℝ)) * ((∑ ρ, lt ρ) / (Module.finrank ℚ M : ℝ)) ≤
        ((N.R.N 0 : ℝ) * (N.R.N 1 : ℝ)) * (max Ct 0 * N.R.f * (2 * N.sc.L)) := by
      rw [← e]
      refine le_trans h5' ?_
      calc _ ≤ max Ct 0 * N.R.f * (N.R.N 0 : ℝ) * (N.R.N 1 : ℝ) * (2 * N.sc.L) := by
            gcongr
            exact le_max_left _ _
        _ = _ := by ring
    exact le_of_mul_le_mul_left h6 hpos
  refine kerSide_of_means N δ (Pr.T u) (hPr.T_prime u).two_le h10 eJ R hR CK (Cc + Ci + Cy) (max Ct 0) (Module.finrank ℚ M : ℝ) hCK
    (by positivity) (le_max_right _ _) wt w1 wmean (fun ρ z => logOmAt B cD M ρ (s.iT (pl z))) lt ?_ hmean
    (classNumberAt W Ch sel mu I u) (indexCount sel mu cst I) hh hn _ ?_
  · intro z
    rw [tOm]
    exact (GlobalTheory.T.mean_logMetric_generator_eq_meanPeriod D _ dl cD hcrv (hP D _ dl tcc h4.1) h4.2.2).2 M hM.2.1 hM.2.2.1 _
  · intro t ht
    refine factorBounds_of_weights _ hm rfl eJ (fun ρ => placeUnder s.σ₀ hM.1 ρ) wt w0 w1 wup
      (fun ρ j => liftBound_sq N s W Ch sel mu cst I B cD pl u δ CK M ρ j)
      (fun i v φ => GlobalTheory.ColumnFamilyMetric.famIpAt_nonneg X Pr N.R W sel Sg mu I u i (hF i) v φ)
      (fun a i hi => (hfac a).1 i hi) (fun a => (hfac a).2) t fun l v => ?_
    rw [ht]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    unfold liftBound_sq
    simp only [Nat.add_sub_cancel]
    rw [hlt ρ _ (eJ l).2]

end GlobalTheory.KernelHalf
