import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrKIsometricAndOneSubSurjectiveStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualExpTeichmullerPowerSumFormulaStatement

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

noncomputable section

namespace GlobalTheory.ExpImage.PosWeight

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simp [P.ζQ_zero]`. Consider the case `succ k ih => rw [pow_succ', pow_mul, P.ζQ_succ, ih]`.
-/
theorem zeta_pow_self (P : LocPrime l) (m : ℕ) : P.ζQ m ^ (l ^ m) = 1 := by
  induction m with
  | zero => simp [P.ζQ_zero]
  | succ k ih => rw [pow_succ', pow_mul, P.ζQ_succ, ih]

/- English proof (translation)
Rewrite using `[← map_natCast (algebraMap ℚ_[l] (Om l)), norm_algebraMap']`. Conclude with `Padic.norm_natCast_eq_one_iff.mpr ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr ha)`.
-/
theorem norm_nat_eq_one {a : ℕ} (ha : ¬ l ∣ a) : ‖(a : Om l)‖ = 1 := by
  rw [← map_natCast (algebraMap ℚ_[l] (Om l)), norm_algebraMap']
  exact Padic.norm_natCast_eq_one_iff.mpr ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr ha)

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ k ih => rw [pow_succ', AlgHom.mul_apply, (GlobalTheory.T.norm_frK_eq_and_exists_sub_pow_smul_frK_eq l P K).1, ih]`.
-/
theorem norm_frK_pow (P : LocPrime l) (K : FinExt l) (n : ℕ) (c : ↥(K0 K)) :
    ‖(((frK P K ^ n) c : ↥(K0 K)) : Om l)‖ = ‖(c : Om l)‖ := by
  induction n with
  | zero => simp
  | succ k ih => rw [pow_succ', AlgHom.mul_apply, (GlobalTheory.T.norm_frK_eq_and_exists_sub_pow_smul_frK_eq l P K).1, ih]

def co {K : FinExt l} (e : ℕ) (lam : ℕ → ↥(K0 K)) (i : ℕ × Bool) : ↥(K0 K) :=
  if i.2 then lam i.1 * ((i.1 : ↥(K0 K)) ^ e)⁻¹ else -(lam i.1 * ((i.1 : ↥(K0 K)) ^ e)⁻¹)

def ex (l s : ℕ) (i : ℕ × Bool) : ℕ := if i.2 then (1 + l ^ s) * i.1 else i.1

/- English proof (translation)
Introduce `LT l _ AI hT K s hs e he g hg hχ lam d hlam hd hrec`. Establish `hl : l.Prime` using `Fact.out`. Establish `hu : ¬ l ∣ 1 + l ^ s`. Introduce `h`. Establish `h1 : l ∣ l ^ s` using `dvd_pow_self l (by have := hs.1; omega)`.

Conclude with `hl.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_left h1).mp h))`. Establish `hmem : ∀ a ∈ primeTo l s, ¬ l ∣ a` using `fun a ha => (Finset.mem_filter.mp ha).2`. Establish `hne : ∀ a ∈ primeTo l s, (a : Om l) ≠ 0` using `fun a ha h => by`. Use `norm_nat_eq_one (hmem a ha)` as an intermediate fact. Rewrite `this` using `[h, norm_zero]`.

Conclude with `zero_ne_one this`. Establish `hne' : ∀ a ∈ primeTo l s, (a : ↥(K0 K)) ≠ 0` using `fun a ha h => hne a ha (by simpa using congrArg (fun x : ↥(K0 K) => (x : Om l)) h)`. Use `set T : Finset (ℕ × Bool) := primeTo l s ×ˢ Finset.univ with hTdef`. Establish `hc : ∀ i ∈ T, ‖(co e lam i : Om l)‖ ≤ 1 ∧ ¬ l ∣ ex l s i`. Introduce and unpack `⟨a, b⟩ hi`.

Establish `ha : a ∈ primeTo l s` using `(Finset.mem_product.mp hi).1`. Establish `h1` using `norm_nat_eq_one (hmem a ha)`. Establish `h2 : ‖(lam a : Om l) * ((a : Om l) ^ e)⁻¹‖ ≤ 1`. Rewrite using `[norm_mul, norm_inv, norm_pow, h1]`. Simplify using `using hlam a`.

Consider the cases of `b`. Use `⟨?_, hmem a ha⟩` and prove the remaining obligations. Simplify `h2` using `[co, -norm_mul]`. Use `⟨by simpa [co, -norm_mul] using h2, ?_⟩` and prove the remaining obligations. Introduce `h`.

Break down `(Nat.Prime.dvd_mul hl).mp h with h | h` into its components or cases. Conclude with `hu h`. Conclude with `hmem a ha h`. Establish `hall : ∀ j : ℕ, ∃ dj : ↥(K0 K), j ≤ e → (‖(dj : Om l)‖ ≤ 1 ∧ dj - (l : ↥(K0 K)) ^ j * frK (LT l) K dj = (frK (LT l) K ^ s) (∑ i ∈ T, co e lam i * (ex l s i : ↥(K0 K)) ^ j)) ∧ (j = e → dj = (((1 + l ^ s : ℕ) : ↥(K0 K)) ^ e - 1) * d)`. Introduce `j`.

Distinguish the cases in `hje : j = e`. Substitute `hje` using the available equality. Use `⟨(((1 + l ^ s : ℕ) : ↥(K0 K)) ^ j - 1) * d, fun _ => ⟨⟨?_, ?_⟩, fun _ => rfl⟩⟩` and prove the remaining obligations. Establish `h1 : ‖((1 + l ^ s : ℕ) : Om l) ^ j - 1‖ ≤ 1`. Use `IsUltrametricDist.norm_intCast_le_one (Om l) (((1 + l ^ s : ℕ) : ℤ) ^ j - 1)` as an intermediate fact.

Simplify using `using this`. Establish `h2 : ((((((1 + l ^ s : ℕ) : ↥(K0 K)) ^ j - 1) * d : ↥(K0 K))) : Om l) = (((1 + l ^ s : ℕ) : Om l) ^ j - 1) * (d : Om l)` using `by simp`. Rewrite using `[h2, norm_mul]`. Conclude with `mul_le_one₀ h1 (norm_nonneg _) hd`. Establish `h3 : ∑ i ∈ T, co j lam i * (ex l s i : ↥(K0 K)) ^ j = (((1 + l ^ s : ℕ) : ↥(K0 K)) ^ j - 1) * ∑ a ∈ primeTo l s, lam a`.

Rewrite using `[hTdef, Finset.sum_product, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun a ha => ?_` and prove the remaining obligations. Use `hne' a ha` as an intermediate fact. Simplify using `only [Fintype.sum_bool, co, ex, if_true, Bool.false_eq_true, if_false, Nat.cast_mul]`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h3, map_mul, map_mul, ← hrec]`. Simplify using `only [map_sub, map_pow, map_natCast, map_one]`. Expand and normalize the polynomial expressions, which then agree. Break down `Nat.eq_zero_or_pos j with rfl | hj` into its components or cases.

Use `⟨0, fun _ => ⟨⟨by simp, ?_⟩, fun h => absurd h hje⟩⟩` and prove the remaining obligations. Rewrite using `[hTdef, Finset.sum_product]`. Simplify using `[co]`. Take `⟨dj, h1, h2⟩` from `(GlobalTheory.T.norm_frK_eq_and_exists_sub_pow_smul_frK_eq l (LT l) K).2 j hj ((frK (LT l) K ^ s) (∑ i ∈ T, co e lam i * (ex l s i : ↥(K0 K)) ^ j)) (by`. Rewrite using `[norm_frK_pow, AddSubmonoidClass.coe_finset_sum]`.

Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i hi => ?_` and prove the remaining obligations. Establish `h2 : ((co e lam i * (ex l s i : ↥(K0 K)) ^ j : ↥(K0 K)) : Om l) = (co e lam i : Om l) * (ex l s i : Om l) ^ j` using `by simp`. Rewrite using `[h2, norm_mul, norm_pow, norm_nat_eq_one (hc i hi).2]`. Simplify using `using (hc i hi).1)`. Conclude with `⟨dj, fun _ => ⟨⟨h1, h2⟩, fun h => absurd h hje⟩⟩`.

Use `choose D hD using hall`. Take `⟨z, hz, hE⟩` from `GlobalTheory.T.dualExp_teichmuller_power_sum_formula LT l AI hT K s hs e g hg hχ (ℕ × Bool) T (co e lam) (ex l s) D hc (fun j hj => (hD j hj).1)`. Use `⟨z, hz, ?_⟩` and prove the remaining obligations. Establish `hlev : levSum (LT l) K s e T (co e lam) (ex l s) (D e) = (((1 + l ^ s : ℕ) : Om l) ^ e - 1) * cycVal (LT l) K s e lam d`. Rewrite using `[(hD e le_rfl).2 rfl]`.

Unfold `levSum cycVal`. Rewrite using `[mul_add, Finset.mul_sum]`. Use `congr 1`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[mul_left_comm]`.

Use `congr 1`. Rewrite using `[hTdef, Finset.sum_product, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun a ha => ?_` and prove the remaining obligations. Establish `h0` using `hne a ha`. Establish `hz : (LT l).ζQ s ^ ((1 + l ^ s) * a * l ^ i) = (LT l).ζQ s ^ (a * l ^ i)`.

Rewrite using `[mul_assoc, add_mul, one_mul, pow_add, pow_mul _ (l ^ s), zeta_pow_self, one_pow, mul_one]`. Establish `hco : (((frK (LT l) K ^ i) (lam a * ((a : ↥(K0 K)) ^ e)⁻¹) : ↥(K0 K)) : Om l) = (((frK (LT l) K ^ i) (lam a) : ↥(K0 K)) : Om l) * ((a : Om l) ^ e)⁻¹`. Rewrite using `[map_mul, map_inv₀, map_pow, map_natCast]`. Simplify using the standard rewrite rules. Simplify using `only [Fintype.sum_bool, co, ex, if_true, Bool.false_eq_true, if_false, map_neg, NegMemClass.coe_neg, hco, hz, Nat.cast_mul]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `h2 : ((((((1 + l ^ s : ℕ) : ↥(K0 K)) ^ e - 1) * d : ↥(K0 K))) : Om l) = (((1 + l ^ s : ℕ) : Om l) ^ e - 1) * (d : Om l)` using `by simp`. Rewrite using `[h2]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite `hE` using `[hlev]`. Use `hE using 1` and compare the differences between its conclusion and the goal. Rewrite using `[div_eq_mul_inv, map_mul, map_sub, map_pow, map_natCast, map_one]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem formula_pos : ∀ (LT : LocTheory) (l : ℕ) [Fact l.Prime] (AI : LocAinf l (LT l)), LocTied l (LT l) AI → ∀ (K : FinExt l) (s : ℕ), Lev l s → ∀ (e : ℕ), 1 ≤ e → ∀ (g : GQ l), g ∈ Gj K s → ((LT l).χQ g : ℚ_[l]) = ((1 + l ^ s : ℕ) : ℚ_[l]) → ∀ (lam : ℕ → ↥(K0 K)) (d : ↥(K0 K)), (∀ a, ‖(lam a : Om l)‖ ≤ 1) → ‖(d : Om l)‖ ≤ 1 → d - (l : ↥(K0 K)) ^ e * frK (LT l) K d = (frK (LT l) K ^ s) (∑ a ∈ primeTo l s, lam a) → ∃ z : GQ l → ℚ_[l], (∀ σ ∈ Gj K s, ‖z σ‖ ≤ 1) ∧ ExpStar LT (Gj K s) e z (algebraMap ℚ_[l] (Om l) ((((1 + l ^ s : ℕ) : ℚ_[l]) ^ e - 1) / (logZl l ((1 + l ^ s : ℕ) : ℚ_[l]) * ((e.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (s * e)))) * cycVal (LT l) K s e lam d) := by
  intro LT l _ AI hT K s hs e he g hg hχ lam d hlam hd hrec
  have hl : l.Prime := Fact.out
  have hu : ¬ l ∣ 1 + l ^ s := by
    intro h
    have h1 : l ∣ l ^ s := dvd_pow_self l (by have := hs.1; omega)
    exact hl.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_left h1).mp h))
  have hmem : ∀ a ∈ primeTo l s, ¬ l ∣ a := fun a ha => (Finset.mem_filter.mp ha).2
  have hne : ∀ a ∈ primeTo l s, (a : Om l) ≠ 0 := fun a ha h => by
    have := norm_nat_eq_one (hmem a ha)
    rw [h, norm_zero] at this
    exact zero_ne_one this
  have hne' : ∀ a ∈ primeTo l s, (a : ↥(K0 K)) ≠ 0 := fun a ha h =>
    hne a ha (by simpa using congrArg (fun x : ↥(K0 K) => (x : Om l)) h)
  set T : Finset (ℕ × Bool) := primeTo l s ×ˢ Finset.univ with hTdef
  have hc : ∀ i ∈ T, ‖(co e lam i : Om l)‖ ≤ 1 ∧ ¬ l ∣ ex l s i := by
    rintro ⟨a, b⟩ hi
    have ha : a ∈ primeTo l s := (Finset.mem_product.mp hi).1
    have h1 := norm_nat_eq_one (hmem a ha)
    have h2 : ‖(lam a : Om l) * ((a : Om l) ^ e)⁻¹‖ ≤ 1 := by
      rw [norm_mul, norm_inv, norm_pow, h1]
      simpa using hlam a
    cases b
    · refine ⟨?_, hmem a ha⟩
      simpa [co, -norm_mul] using h2
    · refine ⟨by simpa [co, -norm_mul] using h2, ?_⟩
      intro h
      rcases (Nat.Prime.dvd_mul hl).mp h with h | h
      · exact hu h
      · exact hmem a ha h
  have hall : ∀ j : ℕ, ∃ dj : ↥(K0 K), j ≤ e → (‖(dj : Om l)‖ ≤ 1 ∧
      dj - (l : ↥(K0 K)) ^ j * frK (LT l) K dj =
        (frK (LT l) K ^ s) (∑ i ∈ T, co e lam i * (ex l s i : ↥(K0 K)) ^ j)) ∧
      (j = e → dj = (((1 + l ^ s : ℕ) : ↥(K0 K)) ^ e - 1) * d) := by
    intro j
    by_cases hje : j = e
    · subst hje
      refine ⟨(((1 + l ^ s : ℕ) : ↥(K0 K)) ^ j - 1) * d, fun _ => ⟨⟨?_, ?_⟩, fun _ => rfl⟩⟩
      · have h1 : ‖((1 + l ^ s : ℕ) : Om l) ^ j - 1‖ ≤ 1 := by
          have := IsUltrametricDist.norm_intCast_le_one (Om l) (((1 + l ^ s : ℕ) : ℤ) ^ j - 1)
          simpa using this
        have h2 : ((((((1 + l ^ s : ℕ) : ↥(K0 K)) ^ j - 1) * d : ↥(K0 K))) : Om l) =
            (((1 + l ^ s : ℕ) : Om l) ^ j - 1) * (d : Om l) := by simp
        rw [h2, norm_mul]
        exact mul_le_one₀ h1 (norm_nonneg _) hd
      · have h3 : ∑ i ∈ T, co j lam i * (ex l s i : ↥(K0 K)) ^ j =
            (((1 + l ^ s : ℕ) : ↥(K0 K)) ^ j - 1) * ∑ a ∈ primeTo l s, lam a := by
          rw [hTdef, Finset.sum_product, Finset.mul_sum]
          refine Finset.sum_congr rfl fun a ha => ?_
          have := hne' a ha
          simp only [Fintype.sum_bool, co, ex, if_true, Bool.false_eq_true, if_false, Nat.cast_mul]
          field_simp
          ring
        rw [h3, map_mul, map_mul, ← hrec]
        simp only [map_sub, map_pow, map_natCast, map_one]
        ring
    · rcases Nat.eq_zero_or_pos j with rfl | hj
      · refine ⟨0, fun _ => ⟨⟨by simp, ?_⟩, fun h => absurd h hje⟩⟩
        rw [hTdef, Finset.sum_product]
        simp [co]
      · obtain ⟨dj, h1, h2⟩ := (GlobalTheory.T.norm_frK_eq_and_exists_sub_pow_smul_frK_eq l (LT l) K).2 j hj
          ((frK (LT l) K ^ s) (∑ i ∈ T, co e lam i * (ex l s i : ↥(K0 K)) ^ j)) (by
            rw [norm_frK_pow, AddSubmonoidClass.coe_finset_sum]
            refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i hi => ?_
            have h2 : ((co e lam i * (ex l s i : ↥(K0 K)) ^ j : ↥(K0 K)) : Om l) =
              (co e lam i : Om l) * (ex l s i : Om l) ^ j := by simp
            rw [h2, norm_mul, norm_pow, norm_nat_eq_one (hc i hi).2]
            simpa using (hc i hi).1)
        exact ⟨dj, fun _ => ⟨⟨h1, h2⟩, fun h => absurd h hje⟩⟩
  choose D hD using hall
  obtain ⟨z, hz, hE⟩ := GlobalTheory.T.dualExp_teichmuller_power_sum_formula LT l AI hT K s hs e g hg hχ (ℕ × Bool) T (co e lam) (ex l s) D hc
    (fun j hj => (hD j hj).1)
  refine ⟨z, hz, ?_⟩
  have hlev : levSum (LT l) K s e T (co e lam) (ex l s) (D e) =
      (((1 + l ^ s : ℕ) : Om l) ^ e - 1) * cycVal (LT l) K s e lam d := by
    rw [(hD e le_rfl).2 rfl]
    unfold levSum cycVal
    rw [mul_add, Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_left_comm]
      congr 1
      rw [hTdef, Finset.sum_product, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a ha => ?_
      have h0 := hne a ha
      have hz : (LT l).ζQ s ^ ((1 + l ^ s) * a * l ^ i) = (LT l).ζQ s ^ (a * l ^ i) := by
        rw [mul_assoc, add_mul, one_mul, pow_add, pow_mul _ (l ^ s), zeta_pow_self, one_pow, mul_one]
      have hco : (((frK (LT l) K ^ i) (lam a * ((a : ↥(K0 K)) ^ e)⁻¹) : ↥(K0 K)) : Om l) =
          (((frK (LT l) K ^ i) (lam a) : ↥(K0 K)) : Om l) * ((a : Om l) ^ e)⁻¹ := by
        rw [map_mul, map_inv₀, map_pow, map_natCast]
        simp
      simp only [Fintype.sum_bool, co, ex, if_true, Bool.false_eq_true, if_false, map_neg,
        NegMemClass.coe_neg, hco, hz, Nat.cast_mul]
      field_simp
      ring
    · have h2 : ((((((1 + l ^ s : ℕ) : ↥(K0 K)) ^ e - 1) * d : ↥(K0 K))) : Om l) =
            (((1 + l ^ s : ℕ) : Om l) ^ e - 1) * (d : Om l) := by simp
      rw [h2]
      ring
  rw [hlev] at hE
  convert hE using 1
  rw [div_eq_mul_inv, map_mul, map_sub, map_pow, map_natCast, map_one]
  ring

end GlobalTheory.ExpImage.PosWeight
