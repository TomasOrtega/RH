import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.LetterShift
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.TopsChoicePartA

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.D

open Formalism.DworkPowerSeriesWeights (Integral letterLog entLog)
open Formalism.InvariantFactorPaths.G7 (frobVar frobVar_eq_expand UnrOK)

namespace KernelCokernelKilling

open MvPowerSeries

section Gen

variable {K : Type} [Field K] {τ : Type} [DecidableEq τ] {l d : ℕ}

def gLog (K : Type) [Field K] (l : ℕ) (φ : ZMod d → τ) (s : ZMod d) : MvPowerSeries τ K :=
  fun n => ∑ e ∈ Finset.range (n.degree + 1),
    if n = Finsupp.single (φ (s - 2 * (e : ZMod d))) ((l ^ 2) ^ e) then ((l : K) ^ e)⁻¹ else 0

/- English proof (translation)
Use `first`. Consider the case `exact Nat.pow_right_injective (by nlinarith) h`. Consider the case `exact Nat.pow_right_injective (le_trans hl (Nat.le_self_pow (by norm_num) l)) h`.
-/
lemma pow_inj (hl : 2 ≤ l) {a b : ℕ} (h : (l ^ 2) ^ a = (l ^ 2) ^ b) : a = b := by
  first
  | exact Nat.pow_right_injective (by nlinarith) h
  | exact Nat.pow_right_injective (le_trans hl (Nat.le_self_pow (by norm_num) l)) h

/- English proof (translation)
Use `first`. Consider the case `rfl`. Consider the case `simp [gLog, coeff_apply]`.
-/
lemma coeff_gLog (φ : ZMod d → τ) (s : ZMod d) (n : τ →₀ ℕ) :
    coeff n (gLog K l φ s) = ∑ e ∈ Finset.range (n.degree + 1),
      if n = Finsupp.single (φ (s - 2 * (e : ZMod d))) ((l ^ 2) ^ e) then ((l : K) ^ e)⁻¹ else 0 := by
  first
  | rfl
  | simp [gLog, coeff_apply]

/- English proof (translation)
Establish `hk : (l ^ 2) ^ e ≠ 0` using `pow_ne_zero _ (pow_ne_zero _ (by omega))`. Rewrite using `[coeff_gLog, Finset.sum_eq_single e]`. Rewrite using `[if_pos rfl]`. Introduce `b _ hb`. Rewrite using `[if_neg]`.

Introduce `h`. Apply `hb` to reduce the goal to its premises. Rewrite `h` using `[Finsupp.single_eq_single_iff]`. Break down `h with ⟨_, h2⟩ | ⟨h2, _⟩` into its components or cases. Conclude with `(pow_inj hl h2).symm`.

Conclude with `absurd h2 hk`. Introduce `he`. It suffices to derive a contradiction. Apply `he` to reduce the goal to its premises. Rewrite using `[Finset.mem_range]`.

Establish `hdeg : (Finsupp.single (φ (s - 2 * (e : ZMod d))) ((l ^ 2) ^ e)).degree = (l ^ 2) ^ e` using `by first`. Consider the case `exact Finsupp.degree_single _ _`. Consider the case `simp [Finsupp.degree, Finsupp.support_single_ne_zero _ hk]`. Consider the case `simp`. Rewrite using `[hdeg]`.

Establish `: e < (l ^ 2) ^ e` using `by first`. Consider the case `exact Nat.lt_pow_self (by nlinarith)`. Consider the case `exact Nat.lt_pow_self (by nlinarith) e`. Use `first`. Consider the case `exact Nat.lt_succ_of_lt this`.

Consider the case `omega`.
-/
lemma coeff_gLog_single (hl : 2 ≤ l) (φ : ZMod d → τ) (s : ZMod d) (e : ℕ) :
    coeff (Finsupp.single (φ (s - 2 * (e : ZMod d))) ((l ^ 2) ^ e)) (gLog K l φ s) =
      ((l : K) ^ e)⁻¹ := by
  have hk : (l ^ 2) ^ e ≠ 0 := pow_ne_zero _ (pow_ne_zero _ (by omega))
  rw [coeff_gLog, Finset.sum_eq_single e]
  · rw [if_pos rfl]
  · intro b _ hb
    rw [if_neg]
    intro h
    apply hb
    rw [Finsupp.single_eq_single_iff] at h
    rcases h with ⟨_, h2⟩ | ⟨h2, _⟩
    · exact (pow_inj hl h2).symm
    · exact absurd h2 hk
  · intro he
    exfalso
    apply he
    rw [Finset.mem_range]
    have hdeg : (Finsupp.single (φ (s - 2 * (e : ZMod d))) ((l ^ 2) ^ e)).degree = (l ^ 2) ^ e := by
      first
      | exact Finsupp.degree_single _ _
      | simp [Finsupp.degree, Finsupp.support_single_ne_zero _ hk]
      | simp
    rw [hdeg]
    have : e < (l ^ 2) ^ e := by
      first
      | exact Nat.lt_pow_self (by nlinarith)
      | exact Nat.lt_pow_self (by nlinarith) e
    first
    | exact Nat.lt_succ_of_lt this
    | omega

/- English proof (translation)
Rewrite using `[coeff_gLog]`. Conclude with `Finset.sum_eq_zero fun e _ => if_neg (h e)`.
-/
lemma coeff_gLog_zero (φ : ZMod d → τ) (s : ZMod d) (n : τ →₀ ℕ)
    (h : ∀ e : ℕ, n ≠ Finsupp.single (φ (s - 2 * (e : ZMod d))) ((l ^ 2) ^ e)) :
    coeff n (gLog K l φ s) = 0 := by
  rw [coeff_gLog]
  exact Finset.sum_eq_zero fun e _ => if_neg (h e)

/- English proof (translation)
Use extensionality with `n`. Rewrite using `[coeff_map, coeff_gLog, map_sum]`. Use `Finset.sum_congr rfl fun e _ => ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> simp`.
-/
lemma map_gLog (ρ : K →+* K) (φ : ZMod d → τ) (s : ZMod d) :
    map ρ (gLog K l φ s) = gLog K l φ s := by
  ext n
  rw [coeff_map, coeff_gLog, map_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  split_ifs <;> simp

/- English proof (translation)
Use `first`. Consider the case `rw [← coeff_zero_eq_constantCoeff_apply]`. Consider the case `show coeff 0 (gLog K l φ s) = 0`. Apply `coeff_gLog_zero` to reduce the goal to its premises. Introduce `e h`.

Rewrite `h` using `[eq_comm, Finsupp.single_eq_zero]`. Conclude with `pow_ne_zero _ (pow_ne_zero _ (by omega)) h`.
-/
lemma constantCoeff_gLog (hl : 2 ≤ l) (φ : ZMod d → τ) (s : ZMod d) :
    constantCoeff (gLog K l φ s) = 0 := by
  first
  | rw [← coeff_zero_eq_constantCoeff_apply]
  | show coeff 0 (gLog K l φ s) = 0
  apply coeff_gLog_zero
  intro e h
  rw [eq_comm, Finsupp.single_eq_zero] at h
  exact pow_ne_zero _ (pow_ne_zero _ (by omega)) h

/- English proof (translation)
Establish `hl2 : 2 ≤ l` using `hl.two_le`. Establish `hq : l ^ 2 ≠ 0` using `pow_ne_zero _ hl.ne_zero`. Establish `hstep : ∀ e : ℕ, s - 2 * ((e + 1 : ℕ) : ZMod d) = s - 2 - 2 * (e : ZMod d)`. Introduce `e`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[map_gLog]`. Use extensionality with `n`. Rewrite using `[map_sub, coeff_C_mul, coeff_X]`. Distinguish the cases in `hn : ∃ e : ℕ, n = Finsupp.single (φ (s - 2 * (e : ZMod d))) ((l ^ 2) ^ e)`.

Take `⟨e, rfl⟩` from `hn`. Rewrite using `[coeff_gLog_single hl2]`. Consider the cases of `e with`. Consider the case `zero`. Establish `hnd : ¬ l ^ 2 ∣ (Finsupp.single (φ (s - 2 * ((0 : ℕ) : ZMod d))) ((l ^ 2) ^ 0)) (φ (s - 2 * ((0 : ℕ) : ZMod d)))`.

Rewrite using `[Finsupp.single_eq_same, pow_zero, Nat.dvd_one]`. Introduce `h`. Use the polynomial consequences of the given equalities and inequalities. Rewrite using `[Formalism.InvariantFactorPaths.G7.coeff_frobVar_of_not_dvd hq _ hnd]`. Simplify using the standard rewrite rules.

Consider the case `succ e`. Establish `hne : Finsupp.single (φ (s - 2 * ((e + 1 : ℕ) : ZMod d))) ((l ^ 2) ^ (e + 1)) ≠ Finsupp.single (φ s) 1`. Introduce `h`. Rewrite `h` using `[Finsupp.single_eq_single_iff]`. Break down `h with ⟨_, h2⟩ | ⟨h2, _⟩` into its components or cases.

Establish `: (l ^ 2) ^ 0 = (l ^ 2) ^ (e + 1)` using `by rw [pow_zero]; exact h2.symm`. Conclude with `absurd (pow_inj hl2 this) (by omega)`. Conclude with `pow_ne_zero _ hq h2`. Rewrite using `[if_neg hne]`. Establish `hsm : Finsupp.single (φ (s - 2 * ((e + 1 : ℕ) : ZMod d))) ((l ^ 2) ^ (e + 1)) = (l ^ 2) • Finsupp.single (φ (s - 2 - 2 * (e : ZMod d))) ((l ^ 2) ^ e)`.

Rewrite using `[hstep, Finsupp.smul_single, smul_eq_mul, ← pow_succ']`. Rewrite using `[hsm, Formalism.InvariantFactorPaths.G7.coeff_frobVar_smul hq, coeff_gLog_single hl2, pow_succ, mul_inv]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [not_exists] at hn`. Rewrite using `[coeff_gLog_zero φ s n hn]`.

Establish `hX : n ≠ Finsupp.single (φ s) 1`. Introduce `h`. Apply `hn 0` to reduce the goal to its premises. Rewrite using `[h]`. Simplify using the standard rewrite rules.

Rewrite using `[if_neg hX]`. Establish `hfz : coeff n (frobVar (l ^ 2) (gLog K l φ (s - 2))) = 0`. Assume the negation of the conclusion as `hne`. Take `⟨m, hm, hm0⟩` from `Formalism.InvariantFactorPaths.G7.coeff_frobVar_ne_zero hq hne`. Distinguish the cases in `hm' : ∃ e : ℕ, m = Finsupp.single (φ (s - 2 - 2 * (e : ZMod d))) ((l ^ 2) ^ e)`.

Take `⟨e, rfl⟩` from `hm'`. Apply `hn (e + 1)` to reduce the goal to its premises. Rewrite using `[hm, hstep, Finsupp.smul_single, smul_eq_mul, ← pow_succ']`. Simplify using `only [not_exists] at hm'`. Conclude with `hm0 (coeff_gLog_zero φ (s - 2) m hm')`.

Rewrite using `[hfz]`. Simplify using the standard rewrite rules.
-/
lemma gLog_shift [CharZero K] (hl : l.Prime) (ρ : K →+* K) (φ : ZMod d → τ) (s : ZMod d) :
    gLog K l φ s - C ((l : K)⁻¹) * frobVar (l ^ 2) (map ρ (gLog K l φ (s - 2))) = X (φ s) := by
  have hl2 : 2 ≤ l := hl.two_le
  have hq : l ^ 2 ≠ 0 := pow_ne_zero _ hl.ne_zero
  have hstep : ∀ e : ℕ, s - 2 * ((e + 1 : ℕ) : ZMod d) = s - 2 - 2 * (e : ZMod d) := by
    intro e
    push_cast
    ring
  rw [map_gLog]
  ext n
  rw [map_sub, coeff_C_mul, coeff_X]
  by_cases hn : ∃ e : ℕ, n = Finsupp.single (φ (s - 2 * (e : ZMod d))) ((l ^ 2) ^ e)
  · obtain ⟨e, rfl⟩ := hn
    rw [coeff_gLog_single hl2]
    cases e with
    | zero =>
      have hnd : ¬ l ^ 2 ∣ (Finsupp.single (φ (s - 2 * ((0 : ℕ) : ZMod d))) ((l ^ 2) ^ 0))
          (φ (s - 2 * ((0 : ℕ) : ZMod d))) := by
        rw [Finsupp.single_eq_same, pow_zero, Nat.dvd_one]
        intro h
        nlinarith
      rw [Formalism.InvariantFactorPaths.G7.coeff_frobVar_of_not_dvd hq _ hnd]
      simp
    | succ e =>
      have hne : Finsupp.single (φ (s - 2 * ((e + 1 : ℕ) : ZMod d))) ((l ^ 2) ^ (e + 1)) ≠
          Finsupp.single (φ s) 1 := by
        intro h
        rw [Finsupp.single_eq_single_iff] at h
        rcases h with ⟨_, h2⟩ | ⟨h2, _⟩
        · have : (l ^ 2) ^ 0 = (l ^ 2) ^ (e + 1) := by rw [pow_zero]; exact h2.symm
          exact absurd (pow_inj hl2 this) (by omega)
        · exact pow_ne_zero _ hq h2
      rw [if_neg hne]
      have hsm : Finsupp.single (φ (s - 2 * ((e + 1 : ℕ) : ZMod d))) ((l ^ 2) ^ (e + 1)) =
          (l ^ 2) • Finsupp.single (φ (s - 2 - 2 * (e : ZMod d))) ((l ^ 2) ^ e) := by
        rw [hstep, Finsupp.smul_single, smul_eq_mul, ← pow_succ']
      rw [hsm, Formalism.InvariantFactorPaths.G7.coeff_frobVar_smul hq, coeff_gLog_single hl2, pow_succ, mul_inv]
      ring
  · simp only [not_exists] at hn
    rw [coeff_gLog_zero φ s n hn]
    have hX : n ≠ Finsupp.single (φ s) 1 := by
      intro h
      apply hn 0
      rw [h]
      simp
    rw [if_neg hX]
    have hfz : coeff n (frobVar (l ^ 2) (gLog K l φ (s - 2))) = 0 := by
      by_contra hne
      obtain ⟨m, hm, hm0⟩ := Formalism.InvariantFactorPaths.G7.coeff_frobVar_ne_zero hq hne
      by_cases hm' : ∃ e : ℕ, m = Finsupp.single (φ (s - 2 - 2 * (e : ZMod d))) ((l ^ 2) ^ e)
      · obtain ⟨e, rfl⟩ := hm'
        apply hn (e + 1)
        rw [hm, hstep, Finsupp.smul_single, smul_eq_mul, ← pow_succ']
      · simp only [not_exists] at hm'
        exact hm0 (coeff_gLog_zero φ (s - 2) m hm')
    rw [hfz]
    simp

end Gen

section Normed

variable {K : Type} [NormedField K] {τ : Type}

/- English proof (translation)
Unfold `Integral`. Introduce `n`. Rewrite using `[coeff_X]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
lemma integral_X' (x : τ) : Integral (X x : MvPowerSeries τ K) := by
  classical
  unfold Integral
  intro n
  rw [coeff_X]
  split_ifs <;> simp

/- English proof (translation)
Introduce `s`. Use `⟨constantCoeff_gLog hl.two_le φ s, ?_⟩` and prove the remaining obligations. Establish `h` using `gLog_shift (K := K) hl (σ.comp σ) φ s`. Use `show Integral (gLog K l φ s - C ((l : K)⁻¹) * frobVar (l ^ 2) (map (σ.comp σ) (gLog K l φ (s - 2))))`. Rewrite using `[h]`.

Conclude with `integral_X' _`.
-/
lemma shiftType_gLog [DecidableEq τ] [CharZero K] {l d : ℕ} (hl : l.Prime) (σ : K →+* K) (φ : ZMod d → τ) :
    ShiftType l σ (fun s : ZMod d => gLog K l φ s) := by
  intro s
  refine ⟨constantCoeff_gLog hl.two_le φ s, ?_⟩
  have h := gLog_shift (K := K) hl (σ.comp σ) φ s
  show Integral (gLog K l φ s - C ((l : K)⁻¹) * frobVar (l ^ 2) (map (σ.comp σ) (gLog K l φ (s - 2))))
  rw [h]
  exact integral_X' _

/- English proof (translation)
Use `⟨((t - 2).val + 2) / d, ?_⟩` and prove the remaining obligations. Establish `h1 : (((t - 2).val + 2 : ℕ) : ZMod d) = ((t.val : ℕ) : ZMod d)` using `by first`. Consider the case `simp`. Consider the case `(push_cast; rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, sub_add_cancel])`. Consider the case `(push_cast; simp)`.

Establish `h2` using `(ZMod.natCast_eq_natCast_iff' _ _ d).mp h1`. Rewrite `h2` using `[Nat.mod_eq_of_lt (ZMod.val_lt t)]`. Establish `h3` using `Nat.mod_add_div ((t - 2).val + 2) d`. Rewrite `h3` using `[h2]`. Conclude with `h3.symm`.
-/
lemma val_sub_two {d : ℕ} [NeZero d] (t : ZMod d) :
    ∃ k : ℕ, (t - 2).val + 2 = t.val + d * k := by
  refine ⟨((t - 2).val + 2) / d, ?_⟩
  have h1 : (((t - 2).val + 2 : ℕ) : ZMod d) = ((t.val : ℕ) : ZMod d) := by
    first
    | simp
    | (push_cast; rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, sub_add_cancel])
    | (push_cast; simp)
  have h2 := (ZMod.natCast_eq_natCast_iff' _ _ d).mp h1
  rw [Nat.mod_eq_of_lt (ZMod.val_lt t)] at h2
  have h3 := Nat.mod_add_div ((t - 2).val + 2) d
  rw [h2] at h3
  exact h3.symm

/- English proof (translation)
Take `⟨k, hk⟩` from `val_sub_two t`. Take `⟨j, hj⟩` from `(even_iff_two_dvd.mp hd).mul_right k`. Rewrite `hk` using `[hj]`. Use linear arithmetic over natural numbers and integers.
-/
lemma parity_sub_two {d : ℕ} [NeZero d] (hd : Even d) (t : ZMod d) :
    (t - 2).val % 2 = t.val % 2 := by
  obtain ⟨k, hk⟩ := val_sub_two t
  obtain ⟨j, hj⟩ := (even_iff_two_dvd.mp hd).mul_right k
  rw [hj] at hk
  omega

/- English proof (translation)
Take `⟨k, hk⟩` from `val_sub_two t`. Establish `h1 : f (f (f^[(t - 2).val] c)) = f^[(t - 2).val + 2] c` using `by first`. Consider the case `(rw [add_comm, Function.iterate_add_apply]; rfl)`. Consider the case `simp only [Function.iterate_succ_apply']`. Rewrite using `[h1, hk, Function.iterate_add_apply, Function.iterate_mul, Function.iterate_fixed hc]`.
-/
lemma iter_sub_two {α : Type} {d : ℕ} [NeZero d] (f : α → α) {c : α} (hc : f^[d] c = c)
    (t : ZMod d) : f (f (f^[(t - 2).val] c)) = f^[t.val] c := by
  obtain ⟨k, hk⟩ := val_sub_two t
  have h1 : f (f (f^[(t - 2).val] c)) = f^[(t - 2).val + 2] c := by
    first
    | (rw [add_comm, Function.iterate_add_apply]; rfl)
    | simp only [Function.iterate_succ_apply']
  rw [h1, hk, Function.iterate_add_apply, Function.iterate_mul, Function.iterate_fixed hc]

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simpa using hc`. Consider the case `succ k ih => rw [Function.iterate_succ_apply']`. Conclude with `hσ _ ih`.
-/
lemma norm_iter {σ : K →+* K} (hσ : ∀ a : K, ‖a‖ ≤ 1 → ‖σ a‖ ≤ 1) {c : K} (hc : ‖c‖ ≤ 1)
    (k : ℕ) : ‖σ^[k] c‖ ≤ 1 := by
  induction k with
  | zero => simpa using hc
  | succ k ih => rw [Function.iterate_succ_apply']; exact hσ _ ih

/- English proof (translation)
Take `⟨a, ha⟩ : ∃ a : ZMod d → K, a = fun s => if P (s.val % 2) then σ^[s.val] c else 0` from `⟨_, rfl⟩`. Establish `hsum : (∑ s : ZMod d, if P (s.val % 2) then C (σ^[s.val] c) * L s else 0) = ∑ s, C (a s) * L s`. Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Apply the tactic sequence `by_cases h : P (s.val % 2) <;> simp [ha, h]`. Establish `hq : l ^ 2 ≠ 0` using `pow_ne_zero _ hl`.

Establish `hshift : ∀ s, (σ.comp σ) (a (s - 2)) = a s`. Introduce `s`. Simplify using `only [ha, parity_sub_two hd s]`. Use `split_ifs`. Rewrite using `[RingHom.comp_apply]`.

Conclude with `iter_sub_two σ hcd s`. Conclude with `map_zero _`. Establish `hle : ∀ s, ‖a s‖ ≤ 1`. Introduce `s`. Simplify using `only [ha]`.

Use `split_ifs`. Conclude with `norm_iter hσ hc _`. Simplify using the standard rewrite rules. Rewrite using `[hsum]`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_sum]`. Use `Finset.sum_eq_zero fun s _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, (hL s).1, mul_zero]`. Establish `key : (∑ s, C (a s) * L s) - C ((l : K)⁻¹) * frobVar (l ^ 2) (map (σ.comp σ) (∑ s, C (a s) * L s)) = ∑ s, C (a s) * (L s - C ((l : K)⁻¹) * frobVar (l ^ 2) (map (σ.comp σ) (L (s - 2))))`. Simplify using `only [Formalism.InvariantFactorPaths.G7.frobVar_eq_expand hq, map_sum, map_mul, MvPowerSeries.map_C, MvPowerSeries.expand_C, Finset.mul_sum, mul_sub, Finset.sum_sub_distrib]`.

Use `congr 1`. Rewrite using `[← (Equiv.subRight (2 : ZMod d)).sum_comp]`. Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Simplify using `only [Equiv.subRight_apply, hshift]`. Expand and normalize the polynomial expressions, which then agree.

Introduce `n`. Rewrite using `[key, map_sum]`. Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun s _ => ?_` and prove the remaining obligations. Rewrite using `[coeff_C_mul, norm_mul]`. Conclude with `mul_le_one₀ (hle s) (norm_nonneg _) ((hL s).2 n)`.
-/
lemma combo [IsUltrametricDist K] {l d : ℕ} [NeZero d] (hl : l ≠ 0) (σ : K →+* K)
    (hσ : ∀ a : K, ‖a‖ ≤ 1 → ‖σ a‖ ≤ 1) (hd : Even d) (L : ZMod d → MvPowerSeries τ K)
    (hL : ShiftType l σ L) {c : K} (hc : ‖c‖ ≤ 1) (hcd : σ^[d] c = c)
    (P : ℕ → Prop) [DecidablePred P] :
    IP l σ (∑ s : ZMod d, if P (s.val % 2) then C (σ^[s.val] c) * L s else 0) := by
  classical
  obtain ⟨a, ha⟩ : ∃ a : ZMod d → K, a = fun s => if P (s.val % 2) then σ^[s.val] c else 0 :=
    ⟨_, rfl⟩
  have hsum : (∑ s : ZMod d, if P (s.val % 2) then C (σ^[s.val] c) * L s else 0) =
      ∑ s, C (a s) * L s := by
    refine Finset.sum_congr rfl fun s _ => ?_
    by_cases h : P (s.val % 2) <;> simp [ha, h]
  have hq : l ^ 2 ≠ 0 := pow_ne_zero _ hl
  have hshift : ∀ s, (σ.comp σ) (a (s - 2)) = a s := by
    intro s
    simp only [ha, parity_sub_two hd s]
    split_ifs
    · rw [RingHom.comp_apply]
      exact iter_sub_two σ hcd s
    · exact map_zero _
  have hle : ∀ s, ‖a s‖ ≤ 1 := by
    intro s
    simp only [ha]
    split_ifs
    · exact norm_iter hσ hc _
    · simp
  rw [hsum]
  refine ⟨?_, ?_⟩
  · rw [map_sum]
    refine Finset.sum_eq_zero fun s _ => ?_
    rw [map_mul, (hL s).1, mul_zero]
  · have key : (∑ s, C (a s) * L s) - C ((l : K)⁻¹) *
          frobVar (l ^ 2) (map (σ.comp σ) (∑ s, C (a s) * L s)) =
        ∑ s, C (a s) * (L s - C ((l : K)⁻¹) * frobVar (l ^ 2) (map (σ.comp σ) (L (s - 2)))) := by
      simp only [Formalism.InvariantFactorPaths.G7.frobVar_eq_expand hq, map_sum, map_mul, MvPowerSeries.map_C,
        MvPowerSeries.expand_C, Finset.mul_sum, mul_sub, Finset.sum_sub_distrib]
      congr 1
      rw [← (Equiv.subRight (2 : ZMod d)).sum_comp]
      refine Finset.sum_congr rfl fun s _ => ?_
      simp only [Equiv.subRight_apply, hshift]
      ring
    intro n
    rw [key, map_sum]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun s _ => ?_
    rw [coeff_C_mul, norm_mul]
    exact mul_le_one₀ (hle s) (norm_nonneg _) ((hL s).2 n)

end Normed

end KernelCokernelKilling

open KernelCokernelKilling in
/- English proof (translation)
Unfold `LetterShift`. Introduce `K _ _ _ l d _ σ hl`. Use `⟨fun b => ?_, ?_, fun N0 N1 a b => ?_⟩` and prove the remaining obligations. Conclude with `shiftType_gLog (K := K) hl σ (fun s : ZMod d => (b, s))`. Conclude with `shiftType_gLog (K := K) hl σ (fun s : ZMod d => s)`.

Conclude with `shiftType_gLog (K := K) hl σ (fun s : ZMod d => ((s, a, b) : ZMod d × Fin N0 × Fin N1))`.
-/
theorem letter_shift : LetterShift := by
  unfold LetterShift
  intro K _ _ _ l d _ σ hl
  refine ⟨fun b => ?_, ?_, fun N0 N1 a b => ?_⟩
  · exact shiftType_gLog (K := K) hl σ (fun s : ZMod d => (b, s))
  · exact shiftType_gLog (K := K) hl σ (fun s : ZMod d => s)
  · exact shiftType_gLog (K := K) hl σ (fun s : ZMod d => ((s, a, b) : ZMod d × Fin N0 × Fin N1))

open KernelCokernelKilling in
/- English proof (translation)
Introduce `hF`. Unfold `ShiftIP`. Introduce `K _ _ _ l d _ σ hU hd τ _ L hL c hc hcd`. Establish `hσ` using `(hF K l σ hU).2`. Establish `hl0 : l ≠ 0` using `hU.1.ne_zero`.

Prove the components needed by the constructor for the conclusion. Establish `h` using `combo hl0 σ hσ hd L hL hc hcd (fun x => x = 0)`. Unfold `linEL`. Conclude with `h`. Establish `h` using `combo hl0 σ hσ hd L hL hc hcd (fun x => ¬ x = 0)`.

Unfold `linOL`. Simplify `h` using `only [ite_not]`.
-/
theorem ShiftIP_of_frobSq : FrobSq → ShiftIP := by
  intro hF
  unfold ShiftIP
  intro K _ _ _ l d _ σ hU hd τ _ L hL c hc hcd
  have hσ := (hF K l σ hU).2
  have hl0 : l ≠ 0 := hU.1.ne_zero
  constructor
  · have h := combo hl0 σ hσ hd L hL hc hcd (fun x => x = 0)
    unfold linEL
    exact h
  · have h := combo hl0 σ hσ hd L hL hc hcd (fun x => ¬ x = 0)
    unfold linOL
    simpa only [ite_not] using h

end Formalism.L2.Th1.D
