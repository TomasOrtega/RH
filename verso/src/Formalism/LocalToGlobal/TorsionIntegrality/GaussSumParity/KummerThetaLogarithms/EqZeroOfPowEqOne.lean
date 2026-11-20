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
Treat this case separately. Treat this case separately. A detailed English derivation is pending.
-/
lemma pow_inj (hl : 2 ≤ l) {a b : ℕ} (h : (l ^ 2) ^ a = (l ^ 2) ^ b) : a = b := by
  first
  | exact Nat.pow_right_injective (by nlinarith) h
  | exact Nat.pow_right_injective (le_trans hl (Nat.le_self_pow (by norm_num) l)) h

/- English proof (translation)
Treat this case separately. Treat this case separately. A detailed English derivation is pending.
-/
lemma coeff_gLog (φ : ZMod d → τ) (s : ZMod d) (n : τ →₀ ℕ) :
    coeff n (gLog K l φ s) = ∑ e ∈ Finset.range (n.degree + 1),
      if n = Finsupp.single (φ (s - 2 * (e : ZMod d))) ((l ^ 2) ^ e) then ((l : K) ^ e)⁻¹ else 0 := by
  first
  | rfl
  | simp [gLog, coeff_apply]

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Rewrite the indicated hypotheses using the stated equalities. Separate the alternatives or extract the components of the hypothesis. Fix the arbitrary inputs or assume the hypotheses.

It suffices to derive a contradiction. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Treat this case separately.

Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Treat this case separately.

Treat this case separately. Treat this case separately. Treat this case separately. A detailed English derivation is pending.
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
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
lemma coeff_gLog_zero (φ : ZMod d → τ) (s : ZMod d) (n : τ →₀ ℕ)
    (h : ∀ e : ℕ, n ≠ Finsupp.single (φ (s - 2 * (e : ZMod d))) ((l ^ 2) ^ e)) :
    coeff n (gLog K l φ s) = 0 := by
  rw [coeff_gLog]
  exact Finset.sum_eq_zero fun e _ => if_neg (h e)

/- English proof (translation)
By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Apply the first step, then apply the next step to every resulting obligation.
-/
lemma map_gLog (ρ : K →+* K) (φ : ZMod d → τ) (s : ZMod d) :
    map ρ (gLog K l φ s) = gLog K l φ s := by
  ext n
  rw [coeff_map, coeff_gLog, map_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  split_ifs <;> simp

/- English proof (translation)
Treat this case separately. Treat this case separately. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities.

A detailed English derivation is pending.
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
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Move the embeddings inside the algebraic operations.

Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails.

Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Split into cases according to the possible forms of the given data. Treat this case separately. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Use the polynomial consequences of the given equalities and inequalities. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Treat this case separately. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Separate the alternatives or extract the components of the hypothesis.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Assume the negation of the conclusion and derive a contradiction. Extract witnesses or component facts from the available result. Consider separately whether the proposition holds or fails. Extract witnesses or component facts from the available result. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
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
Replace the relevant objects with their definitions. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation.
-/
lemma integral_X' (x : τ) : Integral (X x : MvPowerSeries τ K) := by
  classical
  unfold Integral
  intro n
  rw [coeff_X]
  split_ifs <;> simp

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Treat this case separately. Treat this case separately. Treat this case separately.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
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
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities. Use linear arithmetic over natural numbers and integers.
-/
lemma parity_sub_two {d : ℕ} [NeZero d] (hd : Even d) (t : ZMod d) :
    (t - 2).val % 2 = t.val % 2 := by
  obtain ⟨k, hk⟩ := val_sub_two t
  obtain ⟨j, hj⟩ := (even_iff_two_dvd.mp hd).mul_right k
  rw [hj] at hk
  omega

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities.
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
Proceed by induction. Treat this case separately. Treat this case separately. A detailed English derivation is pending.
-/
lemma norm_iter {σ : K →+* K} (hσ : ∀ a : K, ‖a‖ ≤ 1 → ‖σ a‖ ≤ 1) {c : K} (hc : ‖c‖ ≤ 1)
    (k : ℕ) : ‖σ^[k] c‖ ≤ 1 := by
  induction k with
  | zero => simpa using hc
  | succ k ih => rw [Function.iterate_succ_apply']; exact hσ _ ih

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Apply the first step, then apply the next step to every resulting obligation. Establish an intermediate fact.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules.

Reduce the equality to equality of the corresponding arguments. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
Replace the relevant objects with their definitions. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
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
Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact.

Prove the components needed by the constructor for the conclusion. Establish an intermediate fact. Replace the relevant objects with their definitions. Establish an intermediate fact. Replace the relevant objects with their definitions.

Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
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
