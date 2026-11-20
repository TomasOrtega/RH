import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPairingSingleNe
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainOnto

/- English proof (translation)
Simplify using `[Multiset.esymm, Multiset.powersetCard_cons, Multiset.map_map, Multiset.sum_map_mul_left]`.
-/
theorem esymm_cons_succ_C (a : ℂ) (s : Multiset ℂ) (n : ℕ) :
    (a ::ₘ s).esymm (n + 1) = s.esymm (n + 1) + a * s.esymm n := by
  simp [Multiset.esymm, Multiset.powersetCard_cons, Multiset.map_map, Multiset.sum_map_mul_left]

/- English proof (translation)
Proceed by induction on `s using Multiset.induction_on generalizing n with`. Consider the case `empty`. Consider the cases of `n with`. Consider the case `zero => simp [Multiset.esymm]`. Consider the case `succ n => simp [Multiset.esymm, Polynomial.coeff_one, Multiset.powersetCard_zero_right]`.

Consider the case `cons a s ih`. Rewrite using `[Multiset.map_cons, Multiset.prod_cons, add_mul, one_mul, mul_assoc, Polynomial.coeff_add, Polynomial.coeff_C_mul]`. Consider the cases of `n with`. Consider the case `zero => simp [ih, Multiset.esymm]`. Consider the case `succ n => rw [Polynomial.coeff_X_mul, ih, ih, esymm_cons_succ_C]`.
-/
theorem coeff_prod_one_add_C (s : Multiset ℂ) (n : ℕ) :
    ((s.map fun a => (1 + Polynomial.C a * Polynomial.X : Polynomial ℂ)).prod).coeff n = s.esymm n := by
  induction s using Multiset.induction_on generalizing n with
  | empty =>
    cases n with
    | zero => simp [Multiset.esymm]
    | succ n => simp [Multiset.esymm, Polynomial.coeff_one, Multiset.powersetCard_zero_right]
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, add_mul, one_mul, mul_assoc, Polynomial.coeff_add,
      Polynomial.coeff_C_mul]
    cases n with
    | zero => simp [ih, Multiset.esymm]
    | succ n => rw [Polynomial.coeff_X_mul, ih, ih, esymm_cons_succ_C]

/- English proof (translation)
Rewrite using `[← coeff_prod_one_add_C, Multiset.map_add, Multiset.prod_add, Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]`. Simplify using `only [coeff_prod_one_add_C]`.
-/
theorem esymm_add_C (s t : Multiset ℂ) (n : ℕ) :
    (s + t).esymm n = ∑ i ∈ Finset.range (n + 1), s.esymm i * t.esymm (n - i) := by
  rw [← coeff_prod_one_add_C, Multiset.map_add, Multiset.prod_add, Polynomial.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [coeff_prod_one_add_C]

/- English proof (translation)
Establish `h` using `Multiset.pow_smul_esymm c k s`. Simplify `h.symm` using `[smul_eq_mul]`.
-/
theorem esymm_map_mul_C (c : ℂ) (s : Multiset ℂ) (k : ℕ) :
    (s.map (fun x => c * x)).esymm k = c ^ k * s.esymm k := by
  have h := Multiset.pow_smul_esymm c k s
  simpa [smul_eq_mul] using h.symm

/- English proof (translation)
Simplify using `[Multiset.esymm, Multiset.powersetCard_eq_empty k h]`.
-/
theorem esymm_eq_zero_of_lt (s : Multiset ℂ) {k : ℕ} (h : s.card < k) : s.esymm k = 0 := by
  simp [Multiset.esymm, Multiset.powersetCard_eq_empty k h]

/- English proof (translation)
Establish `h1 : ((Real.sqrt Q : ℝ) : ℂ) = (Q : ℂ) ^ ((1 / 2 : ℂ))`. Rewrite using `[Real.sqrt_eq_rpow, Complex.ofReal_cpow (Nat.cast_nonneg _)]`. Use `push_cast`. Both sides reduce to the same expression. Rewrite using `[h1, ← Complex.cpow_int_mul]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem natCast_cpow_half (Q : ℕ) (m : ℤ) :
    (Q : ℂ) ^ ((m : ℂ) / 2) = ((Real.sqrt Q : ℝ) : ℂ) ^ m := by
  have h1 : ((Real.sqrt Q : ℝ) : ℂ) = (Q : ℂ) ^ ((1 / 2 : ℂ)) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (Nat.cast_nonneg _)]
    push_cast
    rfl
  rw [h1, ← Complex.cpow_int_mul]
  congr 1
  ring

/- English proof (translation)
Rewrite using `[← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]`. Use `push_cast`. Both sides reduce to the same expression.
-/
theorem sqrt_sq_C (Q : ℕ) : ((Real.sqrt Q : ℝ) : ℂ) ^ 2 = (Q : ℂ) := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  push_cast
  rfl

/- English proof (translation)
Proceed by induction on `t with`. Consider the case `zero`. Introduce `l`. Consider the cases of `l with`. Consider the case `zero => simp [Multiset.esymm, Formalism.L2.Col.gaussBin]`.

Consider the case `succ l => simp [Multiset.esymm, Formalism.L2.Col.gaussBin, Multiset.powersetCard_zero_right]`. Consider the case `succ t ih`. Introduce `l`. Establish `hm : ((Finset.range (t + 1)).val.map fun i : ℕ => z * s ^ (((t + 1 : ℕ) : ℤ) - 1 - 2 * i)) = (z * s ^ (-(t : ℤ))) ::ₘ (((Finset.range t).val.map fun i : ℕ => z * s ^ ((t : ℤ) - 1 - 2 * i)).map fun x => s * x)`. Rewrite using `[Finset.range_val, Finset.range_val, Multiset.range_succ, Multiset.map_cons, Multiset.map_map]`.

Use `congr 1`. Use `congr 1`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Use `Multiset.map_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only [Function.comp_apply]`. Rewrite using `[mul_left_comm]`. Use `congr 1`. Rewrite using `[show (((t + 1 : ℕ) : ℤ) - 1 - 2 * i) = 1 + ((t : ℤ) - 1 - 2 * i) by push_cast; ring, zpow_add₀ hs, zpow_one]`.

Rewrite using `[hm]`. Consider the cases of `l with`. Consider the case `zero => simp [Multiset.esymm, Formalism.L2.Col.gaussBin]`. Consider the case `succ l`. Rewrite using `[esymm_cons_succ_C, esymm_map_mul_C, esymm_map_mul_C, ih, ih, Formalism.L2.Col.gaussBin]`.

Use `push_cast`. Rewrite using `[← hQ]`. Establish `h1 : s ^ (l + 1) * s ^ (-(((l : ℤ) + 1) * ((t : ℤ) - ((l : ℤ) + 1)))) = s ^ (-(((l : ℤ) + 1) * ((t : ℤ) + 1 - ((l : ℤ) + 1)))) * (s ^ 2) ^ (l + 1)`. Rewrite using `[← pow_mul, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hs, ← zpow_add₀ hs]`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `h2 : s ^ (-(t : ℤ)) * s ^ l * s ^ (-((l : ℤ) * ((t : ℤ) - l))) = s ^ (-(((l : ℤ) + 1) * ((t : ℤ) + 1 - ((l : ℤ) + 1))))`. Rewrite using `[← zpow_natCast, ← zpow_add₀ hs, ← zpow_add₀ hs]`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Take the linear combination `(z ^ (l + 1) * (Formalism.L2.Col.gaussBin Q t (l + 1) : ℂ)) * h1 + (z ^ (l + 1) * (Formalism.L2.Col.gaussBin Q t l : ℂ)) * h2`.
-/
theorem esymm_string (Q : ℕ) (s z : ℂ) (hs : s ≠ 0) (hQ : s ^ 2 = (Q : ℂ)) (t : ℕ) :
    ∀ l : ℕ, ((Finset.range t).val.map fun i : ℕ => z * s ^ ((t : ℤ) - 1 - 2 * i)).esymm l =
      z ^ l * s ^ (-((l : ℤ) * ((t : ℤ) - l))) * (Formalism.L2.Col.gaussBin Q t l : ℂ) := by
  induction t with
  | zero =>
    intro l
    cases l with
    | zero => simp [Multiset.esymm, Formalism.L2.Col.gaussBin]
    | succ l => simp [Multiset.esymm, Formalism.L2.Col.gaussBin, Multiset.powersetCard_zero_right]
  | succ t ih =>
    intro l
    have hm : ((Finset.range (t + 1)).val.map fun i : ℕ => z * s ^ (((t + 1 : ℕ) : ℤ) - 1 - 2 * i)) =
        (z * s ^ (-(t : ℤ))) ::ₘ (((Finset.range t).val.map fun i : ℕ => z * s ^ ((t : ℤ) - 1 - 2 * i)).map
          fun x => s * x) := by
      rw [Finset.range_val, Finset.range_val, Multiset.range_succ, Multiset.map_cons, Multiset.map_map]
      congr 1
      · congr 1; congr 1; push_cast; ring
      · refine Multiset.map_congr rfl fun i _ => ?_
        simp only [Function.comp_apply]
        rw [mul_left_comm]
        congr 1
        rw [show (((t + 1 : ℕ) : ℤ) - 1 - 2 * i) = 1 + ((t : ℤ) - 1 - 2 * i) by push_cast; ring,
          zpow_add₀ hs, zpow_one]
    rw [hm]
    cases l with
    | zero => simp [Multiset.esymm, Formalism.L2.Col.gaussBin]
    | succ l =>
      rw [esymm_cons_succ_C, esymm_map_mul_C, esymm_map_mul_C, ih, ih, Formalism.L2.Col.gaussBin]
      push_cast
      rw [← hQ]
      have h1 : s ^ (l + 1) * s ^ (-(((l : ℤ) + 1) * ((t : ℤ) - ((l : ℤ) + 1)))) =
          s ^ (-(((l : ℤ) + 1) * ((t : ℤ) + 1 - ((l : ℤ) + 1)))) * (s ^ 2) ^ (l + 1) := by
        rw [← pow_mul, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hs, ← zpow_add₀ hs]
        congr 1; push_cast; ring
      have h2 : s ^ (-(t : ℤ)) * s ^ l * s ^ (-((l : ℤ) * ((t : ℤ) - l))) =
          s ^ (-(((l : ℤ) + 1) * ((t : ℤ) + 1 - ((l : ℤ) + 1)))) := by
        rw [← zpow_natCast, ← zpow_add₀ hs, ← zpow_add₀ hs]
        congr 1; push_cast; ring
      linear_combination (z ^ (l + 1) * (Formalism.L2.Col.gaussBin Q t (l + 1) : ℂ)) * h1 +
        (z ^ (l + 1) * (Formalism.L2.Col.gaussBin Q t l : ℂ)) * h2

/- English proof (translation)
Rewrite using `[seg, Multiset.map_map]`. Use `Multiset.map_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only [Function.comp_apply, Units.val_mul, coe_npowU, npow]`. Use `congr 1`. Rewrite using `[← natCast_cpow_half]`.

Use `show ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ _ = ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ _`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem map_coe_seg (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (z : ℂˣ) (t : ℕ) :
    (seg w z t).map (fun b : ℂˣ => (b : ℂ)) =
      (Finset.range t).val.map fun i : ℕ => (z : ℂ) * ((Real.sqrt (qV E w) : ℝ) : ℂ) ^ ((t : ℤ) - 1 - 2 * i) := by
  rw [seg, Multiset.map_map]
  refine Multiset.map_congr rfl fun i _ => ?_
  simp only [Function.comp_apply, Units.val_mul, coe_npowU, npow]
  congr 1
  rw [← natCast_cpow_half]
  show ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ _ = ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ _
  congr 1
  push_cast
  ring

/- English proof (translation)
Introduce `E _ _ w a t k B z y hB _`. Establish `hsQ` using `sqrt_sq_C (qV E w)`. Establish `hs : ((Real.sqrt (qV E w) : ℝ) : ℂ) ≠ 0`. Introduce `h0`. Rewrite `hsQ` using `[h0]`.

Establish `h1 : 1 < qV E w` using `one_lt_absNorm w`. Establish `: ((qV E w : ℕ) : ℂ) = 0` using `by rw [← hsQ]; ring`. Conclude with `(by omega : qV E w ≠ 0) (by exact_mod_cast this)`. Establish `hA : (B.map (z * y⁻¹ * ·)).map (fun b : ℂˣ => (b : ℂ)) = (B.map fun b : ℂˣ => (b : ℂ)).map fun x => ((z : ℂ) * (y : ℂ)⁻¹) * x`. Simplify using `[Multiset.map_map, Function.comp_def]`.

Establish `hBc : (B.map fun b : ℂˣ => (b : ℂ)).card = a` using `by simp [hB]`. Use `set Q := qV E w with hQdef`. Use `set s : ℂ := ((Real.sqrt Q : ℝ) : ℂ) with hsdef`. Use `set F : ℕ → ℂ := fun j => (if j ≤ k then (Q : ℂ) ^ ((a - j) * (k - j)) * (Formalism.L2.Col.gaussBin Q t (k - j) : ℂ) * ((z : ℂ) * (s ^ a)⁻¹) ^ k * (((y : ℂ))⁻¹ * s ^ (a + t)) ^ j else 0) * satEig Q a B j with hF`. Establish `hFa : ∀ j, a < j → F j = 0`.

Introduce `j hj`. Simplify using `only [hF, satEig, esymm_eq_zero_of_lt _ (hBc ▸ hj), mul_zero]`. Establish `hFk : ∀ j, k < j → F j = 0`. Introduce `j hj`. Simplify using `only [hF, if_neg (show ¬ j ≤ k by omega), zero_mul]`.

Establish `hR : ∑ j ∈ Finset.range (a + 1), F j = ∑ j ∈ Finset.range (k + 1), F j`. Rewrite using `[Finset.sum_subset (Finset.range_mono (show a + 1 ≤ a + k + 1 by omega)) (fun j _ hn => hFa j (by simp at hn; omega)), Finset.sum_subset (Finset.range_mono (show k + 1 ≤ a + k + 1 by omega)) (fun j _ hn => hFk j (by simp at hn; omega))]`. Rewrite using `[hR, satEig, Multiset.map_add, esymm_add_C, Finset.mul_sum, hA, map_coe_seg]`. Use `Finset.sum_congr rfl fun j hj => ?_` and prove the remaining obligations. Establish `hjk : j ≤ k` using `Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)`.

Rewrite using `[esymm_map_mul_C, esymm_string Q s z hs hsQ t]`. Distinguish the cases in `hja : j ≤ a`. Simplify using `only [hF, if_pos hjk, satEig]`. Establish `c1 : (Q : ℂ) ^ (((k : ℂ) * (((a + t : ℕ) : ℂ) - k)) / 2) = s ^ ((k : ℤ) * ((a : ℤ) + t - k))`. Rewrite using `[← natCast_cpow_half]`.

Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `c2 : (Q : ℂ) ^ (((j : ℂ) * ((a : ℂ) - j)) / 2) = s ^ ((j : ℤ) * ((a : ℤ) - j))`. Rewrite using `[← natCast_cpow_half]`.

Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[c1, c2]`. Establish `hz : ((z : ℂ) * (y : ℂ)⁻¹) ^ j * (z : ℂ) ^ (k - j) = (z : ℂ) ^ k * ((y : ℂ)⁻¹) ^ j`.

Rewrite using `[mul_pow, mul_right_comm, ← pow_add, Nat.add_sub_cancel' hjk]`. Establish `hsI : s ^ ((k : ℤ) * ((a : ℤ) + t - k)) * s ^ (-(((k - j : ℕ) : ℤ) * ((t : ℤ) - ((k - j : ℕ) : ℤ)))) = (s ^ 2) ^ ((a - j) * (k - j)) * ((s ^ a)⁻¹) ^ k * (s ^ (a + t)) ^ j * s ^ ((j : ℤ) * ((a : ℤ) - j))`. Simplify using `only [← pow_mul, inv_pow, ← zpow_natCast, ← _root_.zpow_neg, ← _root_.zpow_mul, ← zpow_add₀ hs]`. Use `congr 1`. Move the coercions through the operations in `[Nat.cast_sub hja, Nat.cast_sub hjk]`.

Expand and normalize the polynomial expressions, which then agree. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[esymm_eq_zero_of_lt _ (by omega), hFa j (by omega)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem satEig_map_add_seg : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (a t k : ℕ) (B : Multiset ℂˣ) (z y : ℂˣ), B.card = a → k ≤ a + t → satEig (qV E w) (a + t) (B.map (z * y⁻¹ * ·) + seg w z t) k = ∑ j ∈ Finset.range (a + 1), (if j ≤ k then (qV E w : ℂ) ^ ((a - j) * (k - j)) * (Formalism.L2.Col.gaussBin (qV E w) t (k - j) : ℂ) * ((z : ℂ) * ((Real.sqrt (qV E w) : ℂ) ^ a)⁻¹) ^ k * (((y : ℂ))⁻¹ * (Real.sqrt (qV E w) : ℂ) ^ (a + t)) ^ j else 0) * satEig (qV E w) a B j := by
  intro E _ _ w a t k B z y hB _
  have hsQ := sqrt_sq_C (qV E w)
  have hs : ((Real.sqrt (qV E w) : ℝ) : ℂ) ≠ 0 := by
    intro h0
    rw [h0] at hsQ
    have h1 : 1 < qV E w := one_lt_absNorm w
    have : ((qV E w : ℕ) : ℂ) = 0 := by rw [← hsQ]; ring
    exact (by omega : qV E w ≠ 0) (by exact_mod_cast this)
  have hA : (B.map (z * y⁻¹ * ·)).map (fun b : ℂˣ => (b : ℂ)) =
      (B.map fun b : ℂˣ => (b : ℂ)).map fun x => ((z : ℂ) * (y : ℂ)⁻¹) * x := by
    simp [Multiset.map_map, Function.comp_def]
  have hBc : (B.map fun b : ℂˣ => (b : ℂ)).card = a := by simp [hB]
  set Q := qV E w with hQdef
  set s : ℂ := ((Real.sqrt Q : ℝ) : ℂ) with hsdef
  set F : ℕ → ℂ := fun j => (if j ≤ k then (Q : ℂ) ^ ((a - j) * (k - j)) * (Formalism.L2.Col.gaussBin Q t (k - j) : ℂ) *
    ((z : ℂ) * (s ^ a)⁻¹) ^ k * (((y : ℂ))⁻¹ * s ^ (a + t)) ^ j else 0) * satEig Q a B j with hF
  have hFa : ∀ j, a < j → F j = 0 := by
    intro j hj
    simp only [hF, satEig, esymm_eq_zero_of_lt _ (hBc ▸ hj), mul_zero]
  have hFk : ∀ j, k < j → F j = 0 := by
    intro j hj
    simp only [hF, if_neg (show ¬ j ≤ k by omega), zero_mul]
  have hR : ∑ j ∈ Finset.range (a + 1), F j = ∑ j ∈ Finset.range (k + 1), F j := by
    rw [Finset.sum_subset (Finset.range_mono (show a + 1 ≤ a + k + 1 by omega))
        (fun j _ hn => hFa j (by simp at hn; omega)),
      Finset.sum_subset (Finset.range_mono (show k + 1 ≤ a + k + 1 by omega))
        (fun j _ hn => hFk j (by simp at hn; omega))]
  rw [hR, satEig, Multiset.map_add, esymm_add_C, Finset.mul_sum, hA, map_coe_seg]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjk : j ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  rw [esymm_map_mul_C, esymm_string Q s z hs hsQ t]
  by_cases hja : j ≤ a
  · simp only [hF, if_pos hjk, satEig]
    have c1 : (Q : ℂ) ^ (((k : ℂ) * (((a + t : ℕ) : ℂ) - k)) / 2) = s ^ ((k : ℤ) * ((a : ℤ) + t - k)) := by
      rw [← natCast_cpow_half]; congr 1; push_cast; ring
    have c2 : (Q : ℂ) ^ (((j : ℂ) * ((a : ℂ) - j)) / 2) = s ^ ((j : ℤ) * ((a : ℤ) - j)) := by
      rw [← natCast_cpow_half]; congr 1; push_cast; ring
    rw [c1, c2]
    have hz : ((z : ℂ) * (y : ℂ)⁻¹) ^ j * (z : ℂ) ^ (k - j) = (z : ℂ) ^ k * ((y : ℂ)⁻¹) ^ j := by
      rw [mul_pow, mul_right_comm, ← pow_add, Nat.add_sub_cancel' hjk]
    have hsI : s ^ ((k : ℤ) * ((a : ℤ) + t - k)) * s ^ (-(((k - j : ℕ) : ℤ) * ((t : ℤ) - ((k - j : ℕ) : ℤ)))) =
        (s ^ 2) ^ ((a - j) * (k - j)) * ((s ^ a)⁻¹) ^ k * (s ^ (a + t)) ^ j * s ^ ((j : ℤ) * ((a : ℤ) - j)) := by
      simp only [← pow_mul, inv_pow, ← zpow_natCast, ← _root_.zpow_neg, ← _root_.zpow_mul, ← zpow_add₀ hs]
      congr 1
      push_cast [Nat.cast_sub hja, Nat.cast_sub hjk]
      ring
    calc _ = (s ^ ((k : ℤ) * ((a : ℤ) + t - k)) * s ^ (-(((k - j : ℕ) : ℤ) * ((t : ℤ) - ((k - j : ℕ) : ℤ))))) *
          (((z : ℂ) * (y : ℂ)⁻¹) ^ j * (z : ℂ) ^ (k - j)) *
          ((Formalism.L2.Col.gaussBin Q t (k - j) : ℂ) * (B.map fun b : ℂˣ => (b : ℂ)).esymm j) := by ring
      _ = ((s ^ 2) ^ ((a - j) * (k - j)) * ((s ^ a)⁻¹) ^ k * (s ^ (a + t)) ^ j * s ^ ((j : ℤ) * ((a : ℤ) - j))) *
          ((z : ℂ) ^ k * ((y : ℂ)⁻¹) ^ j) *
          ((Formalism.L2.Col.gaussBin Q t (k - j) : ℂ) * (B.map fun b : ℂˣ => (b : ℂ)).esymm j) := by rw [hsI, hz]
      _ = _ := by rw [hsQ]; ring
  · rw [esymm_eq_zero_of_lt _ (by omega), hFa j (by omega)]
    ring

end GlobalTheory.ChainOnto
