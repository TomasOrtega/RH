import Mathlib
import Development.AutomorphicSpectrum.Definitions.TwistedFlags.ReachOrth
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstMemBddAut
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnramifiedCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import GroundTheory.PAdicHodge.AInfGalois
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars (EigSys badPl IsIP IsUp IsUpTop topStep IsLValue)
open GlobalTheory.LFun (Fam twist segFam seg val above IsCont Bounded IsSysParamD IsParamFunV UnrAt)
open GlobalTheory.CompanionTheory.OntoAll
open GlobalTheory.Hk3 GlobalTheory.CompanionTheory.Ipf.Aut
open GlobalTheory.Chain (ChainPar IsStepWeil IsVacVec ptOf expS expT)
open GlobalTheory.PairLift (Inputs RulePar)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Ipf.Aut.GaussEsym

/- English proof (translation)
Rewrite using `[Multiset.esymm, Multiset.powersetCard_eq_empty _ (by simp)]`. Simplify using the standard rewrite rules.
-/
theorem esymm_zero_succ (k : ℕ) : (0 : Multiset ℂ).esymm (k + 1) = 0 := by
  rw [Multiset.esymm, Multiset.powersetCard_eq_empty _ (by simp)]
  simp

/- English proof (translation)
Simplify using `[Multiset.esymm, Multiset.powersetCard_cons, Multiset.sum_map_mul_left]`.
-/
theorem esymm_cons_succ (b : ℂ) (M : Multiset ℂ) (n : ℕ) :
    (b ::ₘ M).esymm (n + 1) = M.esymm (n + 1) + b * M.esymm n := by
  simp [Multiset.esymm, Multiset.powersetCard_cons, Multiset.sum_map_mul_left]

/- English proof (translation)
Simplify using `[Multiset.esymm]`.
-/
theorem esymm_at_zero (M : Multiset ℂ) : M.esymm 0 = 1 := by
  simp [Multiset.esymm]

/- English proof (translation)
Proceed by induction on `M using Multiset.induction_on with`. Consider the case `empty`. Introduce `k`. Consider the cases of `k with`. Consider the case `zero => simp [esymm_at_zero]`.

Consider the case `succ k => simp [esymm_zero_succ]`. Consider the case `cons b M ih`. Introduce `k`. Consider the cases of `k with`. Consider the case `zero => simp [esymm_at_zero]`.

Consider the case `succ k`. Rewrite using `[Multiset.map_cons, esymm_cons_succ, esymm_cons_succ, ih, ih]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem esymm_map_mul (c : ℂ) (M : Multiset ℂ) : ∀ k : ℕ,
    (M.map (c * ·)).esymm k = c ^ k * M.esymm k := by
  induction M using Multiset.induction_on with
  | empty =>
    intro k
    cases k with
    | zero => simp [esymm_at_zero]
    | succ k => simp [esymm_zero_succ]
  | cons b M ih =>
    intro k
    cases k with
    | zero => simp [esymm_at_zero]
    | succ k =>
      rw [Multiset.map_cons, esymm_cons_succ, esymm_cons_succ, ih, ih]
      ring

/- English proof (translation)
Proceed by induction on `A using Multiset.induction_on with`. Consider the case `empty`. Introduce `k`. Rewrite using `[Finset.sum_range_succ', Finset.sum_eq_zero]`. Simplify using `[esymm_at_zero]`.

Introduce `j _`. Rewrite using `[esymm_zero_succ, zero_mul]`. Consider the case `cons b A ih`. Introduce `k`. Consider the cases of `k with`.

Consider the case `zero => simp [esymm_at_zero]`. Consider the case `succ k`. Rewrite using `[Multiset.cons_add, esymm_cons_succ, ih, ih, Finset.sum_range_succ' _ (k + 1), Finset.sum_range_succ' _ (k + 1), Finset.mul_sum, esymm_at_zero, esymm_at_zero]`. Establish `: ∀ j ∈ Finset.range (k + 1), (b ::ₘ A).esymm (j + 1) * C.esymm (k + 1 - (j + 1)) = A.esymm (j + 1) * C.esymm (k + 1 - (j + 1)) + b * (A.esymm j * C.esymm (k - j))`. Introduce `j _`.

Rewrite using `[esymm_cons_succ, Nat.add_sub_add_right]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Finset.sum_congr rfl this, Finset.sum_add_distrib]`. Simplify using `only [Nat.sub_zero]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem esymm_add (A C : Multiset ℂ) : ∀ k : ℕ,
    (A + C).esymm k = ∑ j ∈ Finset.range (k + 1), A.esymm j * C.esymm (k - j) := by
  induction A using Multiset.induction_on with
  | empty =>
    intro k
    rw [Finset.sum_range_succ', Finset.sum_eq_zero]
    · simp [esymm_at_zero]
    · intro j _
      rw [esymm_zero_succ, zero_mul]
  | cons b A ih =>
    intro k
    cases k with
    | zero => simp [esymm_at_zero]
    | succ k =>
      rw [Multiset.cons_add, esymm_cons_succ, ih, ih, Finset.sum_range_succ' _ (k + 1),
        Finset.sum_range_succ' _ (k + 1), Finset.mul_sum, esymm_at_zero, esymm_at_zero]
      have : ∀ j ∈ Finset.range (k + 1), (b ::ₘ A).esymm (j + 1) * C.esymm (k + 1 - (j + 1)) =
          A.esymm (j + 1) * C.esymm (k + 1 - (j + 1)) + b * (A.esymm j * C.esymm (k - j)) := by
        intro j _
        rw [esymm_cons_succ, Nat.add_sub_add_right]
        ring
      rw [Finset.sum_congr rfl this, Finset.sum_add_distrib]
      simp only [Nat.sub_zero]
      ring

/- English proof (translation)
Simplify using `[Multiset.esymm, Multiset.powersetCard_eq_empty _ h]`.
-/
theorem esymm_eq_zero_of_card_lt (M : Multiset ℂ) {k : ℕ} (h : M.card < k) : M.esymm k = 0 := by
  simp [Multiset.esymm, Multiset.powersetCard_eq_empty _ h]

noncomputable def segPow (s : ℂ) (t : ℕ) : Multiset ℂ :=
  (Multiset.range t).map fun l : ℕ => s ^ ((t : ℤ) - 1 - 2 * (l : ℤ))

/- English proof (translation)
Rewrite using `[segPow, Multiset.range_succ, Multiset.map_cons, segPow, Multiset.map_map]`. Use `congr 1`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Use `Multiset.map_congr rfl fun l _ => ?_` and prove the remaining obligations. Simplify using `only [Function.comp_apply]`. Rewrite using `[← zpow_one_add₀ hs]`. Use `congr 1`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem segPow_succ {s : ℂ} (hs : s ≠ 0) (t : ℕ) :
    segPow s (t + 1) = s ^ (-(t : ℤ)) ::ₘ (segPow s t).map (s * ·) := by
  rw [segPow, Multiset.range_succ, Multiset.map_cons, segPow, Multiset.map_map]
  congr 1
  · congr 1
    push_cast
    ring
  · refine Multiset.map_congr rfl fun l _ => ?_
    simp only [Function.comp_apply]
    rw [← zpow_one_add₀ hs]
    congr 1
    push_cast
    ring

/- English proof (translation)
Introduce `t`. Proceed by induction on `t with`. Consider the case `zero`. Introduce `i`. Consider the cases of `i with`.

Consider the case `zero => simp [segPow, esymm_at_zero, Formalism.L2.Col.gaussBin]`. Consider the case `succ i => simp [segPow, esymm_zero_succ, Formalism.L2.Col.gaussBin]`. Consider the case `succ t ih`. Introduce `i`. Consider the cases of `i with`.

Consider the case `zero => cases t <;> simp [esymm_at_zero, Formalism.L2.Col.gaussBin]`. Consider the case `succ i`. Rewrite using `[segPow_succ hs, esymm_cons_succ, esymm_map_mul, esymm_map_mul, ih, ih, Formalism.L2.Col.gaussBin]`. Use `push_cast`. Rewrite using `[← hq]`.

Establish `e1 : s ^ (i + 1) * s ^ (-(((i : ℤ) + 1) * ((t : ℤ) - (i + 1)))) = s ^ (-(((i : ℤ) + 1) * ((t : ℤ) + 1 - (i + 1)))) * (s ^ 2) ^ (i + 1)`. Establish `h1 : s ^ (i + 1) = s ^ ((i : ℤ) + 1)`. Rewrite using `[zpow_add_one₀ hs, zpow_natCast, pow_succ]`. Establish `h2 : (s ^ 2) ^ (i + 1) = s ^ ((2 : ℤ) * ((i : ℤ) + 1))`. Rewrite using `[← pow_mul, ← zpow_natCast]`.

Use `congr 1`. Rewrite using `[h1, h2, ← zpow_add₀ hs, ← zpow_add₀ hs]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `e2 : s ^ (-(t : ℤ)) * (s ^ i * s ^ (-((i : ℤ) * ((t : ℤ) - i)))) = s ^ (-(((i : ℤ) + 1) * ((t : ℤ) + 1 - (i + 1))))`.

Rewrite using `[← zpow_natCast, ← zpow_add₀ hs, ← zpow_add₀ hs]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Take the linear combination `(Formalism.L2.Col.gaussBin q t (i + 1) : ℂ) * e1 + (Formalism.L2.Col.gaussBin q t i : ℂ) * e2`.
-/
theorem esymm_segPow {s : ℂ} (hs : s ≠ 0) {q : ℕ} (hq : s ^ 2 = (q : ℂ)) : ∀ t i : ℕ,
    (segPow s t).esymm i = s ^ (-((i : ℤ) * ((t : ℤ) - i))) * (Formalism.L2.Col.gaussBin q t i : ℂ) := by
  intro t
  induction t with
  | zero =>
    intro i
    cases i with
    | zero => simp [segPow, esymm_at_zero, Formalism.L2.Col.gaussBin]
    | succ i => simp [segPow, esymm_zero_succ, Formalism.L2.Col.gaussBin]
  | succ t ih =>
    intro i
    cases i with
    | zero => cases t <;> simp [esymm_at_zero, Formalism.L2.Col.gaussBin]
    | succ i =>
      rw [segPow_succ hs, esymm_cons_succ, esymm_map_mul, esymm_map_mul, ih, ih, Formalism.L2.Col.gaussBin]
      push_cast
      rw [← hq]
      have e1 : s ^ (i + 1) * s ^ (-(((i : ℤ) + 1) * ((t : ℤ) - (i + 1)))) =
          s ^ (-(((i : ℤ) + 1) * ((t : ℤ) + 1 - (i + 1)))) * (s ^ 2) ^ (i + 1) := by
        have h1 : s ^ (i + 1) = s ^ ((i : ℤ) + 1) := by
          rw [zpow_add_one₀ hs, zpow_natCast, pow_succ]
        have h2 : (s ^ 2) ^ (i + 1) = s ^ ((2 : ℤ) * ((i : ℤ) + 1)) := by
          rw [← pow_mul, ← zpow_natCast]
          congr 1
        rw [h1, h2, ← zpow_add₀ hs, ← zpow_add₀ hs]
        congr 1
        ring
      have e2 : s ^ (-(t : ℤ)) * (s ^ i * s ^ (-((i : ℤ) * ((t : ℤ) - i)))) =
          s ^ (-(((i : ℤ) + 1) * ((t : ℤ) + 1 - (i + 1)))) := by
        rw [← zpow_natCast, ← zpow_add₀ hs, ← zpow_add₀ hs]
        congr 1
        push_cast
        ring
      linear_combination (Formalism.L2.Col.gaussBin q t (i + 1) : ℂ) * e1 +
        (Formalism.L2.Col.gaussBin q t i : ℂ) * e2

/- English proof (translation)
Establish `h : ((Real.sqrt (q : ℝ) : ℝ) : ℂ) = (q : ℂ) ^ ((1 / 2 : ℂ))`. Rewrite using `[Real.sqrt_eq_rpow, Complex.ofReal_cpow (by positivity)]`. Use `push_cast`. Both sides reduce to the same expression. Rewrite using `[h, ← Complex.cpow_int_mul]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cpow_half {q : ℕ} (m : ℤ) :
    (q : ℂ) ^ ((m : ℂ) / 2) = ((Real.sqrt (q : ℝ) : ℝ) : ℂ) ^ m := by
  have h : ((Real.sqrt (q : ℝ) : ℝ) : ℂ) = (q : ℂ) ^ ((1 / 2 : ℂ)) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (by positivity)]
    push_cast
    rfl
  rw [h, ← Complex.cpow_int_mul]
  congr 1
  ring

/- English proof (translation)
Rewrite using `[esymm_add, Finset.mul_sum]`. Establish `hsub : Finset.range (min k a + 1) ⊆ Finset.range (k + 1)`. Introduce `j hj`. Simplify using `only [Finset.mem_range] at hj ⊢`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[← Finset.sum_subset hsub]`. Use `Finset.sum_congr rfl fun j hj => ?_` and prove the remaining obligations. Establish `hj'` using `Finset.mem_range.1 hj`. Take `⟨i, rfl⟩` from `Nat.exists_eq_add_of_le (show j ≤ k by omega)`. Take `⟨c, rfl⟩` from `Nat.exists_eq_add_of_le (show j ≤ a by omega)`.

Rewrite using `[esymm_map_mul, esymm_map_mul, esymm_segPow hs hq]`. Simplify using `only [Nat.add_sub_cancel_left]`. Establish `h1 : (q : ℂ) ^ (c * i) = s ^ ((2 : ℤ) * c * i)`. Rewrite using `[← hq, ← pow_mul, ← zpow_natCast]`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `h2 : ((s ^ (j + c))⁻¹) ^ (j + i) = s ^ (-(((j : ℤ) + c) * ((j : ℤ) + i)))`. Rewrite using `[inv_pow, ← pow_mul, ← zpow_natCast, ← _root_.zpow_neg]`. Use `congr 1`.

Establish `h3 : (s ^ (j + c + t)) ^ j = s ^ (((j : ℤ) + c + t) * j)`. Rewrite using `[← pow_mul, ← zpow_natCast]`. Use `congr 1`. Establish `hS : (q : ℂ) ^ (c * i) * ((s ^ (j + c))⁻¹) ^ (j + i) * (s ^ (j + c + t)) ^ j * s ^ ((j : ℤ) * (((j + c : ℕ) : ℤ) - j)) = s ^ (((j + i : ℕ) : ℤ) * (((j + c + t : ℕ) : ℤ) - ((j + i : ℕ) : ℤ))) * s ^ (-((i : ℤ) * ((t : ℤ) - i)))`. Rewrite using `[h1, h2, h3, ← zpow_add₀ hs, ← zpow_add₀ hs, ← zpow_add₀ hs, ← zpow_add₀ hs]`.

Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [mul_pow]`. Take the linear combination `((Formalism.L2.Col.gaussBin q t i : ℂ) * x ^ (j + i) * (y⁻¹) ^ j * b.esymm j) * hS`.

Introduce `j hj hj'`. Simplify using `only [Finset.mem_range] at hj hj'`. Rewrite using `[esymm_map_mul, esymm_eq_zero_of_card_lt b (by omega)]`. Simplify using the standard rewrite rules.
-/
theorem conv_identity {q : ℕ} {s : ℂ} (hs : s ≠ 0) (hq : s ^ 2 = (q : ℂ)) (a t k : ℕ) (b : Multiset ℂ)
    (hb : b.card = a) (x y : ℂ) :
    ∑ j ∈ Finset.range (min k a + 1), ((q : ℂ) ^ ((a - j) * (k - j)) * (Formalism.L2.Col.gaussBin q t (k - j) : ℂ) *
        (x * (s ^ a)⁻¹) ^ k * (y⁻¹ * s ^ (a + t)) ^ j) * (s ^ ((j : ℤ) * ((a : ℤ) - j)) * b.esymm j) =
      s ^ ((k : ℤ) * (((a + t : ℕ) : ℤ) - k)) *
        (b.map ((x * y⁻¹) * ·) + (segPow s t).map (x * ·)).esymm k := by
  rw [esymm_add, Finset.mul_sum]
  have hsub : Finset.range (min k a + 1) ⊆ Finset.range (k + 1) := by
    intro j hj
    simp only [Finset.mem_range] at hj ⊢
    omega
  rw [← Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl fun j hj => ?_
    have hj' := Finset.mem_range.1 hj
    obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le (show j ≤ k by omega)
    obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le (show j ≤ a by omega)
    rw [esymm_map_mul, esymm_map_mul, esymm_segPow hs hq]
    simp only [Nat.add_sub_cancel_left]
    have h1 : (q : ℂ) ^ (c * i) = s ^ ((2 : ℤ) * c * i) := by
      rw [← hq, ← pow_mul, ← zpow_natCast]
      congr 1
      push_cast
      ring
    have h2 : ((s ^ (j + c))⁻¹) ^ (j + i) = s ^ (-(((j : ℤ) + c) * ((j : ℤ) + i))) := by
      rw [inv_pow, ← pow_mul, ← zpow_natCast, ← _root_.zpow_neg]
      congr 1
    have h3 : (s ^ (j + c + t)) ^ j = s ^ (((j : ℤ) + c + t) * j) := by
      rw [← pow_mul, ← zpow_natCast]
      congr 1
    have hS : (q : ℂ) ^ (c * i) * ((s ^ (j + c))⁻¹) ^ (j + i) * (s ^ (j + c + t)) ^ j *
        s ^ ((j : ℤ) * (((j + c : ℕ) : ℤ) - j)) =
        s ^ (((j + i : ℕ) : ℤ) * (((j + c + t : ℕ) : ℤ) - ((j + i : ℕ) : ℤ))) *
          s ^ (-((i : ℤ) * ((t : ℤ) - i))) := by
      rw [h1, h2, h3, ← zpow_add₀ hs, ← zpow_add₀ hs, ← zpow_add₀ hs, ← zpow_add₀ hs]
      congr 1
      push_cast
      ring
    simp only [mul_pow]
    linear_combination ((Formalism.L2.Col.gaussBin q t i : ℂ) * x ^ (j + i) * (y⁻¹) ^ j * b.esymm j) * hS
  · intro j hj hj'
    simp only [Finset.mem_range] at hj hj'
    rw [esymm_map_mul, esymm_eq_zero_of_card_lt b (by omega)]
    simp

end GlobalTheory.CompanionTheory.Ipf.Aut.GaussEsym

namespace GlobalTheory.CompanionTheory.Ipf.Aut

/- English proof (translation)
Introduce `E _ _ w a t k B x y hB hk`. Establish `hone` using `NumberField.HeightOneSpectrum.one_lt_absNorm w`. Establish `hq0 : ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ≠ 0`. Establish `: Ideal.absNorm w.asIdeal ≠ 0`. Introduce `h`.

Simplify using `[h] at hone`. Conclude with `this` after adjusting the coercions. Establish `hs : ((Real.sqrt ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) : ℝ) : ℂ) ≠ 0`. Establish `: 0 < Real.sqrt ((Ideal.absNorm w.asIdeal : ℕ) : ℝ)` using `Real.sqrt_pos.2 (lt_of_le_of_ne (by positivity) hq0.symm)`. Conclude with `this.ne'` after adjusting the coercions.

Establish `hq2 : ((Real.sqrt ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) : ℝ) : ℂ) ^ 2 = ((Ideal.absNorm w.asIdeal : ℕ) : ℂ)`. Rewrite using `[← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]`. Simplify using the standard rewrite rules. Establish `hc : ∀ m n : ℕ, ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (((m : ℂ) * ((n : ℂ) - m)) / 2) = ((Real.sqrt ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) : ℝ) : ℂ) ^ ((m : ℤ) * ((n : ℤ) - m))`. Introduce `m n`.

Use `GaussEsym.cpow_half (q := Ideal.absNorm w.asIdeal) ((m : ℤ) * ((n : ℤ) - m))` as an intermediate fact. Move the coercions through the operations in `at this`. Conclude with `this`. Establish `hseg : (GlobalTheory.LFun.seg w x t).map (fun b : ℂˣ => (b : ℂ)) = (GaussEsym.segPow ((Real.sqrt ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) : ℝ) : ℂ) t).map ((x : ℂ) * ·)`. Rewrite using `[GlobalTheory.LFun.seg, GaussEsym.segPow, Multiset.map_map, Multiset.map_map]`.

Use `Multiset.map_congr (Finset.range_val t) fun l _ => ?_` and prove the remaining obligations. Simplify using `only [Function.comp_apply, Units.val_mul, GlobalTheory.LFun.coe_npowU, GlobalTheory.LFun.npow]`. Use `congr 1`. Rewrite using `[← GaussEsym.cpow_half]`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `htw : (B.map (x * y⁻¹ * ·)).map (fun b : ℂˣ => (b : ℂ)) = (B.map fun b : ℂˣ => (b : ℂ)).map (((x : ℂ) * (y : ℂ)⁻¹) * ·)`. Simplify using `[Multiset.map_map, Function.comp_def]`. Establish `key` using `GaussEsym.conv_identity hs hq2 a t k (B.map fun b : ℂˣ => (b : ℂ)) (by simpa using hB) (x : ℂ) (y : ℂ)`.

Simplify using `only [GlobalTheory.LFun.satEig, hc, Multiset.map_add, hseg, htw]`. Conclude with `key`.
-/
theorem satEig_twist_add_seg : ∀ {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (a t k : ℕ) (B : Multiset ℂˣ) (x y : ℂˣ), B.card = a → k ≤ a + t → ∑ j ∈ Finset.range (min k a + 1), ((Ideal.absNorm w.asIdeal : ℂ) ^ ((a - j) * (k - j)) * (Formalism.L2.Col.gaussBin (Ideal.absNorm w.asIdeal) t (k - j) : ℂ) * ((x : ℂ) * ((Real.sqrt (Ideal.absNorm w.asIdeal) : ℂ) ^ a)⁻¹) ^ k * (((y : ℂ))⁻¹ * (Real.sqrt (Ideal.absNorm w.asIdeal) : ℂ) ^ (a + t)) ^ j) * GlobalTheory.LFun.satEig (Ideal.absNorm w.asIdeal) a B j = GlobalTheory.LFun.satEig (Ideal.absNorm w.asIdeal) (a + t) (B.map (x * y⁻¹ * ·) + seg w x t) k := by
  intro E _ _ w a t k B x y hB hk
  have hone := NumberField.HeightOneSpectrum.one_lt_absNorm w
  have hq0 : ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ≠ 0 := by
    have : Ideal.absNorm w.asIdeal ≠ 0 := by
      intro h
      simp [h] at hone
    exact_mod_cast this
  have hs : ((Real.sqrt ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) : ℝ) : ℂ) ≠ 0 := by
    have : 0 < Real.sqrt ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) :=
      Real.sqrt_pos.2 (lt_of_le_of_ne (by positivity) hq0.symm)
    exact_mod_cast this.ne'
  have hq2 : ((Real.sqrt ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) : ℝ) : ℂ) ^ 2 =
      ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]
    simp
  have hc : ∀ m n : ℕ, ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (((m : ℂ) * ((n : ℂ) - m)) / 2) =
      ((Real.sqrt ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) : ℝ) : ℂ) ^ ((m : ℤ) * ((n : ℤ) - m)) := by
    intro m n
    have := GaussEsym.cpow_half (q := Ideal.absNorm w.asIdeal) ((m : ℤ) * ((n : ℤ) - m))
    push_cast at this
    exact this
  have hseg : (GlobalTheory.LFun.seg w x t).map (fun b : ℂˣ => (b : ℂ)) =
      (GaussEsym.segPow ((Real.sqrt ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) : ℝ) : ℂ) t).map ((x : ℂ) * ·) := by
    rw [GlobalTheory.LFun.seg, GaussEsym.segPow, Multiset.map_map, Multiset.map_map]
    refine Multiset.map_congr (Finset.range_val t) fun l _ => ?_
    simp only [Function.comp_apply, Units.val_mul, GlobalTheory.LFun.coe_npowU, GlobalTheory.LFun.npow]
    congr 1
    rw [← GaussEsym.cpow_half]
    congr 1
    push_cast
    ring
  have htw : (B.map (x * y⁻¹ * ·)).map (fun b : ℂˣ => (b : ℂ)) =
      (B.map fun b : ℂˣ => (b : ℂ)).map (((x : ℂ) * (y : ℂ)⁻¹) * ·) := by
    simp [Multiset.map_map, Function.comp_def]
  have key := GaussEsym.conv_identity hs hq2 a t k (B.map fun b : ℂˣ => (b : ℂ)) (by simpa using hB) (x : ℂ) (y : ℂ)
  simp only [GlobalTheory.LFun.satEig, hc, Multiset.map_add, hseg, htw]
  exact key

end GlobalTheory.CompanionTheory.Ipf.Aut
