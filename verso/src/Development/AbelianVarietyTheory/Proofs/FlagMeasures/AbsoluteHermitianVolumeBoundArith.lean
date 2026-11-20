import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsGaugeAll
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ZetaProdSphereVolumeBounds
import Formalism.GL3MeanSquares.HookFormulaTorsion.SumWeightsOverPrimeLeHalfDegree

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.VolArith

/- English proof (translation)
Unfold `volU sphV`. Rewrite using `[show Finset.Icc 1 2 = {1, 2} from rfl, Finset.prod_pair (by norm_num)]`. Evaluate the numerical expressions. Expand and normalize the polynomial expressions, which then agree.
-/
theorem volU_two : volU 2 = 8 * Real.pi ^ 3 := by
  unfold volU sphV
  rw [show Finset.Icc 1 2 = {1, 2} from rfl, Finset.prod_pair (by norm_num)]
  norm_num
  ring

/- English proof (translation)
The claim follows from `Fintype.card_pos`.
-/
theorem one_le_fDeg (E : Type) [Field E] [NumberField E] : 1 ≤ Formalism.HermitianLatticesTheory.fDeg E :=
  Fintype.card_pos

/- English proof (translation)
Unfold `Formalism.HermitianLatticesTheory.vInv`. Establish `h : (1 : ℝ) ≤ |(discr E : ℝ)|`. Use `Int.one_le_abs (discr_ne_zero E)` as an intermediate fact. Conclude with `this` after adjusting the coercions. Use `Real.one_le_rpow h (z := (1 : ℝ) / (2 * Formalism.HermitianLatticesTheory.fDeg E)) (by positivity)` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem one_le_rd (E : Type) [Field E] [NumberField E] : 1 ≤ 2 * Formalism.HermitianLatticesTheory.vInv E := by
  unfold Formalism.HermitianLatticesTheory.vInv
  have h : (1 : ℝ) ≤ |(discr E : ℝ)| := by
    have := Int.one_le_abs (discr_ne_zero E)
    exact_mod_cast this
  have := Real.one_le_rpow h (z := (1 : ℝ) / (2 * Formalism.HermitianLatticesTheory.fDeg E)) (by positivity)
  linarith

/- English proof (translation)
Proceed by induction on `n, hn using Nat.le_induction with`. Consider the case `base => norm_num`. Consider the case `succ n hn ih`. Rewrite using `[Finset.sum_Ioc_succ_top hn, ih]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem sum_half (n : ℕ) (hn : 2 ≤ n) :
    ∑ M ∈ Finset.Ioc 2 n, ((M : ℝ) - 1 / 2) = ((n : ℝ) ^ 2 - 4) / 2 := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [Finset.sum_Ioc_succ_top hn, ih]
    push_cast
    ring

/- English proof (translation)
Take `⟨-, h0, h1⟩` from `Formalism.HermitianLattices.GenusMassVolumes.log_l_value_field_bound E hE M hM`. Use `⟨h0, ?_⟩` and prove the remaining obligations. Establish `hs : Summable (fun m : ℕ => 1 / ((m : ℝ) + 1) ^ M)`. Use `(summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 (by omega : 1 < M))` as an intermediate fact. Simplify using `using this`.

Establish `hz : 0 < ∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ M` using `hs.tsum_pos (fun m => by positivity) 0 (by positivity)`. Rewrite using `[← Real.log_le_log_iff h0 (pow_pos hz _), Real.log_pow]`. Conclude with `(le_abs_self _).trans h1`.
-/
theorem lVal_le (E : Type) [Field E] [NumberField E] [StarRing E] (hE : Formalism.HermitianLatticesTheory.IsCMUnram E)
    (M : ℕ) (hM : 3 ≤ M) :
    0 < Formalism.HermitianLatticesTheory.lValEta E M ∧
      Formalism.HermitianLatticesTheory.lValEta E M ≤ (∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ M) ^ Formalism.HermitianLatticesTheory.fDeg E := by
  obtain ⟨-, h0, h1⟩ := Formalism.HermitianLattices.GenusMassVolumes.log_l_value_field_bound E hE M hM
  refine ⟨h0, ?_⟩
  have hs : Summable (fun m : ℕ => 1 / ((m : ℝ) + 1) ^ M) := by
    have := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 (by omega : 1 < M))
    simpa using this
  have hz : 0 < ∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ M :=
    hs.tsum_pos (fun m => by positivity) 0 (by positivity)
  rw [← Real.log_le_log_iff h0 (pow_pos hz _), Real.log_pow]
  exact (le_abs_self _).trans h1

/- English proof (translation)
Establish `hr` using `one_le_rd E`. Establish `hr0 : 0 < 2 * Formalism.HermitianLatticesTheory.vInv E` using `by linarith`. Establish `hL : ∀ M ∈ Finset.Ioc 2 n, 0 ≤ Formalism.HermitianLatticesTheory.lValEta E M` using `fun M hM => (lVal_le E hE M (Finset.mem_Ioc.1 hM).1).1.le`. Unfold `rankFac`. Rewrite using `[Finset.prod_mul_distrib, ← Real.rpow_sum_of_pos hr0, ← Finset.mul_sum, sum_half n hn]`.

Use `⟨mul_nonneg (Real.rpow_nonneg hr0.le _) (Finset.prod_nonneg hL), ?_⟩` and prove the remaining obligations. Use `mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hr0.le _)` and prove the remaining obligations. Use `(Finset.prod_le_prod hL (fun M hM => (lVal_le E hE M (Finset.mem_Ioc.1 hM).1).2)).trans ?_` and prove the remaining obligations. Rewrite using `[Finset.prod_pow]`. Use `pow_le_pow_left₀ (Finset.prod_nonneg fun l _ => GlobalTheory.ZetaProd.zeta_nonneg l) ?_ _` and prove the remaining obligations.

Establish `e : Finset.Ioc 2 n = Finset.Icc 3 n`. Use extensionality with `x`. Simplify using `only [Finset.mem_Ioc, Finset.mem_Icc]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[e]`.

Conclude with `(GlobalTheory.zetaProd_sphereVolume_bounds.2.1 n).le`.
-/
theorem prod_rankFac_le (E : Type) [Field E] [NumberField E] [StarRing E]
    (hE : Formalism.HermitianLatticesTheory.IsCMUnram E) (n : ℕ) (hn : 2 ≤ n) :
    0 ≤ ∏ M ∈ Finset.Ioc 2 n, rankFac E M ∧
    ∏ M ∈ Finset.Ioc 2 n, rankFac E M ≤
      (2 * Formalism.HermitianLatticesTheory.vInv E) ^ ((Formalism.HermitianLatticesTheory.fDeg E : ℝ) * (((n : ℝ) ^ 2 - 4) / 2)) *
        1.4 ^ Formalism.HermitianLatticesTheory.fDeg E := by
  have hr := one_le_rd E
  have hr0 : 0 < 2 * Formalism.HermitianLatticesTheory.vInv E := by linarith
  have hL : ∀ M ∈ Finset.Ioc 2 n, 0 ≤ Formalism.HermitianLatticesTheory.lValEta E M := fun M hM =>
    (lVal_le E hE M (Finset.mem_Ioc.1 hM).1).1.le
  unfold rankFac
  rw [Finset.prod_mul_distrib, ← Real.rpow_sum_of_pos hr0, ← Finset.mul_sum, sum_half n hn]
  refine ⟨mul_nonneg (Real.rpow_nonneg hr0.le _) (Finset.prod_nonneg hL), ?_⟩
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hr0.le _)
  refine (Finset.prod_le_prod hL (fun M hM => (lVal_le E hE M (Finset.mem_Ioc.1 hM).1).2)).trans ?_
  rw [Finset.prod_pow]
  refine pow_le_pow_left₀ (Finset.prod_nonneg fun l _ => GlobalTheory.ZetaProd.zeta_nonneg l) ?_ _
  have e : Finset.Ioc 2 n = Finset.Icc 3 n := by
    ext x
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  rw [e]
  exact (GlobalTheory.zetaProd_sphereVolume_bounds.2.1 n).le

/- English proof (translation)
Introduce `E _ _ _ hE n X hn hX hrX hfX`. Take `⟨hP0, hP⟩` from `prod_rankFac_le E hE n (by omega)`. Establish `hr` using `one_le_rd E`. Establish `hf` using `one_le_fDeg E`. Use `set r := 2 * Formalism.HermitianLatticesTheory.vInv E with hrdef`.

Use `set f := Formalism.HermitianLatticesTheory.fDeg E with hfdef`. Establish `hf' : (1 : ℝ) ≤ f` using `by exact_mod_cast hf`. Establish `hn' : (8 : ℝ) ≤ n` using `by exact_mod_cast hn`. Establish `hlog0 : 0 ≤ Real.log r` using `Real.log_nonneg hr`. Establish `hlog1 : Real.log r ≤ r - 1` using `Real.log_le_sub_one_of_pos (by linarith)`.

Establish `hX0 : 0 < X` using `by linarith`. Establish `hX1 : 1 ≤ X` using `by linarith`. Establish `hA : 1 + f * Real.log r ≤ X ^ 2` using `by nlinarith`. Establish `hA0 : 0 ≤ 1 + f * Real.log r` using `by positivity`. Establish `hpi : Real.pi ^ 3 ≤ 3.15 ^ 3` using `pow_le_pow_left₀ Real.pi_pos.le Real.pi_lt_d2.le 3`.

Establish `hc : 8 * Real.pi ^ 3 * 4 * 1.4 ≤ X ^ 11`. Establish `: (2 : ℝ) ^ 11 ≤ X ^ 11` using `pow_le_pow_left₀ (by norm_num) hX 11`. Use the polynomial consequences of the given equalities and inequalities. Establish `hpi0` using `Real.pi_pos`. Establish `he0 : 0 ≤ (f : ℝ) * (((n : ℝ) ^ 2 - 4) / 2)` using `mul_nonneg (by linarith) (by nlinarith)`.

Establish `h1 : (8 * Real.pi ^ 3 * 4 * 1.4) ^ f ≤ (X ^ 11) ^ f` using `pow_le_pow_left₀ (by positivity) hc f`. Establish `h2 : r ^ (5 * f) ≤ X ^ (5 * f)` using `pow_le_pow_left₀ (by linarith) hrX _`. Establish `h3 : (1 + f * Real.log r) ^ (5 * f) ≤ (X ^ 2) ^ (5 * f)` using `pow_le_pow_left₀ hA0 hA _`. Establish `h4 : r ^ ((f : ℝ) * (((n : ℝ) ^ 2 - 4) / 2)) ≤ X ^ ((f : ℝ) * (((n : ℝ) ^ 2 - 4) / 2))` using `Real.rpow_le_rpow (by linarith) hrX he0`. Establish `hr0 : 0 < r` using `by linarith`.

Rewrite using `[volU_two]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_pow (8 * Real.pi ^ 3 * 4), mul_pow (8 * Real.pi ^ 3)]`. Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ (X ^ 11) ^ f * X ^ (5 * f) * (X ^ 2) ^ (5 * f) * X ^ ((f : ℝ) * (((n : ℝ) ^ 2 - 4) / 2)) := by gcongr`.

Use `_ = X ^ (((26 * f : ℕ) : ℝ) + (f : ℝ) * (((n : ℝ) ^ 2 - 4) / 2)) := by`. Rewrite using `[Real.rpow_add hX0, Real.rpow_natCast, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ X ^ ((n ^ 2 * f : ℕ) : ℝ) := by`.

Use `Real.rpow_le_rpow_of_exponent_le hX1 ?_` and prove the remaining obligations. Use `push_cast`. Establish `: (64 : ℝ) ≤ (n : ℝ) ^ 2` using `by nlinarith`. Use the polynomial consequences of the given equalities and inequalities. Use `_ = X ^ (n ^ 2 * f) := Real.rpow_natCast _ _`.
-/
theorem volume_bound_arith : ∀ (E : Type) [Field E] [NumberField E] [StarRing E], Formalism.HermitianLatticesTheory.IsCMUnram E → ∀ (n : ℕ) (X : ℝ), 8 ≤ n → 2 ≤ X → 2 * Formalism.HermitianLatticesTheory.vInv E ≤ X → 2 * Formalism.HermitianLatticesTheory.fDeg E * (2 * Formalism.HermitianLatticesTheory.vInv E) ≤ X ^ 2 → volU 2 ^ Formalism.HermitianLatticesTheory.fDeg E * (4 ^ Formalism.HermitianLatticesTheory.fDeg E * (2 * Formalism.HermitianLatticesTheory.vInv E) ^ (5 * Formalism.HermitianLatticesTheory.fDeg E) * (1 + Formalism.HermitianLatticesTheory.fDeg E * Real.log (2 * Formalism.HermitianLatticesTheory.vInv E)) ^ (5 * Formalism.HermitianLatticesTheory.fDeg E)) * ∏ M ∈ Finset.Ioc 2 n, rankFac E M ≤ X ^ (n ^ 2 * Formalism.HermitianLatticesTheory.fDeg E) := by
  intro E _ _ _ hE n X hn hX hrX hfX
  obtain ⟨hP0, hP⟩ := prod_rankFac_le E hE n (by omega)
  have hr := one_le_rd E
  have hf := one_le_fDeg E
  set r := 2 * Formalism.HermitianLatticesTheory.vInv E with hrdef
  set f := Formalism.HermitianLatticesTheory.fDeg E with hfdef
  have hf' : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hn' : (8 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog0 : 0 ≤ Real.log r := Real.log_nonneg hr
  have hlog1 : Real.log r ≤ r - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have hX0 : 0 < X := by linarith
  have hX1 : 1 ≤ X := by linarith
  have hA : 1 + f * Real.log r ≤ X ^ 2 := by nlinarith
  have hA0 : 0 ≤ 1 + f * Real.log r := by positivity
  have hpi : Real.pi ^ 3 ≤ 3.15 ^ 3 := pow_le_pow_left₀ Real.pi_pos.le Real.pi_lt_d2.le 3
  have hc : 8 * Real.pi ^ 3 * 4 * 1.4 ≤ X ^ 11 := by
    have : (2 : ℝ) ^ 11 ≤ X ^ 11 := pow_le_pow_left₀ (by norm_num) hX 11
    nlinarith
  have hpi0 := Real.pi_pos
  have he0 : 0 ≤ (f : ℝ) * (((n : ℝ) ^ 2 - 4) / 2) := mul_nonneg (by linarith) (by nlinarith)
  have h1 : (8 * Real.pi ^ 3 * 4 * 1.4) ^ f ≤ (X ^ 11) ^ f := pow_le_pow_left₀ (by positivity) hc f
  have h2 : r ^ (5 * f) ≤ X ^ (5 * f) := pow_le_pow_left₀ (by linarith) hrX _
  have h3 : (1 + f * Real.log r) ^ (5 * f) ≤ (X ^ 2) ^ (5 * f) := pow_le_pow_left₀ hA0 hA _
  have h4 : r ^ ((f : ℝ) * (((n : ℝ) ^ 2 - 4) / 2)) ≤ X ^ ((f : ℝ) * (((n : ℝ) ^ 2 - 4) / 2)) :=
    Real.rpow_le_rpow (by linarith) hrX he0
  have hr0 : 0 < r := by linarith
  rw [volU_two]
  calc (8 * Real.pi ^ 3) ^ f * (4 ^ f * r ^ (5 * f) * (1 + f * Real.log r) ^ (5 * f)) *
        ∏ M ∈ Finset.Ioc 2 n, rankFac E M
      ≤ (8 * Real.pi ^ 3) ^ f * (4 ^ f * r ^ (5 * f) * (1 + f * Real.log r) ^ (5 * f)) *
        (r ^ ((f : ℝ) * (((n : ℝ) ^ 2 - 4) / 2)) * 1.4 ^ f) :=
        mul_le_mul_of_nonneg_left hP (by positivity)
    _ = (8 * Real.pi ^ 3 * 4 * 1.4) ^ f * r ^ (5 * f) * (1 + f * Real.log r) ^ (5 * f) *
        r ^ ((f : ℝ) * (((n : ℝ) ^ 2 - 4) / 2)) := by
        rw [mul_pow (8 * Real.pi ^ 3 * 4), mul_pow (8 * Real.pi ^ 3)]
        ring
    _ ≤ (X ^ 11) ^ f * X ^ (5 * f) * (X ^ 2) ^ (5 * f) *
        X ^ ((f : ℝ) * (((n : ℝ) ^ 2 - 4) / 2)) := by
        gcongr
    _ = X ^ (((26 * f : ℕ) : ℝ) + (f : ℝ) * (((n : ℝ) ^ 2 - 4) / 2)) := by
        rw [Real.rpow_add hX0, Real.rpow_natCast, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
        congr 2
        ring
    _ ≤ X ^ ((n ^ 2 * f : ℕ) : ℝ) := by
        refine Real.rpow_le_rpow_of_exponent_le hX1 ?_
        push_cast
        have : (64 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
        nlinarith
    _ = X ^ (n ^ 2 * f) := Real.rpow_natCast _ _

end GlobalTheory.VolArith
