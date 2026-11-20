import Mathlib
import Formalism.LocalToGlobal.LocalInduction.BridgeInd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory.LocArith

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Rewrite using `[P.v_O]`. Conclude with `GlobalTheory.mem_integralClosure_padicInt_iff LL.1 y`.
-/
theorem v_nonneg_iff (P : LocPrime l) (LL : FinExt l) (y : ↥LL.1) :
    0 ≤ P.v LL y ↔ ‖((y : ↥LL.1) : Om l)‖ ≤ 1 := by
  rw [P.v_O]
  exact GlobalTheory.mem_integralClosure_padicInt_iff LL.1 y

/- English proof (translation)
Rewrite using `[← map_natCast (algebraMap ℚ_[l] (Om l)), PadicAlgCl.norm_extends, Padic.norm_p]`.
-/
theorem norm_natCast_prime : ‖((l : ℕ) : Om l)‖ = (l : ℝ)⁻¹ := by
  rw [← map_natCast (algebraMap ℚ_[l] (Om l)), PadicAlgCl.norm_extends, Padic.norm_p]

/- English proof (translation)
Establish `hy0 : y ≠ 0`. Introduce and unpack `rfl`. Rewrite `hy` using `[AddValuation.map_zero]`. Conclude with `WithTop.top_ne_zero hy`. Establish `h1 : ‖((y : ↥LL.1) : Om l)‖ ≤ 1` using `(v_nonneg_iff P LL y).1 (hy ▸ le_rfl)`.

Establish `hinv : P.v LL y⁻¹ = 0`. Establish `h` using `(P.v LL).map_mul y y⁻¹`. Rewrite `h` using `[mul_inv_cancel₀ hy0, AddValuation.map_one, hy, zero_add]`. Conclude with `h.symm`. Establish `h2 : ‖((y⁻¹ : ↥LL.1) : Om l)‖ ≤ 1` using `(v_nonneg_iff P LL _).1 (hinv ▸ le_rfl)`.

Establish `hc : ((y : ↥LL.1) : Om l) ≠ 0` using `by simpa using hy0`. Establish `hpos : 0 < ‖((y : ↥LL.1) : Om l)‖` using `norm_pos_iff.2 hc`. Rewrite `h2` using `[IntermediateField.coe_inv, norm_inv, inv_le_one₀ hpos]`. Conclude with `le_antisymm h1 h2`.
-/
theorem norm_eq_one_of_v_eq_zero (P : LocPrime l) (LL : FinExt l) (y : ↥LL.1) (hy : P.v LL y = 0) :
    ‖((y : ↥LL.1) : Om l)‖ = 1 := by
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [AddValuation.map_zero] at hy
    exact WithTop.top_ne_zero hy
  have h1 : ‖((y : ↥LL.1) : Om l)‖ ≤ 1 := (v_nonneg_iff P LL y).1 (hy ▸ le_rfl)
  have hinv : P.v LL y⁻¹ = 0 := by
    have h := (P.v LL).map_mul y y⁻¹
    rw [mul_inv_cancel₀ hy0, AddValuation.map_one, hy, zero_add] at h
    exact h.symm
  have h2 : ‖((y⁻¹ : ↥LL.1) : Om l)‖ ≤ 1 := (v_nonneg_iff P LL _).1 (hinv ▸ le_rfl)
  have hc : ((y : ↥LL.1) : Om l) ≠ 0 := by simpa using hy0
  have hpos : 0 < ‖((y : ↥LL.1) : Om l)‖ := norm_pos_iff.2 hc
  rw [IntermediateField.coe_inv, norm_inv, inv_le_one₀ hpos] at h2
  exact le_antisymm h1 h2

/- English proof (translation)
Use `set n := r.den with hn`. Use `set a := r.num.toNat with ha`. Use `set b := (-r.num).toNat with hb`. Establish `hkab : (r.num : ℚ) = (a : ℚ) - (b : ℚ)`. Establish `: r.num = (a : ℤ) - (b : ℤ)` using `by simp [ha, hb]`.

Conclude with `this` after adjusting the coercions. Establish `hnr : (n : ℚ) * r = (a : ℚ) - b` using `by rw [mul_comm, hn, Rat.mul_den_eq_num, hkab]`. Establish `hL0 : ((l : ℕ) : ↥LL.1) ≠ 0` using `Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero`. Use `set y : ↥LL.1 := x ^ n * (l : ↥LL.1) ^ b / (l : ↥LL.1) ^ a with hy`. Establish `hya : y * (l : ↥LL.1) ^ a = x ^ n * (l : ↥LL.1) ^ b` using `div_mul_cancel₀ _ (pow_ne_zero _ hL0)`.

Establish `hvy : P.v LL y = 0`. Establish `h` using `congrArg (P.v LL) hya`. Rewrite `h` using `[AddValuation.map_mul, AddValuation.map_mul, AddValuation.map_pow, AddValuation.map_pow, AddValuation.map_pow, P.v_l, hx]`. Establish `e1 : (n • ((r : ℚ) : WithTop ℚ)) = (((n : ℚ) * r : ℚ) : WithTop ℚ)`. Rewrite using `[← WithTop.coe_nsmul, nsmul_eq_mul]`.

Establish `e2 : ∀ m : ℕ, m • (1 : WithTop ℚ) = (((m : ℚ) : ℚ) : WithTop ℚ)` using `fun m => by`. Rewrite using `[← WithTop.coe_one, ← WithTop.coe_nsmul, nsmul_eq_mul, mul_one]`. Rewrite `h` using `[e1, e2, e2, hnr]`. Distinguish the cases in `ht : P.v LL y = ⊤`. Rewrite `h` using `[ht, WithTop.top_add]`.

Conclude with `absurd h.symm (WithTop.coe_ne_top)`. Take `⟨s, hs⟩` from `WithTop.ne_top_iff_exists.1 ht`. Rewrite `h`, the goal using `[← hs]`. Rewrite `h` using `[← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_inj]`. Establish `: s = 0` using `by linarith`.

Rewrite using `[this, WithTop.coe_zero]`. Establish `hN` using `congrArg (fun z : ↥LL.1 => ‖((z : ↥LL.1) : Om l)‖) hya`. Simplify using `only [IntermediateField.coe_mul, IntermediateField.coe_pow, norm_mul, norm_pow] at hN`. Establish `hc : (((l : ℕ) : ↥LL.1) : Om l) = ((l : ℕ) : Om l)` using `map_natCast (IntermediateField.val LL.1) l`. Rewrite `hN` using `[norm_eq_one_of_v_eq_zero P LL y hvy, hc, norm_natCast_prime]`.

Establish `hpos : (0 : ℝ) < l` using `by exact_mod_cast (Fact.out : l.Prime).pos`. Establish `hn0 : n ≠ 0` using `r.den_nz`. Establish `hxn : ‖((x : ↥LL.1) : Om l)‖ ^ n = (l : ℝ) ^ b / (l : ℝ) ^ a`. Rewrite `hN` using `[inv_pow, inv_pow, one_mul]`. Establish `hb0 : (0 : ℝ) < (l : ℝ) ^ b` using `pow_pos hpos b`.

Establish `ha0 : (0 : ℝ) < (l : ℝ) ^ a` using `pow_pos hpos a`. Clear denominators, using `at hN ⊢` for the nonvanishing conditions. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hrn : ((l : ℝ) ^ (-(r : ℝ))) ^ n = (l : ℝ) ^ b / (l : ℝ) ^ a`. Rewrite using `[← Real.rpow_natCast, ← Real.rpow_mul hpos.le]`.

Establish `: -(r : ℝ) * (n : ℝ) = (b : ℝ) - (a : ℝ)`. Establish `h2 : ((n : ℚ) * r : ℚ) = (a : ℚ) - b` using `hnr`. Establish `h3 : ((n : ℝ) * (r : ℝ)) = (a : ℝ) - b` using `by exact_mod_cast h2`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[this, Real.rpow_sub hpos, Real.rpow_natCast, Real.rpow_natCast]`.

Rewrite `hxn` using `[← hrn]`. Conclude with `(pow_left_inj₀ (norm_nonneg _) (Real.rpow_nonneg hpos.le _) hn0).1 hxn`.
-/
theorem norm_of_v_eq (P : LocPrime l) (LL : FinExt l) (x : ↥LL.1) (r : ℚ)
    (hx : P.v LL x = ((r : ℚ) : WithTop ℚ)) :
    ‖((x : ↥LL.1) : Om l)‖ = (l : ℝ) ^ (-(r : ℝ)) := by
  set n := r.den with hn
  set a := r.num.toNat with ha
  set b := (-r.num).toNat with hb
  have hkab : (r.num : ℚ) = (a : ℚ) - (b : ℚ) := by
    have : r.num = (a : ℤ) - (b : ℤ) := by simp [ha, hb]
    exact_mod_cast this
  have hnr : (n : ℚ) * r = (a : ℚ) - b := by rw [mul_comm, hn, Rat.mul_den_eq_num, hkab]
  have hL0 : ((l : ℕ) : ↥LL.1) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  set y : ↥LL.1 := x ^ n * (l : ↥LL.1) ^ b / (l : ↥LL.1) ^ a with hy
  have hya : y * (l : ↥LL.1) ^ a = x ^ n * (l : ↥LL.1) ^ b := div_mul_cancel₀ _ (pow_ne_zero _ hL0)
  have hvy : P.v LL y = 0 := by
    have h := congrArg (P.v LL) hya
    rw [AddValuation.map_mul, AddValuation.map_mul, AddValuation.map_pow, AddValuation.map_pow,
      AddValuation.map_pow, P.v_l, hx] at h
    have e1 : (n • ((r : ℚ) : WithTop ℚ)) = (((n : ℚ) * r : ℚ) : WithTop ℚ) := by
      rw [← WithTop.coe_nsmul, nsmul_eq_mul]
    have e2 : ∀ m : ℕ, m • (1 : WithTop ℚ) = (((m : ℚ) : ℚ) : WithTop ℚ) := fun m => by
      rw [← WithTop.coe_one, ← WithTop.coe_nsmul, nsmul_eq_mul, mul_one]
    rw [e1, e2, e2, hnr] at h
    by_cases ht : P.v LL y = ⊤
    · rw [ht, WithTop.top_add] at h
      exact absurd h.symm (WithTop.coe_ne_top)
    · obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.1 ht
      rw [← hs] at h ⊢
      rw [← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_inj] at h
      have : s = 0 := by linarith
      rw [this, WithTop.coe_zero]
  have hN := congrArg (fun z : ↥LL.1 => ‖((z : ↥LL.1) : Om l)‖) hya
  simp only [IntermediateField.coe_mul, IntermediateField.coe_pow,
    norm_mul, norm_pow] at hN
  have hc : (((l : ℕ) : ↥LL.1) : Om l) = ((l : ℕ) : Om l) := map_natCast (IntermediateField.val LL.1) l
  rw [norm_eq_one_of_v_eq_zero P LL y hvy, hc, norm_natCast_prime] at hN
  have hpos : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  have hn0 : n ≠ 0 := r.den_nz
  have hxn : ‖((x : ↥LL.1) : Om l)‖ ^ n = (l : ℝ) ^ b / (l : ℝ) ^ a := by
    rw [inv_pow, inv_pow, one_mul] at hN
    have hb0 : (0 : ℝ) < (l : ℝ) ^ b := pow_pos hpos b
    have ha0 : (0 : ℝ) < (l : ℝ) ^ a := pow_pos hpos a
    field_simp at hN ⊢
    linarith
  have hrn : ((l : ℝ) ^ (-(r : ℝ))) ^ n = (l : ℝ) ^ b / (l : ℝ) ^ a := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hpos.le]
    have : -(r : ℝ) * (n : ℝ) = (b : ℝ) - (a : ℝ) := by
      have h2 : ((n : ℚ) * r : ℚ) = (a : ℚ) - b := hnr
      have h3 : ((n : ℝ) * (r : ℝ)) = (a : ℝ) - b := by exact_mod_cast h2
      linarith
    rw [this, Real.rpow_sub hpos, Real.rpow_natCast, Real.rpow_natCast]
  rw [← hrn] at hxn
  exact (pow_left_inj₀ (norm_nonneg _) (Real.rpow_nonneg hpos.le _) hn0).1 hxn

/- English proof (translation)
Use `⟨norm_of_v_eq P LL x q, fun h => ?_⟩` and prove the remaining obligations. Establish `hpos : (0 : ℝ) < l` using `by exact_mod_cast (Fact.out : l.Prime).pos`. Establish `hl1 : (1 : ℝ) < l` using `by exact_mod_cast (Fact.out : l.Prime).one_lt`. Establish `hx0 : x ≠ 0`. Introduce and unpack `rfl`.

Establish `: (0 : ℝ) < (l : ℝ) ^ (-(q : ℝ))` using `Real.rpow_pos_of_pos hpos _`. Simplify using `at h`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `ht : P.v LL x ≠ ⊤` using `fun ht => hx0 ((P.v LL).top_iff.1 ht)`. Take `⟨s, hs⟩` from `WithTop.ne_top_iff_exists.1 ht`.

Establish `h2` using `norm_of_v_eq P LL x s hs.symm`. Rewrite `h` using `[h2]`. Establish `hqs : (q : ℝ) = (s : ℝ)`. Use `le_antisymm ((Real.rpow_le_rpow_left_iff hl1).1 h.le) ((Real.rpow_le_rpow_left_iff hl1).1 h.ge)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Rewrite using `[← hs, show q = s by exact_mod_cast hqs]`.
-/
theorem v_eq_iff (P : LocPrime l) (LL : FinExt l) (x : ↥LL.1) (q : ℚ) :
    P.v LL x = ((q : ℚ) : WithTop ℚ) ↔ ‖((x : ↥LL.1) : Om l)‖ = (l : ℝ) ^ (-(q : ℝ)) := by
  refine ⟨norm_of_v_eq P LL x q, fun h => ?_⟩
  have hpos : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hx0 : x ≠ 0 := by
    rintro rfl
    have : (0 : ℝ) < (l : ℝ) ^ (-(q : ℝ)) := Real.rpow_pos_of_pos hpos _
    simp at h
    linarith
  have ht : P.v LL x ≠ ⊤ := fun ht => hx0 ((P.v LL).top_iff.1 ht)
  obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.1 ht
  have h2 := norm_of_v_eq P LL x s hs.symm
  rw [h2] at h
  have hqs : (q : ℝ) = (s : ℝ) := by
    have := le_antisymm ((Real.rpow_le_rpow_left_iff hl1).1 h.le) ((Real.rpow_le_rpow_left_iff hl1).1 h.ge)
    linarith
  rw [← hs, show q = s by exact_mod_cast hqs]

/- English proof (translation)
Take `⟨a, ha, -⟩` from `P.χQ_cyc g 0 1 (one_pow _)`. Rewrite `ha` using `[Nat.cast_zero, neg_zero, zpow_zero]`. Establish `hA : ‖((a : ℕ) : ℚ_[l])‖ ≤ 1`. Use `IsUltrametricDist.norm_intCast_le_one ℚ_[l] (a : ℤ)` as an intermediate fact. Simplify using `using this`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem norm_chiQ_le_one (P : LocPrime l) (g : GQ l) : ‖((P.χQ g : ℚ_[l]ˣ) : ℚ_[l])‖ ≤ 1 := by
  obtain ⟨a, ha, -⟩ := P.χQ_cyc g 0 1 (one_pow _)
  rw [Nat.cast_zero, neg_zero, zpow_zero] at ha
  have hA : ‖((a : ℕ) : ℚ_[l])‖ ≤ 1 := by
    have := IsUltrametricDist.norm_intCast_le_one ℚ_[l] (a : ℤ)
    simpa using this
  calc ‖((P.χQ g : ℚ_[l]ˣ) : ℚ_[l])‖
      = ‖(((P.χQ g : ℚ_[l]ˣ) : ℚ_[l]) - a) + a‖ := by rw [sub_add_cancel]
    _ ≤ max ‖((P.χQ g : ℚ_[l]ˣ) : ℚ_[l]) - a‖ ‖((a : ℕ) : ℚ_[l])‖ := IsUltrametricDist.norm_add_le_max _ _
    _ ≤ 1 := max_le ha hA

def chiInt (P : LocPrime l) (g : GQ l) : ℤ_[l] := ⟨(P.χQ g : ℚ_[l]), norm_chiQ_le_one P g⟩

/- English proof (translation)
Introduce `l _ P` and use `⟨fun LL x q => v_eq_iff P LL x q⟩`.
-/
theorem arithTied : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l), Formalism.L2.ArithTied P := fun l _ P =>
  ⟨fun LL x q => v_eq_iff P LL x q⟩

end GlobalTheory.LocArith
