import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KurComplete
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.GramExists
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.NormLeInvOfLtOne

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.D

open Formalism.InvariantFactorPaths.G7 (lgF at1 UnrOK)

namespace OrbitCoverLemmas

/- English proof (translation)
Establish `hE` using `expSpec K l hl`. Establish `hsum0 : ∀ r', MvPowerSeries.constantCoeff (∑ r, MvPowerSeries.C (M r' r) * at1 ((true, r) : Bool × ι) (lgF K l)) = 0`. Introduce `r'`. Rewrite using `[map_sum]`. Use `Finset.sum_eq_zero fun r _ => ?_` and prove the remaining obligations.

Rewrite using `[map_mul, Pair.constantCoeff_inVar_eq_zero _ (Pair.cc_lgF hl), mul_zero]`. Take `⟨φ, hφdef⟩ : ∃ φ : Bool × ι → MvPowerSeries (Bool × ι) K, φ = fun x : Bool × ι => if x.1 = true then PowerSeries.subst (∑ r, MvPowerSeries.C (M x.2 r) * at1 (true, r) (lgF K l)) (expF K l) else (MvPowerSeries.X x : MvPowerSeries (Bool × ι) K)` from `⟨_, rfl⟩`. Rewrite using `[← hφdef]`. Establish `hφ0 : ∀ x, MvPowerSeries.constantCoeff (φ x) = 0`. Introduce `x`.

Rewrite using `[hφdef]`. Simplify using `only`. Use `split_ifs`. Conclude with `Pair.cc_ps (hsum0 _) hE.1`. Simplify using the standard rewrite rules.

Establish `hφ : MvPowerSeries.HasSubst φ` using `MvPowerSeries.hasSubst_of_constantCoeff_zero hφ0`. Rewrite using `[Pair.subst_sum hφ, Finset.mul_sum]`. Establish `h1 : ∀ r', MvPowerSeries.subst φ (MvPowerSeries.C (w r') * at1 (true, r') (lgF K l)) = MvPowerSeries.C (w r') * ∑ r, MvPowerSeries.C (M r' r) * at1 (true, r) (lgF K l)`. Introduce `r'`. Rewrite using `[TorusDerivation.subst_C_mul hφ, Pair.subst_single_var hφ]`.

Use `congr 1`. Establish `e : φ (true, r') = PowerSeries.subst (∑ r, MvPowerSeries.C (M r' r) * at1 (true, r) (lgF K l)) (expF K l)`. Rewrite using `[hφdef]`. Conclude with `if_pos rfl`. Rewrite using `[e, Pair.ps_comp (hsum0 r') hE.1, hE.2.1, PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero (hsum0 r'))]`.

Simplify using `only [h1, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun r _ => ?_` and prove the remaining obligations. Rewrite using `[← mul_assoc, ← map_mul, h r, map_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun r' _ => ?_` and prove the remaining obligations.

Rewrite using `[map_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem odd_gen {K : Type} [Field K] {l : ℕ} (hl : 2 ≤ l) {ι : Type} [Fintype ι]
    (M : ι → ι → K) (e : K) (w : ι → K) (h : ∀ r, e * w r = ∑ r', M r' r * w r') :
    MvPowerSeries.subst (fun x : Bool × ι => if x.1 = true then
        PowerSeries.subst (∑ r, MvPowerSeries.C (M x.2 r) * at1 (true, r) (lgF K l)) (expF K l)
        else (MvPowerSeries.X x : MvPowerSeries (Bool × ι) K))
        (∑ r, MvPowerSeries.C (w r) * at1 (true, r) (lgF K l)) =
      MvPowerSeries.C e * ∑ r, MvPowerSeries.C (w r) * at1 (true, r) (lgF K l) := by
  have hE := expSpec K l hl
  have hsum0 : ∀ r', MvPowerSeries.constantCoeff
      (∑ r, MvPowerSeries.C (M r' r) * at1 ((true, r) : Bool × ι) (lgF K l)) = 0 := by
    intro r'
    rw [map_sum]
    refine Finset.sum_eq_zero fun r _ => ?_
    rw [map_mul, Pair.constantCoeff_inVar_eq_zero _ (Pair.cc_lgF hl), mul_zero]
  obtain ⟨φ, hφdef⟩ : ∃ φ : Bool × ι → MvPowerSeries (Bool × ι) K, φ = fun x : Bool × ι =>
      if x.1 = true then
        PowerSeries.subst (∑ r, MvPowerSeries.C (M x.2 r) * at1 (true, r) (lgF K l)) (expF K l)
        else (MvPowerSeries.X x : MvPowerSeries (Bool × ι) K) := ⟨_, rfl⟩
  rw [← hφdef]
  have hφ0 : ∀ x, MvPowerSeries.constantCoeff (φ x) = 0 := by
    intro x
    rw [hφdef]
    dsimp only
    split_ifs
    · exact Pair.cc_ps (hsum0 _) hE.1
    · simp
  have hφ : MvPowerSeries.HasSubst φ := MvPowerSeries.hasSubst_of_constantCoeff_zero hφ0
  rw [Pair.subst_sum hφ, Finset.mul_sum]
  have h1 : ∀ r', MvPowerSeries.subst φ
      (MvPowerSeries.C (w r') * at1 (true, r') (lgF K l)) =
      MvPowerSeries.C (w r') *
        ∑ r, MvPowerSeries.C (M r' r) * at1 (true, r) (lgF K l) := by
    intro r'
    rw [TorusDerivation.subst_C_mul hφ, Pair.subst_single_var hφ]
    congr 1
    have e : φ (true, r') = PowerSeries.subst
        (∑ r, MvPowerSeries.C (M r' r) * at1 (true, r) (lgF K l)) (expF K l) := by
      rw [hφdef]
      exact if_pos rfl
    rw [e, Pair.ps_comp (hsum0 r') hE.1, hE.2.1,
      PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero (hsum0 r'))]
  simp only [h1, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [← mul_assoc, ← map_mul, h r, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun r' _ => ?_
  rw [map_mul]
  ring

/- English proof (translation)
Establish `hpw : ∀ x, σ^[k] x = (σ ^ k) x` using `fun x => by rw [RingHom.coe_pow]`. Rewrite using `[hpw, map_sum]`. Use `Finset.sum_congr rfl fun r _ => ?_` and prove the remaining obligations. Rewrite using `[← hpw, iterate_map_mul]`.
-/
theorem iter_sum {K : Type} [Field K] (σ : K →+* K) (k : ℕ) {ι : Type} [Fintype ι] (f g : ι → K) :
    σ^[k] (∑ r, f r * g r) = ∑ r, σ^[k] (f r) * σ^[k] (g r) := by
  have hpw : ∀ x, σ^[k] x = (σ ^ k) x := fun x => by rw [RingHom.coe_pow]
  rw [hpw, map_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [← hpw, iterate_map_mul]

end OrbitCoverLemmas

/- English proof (translation)
Establish `hs' : ¬ s.val % 2 = 0` using `by omega`. Unfold `zXY`. Rewrite using `[if_neg hs']`. Use `OrbitCoverLemmas.odd_gen hl (fun r' r => σ (c r' r)) _ _ fun r => ?_` and prove the remaining obligations. Rewrite using `[← iterate_map_mul, hact r, OrbitCoverLemmas.iter_sum]`.

Use `Finset.sum_congr rfl fun r' _ => ?_` and prove the remaining obligations. Rewrite using `[InverseCommuting.iter_odd (hc r r') hs']`.
-/
theorem eigenOdd_conj (K : Type) [Field K] (l d : ℕ) [NeZero d] (σ : K →+* K) (hl : 2 ≤ l)
    (ι : Type) [Fintype ι] (om oms : ι → K) (b : K) (c : ι → ι → K)
    (hc : ∀ r r', σ (σ (c r' r)) = c r' r)
    (hact : ∀ r, b * oms r = ∑ r', c r' r * oms r') (s : ZMod d) (hs : s.val % 2 = 1) :
    MvPowerSeries.subst (fun x : Bool × ι => if x.1 = true then
        PowerSeries.subst (∑ r, MvPowerSeries.C (σ (c x.2 r)) * at1 (true, r) (lgF K l)) (expF K l)
        else (MvPowerSeries.X x : MvPowerSeries (Bool × ι) K)) (zXY l σ om oms s) =
      MvPowerSeries.C (σ^[s.val] b) * zXY l σ om oms s := by
  have hs' : ¬ s.val % 2 = 0 := by omega
  unfold zXY
  rw [if_neg hs']
  refine OrbitCoverLemmas.odd_gen hl (fun r' r => σ (c r' r)) _ _ fun r => ?_
  rw [← iterate_map_mul, hact r, OrbitCoverLemmas.iter_sum]
  refine Finset.sum_congr rfl fun r' _ => ?_
  rw [InverseCommuting.iter_odd (hc r r') hs']

/- English proof (translation)
Establish `h` using `eigenOdd_conj K l d σ hl ι om oms b (fun r' r => σ (c r' r)) (fun r r' => by rw [hc]) hact s hs`. Simplify `h` using `only [hc]`.
-/
theorem eigenOdd_plain (K : Type) [Field K] (l d : ℕ) [NeZero d] (σ : K →+* K) (hl : 2 ≤ l)
    (ι : Type) [Fintype ι] (om oms : ι → K) (b : K) (c : ι → ι → K)
    (hc : ∀ r r', σ (σ (c r' r)) = c r' r)
    (hact : ∀ r, b * oms r = ∑ r', σ (c r' r) * oms r') (s : ZMod d) (hs : s.val % 2 = 1) :
    MvPowerSeries.subst (fun x : Bool × ι => if x.1 = true then
        PowerSeries.subst (∑ r, MvPowerSeries.C (c x.2 r) * at1 (true, r) (lgF K l)) (expF K l)
        else (MvPowerSeries.X x : MvPowerSeries (Bool × ι) K)) (zXY l σ om oms s) =
      MvPowerSeries.C (σ^[s.val] b) * zXY l σ om oms s := by
  have h := eigenOdd_conj K l d σ hl ι om oms b (fun r' r => σ (c r' r))
    (fun r r' => by rw [hc]) hact s hs
  simpa only [hc] using h

/- English proof (translation)
The claim follows from `eigenOdd_plain`.
-/
theorem odd_eigenspace : EigenOdd := eigenOdd_plain

namespace OrbitCoverLemmas

def blk {K : Type} [Field K] (lam : K) (k x : Bool) : K :=
  if x = false then (if k = false then 1 else lam) else (if k = false then 2⁻¹ else -lam * 2⁻¹)

/- English proof (translation)
Establish `s2 : σ 2 = 2` using `map_ofNat σ 2`. Apply the tactic sequence `cases x <;> cases x' <;> simp [blk, map_inv₀, s2]`. Take the linear combination `h`. Clear the denominators using the available nonvanishing facts. Take the linear combination `-h`.

Clear the denominators using the available nonvanishing facts. Take the linear combination `-h`. Clear the denominators using the available nonvanishing facts. Take the linear combination `h`.
-/
theorem blk_gram {K : Type} [Field K] (σ : K →+* K) (lam : K) (h2 : (2 : K) ≠ 0)
    (h : lam * σ lam = -1) (x x' : Bool) :
    ∑ k, blk lam k x * σ (blk lam k x') = if x ≠ x' then 1 else 0 := by
  have s2 : σ 2 = 2 := map_ofNat σ 2
  cases x <;> cases x' <;> simp [blk, map_inv₀, s2]
  · linear_combination h
  · field_simp; linear_combination -h
  · field_simp; linear_combination -h
  · field_simp; linear_combination h

/- English proof (translation)
Establish `e : (2 * m + 1) ^ 2 - 1 = (m * (2 * m + 2)) * 2`. Establish `: (2 * m + 1) ^ 2 = (m * (2 * m + 2)) * 2 + 1` using `by ring`. Use linear arithmetic over natural numbers and integers. Establish `hp : IsPrimitiveRoot (ζ ^ (m * (2 * m + 2))) 2`. Use `hζ.pow_of_dvd (p := m * (2 * m + 2)) (by positivity) (by rw [e]; exact Dvd.intro _ rfl)` as an intermediate fact.

Rewrite `this` using `[e, Nat.mul_div_cancel_left _ (by positivity)]`. Then use the resulting hypothesis. Use `hp.eq_neg_one_of_two_right` as an intermediate fact. Rewrite using `[map_pow, hσ, ← this]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem lam_spec {K : Type} [Field K] (σ : K →+* K) (m : ℕ) (hm : 0 < m) (ζ : K)
    (hζ : IsPrimitiveRoot ζ ((2 * m + 1) ^ 2 - 1)) (hσ : σ ζ = ζ ^ (2 * m + 1)) :
    (ζ ^ m) * σ (ζ ^ m) = -1 := by
  have e : (2 * m + 1) ^ 2 - 1 = (m * (2 * m + 2)) * 2 := by
    have : (2 * m + 1) ^ 2 = (m * (2 * m + 2)) * 2 + 1 := by ring
    omega
  have hp : IsPrimitiveRoot (ζ ^ (m * (2 * m + 2))) 2 := by
    have := hζ.pow_of_dvd (p := m * (2 * m + 2)) (by positivity) (by rw [e]; exact Dvd.intro _ rfl)
    rwa [e, Nat.mul_div_cancel_left _ (by positivity)] at this
  have := hp.eq_neg_one_of_two_right
  rw [map_pow, hσ, ← this]; ring

/- English proof (translation)
Establish `h2 : ‖(2 : K)‖ ≤ 1`. Use `IsUltrametricDist.norm_natCast_le_one K 2` as an intermediate fact. Simplify using `using this`. Use `le_antisymm h2 ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hlt`.

Rewrite `hlt` using `[not_le]`. Establish `hm : ‖(m : K)‖ ≤ 1` using `IsUltrametricDist.norm_natCast_le_one K m`. Establish `e : (1 : K) = ((2 * m + 1 : ℕ) : K) + -(2 * (m : K))` using `by push_cast; ring`. Establish `h1 : ‖(1 : K)‖ < 1`. Rewrite using `[e]`.

Use `lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt h ?_)` and prove the remaining obligations. Rewrite using `[norm_neg, norm_mul]`. Combine the equalities or inequalities in the displayed calculation. Rewrite `h1` using `[norm_one]`. Conclude with `lt_irrefl _ h1`.
-/
theorem norm_two {K : Type} [NormedField K] [IsUltrametricDist K] (m : ℕ)
    (h : ‖((2 * m + 1 : ℕ) : K)‖ < 1) : ‖(2 : K)‖ = 1 := by
  have h2 : ‖(2 : K)‖ ≤ 1 := by
    have := IsUltrametricDist.norm_natCast_le_one K 2
    simpa using this
  refine le_antisymm h2 ?_
  by_contra hlt
  rw [not_le] at hlt
  have hm : ‖(m : K)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one K m
  have e : (1 : K) = ((2 * m + 1 : ℕ) : K) + -(2 * (m : K)) := by push_cast; ring
  have h1 : ‖(1 : K)‖ < 1 := by
    rw [e]
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt h ?_)
    rw [norm_neg, norm_mul]
    calc ‖(2 : K)‖ * ‖(m : K)‖ ≤ ‖(2 : K)‖ * 1 := by gcongr
      _ < 1 := by rwa [mul_one]
  rw [norm_one] at h1
  exact lt_irrefl _ h1

end OrbitCoverLemmas

/- English proof (translation)
Introduce `K _ _ _ l σ hU hζ E _ _`. Take `⟨ζ, hζ⟩` from `hζ`. Take `⟨hp, hl2, hnl, -, -⟩` from `id hU`. Choose the witnesses or unpack the hypotheses as in `⟨m, rfl⟩ : ∃ m, l = 2 * m + 1 := by`. Break down `hp.eq_two_or_odd' with h | h` into its components or cases.

Use linear arithmetic over natural numbers and integers. Conclude with `h`. Establish `hm : 0 < m` using `by omega`. Establish `hσζ : σ ζ = ζ ^ (2 * m + 1)` using `teichSigma K _ 2 σ hU (by norm_num) ζ hζ.pow_eq_one`. Establish `hN0 : (2 * m + 1) ^ 2 - 1 ≠ 0`.

Establish `: 1 < (2 * m + 1) ^ 2` using `Nat.one_lt_pow (by norm_num) (by omega)`. Use linear arithmetic over natural numbers and integers. Establish `nζ : ‖ζ‖ = 1` using `FormalExponential.norm_eq_one_of_pow hN0 hζ.pow_eq_one`. Establish `hσσ : σ (σ ζ) = ζ`. Rewrite using `[hσζ, map_pow, hσζ, ← pow_mul, ← sq]`.

Establish `e : (2 * m + 1) ^ 2 = ((2 * m + 1) ^ 2 - 1) + 1` using `by omega`. Rewrite using `[e, pow_succ, hζ.pow_eq_one, one_mul]`. Establish `hlam` using `OrbitCoverLemmas.lam_spec σ m hm ζ hζ hσζ`. Establish `n2 : ‖(2 : K)‖ = 1`. Use `OrbitCoverLemmas.norm_two m ?_` and prove the remaining obligations.

Rewrite using `[hnl]`. Conclude with `inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)`. Establish `h2 : (2 : K) ≠ 0` using `two_ne_zero`. Establish `nlam : ‖ζ ^ m‖ = 1` using `by rw [norm_pow, nζ, one_pow]`. Establish `s2 : σ 2 = 2` using `map_ofNat σ 2`.

Establish `hblk : ∀ k x : Bool, ‖OrbitCoverLemmas.blk (ζ ^ m) k x‖ ≤ 1 ∧ σ (σ (OrbitCoverLemmas.blk (ζ ^ m) k x)) = OrbitCoverLemmas.blk (ζ ^ m) k x`. Introduce `k x`. Apply the tactic sequence `cases k <;> cases x <;> simp [OrbitCoverLemmas.blk, nlam, hσσ, n2, s2, map_inv₀]`. Use `⟨fun k x => if k.2 = x.2 then OrbitCoverLemmas.blk (ζ ^ m) k.1 x.1 else 0, fun k x => ?_, ?_⟩` and prove the remaining obligations. Simplify using `only split_ifs`.

Conclude with `hblk _ _`. Simplify using the standard rewrite rules. Introduce and unpack `⟨b, e⟩ ⟨b', e'⟩`. Rewrite using `[Fintype.sum_prod_type]`. Simplify using `only`.

Distinguish the cases in `h : e = e'`. Substitute `h` using the available equality. Establish `h3 : ∀ k : Bool, ∑ y : E, (if y = e then OrbitCoverLemmas.blk (ζ ^ m) k b else 0) * σ (if y = e then OrbitCoverLemmas.blk (ζ ^ m) k b' else 0) = OrbitCoverLemmas.blk (ζ ^ m) k b * σ (OrbitCoverLemmas.blk (ζ ^ m) k b')`. Introduce `k`. Rewrite using `[Finset.sum_eq_single e]`.

Simplify using the standard rewrite rules. Introduce `y _ hy`. Simplify using `[hy]`. Simplify using the standard rewrite rules. Simplify using `only [h3]`.

Rewrite using `[OrbitCoverLemmas.blk_gram σ _ h2 hlam]`. Simplify using the standard rewrite rules. Rewrite using `[if_neg (fun h' => h h'.2)]`. Use `Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun y _ => ?_` and prove the remaining obligations. Distinguish the cases in `hy : y = e`.

Establish `: ¬ y = e'` using `fun h' => h (hy ▸ h')`. Simplify using `[this]`. Simplify using `[hy]`.
-/
theorem gram_matrix_exists : GramExists := by
  intro K _ _ _ l σ hU hζ E _ _
  obtain ⟨ζ, hζ⟩ := hζ
  obtain ⟨hp, hl2, hnl, -, -⟩ := id hU
  obtain ⟨m, rfl⟩ : ∃ m, l = 2 * m + 1 := by
    rcases hp.eq_two_or_odd' with h | h
    · omega
    · exact h
  have hm : 0 < m := by omega
  have hσζ : σ ζ = ζ ^ (2 * m + 1) := teichSigma K _ 2 σ hU (by norm_num) ζ hζ.pow_eq_one
  have hN0 : (2 * m + 1) ^ 2 - 1 ≠ 0 := by
    have : 1 < (2 * m + 1) ^ 2 := Nat.one_lt_pow (by norm_num) (by omega)
    omega
  have nζ : ‖ζ‖ = 1 := FormalExponential.norm_eq_one_of_pow hN0 hζ.pow_eq_one
  have hσσ : σ (σ ζ) = ζ := by
    rw [hσζ, map_pow, hσζ, ← pow_mul, ← sq]
    have e : (2 * m + 1) ^ 2 = ((2 * m + 1) ^ 2 - 1) + 1 := by omega
    rw [e, pow_succ, hζ.pow_eq_one, one_mul]
  have hlam := OrbitCoverLemmas.lam_spec σ m hm ζ hζ hσζ
  have n2 : ‖(2 : K)‖ = 1 := by
    refine OrbitCoverLemmas.norm_two m ?_
    rw [hnl]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  have nlam : ‖ζ ^ m‖ = 1 := by rw [norm_pow, nζ, one_pow]
  have s2 : σ 2 = 2 := map_ofNat σ 2
  have hblk : ∀ k x : Bool, ‖OrbitCoverLemmas.blk (ζ ^ m) k x‖ ≤ 1 ∧
      σ (σ (OrbitCoverLemmas.blk (ζ ^ m) k x)) = OrbitCoverLemmas.blk (ζ ^ m) k x := by
    intro k x
    cases k <;> cases x <;> simp [OrbitCoverLemmas.blk, nlam, hσσ, n2, s2, map_inv₀]
  refine ⟨fun k x => if k.2 = x.2 then OrbitCoverLemmas.blk (ζ ^ m) k.1 x.1 else 0, fun k x => ?_, ?_⟩
  · dsimp only
    split_ifs
    · exact hblk _ _
    · simp
  · rintro ⟨b, e⟩ ⟨b', e'⟩
    rw [Fintype.sum_prod_type]
    dsimp only
    by_cases h : e = e'
    · subst h
      have h3 : ∀ k : Bool, ∑ y : E, (if y = e then OrbitCoverLemmas.blk (ζ ^ m) k b else 0) *
          σ (if y = e then OrbitCoverLemmas.blk (ζ ^ m) k b' else 0) =
          OrbitCoverLemmas.blk (ζ ^ m) k b * σ (OrbitCoverLemmas.blk (ζ ^ m) k b') := by
        intro k
        rw [Finset.sum_eq_single e]
        · simp
        · intro y _ hy
          simp [hy]
        · simp
      simp only [h3]
      rw [OrbitCoverLemmas.blk_gram σ _ h2 hlam]
      simp
    · rw [if_neg (fun h' => h h'.2)]
      refine Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun y _ => ?_
      by_cases hy : y = e
      · have : ¬ y = e' := fun h' => h (hy ▸ h')
        simp [this]
      · simp [hy]

end Formalism.L2.Th1.D
