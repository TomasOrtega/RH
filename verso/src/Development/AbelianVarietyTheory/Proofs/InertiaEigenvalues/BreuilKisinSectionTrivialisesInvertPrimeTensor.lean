import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemInvLSIffTendsto
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerContentValuationDetPowBounds
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinXiExtMemRigidTensorIffStatement
open PowerSeries GlobalTheory.BK Filter Topology

namespace GlobalTheory.BK

/- English proof (translation)
Rewrite using `[← map_natCast (algebraMap ℚ_[l] K), norm_algebraMap', Padic.norm_eq_zpow_neg_valuation (by exact_mod_cast hN), Padic.valuation_natCast, ← Real.rpow_intCast]`. Use `congr 1`. Use `push_cast`. Simplify using `[padicValRat.of_nat]`.
-/
theorem norm_natCast_eq_rpow_padicValNat (l : ℕ) [Fact l.Prime] (K : Type) [NormedField K]
    [NormedAlgebra ℚ_[l] K] (N : ℕ) (hN : N ≠ 0) :
    ‖(N : K)‖ = (l : ℝ) ^ (-(padicValNat l N : ℝ)) := by
  rw [← map_natCast (algebraMap ℚ_[l] K), norm_algebraMap',
    Padic.norm_eq_zpow_neg_valuation (by exact_mod_cast hN), Padic.valuation_natCast,
    ← Real.rpow_intCast]
  congr 1
  push_cast
  simp [padicValRat.of_nat]

/- English proof (translation)
Establish `hl : (1 : ℝ) < l` using `by exact_mod_cast (Fact.out : l.Prime).one_lt`. Establish `hl0 : (0 : ℝ) < l` using `by linarith`. Establish `hq : (0 : ℝ) < (l : ℝ) - 1` using `by linarith`. Establish `he : (0 : ℝ) < e` using `by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne e)`. Use `set m := n / e with hmdef`.

Establish `hv` using `GlobalTheory.DetPowContent.padicValNat_factorial_ge l (Fact.out : l.Prime) m`. Establish `hm : (n : ℝ) / e - 1 ≤ m`. Establish `h1 : n < (m + 1) * e`. Use `Nat.lt_div_mul_add (a := n) (Nat.pos_of_ne_zero (NeZero.ne e))` as an intermediate fact. Rewrite using `[hmdef]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `h2 : (n : ℝ) < ((m : ℝ) + 1) * e` using `by exact_mod_cast h1`. Rewrite using `[div_sub_one he.ne', div_le_iff₀ he]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hm1 : ((m : ℝ) + 1) ≤ (n : ℝ) + 1`.

Establish `: m ≤ n` using `Nat.div_le_self n e`. Conclude with `Nat.add_le_add_right this 1` after adjusting the coercions. Unfold `wS`. Rewrite using `[← hmdef, norm_natCast_eq_rpow_padicValNat l K _ (Nat.factorial_ne_zero m)]`. Establish `hexp : -(padicValNat l m.factorial : ℝ) ≤ Real.logb l ((m : ℝ) + 1) + 1 / ((l : ℝ) - 1) + -(n : ℝ) * (1 / ((e : ℝ) * ((l : ℝ) - 1)))`.

Establish `h3 : (n : ℝ) * (1 / ((e : ℝ) * ((l : ℝ) - 1))) = ((n : ℝ) / e) / ((l : ℝ) - 1)`. Clear the denominators using the available nonvanishing facts. Establish `h4 : ((n : ℝ) / e) / ((l : ℝ) - 1) ≤ (m : ℝ) / ((l : ℝ) - 1) + 1 / ((l : ℝ) - 1)`. Rewrite using `[← add_div]; exact div_le_div_of_nonneg_right (by linarith) hq.le`. Use the polynomial consequences of the given equalities and inequalities.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Real.rpow_add hl0, Real.rpow_add hl0, Real.rpow_logb hl0 hl.ne' (by positivity)]`. Use `_ ≤ _ := by`. Rewrite using `[mul_comm ((m : ℝ) + 1)]`. Use `gcongr`.
-/
theorem wS_le_rpow (K : Type) [NormedField K] [IsUltrametricDist K] (l e : ℕ) [Fact l.Prime]
    [NormedAlgebra ℚ_[l] K] [NeZero e] (n : ℕ) :
    wS K e n ≤ (l : ℝ) ^ (1 / ((l : ℝ) - 1)) * ((n : ℝ) + 1) *
      (l : ℝ) ^ (-(n : ℝ) * (1 / ((e : ℝ) * ((l : ℝ) - 1)))) := by
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl0 : (0 : ℝ) < l := by linarith
  have hq : (0 : ℝ) < (l : ℝ) - 1 := by linarith
  have he : (0 : ℝ) < e := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne e)
  set m := n / e with hmdef
  have hv := GlobalTheory.DetPowContent.padicValNat_factorial_ge l (Fact.out : l.Prime) m
  have hm : (n : ℝ) / e - 1 ≤ m := by
    have h1 : n < (m + 1) * e := by
      have := Nat.lt_div_mul_add (a := n) (Nat.pos_of_ne_zero (NeZero.ne e))
      rw [hmdef]; linarith
    have h2 : (n : ℝ) < ((m : ℝ) + 1) * e := by exact_mod_cast h1
    rw [div_sub_one he.ne', div_le_iff₀ he]; linarith
  have hm1 : ((m : ℝ) + 1) ≤ (n : ℝ) + 1 := by
    have : m ≤ n := Nat.div_le_self n e
    exact_mod_cast Nat.add_le_add_right this 1
  unfold wS
  rw [← hmdef, norm_natCast_eq_rpow_padicValNat l K _ (Nat.factorial_ne_zero m)]
  have hexp : -(padicValNat l m.factorial : ℝ) ≤ Real.logb l ((m : ℝ) + 1) + 1 / ((l : ℝ) - 1) +
      -(n : ℝ) * (1 / ((e : ℝ) * ((l : ℝ) - 1))) := by
    have h3 : (n : ℝ) * (1 / ((e : ℝ) * ((l : ℝ) - 1))) = ((n : ℝ) / e) / ((l : ℝ) - 1) := by
      field_simp
    have h4 : ((n : ℝ) / e) / ((l : ℝ) - 1) ≤ (m : ℝ) / ((l : ℝ) - 1) + 1 / ((l : ℝ) - 1) := by
      rw [← add_div]; exact div_le_div_of_nonneg_right (by linarith) hq.le
    nlinarith
  calc (l : ℝ) ^ (-(padicValNat l m.factorial : ℝ))
      ≤ (l : ℝ) ^ (Real.logb l ((m : ℝ) + 1) + 1 / ((l : ℝ) - 1) +
          -(n : ℝ) * (1 / ((e : ℝ) * ((l : ℝ) - 1)))) := Real.rpow_le_rpow_of_exponent_le hl.le hexp
    _ = ((m : ℝ) + 1) * (l : ℝ) ^ (1 / ((l : ℝ) - 1)) *
          (l : ℝ) ^ (-(n : ℝ) * (1 / ((e : ℝ) * ((l : ℝ) - 1)))) := by
      rw [Real.rpow_add hl0, Real.rpow_add hl0, Real.rpow_logb hl0 hl.ne' (by positivity)]
    _ ≤ _ := by
      rw [mul_comm ((m : ℝ) + 1)]
      gcongr

end GlobalTheory.BK

open Matrix

namespace GlobalTheory.BK

/- English proof (translation)
Introduce `f hf`. Rewrite using `[mem_invL_S_iff_tendsto O K l e f]`. Establish `hR` using `mem_R.1 hf`. Establish `hl : (1 : ℝ) < l` using `by exact_mod_cast (Fact.out : l.Prime).one_lt`. Establish `hl0 : (0 : ℝ) < l` using `by linarith`.

Use `set k0 := 1 / ((e : ℝ) * (l - 1)) with hk0`. Use `set q := (l : ℝ) ^ (k - k0) with hqdef`. Establish `hq0 : 0 ≤ q` using `Real.rpow_nonneg hl0.le _`. Establish `hq1 : q < 1` using `Real.rpow_lt_one_of_one_lt_of_neg hl (by linarith)`. Use `set C := (l : ℝ) ^ (1 / ((l : ℝ) - 1)) with hC`.

Establish `hg : Tendsto (fun n : ℕ => C * (((n : ℝ) + 1) * q ^ n)) atTop (𝓝 0)`. Establish `h1` using `(tendsto_self_mul_const_pow_of_lt_one hq0 hq1).add (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1)`. Rewrite `h1` using `[add_zero]`. Establish `h2` using `h1.const_mul C`. Rewrite `h2` using `[mul_zero]`.

Conclude with `h2.congr fun n => by ring`. Establish `hprod` using `hR.mul hg`. Rewrite `hprod` using `[zero_mul]`. Use `squeeze_zero (fun n => mul_nonneg (norm_nonneg _) (wS_nonneg e n)) (fun n => ?_) hprod` and prove the remaining obligations. Establish `hw` using `wS_le_rpow K l e n`.

Establish `hrad : rad l k ^ n * q ^ n = (l : ℝ) ^ (-(n : ℝ) * k0)`. Rewrite using `[rad, hqdef, ← Real.rpow_mul_natCast hl0.le, ← Real.rpow_mul_natCast hl0.le, ← Real.rpow_add hl0]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[← hrad]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem R_le_invL_S (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [Algebra O K] [IsUnitBall O K] (l e : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e]
    (k : ℝ) (hk : k < 1 / ((e : ℝ) * (l - 1))) : R O K l k ≤ invL l (S O K e) := by
  intro f hf
  rw [mem_invL_S_iff_tendsto O K l e f]
  have hR := mem_R.1 hf
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl0 : (0 : ℝ) < l := by linarith
  set k0 := 1 / ((e : ℝ) * (l - 1)) with hk0
  set q := (l : ℝ) ^ (k - k0) with hqdef
  have hq0 : 0 ≤ q := Real.rpow_nonneg hl0.le _
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg hl (by linarith)
  set C := (l : ℝ) ^ (1 / ((l : ℝ) - 1)) with hC
  have hg : Tendsto (fun n : ℕ => C * (((n : ℝ) + 1) * q ^ n)) atTop (𝓝 0) := by
    have h1 := (tendsto_self_mul_const_pow_of_lt_one hq0 hq1).add
      (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1)
    rw [add_zero] at h1
    have h2 := h1.const_mul C
    rw [mul_zero] at h2
    exact h2.congr fun n => by ring
  have hprod := hR.mul hg
  rw [zero_mul] at hprod
  refine squeeze_zero (fun n => mul_nonneg (norm_nonneg _) (wS_nonneg e n)) (fun n => ?_) hprod
  have hw := wS_le_rpow K l e n
  have hrad : rad l k ^ n * q ^ n = (l : ℝ) ^ (-(n : ℝ) * k0) := by
    rw [rad, hqdef, ← Real.rpow_mul_natCast hl0.le, ← Real.rpow_mul_natCast hl0.le,
      ← Real.rpow_add hl0]
    congr 1; ring
  calc ‖coeff n f‖ * wS K e n ≤ ‖coeff n f‖ * (C * ((n : ℝ) + 1) * (l : ℝ) ^ (-(n : ℝ) * k0)) :=
        mul_le_mul_of_nonneg_left hw (norm_nonneg _)
    _ = ‖coeff n f‖ * rad l k ^ n * (C * (((n : ℝ) + 1) * q ^ n)) := by
        rw [← hrad]; ring

/- English proof (translation)
Introduce `i` and use `Subalgebra.sum_mem _ fun j _ => B.mul_mem (hM i j) (hv j)`.
-/
theorem mulVec_mem_vecs {ι : Type} [Fintype ι] {O K : Type} [CommRing O] [NormedField K] [Algebra O K]
    {B : Subalgebra O K⟦X⟧} {M : Matrix ι ι K⟦X⟧} (hM : ∀ i j, M i j ∈ B) {v : ι → K⟦X⟧}
    (hv : v ∈ vecs ι B) : M *ᵥ v ∈ vecs ι B := fun i =>
  Subalgebra.sum_mem _ fun j _ => B.mul_mem (hM i j) (hv j)

end GlobalTheory.BK

open GlobalTheory.BK in
/- English proof (translation)
Introduce `O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ P`. Use `⟨fun k hk => R_le_invL_S O K l e k hk, fun w => ?_⟩` and prove the remaining obligations. Establish `hl : (2 : ℝ) ≤ l` using `by exact_mod_cast (Fact.out : l.Prime).two_le`. Establish `he : (0 : ℝ) < e` using `by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne e)`. Use `set k : ℝ := (1 / ((e : ℝ) * l) + 1 / ((e : ℝ) * (l - 1))) / 2 with hkdef`.

Establish `hlt : 1 / ((e : ℝ) * l) < 1 / ((e : ℝ) * (l - 1))` using `one_div_lt_one_div_of_lt (by nlinarith) (by nlinarith)`. Establish `hk1 : 1 / ((e : ℝ) * l) < k` using `by rw [hkdef]; linarith`. Establish `hk2 : k < 1 / ((e : ℝ) * (l - 1))` using `by rw [hkdef]; linarith`. Establish `hRB` using `R_le_invL_S O K l e k hk2`. Establish `hT` using `GlobalTheory.T.breuilKisin_xiExt_mem_rigidTensor_iff O K l e a ι P k hk1`.

Use `set Y : ZMod a → Matrix ι ι K⟦X⟧ := fun τ => P.mxInv τ * P.xiMat τ with hY`. Establish `hext : ∀ (B : Subalgebra O K⟦X⟧) (v : Vec K a ι), P.xiExt v ∈ P.ext B ↔ ∀ τ, Y τ *ᵥ v τ ∈ vecs ι B`. Introduce `B v`. Simplify using `only [PhiMod.ext, mem_tot, PhiMod.mem_extc_iff, PhiMod.xiExt_apply, Matrix.mulVec_mulVec, hY]`. Establish `hM : ∀ (B : Subalgebra O K⟦X⟧) (v : Vec K a ι), v ∈ P.Mext B ↔ ∀ τ, v τ ∈ vecs ι B`.

Introduce `B v`. Simplify using `only [PhiMod.Mext, mem_tot]`. Establish `hYu : ∀ τ, IsUnit (Y τ).det`. Introduce `τ`. Rewrite using `[hY, Matrix.det_mul]`.

Conclude with `(Matrix.isUnit_det_of_left_inverse (P.mx_mul_mxInv τ)).mul (P.isUnit_det_xiMat τ)`. Establish `hYR : ∀ τ i j, Y τ i j ∈ R O K l k`. Introduce `τ i j`. Establish `h0 : (fun _ : ZMod a => (Pi.single j 1 : ι → K⟦X⟧)) ∈ P.Mext (R O K l k)`. Rewrite using `[hM]`.

Introduce `τ' i'`. Rewrite using `[Pi.single_apply]`. Use `split_ifs`. Use `exacts [one_mem _, zero_mem _]`. Establish `h1` using `(hext _ _).1 ((hT _).2 h0) τ i`.

Simplify `h1` using `[Matrix.mulVec_single_one]`. Establish `hZR : ∀ τ i j, (Y τ)⁻¹ i j ∈ R O K l k`. Introduce `τ i j`. Establish `h0 : P.xiExt (fun τ' => (Y τ')⁻¹ *ᵥ (Pi.single j 1 : ι → K⟦X⟧)) ∈ P.Lk k`. Rewrite using `[PhiMod.Lk, hext]`.

Introduce `τ' i'`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (hYu τ'), Matrix.one_mulVec, Pi.single_apply]`. Use `split_ifs`. Use `exacts [one_mem _, zero_mem _]`. Establish `h1` using `(hM _ _).1 ((hT _).1 h0) τ i`.

Simplify `h1` using `[Matrix.mulVec_single_one]`. Rewrite using `[PhiMod.MMl, hext, hM]`. Prove the components needed by the constructor for the conclusion. Introduce `h τ`. Use `mulVec_mem_vecs (fun i j => hRB (hZR τ i j)) (h τ)` as an intermediate fact.

Rewrite `this` using `[Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (hYu τ), Matrix.one_mulVec]`. Then use the resulting hypothesis. Introduce `h τ`. Conclude with `mulVec_mem_vecs (fun i j => hRB (hYR τ i j)) (h τ)`.
-/
theorem GlobalTheory.BK.xi_trivialises_invL_S : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] (P : PhiMod O K l e a ι), (∀ k : ℝ, k < 1 / ((e : ℝ) * (l - 1)) → R O K l k ≤ invL l (S O K e)) ∧ ∀ w : Vec K a ι, P.xiExt w ∈ P.MMl ↔ w ∈ P.Mext (invL l (S O K e)) := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ P
  refine ⟨fun k hk => R_le_invL_S O K l e k hk, fun w => ?_⟩
  have hl : (2 : ℝ) ≤ l := by exact_mod_cast (Fact.out : l.Prime).two_le
  have he : (0 : ℝ) < e := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne e)
  set k : ℝ := (1 / ((e : ℝ) * l) + 1 / ((e : ℝ) * (l - 1))) / 2 with hkdef
  have hlt : 1 / ((e : ℝ) * l) < 1 / ((e : ℝ) * (l - 1)) :=
    one_div_lt_one_div_of_lt (by nlinarith) (by nlinarith)
  have hk1 : 1 / ((e : ℝ) * l) < k := by rw [hkdef]; linarith
  have hk2 : k < 1 / ((e : ℝ) * (l - 1)) := by rw [hkdef]; linarith
  have hRB := R_le_invL_S O K l e k hk2
  have hT := GlobalTheory.T.breuilKisin_xiExt_mem_rigidTensor_iff O K l e a ι P k hk1
  set Y : ZMod a → Matrix ι ι K⟦X⟧ := fun τ => P.mxInv τ * P.xiMat τ with hY
  have hext : ∀ (B : Subalgebra O K⟦X⟧) (v : Vec K a ι),
      P.xiExt v ∈ P.ext B ↔ ∀ τ, Y τ *ᵥ v τ ∈ vecs ι B := by
    intro B v
    simp only [PhiMod.ext, mem_tot, PhiMod.mem_extc_iff, PhiMod.xiExt_apply, Matrix.mulVec_mulVec, hY]
  have hM : ∀ (B : Subalgebra O K⟦X⟧) (v : Vec K a ι), v ∈ P.Mext B ↔ ∀ τ, v τ ∈ vecs ι B := by
    intro B v
    simp only [PhiMod.Mext, mem_tot]
  have hYu : ∀ τ, IsUnit (Y τ).det := by
    intro τ
    rw [hY, Matrix.det_mul]
    exact (Matrix.isUnit_det_of_left_inverse (P.mx_mul_mxInv τ)).mul (P.isUnit_det_xiMat τ)

  have hYR : ∀ τ i j, Y τ i j ∈ R O K l k := by
    intro τ i j
    have h0 : (fun _ : ZMod a => (Pi.single j 1 : ι → K⟦X⟧)) ∈ P.Mext (R O K l k) := by
      rw [hM]; intro τ' i'
      rw [Pi.single_apply]; split_ifs
      exacts [one_mem _, zero_mem _]
    have h1 := (hext _ _).1 ((hT _).2 h0) τ i
    simpa [Matrix.mulVec_single_one] using h1

  have hZR : ∀ τ i j, (Y τ)⁻¹ i j ∈ R O K l k := by
    intro τ i j
    have h0 : P.xiExt (fun τ' => (Y τ')⁻¹ *ᵥ (Pi.single j 1 : ι → K⟦X⟧)) ∈ P.Lk k := by
      rw [PhiMod.Lk, hext]; intro τ' i'
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (hYu τ'), Matrix.one_mulVec, Pi.single_apply]
      split_ifs
      exacts [one_mem _, zero_mem _]
    have h1 := (hM _ _).1 ((hT _).1 h0) τ i
    simpa [Matrix.mulVec_single_one] using h1
  rw [PhiMod.MMl, hext, hM]
  constructor
  · intro h τ
    have := mulVec_mem_vecs (fun i j => hRB (hZR τ i j)) (h τ)
    rwa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (hYu τ), Matrix.one_mulVec] at this
  · intro h τ
    exact mulVec_mem_vecs (fun i j => hRB (hYR τ i j)) (h τ)
