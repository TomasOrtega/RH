import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.VeluIntegral
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.DegreeLeOfMemAntidiagonal

noncomputable section
open scoped BigOperators
open PowerSeries

namespace Formalism.L2.Th1.C

namespace USideA

section Int

variable {K : Type} [Field K] {R : Subring K}

/- English proof (translation)
Introduce `n` and use `by rw [map_add] exact R.add_mem (hf n) (hg n)`.
-/
theorem intPS_add {f g : PowerSeries K} (hf : IntPS R f) (hg : IntPS R g) : IntPS R (f + g) := fun n => by
  rw [map_add]
  exact R.add_mem (hf n) (hg n)

/- English proof (translation)
Introduce `n` and use `by rw [map_sub] exact R.sub_mem (hf n) (hg n)`.
-/
theorem intPS_sub {f g : PowerSeries K} (hf : IntPS R f) (hg : IntPS R g) : IntPS R (f - g) := fun n => by
  rw [map_sub]
  exact R.sub_mem (hf n) (hg n)

/- English proof (translation)
Introduce `n` and use `by rw [PowerSeries.coeff_mul] exact R.sum_mem (fun p _ => R.mul_mem (hf _) (hg _))`.
-/
theorem intPS_mul {f g : PowerSeries K} (hf : IntPS R f) (hg : IntPS R g) : IntPS R (f * g) := fun n => by
  rw [PowerSeries.coeff_mul]
  exact R.sum_mem (fun p _ => R.mul_mem (hf _) (hg _))

/- English proof (translation)
Introduce `n` and use `by rw [PowerSeries.coeff_C] split_ifs · exact hc · exact R.zero_mem`.
-/
theorem intPS_C {c : K} (hc : c ∈ R) : IntPS R (PowerSeries.C c) := fun n => by
  rw [PowerSeries.coeff_C]
  split_ifs
  · exact hc
  · exact R.zero_mem

/- English proof (translation)
Introduce `n` and use `by rw [PowerSeries.coeff_X_pow] split_ifs · exact R.one_mem · exact R.zero_mem`.
-/
theorem intPS_X_pow (k : ℕ) : IntPS R (PowerSeries.X ^ k : PowerSeries K) := fun n => by
  rw [PowerSeries.coeff_X_pow]
  split_ifs
  · exact R.one_mem
  · exact R.zero_mem

/- English proof (translation)
Simplify using `using (intPS_X_pow 1 : IntPS R (PowerSeries.X ^ 1 : PowerSeries K))`.
-/
theorem intPS_X : IntPS R (PowerSeries.X : PowerSeries K) := by
  simpa using (intPS_X_pow 1 : IntPS R (PowerSeries.X ^ 1 : PowerSeries K))

/- English proof (translation)
Introduce `n` and use `by rw [map_sum] exact R.sum_mem (fun i hi => hF i hi n)`.
-/
theorem intPS_sum {ι : Type} (s : Finset ι) {F : ι → PowerSeries K} (hF : ∀ i ∈ s, IntPS R (F i)) :
    IntPS R (∑ i ∈ s, F i) := fun n => by
  rw [map_sum]
  exact R.sum_mem (fun i hi => hF i hi n)

/- English proof (translation)
Introduce `n`. Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Establish `h` using `congrArg (PowerSeries.coeff n) hUV`. Rewrite `h` using `[PowerSeries.coeff_mul, PowerSeries.coeff_one]`.

Establish `hmem0 : ((0, n) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal n` using `by simp`. Rewrite `h` using `[← Finset.add_sum_erase (Finset.HasAntidiagonal.antidiagonal n) (fun p : ℕ × ℕ => PowerSeries.coeff p.1 U * PowerSeries.coeff p.2 V) hmem0]`. Simplify using `only [PowerSeries.coeff_zero_eq_constantCoeff_apply, hU0, one_mul] at h`. Establish `hrest : (∑ p ∈ (Finset.HasAntidiagonal.antidiagonal n).erase (0, n), PowerSeries.coeff p.1 U * PowerSeries.coeff p.2 V) ∈ R`. Use `R.sum_mem (fun p hp => R.mul_mem (hU _) (ih _ ?_))` and prove the remaining obligations.

Take `⟨hne, hmem⟩` from `Finset.mem_erase.mp hp`. Rewrite `hmem` using `[Finset.HasAntidiagonal.mem_antidiagonal]`. Assume the negation of the conclusion as `hle`. Apply `hne` to reduce the goal to its premises. Take `⟨a, b⟩` from `p`.

Simplify using `only [Prod.mk.injEq] at hmem hle ⊢`. Apply the tactic sequence `refine ⟨?_, ?_⟩ <;> omega`. Establish `h' : PowerSeries.coeff n V = (if n = 0 then 1 else 0) - ∑ p ∈ (Finset.HasAntidiagonal.antidiagonal n).erase (0, n), PowerSeries.coeff p.1 U * PowerSeries.coeff p.2 V`. Take the linear combination `h`. Rewrite using `[h']`.

Use `R.sub_mem ?_ hrest` and prove the remaining obligations. Use `split_ifs`. Conclude with `R.one_mem`. Conclude with `R.zero_mem`.
-/
theorem intPS_of_mul_eq_one {U V : PowerSeries K} (hU : IntPS R U)
    (hU0 : PowerSeries.constantCoeff U = 1) (hUV : U * V = 1) : IntPS R V := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have h := congrArg (PowerSeries.coeff n) hUV
    rw [PowerSeries.coeff_mul, PowerSeries.coeff_one] at h
    have hmem0 : ((0, n) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal n := by simp
    rw [← Finset.add_sum_erase (Finset.HasAntidiagonal.antidiagonal n)
      (fun p : ℕ × ℕ => PowerSeries.coeff p.1 U * PowerSeries.coeff p.2 V)
      hmem0] at h
    simp only [PowerSeries.coeff_zero_eq_constantCoeff_apply, hU0, one_mul] at h
    have hrest : (∑ p ∈ (Finset.HasAntidiagonal.antidiagonal n).erase (0, n),
        PowerSeries.coeff p.1 U * PowerSeries.coeff p.2 V) ∈ R := by
      refine R.sum_mem (fun p hp => R.mul_mem (hU _) (ih _ ?_))
      obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hp
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hmem
      by_contra hle
      apply hne
      obtain ⟨a, b⟩ := p
      simp only [Prod.mk.injEq] at hmem hle ⊢
      refine ⟨?_, ?_⟩ <;> omega
    have h' : PowerSeries.coeff n V = (if n = 0 then 1 else 0) -
        ∑ p ∈ (Finset.HasAntidiagonal.antidiagonal n).erase (0, n),
          PowerSeries.coeff p.1 U * PowerSeries.coeff p.2 V := by
      linear_combination h
    rw [h']
    refine R.sub_mem ?_ hrest
    split_ifs
    · exact R.one_mem
    · exact R.zero_mem

end Int

section Log

variable {K : Type} [Field K]

/- English proof (translation)
The claim follows from `PowerSeries.HasSubst.of_constantCoeff_zero h`.
-/
theorem hs_of {a : PowerSeries K} (h : PowerSeries.constantCoeff a = 0) : PowerSeries.HasSubst a :=
  PowerSeries.HasSubst.of_constantCoeff_zero h

/- English proof (translation)
Take `⟨q, hq⟩` from `PowerSeries.X_dvd_iff.mpr h.2.2.1`. Establish `ha : PowerSeries.HasSubst (PowerSeries.C al * l)` using `hs_of (by simp [h.1])`. Unfold `mulBy`. Rewrite using `[hq, ← PowerSeries.coe_substAlgHom ha, map_mul, PowerSeries.coe_substAlgHom, PowerSeries.subst_X ha, map_mul, map_mul, h.1, mul_zero, zero_mul]`.
-/
theorem cc_mulBy {l linv : PowerSeries K} (h : IsLogPair l linv) (al : K) :
    PowerSeries.constantCoeff (mulBy l linv al) = 0 := by
  obtain ⟨q, hq⟩ := PowerSeries.X_dvd_iff.mpr h.2.2.1
  have ha : PowerSeries.HasSubst (PowerSeries.C al * l) := hs_of (by simp [h.1])
  unfold mulBy
  rw [hq, ← PowerSeries.coe_substAlgHom ha, map_mul, PowerSeries.coe_substAlgHom,
    PowerSeries.subst_X ha, map_mul, map_mul, h.1, mul_zero, zero_mul]

/- English proof (translation)
Establish `ha : PowerSeries.HasSubst (PowerSeries.C al * l)` using `hs_of (by simp [h.1])`. Establish `hlinv : PowerSeries.HasSubst linv` using `hs_of h.2.2.1`. Unfold `mulBy`. Rewrite using `[← PowerSeries.subst_comp_subst_apply hlinv ha, h.2.2.2.2, PowerSeries.subst_X ha]`.
-/
theorem subst_mulBy_l {l linv : PowerSeries K} (h : IsLogPair l linv) (al : K) :
    PowerSeries.subst (mulBy l linv al) l = PowerSeries.C al * l := by
  have ha : PowerSeries.HasSubst (PowerSeries.C al * l) := hs_of (by simp [h.1])
  have hlinv : PowerSeries.HasSubst linv := hs_of h.2.2.1
  unfold mulBy
  rw [← PowerSeries.subst_comp_subst_apply hlinv ha, h.2.2.2.2, PowerSeries.subst_X ha]

/- English proof (translation)
Establish `hl : PowerSeries.HasSubst l` using `hs_of h.1`. Establish `hm : PowerSeries.HasSubst (mulBy l linv al)` using `hs_of (cc_mulBy h al)`. Establish `hX : PowerSeries.HasSubst (PowerSeries.C al * PowerSeries.X : PowerSeries K)` using `hs_of (by simp)`. Establish `hC : PowerSeries.subst l (PowerSeries.C al) = PowerSeries.C al` using `PowerSeries.subst_C al`. Rewrite using `[PowerSeries.subst_comp_subst_apply hl hm, subst_mulBy_l h, PowerSeries.rescale_eq_subst, PowerSeries.smul_eq_C_mul, PowerSeries.subst_comp_subst_apply hX hl, ← PowerSeries.coe_substAlgHom hl, map_mul, PowerSeries.coe_substAlgHom, hC, PowerSeries.subst_X hl]`.
-/
theorem subst_rescale {l linv : PowerSeries K} (h : IsLogPair l linv) (al : K) (g : PowerSeries K) :
    PowerSeries.subst l (PowerSeries.rescale al g) =
      PowerSeries.subst (mulBy l linv al) (PowerSeries.subst l g) := by
  have hl : PowerSeries.HasSubst l := hs_of h.1
  have hm : PowerSeries.HasSubst (mulBy l linv al) := hs_of (cc_mulBy h al)
  have hX : PowerSeries.HasSubst (PowerSeries.C al * PowerSeries.X : PowerSeries K) := hs_of (by simp)
  have hC : PowerSeries.subst l (PowerSeries.C al) = PowerSeries.C al := PowerSeries.subst_C al
  rw [PowerSeries.subst_comp_subst_apply hl hm, subst_mulBy_l h, PowerSeries.rescale_eq_subst,
    PowerSeries.smul_eq_C_mul, PowerSeries.subst_comp_subst_apply hX hl,
    ← PowerSeries.coe_substAlgHom hl, map_mul, PowerSeries.coe_substAlgHom, hC,
    PowerSeries.subst_X hl]

/- English proof (translation)
Introduce `h0`. Establish `h1` using `h.2.1`. Rewrite `h1` using `[h0, map_zero]`. Conclude with `zero_ne_one h1`.
-/
theorem l_ne_zero {l linv : PowerSeries K} (h : IsLogPair l linv) : l ≠ 0 := by
  intro h0
  have h1 := h.2.1
  rw [h0, map_zero] at h1
  exact zero_ne_one h1

/- English proof (translation)
The claim follows from `PowerSeries.subst_C c`.
-/
theorem subst_C' (a : PowerSeries K) (c : K) :
    PowerSeries.subst a (PowerSeries.C c) = PowerSeries.C c :=
  PowerSeries.subst_C c

/- English proof (translation)
Rewrite using `[← PowerSeries.coe_substAlgHom ha, map_sum]`.
-/
theorem subst_sum {ι : Type} {a : PowerSeries K} (ha : PowerSeries.HasSubst a) (s : Finset ι)
    (F : ι → PowerSeries K) :
    PowerSeries.subst a (∑ i ∈ s, F i) = ∑ i ∈ s, PowerSeries.subst a (F i) := by
  rw [← PowerSeries.coe_substAlgHom ha, map_sum]

/- English proof (translation)
Unfold `wpShift`. Rewrite using `[← PowerSeries.coe_substAlgHom ha]`. Simplify using `only [map_add, map_one, map_mul, map_pow, map_sub, map_zero, sub_zero, PowerSeries.coe_substAlgHom, PowerSeries.subst_X ha]`.
-/
theorem subst_wpShift_zero {a : PowerSeries K} (ha : PowerSeries.HasSubst a) (e : PowerSeries K) :
    PowerSeries.subst a (wpShift e 0) = 1 + a ^ 2 * PowerSeries.subst a e := by
  unfold wpShift
  rw [← PowerSeries.coe_substAlgHom ha]
  simp only [map_add, map_one, map_mul, map_pow, map_sub, map_zero, sub_zero,
    PowerSeries.coe_substAlgHom, PowerSeries.subst_X ha]

end Log

end USideA

open USideA

/- English proof (translation)
Introduce `K _ _ e l linv A c0 ι _ neg xP w xs al h hXW hE hw`. Establish `hl : PowerSeries.HasSubst l` using `hs_of h.1`. Establish `hm : PowerSeries.HasSubst (mulBy l linv al)` using `hs_of (cc_mulBy h al)`. Establish `hal : PowerSeries.HasSubst (PowerSeries.C al * l)` using `hs_of (by simp [h.1])`. Establish `F0 : (A + PowerSeries.C c0 * PowerSeries.X ^ 2) * l ^ 2 = PowerSeries.X ^ 2 * PowerSeries.subst l (wpShift e 0)` using `hXW`.

Establish `F1` using `F0`. Rewrite `F1` using `[subst_wpShift_zero hl]`. Establish `F2` using `congrArg (PowerSeries.subst (mulBy l linv al)) F0`. Rewrite `F2` using `[← PowerSeries.coe_substAlgHom hm]`. Simplify using `only [map_add, map_mul, map_pow, PowerSeries.coe_substAlgHom] at F2`.

Rewrite `F2` using `[subst_C', PowerSeries.subst_X hm, subst_mulBy_l h, PowerSeries.subst_comp_subst_apply hl hm, subst_mulBy_l h, subst_wpShift_zero hal]`. Establish `hZr : PowerSeries.subst (PowerSeries.C al * l) e = PowerSeries.subst l (PowerSeries.rescale al e)`. Rewrite using `[subst_rescale h, PowerSeries.subst_comp_subst_apply hl hm, subst_mulBy_l h]`. Establish `F3` using `congrArg (PowerSeries.subst l) hE.2.2`. Rewrite `F3` using `[← PowerSeries.coe_substAlgHom hl]`.

Simplify using `only [map_add, map_mul, map_sum, map_sub, PowerSeries.coe_substAlgHom] at F3`. Simplify using `only [subst_C'] at F3`. Simplify using `only [hw, ← hZr, map_pow, map_add] at F3`. Establish `hsum : ∑ P, (xs P + PowerSeries.C c0 - (PowerSeries.C (xP P) + PowerSeries.C c0)) = ∑ P, (xs P - PowerSeries.C (xP P))` using `Finset.sum_congr rfl (fun P _ => by ring)`. Rewrite `F3` using `[hsum]`.

Unfold `veluXs`. Simplify using `only [map_pow, map_mul, map_sub, map_one]`. Establish `key : l ^ 2 * (PowerSeries.C al ^ 2 * PowerSeries.subst (mulBy l linv al) A * PowerSeries.X ^ 2 - mulBy l linv al ^ 2 * (A + PowerSeries.X ^ 2 * (∑ P, (xs P - PowerSeries.C (xP P)) - (PowerSeries.C al ^ 2 - 1) * PowerSeries.C c0))) = 0`. Take the linear combination `PowerSeries.X ^ 2 * F2 + mulBy l linv al ^ 2 * PowerSeries.X ^ 2 * l ^ 2 * F3 - mulBy l linv al ^ 2 * F1`. Conclude with `sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_left (pow_ne_zero 2 (l_ne_zero h)))`.
-/
theorem veluXOfSigma' : VeluXFromZ := by
  intro K _ _ e l linv A c0 ι _ neg xP w xs al h hXW hE hw
  have hl : PowerSeries.HasSubst l := hs_of h.1
  have hm : PowerSeries.HasSubst (mulBy l linv al) := hs_of (cc_mulBy h al)
  have hal : PowerSeries.HasSubst (PowerSeries.C al * l) := hs_of (by simp [h.1])
  have F0 : (A + PowerSeries.C c0 * PowerSeries.X ^ 2) * l ^ 2 =
      PowerSeries.X ^ 2 * PowerSeries.subst l (wpShift e 0) := hXW
  have F1 := F0
  rw [subst_wpShift_zero hl] at F1
  have F2 := congrArg (PowerSeries.subst (mulBy l linv al)) F0
  rw [← PowerSeries.coe_substAlgHom hm] at F2
  simp only [map_add, map_mul, map_pow, PowerSeries.coe_substAlgHom] at F2
  rw [subst_C', PowerSeries.subst_X hm, subst_mulBy_l h, PowerSeries.subst_comp_subst_apply hl hm,
    subst_mulBy_l h, subst_wpShift_zero hal] at F2
  have hZr : PowerSeries.subst (PowerSeries.C al * l) e = PowerSeries.subst l (PowerSeries.rescale al e) := by
    rw [subst_rescale h, PowerSeries.subst_comp_subst_apply hl hm, subst_mulBy_l h]
  have F3 := congrArg (PowerSeries.subst l) hE.2.2
  rw [← PowerSeries.coe_substAlgHom hl] at F3
  simp only [map_add, map_mul, map_sum, map_sub, PowerSeries.coe_substAlgHom] at F3
  simp only [subst_C'] at F3
  simp only [hw, ← hZr, map_pow, map_add] at F3
  have hsum : ∑ P, (xs P + PowerSeries.C c0 - (PowerSeries.C (xP P) + PowerSeries.C c0)) =
      ∑ P, (xs P - PowerSeries.C (xP P)) := Finset.sum_congr rfl (fun P _ => by ring)
  rw [hsum] at F3
  unfold veluXs
  simp only [map_pow, map_mul, map_sub, map_one]
  have key : l ^ 2 * (PowerSeries.C al ^ 2 * PowerSeries.subst (mulBy l linv al) A * PowerSeries.X ^ 2 -
      mulBy l linv al ^ 2 * (A + PowerSeries.X ^ 2 * (∑ P, (xs P - PowerSeries.C (xP P)) -
        (PowerSeries.C al ^ 2 - 1) * PowerSeries.C c0))) = 0 := by
    linear_combination PowerSeries.X ^ 2 * F2 + mulBy l linv al ^ 2 * PowerSeries.X ^ 2 * l ^ 2 * F3 -
      mulBy l linv al ^ 2 * F1
  exact sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_left (pow_ne_zero 2 (l_ne_zero h)))

end Formalism.L2.Th1.C
