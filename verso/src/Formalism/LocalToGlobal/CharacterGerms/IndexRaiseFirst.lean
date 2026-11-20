import Formalism.LocalToGlobal.CharacterGerms.ConstantZeroRestrictPoints

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.FunEq

open Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.PartialDerivEval ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ MvPowerSeries

variable {C : Type} [Field C] [CharZero C] {dd : ℕ} {V : VF C}

def ix (i : Fin dd) (L : ℕ) (γ : Fin 2 × Fin dd →₀ ℕ) : Fin 3 × Fin dd →₀ ℕ :=
  Finsupp.single ((0 : Fin 3), i) L + γ.mapDomain (up 2)

/- English proof (translation)
Establish `hn : ((0 : Fin 3), j) ∉ Set.range (up (dd` using `dd) 2) := by`. Introduce and unpack `⟨q, hq⟩`. Simplify using `only [up, Prod.mk.injEq] at hq`. Conclude with `Fin.succ_ne_zero _ hq.1`. Simplify using `only [ix, Finsupp.add_apply, Finsupp.mapDomain_notin_range _ _ hn, add_zero, Finsupp.single_apply, Prod.mk.injEq, true_and]`.

Distinguish the cases in `h : j = i`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[h, Ne.symm h]`.
-/
theorem index_raise_first (i : Fin dd) (L : ℕ) (γ : Fin 2 × Fin dd →₀ ℕ) (j : Fin dd) :
    ix i L γ ((0 : Fin 3), j) = if j = i then L else 0 := by
  have hn : ((0 : Fin 3), j) ∉ Set.range (up (dd := dd) 2) := by
    rintro ⟨q, hq⟩
    simp only [up, Prod.mk.injEq] at hq
    exact Fin.succ_ne_zero _ hq.1
  simp only [ix, Finsupp.add_apply, Finsupp.mapDomain_notin_range _ _ hn, add_zero, Finsupp.single_apply,
    Prod.mk.injEq, true_and]
  by_cases h : j = i
  · subst h; simp
  · simp [h, Ne.symm h]

def FrobX (V : VF C) (f : PS C 3 dd) : Prop :=
  ∀ p : Fin 3 × Fin dd →₀ ℕ, (∃ j, ¬ V.l ∣ p ((0 : Fin 3), j)) → V.MM (coeff p f)

def FrobD (V : VF C) (f : PS C 3 dd) : Prop := ∀ j : Fin dd, MaximalIdealCongruence.MMS V (pderiv C ((0 : Fin 3), j) f)

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simp [AddValuation.map_zero]`. Consider the case `succ m ih`. Rewrite using `[Nat.cast_succ]`. Use `le_trans (le_min ih ?_) (AddValuation.map_add _ _ _)` and prove the remaining obligations.

Rewrite using `[AddValuation.map_one]`.
-/
private theorem v_natCast_nonneg_of_vf (V : VF C) (m : ℕ) : 0 ≤ V.v (m : C) := by
  induction m with
  | zero => simp [AddValuation.map_zero]
  | succ m ih =>
    rw [Nat.cast_succ]
    refine le_trans (le_min ih ?_) (AddValuation.map_add _ _ _)
    rw [AddValuation.map_one]

/- English proof (translation)
Take `⟨m, rfl | rfl⟩` from `Int.eq_nat_or_neg a`. Rewrite using `[Int.cast_natCast]`. Conclude with `v_natCast_nonneg_of_vf V m`. Rewrite using `[Int.cast_neg, Int.cast_natCast, AddValuation.map_neg]`. Conclude with `v_natCast_nonneg_of_vf V m`.
-/
private theorem v_intCast_nonneg' (V : VF C) (a : ℤ) : 0 ≤ V.v (a : C) := by
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg a
  · rw [Int.cast_natCast]
    exact v_natCast_nonneg_of_vf V m
  · rw [Int.cast_neg, Int.cast_natCast, AddValuation.map_neg]
    exact v_natCast_nonneg_of_vf V m

/- English proof (translation)
Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`. Establish `hcop : Nat.Coprime n V.l` using `Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd V.l_prime).mpr hn)`. Establish `hb` using `Nat.gcd_eq_gcd_ab n V.l`. Rewrite `hb` using `[hcop.gcd_eq_one, Nat.cast_one]`.

Establish `h1 : (1 : C) = (n : C) * (Nat.gcdA n V.l : C) + (V.l : C) * (Nat.gcdB n V.l : C)`. Use `congrArg (fun z : ℤ => (z : C)) hb` as an intermediate fact. Conclude with `this` after adjusting the coercions. Establish `h01 : (0 : WithTop ℝ) < 1`. Rewrite using `[← WithTop.coe_zero, ← WithTop.coe_one, WithTop.coe_lt_coe]`.

Conclude with `one_pos`. Establish `ha : 0 < V.v ((n : C) * (Nat.gcdA n V.l : C))`. Rewrite using `[AddValuation.map_mul]`. Conclude with `add_pos_of_pos_of_nonneg hlt (v_intCast_nonneg' V _)`. Establish `hb' : 0 < V.v ((V.l : C) * (Nat.gcdB n V.l : C))`.

Rewrite using `[AddValuation.map_mul, V.v_l]`. Conclude with `add_pos_of_pos_of_nonneg h01 (v_intCast_nonneg' V _)`. Use `lt_of_lt_of_le (lt_min ha hb') (AddValuation.map_add _ _ _)` as an intermediate fact. Rewrite `this` using `[← h1, AddValuation.map_one]`. Conclude with `lt_irrefl _ this`.
-/
private theorem v_natCast_nonpos_of_not_dvd (V : VF C) (n : ℕ) (hn : ¬ V.l ∣ n) : V.v (n : C) ≤ 0 := by
  by_contra hlt
  push_neg at hlt
  have hcop : Nat.Coprime n V.l :=
    Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd V.l_prime).mpr hn)
  have hb := Nat.gcd_eq_gcd_ab n V.l
  rw [hcop.gcd_eq_one, Nat.cast_one] at hb
  have h1 : (1 : C) = (n : C) * (Nat.gcdA n V.l : C) + (V.l : C) * (Nat.gcdB n V.l : C) := by
    have := congrArg (fun z : ℤ => (z : C)) hb
    exact_mod_cast this
  have h01 : (0 : WithTop ℝ) < 1 := by
    rw [← WithTop.coe_zero, ← WithTop.coe_one, WithTop.coe_lt_coe]
    exact one_pos
  have ha : 0 < V.v ((n : C) * (Nat.gcdA n V.l : C)) := by
    rw [AddValuation.map_mul]
    exact add_pos_of_pos_of_nonneg hlt (v_intCast_nonneg' V _)
  have hb' : 0 < V.v ((V.l : C) * (Nat.gcdB n V.l : C)) := by
    rw [AddValuation.map_mul, V.v_l]
    exact add_pos_of_pos_of_nonneg h01 (v_intCast_nonneg' V _)
  have := lt_of_lt_of_le (lt_min ha hb') (AddValuation.map_add _ _ _)
  rw [← h1, AddValuation.map_one] at this
  exact lt_irrefl _ this

/- English proof (translation)
Unfold `FrobD MaximalIdealCongruence.MMS at hd`. Introduce and unpack `p ⟨j, hj⟩`. Establish `hp0 : p ((0 : Fin 3), j) ≠ 0`. Introduce `h`. Rewrite `hj` using `[h]`.

Conclude with `hj (dvd_zero _)`. Establish `h` using `hd j (p - Finsupp.single ((0 : Fin 3), j) 1)`. Establish `hle : Finsupp.single ((0 : Fin 3), j) 1 ≤ p`. Rewrite using `[Finsupp.single_le_iff]`. Conclude with `Nat.one_le_iff_ne_zero.mpr hp0`.

Rewrite `h` using `[MvPowerSeries.coeff_pderiv, tsub_add_cancel_of_le hle]`. Establish `hn : ((((p - Finsupp.single ((0 : Fin 3), j) 1 : Fin 3 × Fin dd →₀ ℕ) ((0 : Fin 3), j)) : ℕ) : C) + 1 = (p ((0 : Fin 3), j) : C)`. Rewrite using `[Finsupp.tsub_apply, Finsupp.single_eq_same]`. Conclude with `Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hp0)` after adjusting the coercions. Rewrite `h` using `[hn]`.

Unfold `VF.MM at h ⊢`. Rewrite `h` using `[AddValuation.map_mul]`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Use `add_le_add hc (v_natCast_nonpos_of_not_dvd V _ hj)` as an intermediate fact.

Rewrite `this` using `[add_zero]`. Conclude with `absurd h (not_lt.mpr this)`.
-/
theorem frobX_of {f : PS C 3 dd} (hi : IntS V f) (hd : FrobD V f) : FrobX V f := by
  unfold FrobD MaximalIdealCongruence.MMS at hd
  rintro p ⟨j, hj⟩
  have hp0 : p ((0 : Fin 3), j) ≠ 0 := by
    intro h
    rw [h] at hj
    exact hj (dvd_zero _)
  have h := hd j (p - Finsupp.single ((0 : Fin 3), j) 1)
  have hle : Finsupp.single ((0 : Fin 3), j) 1 ≤ p := by
    rw [Finsupp.single_le_iff]
    exact Nat.one_le_iff_ne_zero.mpr hp0
  rw [MvPowerSeries.coeff_pderiv, tsub_add_cancel_of_le hle] at h
  have hn : ((((p - Finsupp.single ((0 : Fin 3), j) 1 : Fin 3 × Fin dd →₀ ℕ) ((0 : Fin 3), j)) : ℕ) : C) + 1 =
      (p ((0 : Fin 3), j) : C) := by
    rw [Finsupp.tsub_apply, Finsupp.single_eq_same]
    exact_mod_cast Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hp0)
  rw [hn] at h
  unfold VF.MM at h ⊢
  rw [AddValuation.map_mul] at h
  by_contra hc
  push_neg at hc
  have := add_le_add hc (v_natCast_nonpos_of_not_dvd V _ hj)
  rw [add_zero] at this
  exact absurd h (not_lt.mpr this)

/- English proof (translation)
Unfold `VF.MM at *`. Conclude with `lt_of_lt_of_le (lt_min ha hb) (AddValuation.map_add _ _ _)`.
-/
private theorem mm_add_of_mm_of_mm {V : VF C} {a b : C} (ha : V.MM a) (hb : V.MM b) : V.MM (a + b) := by
  unfold VF.MM at *
  exact lt_of_lt_of_le (lt_min ha hb) (AddValuation.map_add _ _ _)

/- English proof (translation)
Use `Finset.sum_induction a (fun x => V.MM x) (fun x y hx hy => mm_add_of_mm_of_mm hx hy) ?_ h` and prove the remaining obligations. Unfold `VF.MM`. Rewrite using `[AddValuation.map_zero, ← WithTop.coe_zero]`. Conclude with `WithTop.coe_lt_top _`.
-/
private theorem mm_finset_sum_of_forall_mm {V : VF C} {ι : Type} (s : Finset ι) (a : ι → C) (h : ∀ i ∈ s, V.MM (a i)) :
    V.MM (∑ i ∈ s, a i) := by
  refine Finset.sum_induction a (fun x => V.MM x) (fun x y hx hy => mm_add_of_mm_of_mm hx hy) ?_ h
  unfold VF.MM
  rw [AddValuation.map_zero, ← WithTop.coe_zero]
  exact WithTop.coe_lt_top _

/- English proof (translation)
Introduce `μ`. Rewrite using `[MvPowerSeries.coeff_mul]`. Apply `mm_finset_sum_of_forall_mm` to reduce the goal to its premises. Introduce `x _`. Establish `h1` using `hf x.1`.

Establish `h2` using `hh x.2`. Unfold `VF.Ge at h1`. Unfold `VF.MM at h2 ⊢`. Rewrite using `[AddValuation.map_mul]`. Establish `h1' : (0 : WithTop ℝ) ≤ V.v (coeff x.1 f)` using `by simpa using h1`.

Conclude with `lt_of_lt_of_le h2 (le_add_of_nonneg_left h1')`.
-/
private theorem mms_mul_of_intS_of_mms {V : VF C} {σ : Type} {f h : MvPowerSeries σ C} (hf : IntS V f)
    (hh : MaximalIdealCongruence.MMS V h) : MaximalIdealCongruence.MMS V (f * h) := by
  intro μ
  rw [MvPowerSeries.coeff_mul]
  apply mm_finset_sum_of_forall_mm
  intro x _
  have h1 := hf x.1
  have h2 := hh x.2
  unfold VF.Ge at h1
  unfold VF.MM at h2 ⊢
  rw [AddValuation.map_mul]
  have h1' : (0 : WithTop ℝ) ≤ V.v (coeff x.1 f) := by simpa using h1
  exact lt_of_lt_of_le h2 (le_add_of_nonneg_left h1')

/- English proof (translation)
Introduce `j`. Rewrite using `[Derivation.leibniz, smul_eq_mul, smul_eq_mul]`. Introduce `μ`. Rewrite using `[map_add]`. Apply `mm_add_of_mm_of_mm` to reduce the goal to its premises.

Conclude with `mms_mul_of_intS_of_mms hf (hg' j) μ`. Conclude with `mms_mul_of_intS_of_mms hg (hf' j) μ`.
-/
theorem frobD_mul {f g : PS C 3 dd} (hf : IntS V f) (hg : IntS V g) (hf' : FrobD V f) (hg' : FrobD V g) :
    FrobD V (f * g) := by
  intro j
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  intro μ
  rw [map_add]
  apply mm_add_of_mm_of_mm
  · exact mms_mul_of_intS_of_mms hf (hg' j) μ
  · exact mms_mul_of_intS_of_mms hg (hf' j) μ

/- English proof (translation)
Use extensionality with `⟨k, j⟩`. Proceed by induction on `k using Fin.cases with`. Consider the case `zero`. Rewrite using `[Finsupp.mapDomain_notin_range, hp]`. Introduce and unpack `⟨q, hq⟩`.

Simplify using `only [up, Prod.mk.injEq] at hq`. Conclude with `Fin.succ_ne_zero _ hq.1`. Consider the case `succ k'`. Establish `e : ((Fin.succ k', j) : Fin 3 × Fin dd) = up 2 (k', j)` using `rfl`. Rewrite using `[e, Finsupp.mapDomain_apply (up_inj 2), Finsupp.comapDomain_apply]`.
-/
theorem eq_up_of {p : Fin 3 × Fin dd →₀ ℕ} (hp : ∀ j, p ((0 : Fin 3), j) = 0) :
    (Finsupp.comapDomain (up 2) p ((up_inj 2).injOn)).mapDomain (up 2) = p := by
  ext ⟨k, j⟩
  induction k using Fin.cases with
  | zero =>
    rw [Finsupp.mapDomain_notin_range, hp]
    rintro ⟨q, hq⟩
    simp only [up, Prod.mk.injEq] at hq
    exact Fin.succ_ne_zero _ hq.1
  | succ k' =>
    have e : ((Fin.succ k', j) : Fin 3 × Fin dd) = up 2 (k', j) := rfl
    rw [e, Finsupp.mapDomain_apply (up_inj 2), Finsupp.comapDomain_apply]

/- English proof (translation)
Establish `hs : MvPowerSeries.HasSubst (fun q : Fin 3 × Fin dd => rz (C` using `C) (dd := dd) 2 q.1 q.2) := by`. Establish `hz : ∀ q : Fin 3 × Fin dd, constantCoeff (rz (C` using `C) (dd := dd) 2 q.1 q.2) = 0 := by`. Introduce and unpack `⟨k, i⟩`. Apply the tactic sequence `induction k using Fin.cases <;> simp [rz, pt]`. Use `first`.

Consider the case `exact MvPowerSeries.hasSubst_of_constantCoeff_zero hz`. Consider the case `exact MvPowerSeries.HasSubst.of_constantCoeff_zero' hz`. Consider the case `exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun q => by rw [hz q]; exact IsNilpotent.zero)`. Consider the case `exact MvPowerSeries.hasSubst_of_constantCoeff_nilpotent (fun q => by rw [hz q]; exact IsNilpotent.zero)`. Establish `hmon : ∀ d' : Fin 2 × Fin dd →₀ ℕ, (d'.prod fun s n => (X s : PS C 2 dd) ^ n) = MvPowerSeries.monomial d' (1 : C)`.

Introduce `d'`. Proceed by induction on `d' using Finsupp.induction with`. Consider the case `zero => rw [Finsupp.prod_zero_index, MvPowerSeries.monomial_zero_one]`. Consider the case `single_add a b g _ _ ih`. Rewrite using `[Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _), ih, Finsupp.prod_single_index (h := fun x n => (X x : PS C 2 dd) ^ n) (pow_zero _), MvPowerSeries.X_pow_eq, MvPowerSeries.monomial_mul_monomial, one_mul]`.

Establish `inj : Function.Injective (Finsupp.mapDomain (M` using `ℕ) (up (dd := dd) 2)) := Finsupp.mapDomain_injective (up_inj 2)`. Establish `hprod : ∀ (d : Fin 3 × Fin dd →₀ ℕ) (e : Fin 2 × Fin dd →₀ ℕ), coeff e (d.prod fun s n => (fun q : Fin 3 × Fin dd => rz (C` using `C) (dd := dd) 2 q.1 q.2) s ^ n) = if d = e.mapDomain (up 2) then 1 else 0 := by`. Introduce `d e`. Distinguish the cases in `hx : ∀ j, d ((0 : Fin 3), j) = 0`. Establish `hd` using `(eq_up_of hx).symm`.

Rewrite using `[hd, Finsupp.prod_mapDomain_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]`. Use `show coeff e ((Finsupp.comapDomain (up 2) d ((up_inj 2).injOn)).prod fun s n => (X s : PS C 2 dd) ^ n) = _`. Rewrite using `[hmon, MvPowerSeries.coeff_monomial]`. Distinguish the cases in `he : e = Finsupp.comapDomain (up 2) d ((up_inj 2).injOn)`. Rewrite using `[if_pos he, if_pos (by rw [he])]`.

Rewrite using `[if_neg he, if_neg (fun h => he (inj h).symm)]`. Use `push_neg at hx`. Take `⟨j, hj⟩` from `hx`. Establish `h0 : (d.prod fun s n => (fun q : Fin 3 × Fin dd => rz (C` using `C) (dd := dd) 2 q.1 q.2) s ^ n) = 0 := by`. Apply `Finset.prod_eq_zero (i := ((0 : Fin 3), j))` to reduce the goal to its premises.

Conclude with `Finsupp.mem_support_iff.mpr hj`. Use `show (rz (C := C) (dd := dd) 2 0 j) ^ (d ((0 : Fin 3), j)) = 0`. Rewrite using `[show rz (C := C) (dd := dd) 2 0 j = 0 from rfl, zero_pow hj]`. Rewrite using `[h0, map_zero, if_neg]`. Introduce `h`.

Apply `hj` to reduce the goal to its premises. Rewrite using `[h, Finsupp.mapDomain_notin_range]`. Introduce and unpack `⟨q, hq⟩`. Simplify using `only [up, Prod.mk.injEq] at hq`. Conclude with `Fin.succ_ne_zero _ hq.1`.

Establish `key : ∀ e : Fin 2 × Fin dd →₀ ℕ, coeff e (ev (rz (C` using `C) (dd := dd) 2) f) = coeff (e.mapDomain (up 2)) f := by`. Introduce `e`. Use `show coeff e (MvPowerSeries.subst (fun q : Fin 3 × Fin dd => rz (C := C) (dd := dd) 2 q.1 q.2) f) = _`. Rewrite using `[MvPowerSeries.coeff_subst hs, finsum_eq_single _ (e.mapDomain (up 2))]`. Rewrite using `[hprod, if_pos rfl, smul_eq_mul, mul_one]`.

Introduce `d hd`. Rewrite using `[hprod, if_neg hd, smul_zero]`. Establish `h2` using `key (Finsupp.comapDomain (up 2) p ((up_inj 2).injOn))`. Rewrite `h2` using `[h1, eq_up_of hp, MvPowerSeries.coeff_one]`. Rewrite using `[← h2]`.

Distinguish the cases in `hp0 : p = 0`. Substitute `hp0` using the available equality. Rewrite using `[if_pos rfl, if_pos]`. Use extensionality with `s`. Both sides reduce to the same expression.

Rewrite using `[if_neg hp0, if_neg]`. Introduce `h`. Apply `hp0` to reduce the goal to its premises. Rewrite using `[← eq_up_of hp, h, Finsupp.mapDomain_zero]`.
-/
theorem coeff_free {f : PS C 3 dd} (h1 : ev (rz 2) f = 1) {p : Fin 3 × Fin dd →₀ ℕ}
    (hp : ∀ j, p ((0 : Fin 3), j) = 0) : coeff p f = if p = 0 then 1 else 0 := by
  classical
  have hs : MvPowerSeries.HasSubst (fun q : Fin 3 × Fin dd => rz (C := C) (dd := dd) 2 q.1 q.2) := by
    have hz : ∀ q : Fin 3 × Fin dd, constantCoeff (rz (C := C) (dd := dd) 2 q.1 q.2) = 0 := by
      rintro ⟨k, i⟩
      induction k using Fin.cases <;> simp [rz, pt]
    first
    | exact MvPowerSeries.hasSubst_of_constantCoeff_zero hz
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero' hz
    | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun q => by rw [hz q]; exact IsNilpotent.zero)
    | exact MvPowerSeries.hasSubst_of_constantCoeff_nilpotent (fun q => by rw [hz q]; exact IsNilpotent.zero)
  have hmon : ∀ d' : Fin 2 × Fin dd →₀ ℕ,
      (d'.prod fun s n => (X s : PS C 2 dd) ^ n) = MvPowerSeries.monomial d' (1 : C) := by
    intro d'
    induction d' using Finsupp.induction with
    | zero => rw [Finsupp.prod_zero_index, MvPowerSeries.monomial_zero_one]
    | single_add a b g _ _ ih =>
      rw [Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _), ih,
        Finsupp.prod_single_index (h := fun x n => (X x : PS C 2 dd) ^ n) (pow_zero _), MvPowerSeries.X_pow_eq, MvPowerSeries.monomial_mul_monomial,
        one_mul]
  have inj : Function.Injective (Finsupp.mapDomain (M := ℕ) (up (dd := dd) 2)) :=
    Finsupp.mapDomain_injective (up_inj 2)
  have hprod : ∀ (d : Fin 3 × Fin dd →₀ ℕ) (e : Fin 2 × Fin dd →₀ ℕ),
      coeff e (d.prod fun s n => (fun q : Fin 3 × Fin dd => rz (C := C) (dd := dd) 2 q.1 q.2) s ^ n) =
        if d = e.mapDomain (up 2) then 1 else 0 := by
    intro d e
    by_cases hx : ∀ j, d ((0 : Fin 3), j) = 0
    · have hd := (eq_up_of hx).symm
      rw [hd, Finsupp.prod_mapDomain_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
      show coeff e ((Finsupp.comapDomain (up 2) d ((up_inj 2).injOn)).prod
        fun s n => (X s : PS C 2 dd) ^ n) = _
      rw [hmon, MvPowerSeries.coeff_monomial]
      by_cases he : e = Finsupp.comapDomain (up 2) d ((up_inj 2).injOn)
      · rw [if_pos he, if_pos (by rw [he])]
      · rw [if_neg he, if_neg (fun h => he (inj h).symm)]
    · push_neg at hx
      obtain ⟨j, hj⟩ := hx
      have h0 : (d.prod fun s n => (fun q : Fin 3 × Fin dd => rz (C := C) (dd := dd) 2 q.1 q.2) s ^ n) = 0 := by
        apply Finset.prod_eq_zero (i := ((0 : Fin 3), j))
        · exact Finsupp.mem_support_iff.mpr hj
        · show (rz (C := C) (dd := dd) 2 0 j) ^ (d ((0 : Fin 3), j)) = 0
          rw [show rz (C := C) (dd := dd) 2 0 j = 0 from rfl, zero_pow hj]
      rw [h0, map_zero, if_neg]
      intro h
      apply hj
      rw [h, Finsupp.mapDomain_notin_range]
      rintro ⟨q, hq⟩
      simp only [up, Prod.mk.injEq] at hq
      exact Fin.succ_ne_zero _ hq.1
  have key : ∀ e : Fin 2 × Fin dd →₀ ℕ,
      coeff e (ev (rz (C := C) (dd := dd) 2) f) = coeff (e.mapDomain (up 2)) f := by
    intro e
    show coeff e (MvPowerSeries.subst (fun q : Fin 3 × Fin dd => rz (C := C) (dd := dd) 2 q.1 q.2) f) = _
    rw [MvPowerSeries.coeff_subst hs, finsum_eq_single _ (e.mapDomain (up 2))]
    · rw [hprod, if_pos rfl, smul_eq_mul, mul_one]
    · intro d hd
      rw [hprod, if_neg hd, smul_zero]
  have h2 := key (Finsupp.comapDomain (up 2) p ((up_inj 2).injOn))
  rw [h1, eq_up_of hp, MvPowerSeries.coeff_one] at h2
  rw [← h2]
  by_cases hp0 : p = 0
  · subst hp0
    rw [if_pos rfl, if_pos]
    ext s
    rfl
  · rw [if_neg hp0, if_neg]
    intro h
    apply hp0
    rw [← eq_up_of hp, h, Finsupp.mapDomain_zero]

/- English proof (translation)
Establish `h` using `hp ((0 : Fin 3), j)`. Rewrite `h` using `[index_raise_first, if_neg hj]`. Conclude with `Nat.le_zero.mp h`.
-/
theorem x_le (i : Fin dd) (γ : Fin 2 × Fin dd →₀ ℕ) {p : Fin 3 × Fin dd →₀ ℕ} (hp : p ≤ ix i V.l γ)
    (j : Fin dd) (hj : j ≠ i) : p ((0 : Fin 3), j) = 0 := by
  have h := hp ((0 : Fin 3), j)
  rw [index_raise_first, if_neg hj] at h
  exact Nat.le_zero.mp h

/- English proof (translation)
Unfold `VF.MM`. Rewrite using `[AddValuation.map_zero, ← WithTop.coe_zero]`. Conclude with `WithTop.coe_lt_top _`.
-/
private theorem mm_zero' : V.MM (0 : C) := by
  unfold VF.MM
  rw [AddValuation.map_zero, ← WithTop.coe_zero]
  exact WithTop.coe_lt_top _

/- English proof (translation)
Unfold `VF.MM at *`. Unfold `VF.Ge at hb`. Rewrite using `[AddValuation.map_mul]`. Establish `hb' : (0 : WithTop ℝ) ≤ V.v b` using `by simpa using hb`. Conclude with `lt_of_lt_of_le ha (le_add_of_nonneg_right hb')`.
-/
private theorem mm_mul_of_mm_of_ge_zero {a b : C} (ha : V.MM a) (hb : V.Ge 0 b) : V.MM (a * b) := by
  unfold VF.MM at *
  unfold VF.Ge at hb
  rw [AddValuation.map_mul]
  have hb' : (0 : WithTop ℝ) ≤ V.v b := by simpa using hb
  exact lt_of_lt_of_le ha (le_add_of_nonneg_right hb')

/- English proof (translation)
Unfold `FrobX at hfF hgF`. Use `set N := ix i V.l γ with hN`. Establish `hN0 : N ≠ 0`. Introduce `h`. Establish `h2` using `congrArg (fun p => p ((0 : Fin 3), i)) h`.

Simplify using `[hN, index_raise_first] at h2`. Conclude with `V.l_prime.ne_zero h2`. Establish `hf0 : coeff 0 f = 1`. Use `coeff_free hf1 (p := 0) (fun j => rfl)` as an intermediate fact. Simplify using `using this`.

Establish `hg0 : coeff 0 g = 1`. Use `coeff_free hg1 (p := 0) (fun j => rfl)` as an intermediate fact. Simplify using `using this`. Rewrite using `[MvPowerSeries.coeff_mul]`. Establish `h1 : ((0 : Fin 3 × Fin dd →₀ ℕ), N) ∈ Finset.HasAntidiagonal.antidiagonal N`.

Rewrite using `[Finset.HasAntidiagonal.mem_antidiagonal]`. Simplify using the standard rewrite rules. Establish `h2 : (N, (0 : Fin 3 × Fin dd →₀ ℕ)) ∈ (Finset.HasAntidiagonal.antidiagonal N).erase (0, N)`. Rewrite using `[Finset.mem_erase]`. Use `⟨fun h => hN0 (congrArg Prod.fst h), ?_⟩` and prove the remaining obligations.

Rewrite using `[Finset.HasAntidiagonal.mem_antidiagonal]`. Simplify using the standard rewrite rules. Rewrite using `[← Finset.add_sum_erase _ _ h1, ← Finset.add_sum_erase _ _ h2]`. Simplify using `only`. Rewrite using `[hf0, hg0, one_mul, mul_one]`.

Establish `e : ∀ A B S : C, A + (B + S) - B - A = S`. Use `intros`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Apply `mm_finset_sum_of_forall_mm` to reduce the goal to its premises.

Introduce `x hx`. Take `⟨hne2, hx'⟩` from `Finset.mem_erase.mp hx`. Take `⟨hne1, hx''⟩` from `Finset.mem_erase.mp hx'`. Establish `hsum` using `Finset.HasAntidiagonal.mem_antidiagonal.mp hx''`. Establish `ha : x.1 ≤ N`.

Rewrite using `[← hsum]`. Conclude with `le_self_add`. Establish `hb : x.2 ≤ N`. Rewrite using `[← hsum]`. Conclude with `le_add_self`.

Establish `ha0 : x.1 ≠ 0`. Introduce `h`. Apply `hne1` to reduce the goal to its premises. Use `Prod.ext h ?_` and prove the remaining obligations. Use `show x.2 = N`.

Rewrite using `[← hsum, h, zero_add]`. Establish `hb0 : x.2 ≠ 0`. Introduce `h`. Apply `hne2` to reduce the goal to its premises. Use `Prod.ext ?_ h` and prove the remaining obligations.

Use `show x.1 = N`. Rewrite using `[← hsum, h, add_zero]`. Establish `hxa : ∀ j, j ≠ i → x.1 ((0 : Fin 3), j) = 0` using `fun j hj => x_le i γ ha j hj`. Establish `hxb : ∀ j, j ≠ i → x.2 ((0 : Fin 3), j) = 0` using `fun j hj => x_le i γ hb j hj`. Establish `hti : x.1 ((0 : Fin 3), i) + x.2 ((0 : Fin 3), i) = V.l`.

Establish `h3` using `congrArg (fun p => p ((0 : Fin 3), i)) hsum`. Simplify using `only [Finsupp.add_apply] at h3`. Rewrite using `[h3, hN, index_raise_first, if_pos rfl]`. Distinguish the cases in `hd : V.l ∣ x.1 ((0 : Fin 3), i)`. Take `⟨q, hq⟩` from `hd`.

Break down `q with _ | _ | q` into its components or cases. Establish `hfree : ∀ j, x.1 ((0 : Fin 3), j) = 0`. Introduce `j`. Distinguish the cases in `hj : j = i`. Rewrite using `[hj]`.

Simplify using `using hq`. Conclude with `hxa j hj`. Rewrite using `[coeff_free hf1 hfree, if_neg ha0, zero_mul]`. Conclude with `mm_zero'`. Establish `hfree : ∀ j, x.2 ((0 : Fin 3), j) = 0`.

Introduce `j`. Distinguish the cases in `hj : j = i`. Rewrite using `[hj]`. Simplify using `at hq`. Use linear arithmetic over natural numbers and integers.

Conclude with `hxb j hj`. Rewrite using `[coeff_free hg1 hfree, if_neg hb0, mul_zero]`. Conclude with `mm_zero'`. It suffices to derive a contradiction. Use polynomial arithmetic with `[V.l_prime.pos]`.

Conclude with `mm_mul_of_mm_of_ge_zero (hfF x.1 ⟨i, hd⟩) (hg x.2)`.
-/
theorem coeff_mul_cong {f g : PS C 3 dd} (hf : IntS V f) (hg : IntS V g) (hfF : FrobX V f) (hgF : FrobX V g)
    (hf1 : ev (rz 2) f = 1) (hg1 : ev (rz 2) g = 1) (i : Fin dd) (γ : Fin 2 × Fin dd →₀ ℕ) :
    V.MM (coeff (ix i V.l γ) (f * g) - coeff (ix i V.l γ) f - coeff (ix i V.l γ) g) := by
  classical
  unfold FrobX at hfF hgF
  set N := ix i V.l γ with hN
  have hN0 : N ≠ 0 := by
    intro h
    have h2 := congrArg (fun p => p ((0 : Fin 3), i)) h
    simp [hN, index_raise_first] at h2
    exact V.l_prime.ne_zero h2
  have hf0 : coeff 0 f = 1 := by
    have := coeff_free hf1 (p := 0) (fun j => rfl)
    simpa using this
  have hg0 : coeff 0 g = 1 := by
    have := coeff_free hg1 (p := 0) (fun j => rfl)
    simpa using this
  rw [MvPowerSeries.coeff_mul]
  have h1 : ((0 : Fin 3 × Fin dd →₀ ℕ), N) ∈ Finset.HasAntidiagonal.antidiagonal N := by
    rw [Finset.HasAntidiagonal.mem_antidiagonal]
    simp
  have h2 : (N, (0 : Fin 3 × Fin dd →₀ ℕ)) ∈ (Finset.HasAntidiagonal.antidiagonal N).erase (0, N) := by
    rw [Finset.mem_erase]
    refine ⟨fun h => hN0 (congrArg Prod.fst h), ?_⟩
    rw [Finset.HasAntidiagonal.mem_antidiagonal]
    simp
  rw [← Finset.add_sum_erase _ _ h1, ← Finset.add_sum_erase _ _ h2]
  dsimp only
  rw [hf0, hg0, one_mul, mul_one]
  have e : ∀ A B S : C, A + (B + S) - B - A = S := by
    intros
    ring
  rw [e]
  apply mm_finset_sum_of_forall_mm
  intro x hx
  obtain ⟨hne2, hx'⟩ := Finset.mem_erase.mp hx
  obtain ⟨hne1, hx''⟩ := Finset.mem_erase.mp hx'
  have hsum := Finset.HasAntidiagonal.mem_antidiagonal.mp hx''
  have ha : x.1 ≤ N := by
    rw [← hsum]
    exact le_self_add
  have hb : x.2 ≤ N := by
    rw [← hsum]
    exact le_add_self
  have ha0 : x.1 ≠ 0 := by
    intro h
    apply hne1
    refine Prod.ext h ?_
    show x.2 = N
    rw [← hsum, h, zero_add]
  have hb0 : x.2 ≠ 0 := by
    intro h
    apply hne2
    refine Prod.ext ?_ h
    show x.1 = N
    rw [← hsum, h, add_zero]
  have hxa : ∀ j, j ≠ i → x.1 ((0 : Fin 3), j) = 0 := fun j hj => x_le i γ ha j hj
  have hxb : ∀ j, j ≠ i → x.2 ((0 : Fin 3), j) = 0 := fun j hj => x_le i γ hb j hj
  have hti : x.1 ((0 : Fin 3), i) + x.2 ((0 : Fin 3), i) = V.l := by
    have h3 := congrArg (fun p => p ((0 : Fin 3), i)) hsum
    simp only [Finsupp.add_apply] at h3
    rw [h3, hN, index_raise_first, if_pos rfl]
  by_cases hd : V.l ∣ x.1 ((0 : Fin 3), i)
  · obtain ⟨q, hq⟩ := hd
    rcases q with _ | _ | q
    · have hfree : ∀ j, x.1 ((0 : Fin 3), j) = 0 := by
        intro j
        by_cases hj : j = i
        · rw [hj]
          simpa using hq
        · exact hxa j hj
      rw [coeff_free hf1 hfree, if_neg ha0, zero_mul]
      exact mm_zero'
    · have hfree : ∀ j, x.2 ((0 : Fin 3), j) = 0 := by
        intro j
        by_cases hj : j = i
        · rw [hj]
          simp at hq
          omega
        · exact hxb j hj
      rw [coeff_free hg1 hfree, if_neg hb0, mul_zero]
      exact mm_zero'
    · exfalso
      nlinarith [V.l_prime.pos]
  · exact mm_mul_of_mm_of_ge_zero (hfF x.1 ⟨i, hd⟩) (hg x.2)

end Formalism.L2.FormalSeriesBounds.FunEq
