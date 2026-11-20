import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.PowerSeriesHasSumAt

noncomputable section

namespace GlobalTheory.ConvSer

open MvPowerSeries Finsupp

open MvPowerSeries Finsupp in
/- English proof (translation)
Use `hasSubst_of_constantCoeff_zero fun s => ?_` and prove the remaining obligations. Use `fin_cases s`. Conclude with `hf`. Conclude with `hg`.
-/
theorem _root_.GlobalTheory.ConvSer.nMul_hasSubst_pair {R : Type*} [CommRing R] {f g : PowerSeries R}
    (hf : PowerSeries.constantCoeff f = 0) (hg : PowerSeries.constantCoeff g = 0) :
    MvPowerSeries.HasSubst (![f, g] : Fin 2 → MvPowerSeries Unit R) := by
  refine hasSubst_of_constantCoeff_zero fun s => ?_
  fin_cases s
  · exact hf
  · exact hg

open MvPowerSeries Finsupp in
/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp [_root_.GlobalTheory.ConvSer.nMul_zero]`. Consider the case `succ n ih`. Rewrite using `[_root_.GlobalTheory.ConvSer.nMul_succ]`. Use `constantCoeff_subst_eq_zero (_root_.GlobalTheory.ConvSer.nMul_hasSubst_pair ih PowerSeries.constantCoeff_X) (fun s => ?_) F.2` and prove the remaining obligations.

Use `fin_cases s`. Conclude with `ih`. Conclude with `PowerSeries.constantCoeff_X`.
-/
theorem _root_.GlobalTheory.ConvSer.nMul_constantCoeff {R : Type*} [CommRing R] (F : FormalGroup R)
    (n : ℕ) : PowerSeries.constantCoeff (_root_.GlobalTheory.ConvSer.nMul F n) = 0 := by
  induction n with
  | zero => simp [_root_.GlobalTheory.ConvSer.nMul_zero]
  | succ n ih =>
    rw [_root_.GlobalTheory.ConvSer.nMul_succ]
    refine constantCoeff_subst_eq_zero
      (_root_.GlobalTheory.ConvSer.nMul_hasSubst_pair ih PowerSeries.constantCoeff_X) (fun s => ?_) F.2
    fin_cases s
    · exact ih
    · exact PowerSeries.constantCoeff_X

/- English proof (translation)
The claim follows from `PowerSeries.HasSubst.of_constantCoeff_zero' (nMul_constantCoeff F n)`.
-/
theorem nMul_hasSubst {R : Type*} [CommRing R] (F : FormalGroup R) (n : ℕ) :
    PowerSeries.HasSubst (nMul F n) :=
  PowerSeries.HasSubst.of_constantCoeff_zero' (nMul_constantCoeff F n)

/- English proof (translation)
Establish `hne : (single 0 1 : Fin 2 →₀ ℕ) ≠ single 1 1`. Introduce `h`. Use `DFunLike.congr_fun h 0` as an intermediate fact. Simplify using `at this`. Establish `key : ∀ d : Fin 2 →₀ ℕ, (d.prod fun s e => (![f, g] : Fin 2 → MvPowerSeries Unit R) s ^ e) = (f ^ d 0 * g ^ d 1 : PowerSeries R)`.

Introduce `d`. Rewrite using `[Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_two]`. Both sides reduce to the same expression. Establish `hc : ∀ h : PowerSeries R, MvPowerSeries.coeff (single () 1) h = PowerSeries.coeff 1 h` using `fun _ => rfl`. Rewrite using `[← hc, coeff_subst (nMul_hasSubst_pair hf hg), finsum_eq_sum_of_support_subset (s := {single 0 1, single 1 1})]`.

Rewrite using `[Finset.sum_pair hne, key, key, hc, hc, F.lin_coeff_X, F.lin_coeff_Y]`. Simplify using the standard rewrite rules. Introduce `d hd`. Assume the negation of the conclusion as `hn`. Apply `hd` to reduce the goal to its premises.

Simplify using `only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hn`. Establish `h2 : d 0 + d 1 = 0 ∨ 2 ≤ d 0 + d 1`. Assume the negation of the conclusion as `hh`. Establish `: (d 0 = 1 ∧ d 1 = 0) ∨ (d 0 = 0 ∧ d 1 = 1)` using `by omega`. Break down `this with h | h` into its components or cases.

Apply `hn.1` to reduce the goal to its premises. Use extensionality with `s`. Apply the tactic sequence `fin_cases s <;> simp [h]`. Apply `hn.2` to reduce the goal to its premises. Use extensionality with `s`.

Apply the tactic sequence `fin_cases s <;> simp [h]`. Establish `h0 : PowerSeries.coeff 1 (f ^ d 0 * g ^ d 1) = 0`. Break down `h2 with h | h` into its components or cases. Establish `h0 : d 0 = 0` using `by omega`. Establish `h1 : d 1 = 0` using `by omega`.

Simplify using `[h0, h1, PowerSeries.coeff_one]`. Establish `hd : (PowerSeries.X : PowerSeries R) ^ (d 0 + d 1) ∣ f ^ d 0 * g ^ d 1`. Rewrite using `[pow_add]`. Conclude with `mul_dvd_mul (pow_dvd_pow_of_dvd (PowerSeries.X_dvd_iff.2 hf) _) (pow_dvd_pow_of_dvd (PowerSeries.X_dvd_iff.2 hg) _)`. Conclude with `PowerSeries.X_pow_dvd_iff.1 hd 1 (by omega)`.

Use `show _ • _ = _`. Rewrite using `[key, hc, h0, smul_zero]`.
-/
theorem coeff_one_formalGroup_subst {R : Type*} [CommRing R] (F : FormalGroup R)
    {f g : PowerSeries R}
    (hf : PowerSeries.constantCoeff f = 0) (hg : PowerSeries.constantCoeff g = 0) :
    PowerSeries.coeff 1 (MvPowerSeries.subst (![f, g] : Fin 2 → MvPowerSeries Unit R)
      F.toPowerSeries) = PowerSeries.coeff 1 f + PowerSeries.coeff 1 g := by
  have hne : (single 0 1 : Fin 2 →₀ ℕ) ≠ single 1 1 := by
    intro h
    have := DFunLike.congr_fun h 0
    simp at this
  have key : ∀ d : Fin 2 →₀ ℕ, (d.prod fun s e => (![f, g] : Fin 2 → MvPowerSeries Unit R) s ^ e)
      = (f ^ d 0 * g ^ d 1 : PowerSeries R) := by
    intro d
    rw [Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_two]
    rfl
  have hc : ∀ h : PowerSeries R, MvPowerSeries.coeff (single () 1) h = PowerSeries.coeff 1 h :=
    fun _ => rfl
  rw [← hc, coeff_subst (nMul_hasSubst_pair hf hg),
    finsum_eq_sum_of_support_subset (s := {single 0 1, single 1 1})]
  · rw [Finset.sum_pair hne, key, key, hc, hc, F.lin_coeff_X, F.lin_coeff_Y]
    simp
  · intro d hd
    by_contra hn
    apply hd
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff,
      not_or] at hn
    have h2 : d 0 + d 1 = 0 ∨ 2 ≤ d 0 + d 1 := by
      by_contra hh
      have : (d 0 = 1 ∧ d 1 = 0) ∨ (d 0 = 0 ∧ d 1 = 1) := by omega
      rcases this with h | h
      · apply hn.1
        ext s
        fin_cases s <;> simp [h]
      · apply hn.2
        ext s
        fin_cases s <;> simp [h]
    have h0 : PowerSeries.coeff 1 (f ^ d 0 * g ^ d 1) = 0 := by
      rcases h2 with h | h
      · have h0 : d 0 = 0 := by omega
        have h1 : d 1 = 0 := by omega
        simp [h0, h1, PowerSeries.coeff_one]
      · have hd : (PowerSeries.X : PowerSeries R) ^ (d 0 + d 1) ∣ f ^ d 0 * g ^ d 1 := by
          rw [pow_add]
          exact mul_dvd_mul (pow_dvd_pow_of_dvd (PowerSeries.X_dvd_iff.2 hf) _)
            (pow_dvd_pow_of_dvd (PowerSeries.X_dvd_iff.2 hg) _)
        exact PowerSeries.X_pow_dvd_iff.1 hd 1 (by omega)
    show _ • _ = _
    rw [key, hc, h0, smul_zero]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp [nMul_zero]`. Consider the case `succ n ih`. Rewrite using `[nMul_succ, coeff_one_formalGroup_subst F (nMul_constantCoeff F n) PowerSeries.constantCoeff_X, ih]`. Simplify using the standard rewrite rules.
-/
theorem nMul_coeff_one {R : Type*} [CommRing R] (F : FormalGroup R) (n : ℕ) :
    PowerSeries.coeff 1 (nMul F n) = (n : R) := by
  induction n with
  | zero => simp [nMul_zero]
  | succ n ih =>
    rw [nMul_succ, coeff_one_formalGroup_subst F (nMul_constantCoeff F n)
      PowerSeries.constantCoeff_X, ih]
    simp

/- English proof (translation)
Rewrite using `[nMul_succ, nMul_zero]`. Conclude with `F.zeroX_eq_X`.
-/
theorem nMul_one {R : Type*} [CommRing R] (F : FormalGroup R) : nMul F 1 = PowerSeries.X := by
  rw [nMul_succ, nMul_zero]
  exact F.zeroX_eq_X

/- English proof (translation)
Proceed by induction on `j with`. Consider the case `zero => exact F.add_zero (nMul_hasSubst F i)`. Consider the case `succ j ih`. Rewrite using `[← add_assoc, nMul_succ, nMul_succ, ← ih]`. Conclude with `(F.assoc' (nMul_hasSubst F i) (nMul_hasSubst F j) PowerSeries.HasSubst.X').symm`.
-/
theorem nMul_add {R : Type*} [CommRing R] (F : FormalGroup R) (i j : ℕ) :
    MvPowerSeries.subst (![nMul F i, nMul F j] : Fin 2 → MvPowerSeries Unit R) F.toPowerSeries
      = nMul F (i + j) := by
  induction j with
  | zero => exact F.add_zero (nMul_hasSubst F i)
  | succ j ih =>
    rw [← add_assoc, nMul_succ, nMul_succ, ← ih]
    exact (F.assoc' (nMul_hasSubst F i) (nMul_hasSubst F j) PowerSeries.HasSubst.X').symm

/- English proof (translation)
Proceed by induction on `i with`. Consider the case `zero`. Rewrite using `[zero_mul, nMul_zero, ← PowerSeries.coe_substAlgHom (nMul_hasSubst F j), map_zero]`. Consider the case `succ i ih`. Rewrite using `[add_mul, one_mul, ← nMul_add F (i * j) j, nMul_succ F i, PowerSeries.subst, subst_comp_subst_apply (nMul_hasSubst_pair (nMul_constantCoeff F i) PowerSeries.constantCoeff_X) (nMul_hasSubst F j).const]`.

Use `congr! 2 with s`. Use `fin_cases s`. Conclude with `ih`. Conclude with `PowerSeries.subst_X (nMul_hasSubst F j)`.
-/
theorem nMul_subst_nMul {R : Type*} [CommRing R] (F : FormalGroup R) (i j : ℕ) :
    (nMul F i).subst (nMul F j) = nMul F (i * j) := by
  induction i with
  | zero =>
    rw [zero_mul, nMul_zero, ← PowerSeries.coe_substAlgHom (nMul_hasSubst F j), map_zero]
  | succ i ih =>
    rw [add_mul, one_mul, ← nMul_add F (i * j) j, nMul_succ F i, PowerSeries.subst,
      subst_comp_subst_apply
        (nMul_hasSubst_pair (nMul_constantCoeff F i) PowerSeries.constantCoeff_X)
        (nMul_hasSubst F j).const]
    congr! 2 with s
    fin_cases s
    · exact ih
    · exact PowerSeries.subst_X (nMul_hasSubst F j)

open MvPowerSeries Finsupp in
/- English proof (translation)
Establish `ha` using `_root_.GlobalTheory.ConvSer.nMul_hasSubst_pair hf PowerSeries.constantCoeff_X`. Take `⟨g, rfl⟩` from `PowerSeries.X_dvd_iff.mpr hf`. Establish `hprod : ∀ d : Fin 2 →₀ ℕ, (d.prod fun s e => (![PowerSeries.X * g, PowerSeries.X] : Fin 2 → MvPowerSeries Unit R) s ^ e) = PowerSeries.X ^ (d 0 + d 1) * g ^ d 0`. Introduce `d`. Rewrite using `[Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_two]`.

Use `show (PowerSeries.X * g) ^ d 0 * PowerSeries.X ^ d 1 = _`. Expand and normalize the polynomial expressions, which then agree. Establish `hcoeff : ∀ h : PowerSeries R, MvPowerSeries.coeff (single () 1) h = PowerSeries.coeff 1 h` using `fun _ => rfl`. Establish `hne : (single 0 1 : Fin 2 →₀ ℕ) ≠ single 1 1`. Introduce `h`.

Use `congrArg (fun d => d 0) h` as an intermediate fact. Simplify using `at this`. Use `show MvPowerSeries.coeff (single () 1) _ = _`. Rewrite using `[coeff_subst ha, finsum_eq_sum_of_support_subset (s := {single 0 1, single 1 1}), Finset.sum_pair hne]`. Simplify using `only [hprod, hcoeff, F.3, F.4]`.

Simplify using the standard rewrite rules. Introduce `d hd`. Simplify using `only [Function.mem_support, hprod, hcoeff, PowerSeries.coeff_X_pow_mul'] at hd`. Simplify using `only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]`. Distinguish the cases in `h2 : d 0 + d 1 ≤ 1`.

Break down `Nat.le_one_iff_eq_zero_or_eq_one.mp h2 with h | h` into its components or cases. It suffices to derive a contradiction. Apply `hd` to reduce the goal to its premises. Apply the tactic sequence `have hd0 : d = 0 := Finsupp.ext fun i => by fin_cases i <;> simp <;> omega`. Simplify using `[hd0, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, F.2]`.

Establish `h0 : d 0 ≤ 1` using `by omega`. Break down `Nat.le_one_iff_eq_zero_or_eq_one.mp h0 with h0 | h0` into its components or cases. Use `right`. Use extensionality with `i`. Apply the tactic sequence `fin_cases i <;> simp <;> omega`.

Use `left`. Use extensionality with `i`. Apply the tactic sequence `fin_cases i <;> simp <;> omega`. Conclude with `absurd (by simp [h2]) hd`.
-/
private theorem coeff_one_subst_pair_X {R : Type*} [CommRing R] (F : FormalGroup R)
    {f : PowerSeries R} (hf : PowerSeries.constantCoeff f = 0) :
    PowerSeries.coeff 1 (MvPowerSeries.subst (![f, PowerSeries.X] : Fin 2 → MvPowerSeries Unit R)
      F.toPowerSeries : PowerSeries R) = PowerSeries.coeff 1 f + 1 := by
  have ha := _root_.GlobalTheory.ConvSer.nMul_hasSubst_pair hf PowerSeries.constantCoeff_X
  obtain ⟨g, rfl⟩ := PowerSeries.X_dvd_iff.mpr hf
  have hprod : ∀ d : Fin 2 →₀ ℕ, (d.prod fun s e => (![PowerSeries.X * g, PowerSeries.X] :
      Fin 2 → MvPowerSeries Unit R) s ^ e) = PowerSeries.X ^ (d 0 + d 1) * g ^ d 0 := by
    intro d
    rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_two]
    show (PowerSeries.X * g) ^ d 0 * PowerSeries.X ^ d 1 = _
    ring
  have hcoeff : ∀ h : PowerSeries R, MvPowerSeries.coeff (single () 1) h = PowerSeries.coeff 1 h :=
    fun _ => rfl
  have hne : (single 0 1 : Fin 2 →₀ ℕ) ≠ single 1 1 := by
    intro h
    have := congrArg (fun d => d 0) h
    simp at this
  show MvPowerSeries.coeff (single () 1) _ = _
  rw [coeff_subst ha, finsum_eq_sum_of_support_subset (s := {single 0 1, single 1 1}),
    Finset.sum_pair hne]
  · simp only [hprod, hcoeff, F.3, F.4]
    simp
  · intro d hd
    simp only [Function.mem_support, hprod, hcoeff, PowerSeries.coeff_X_pow_mul'] at hd
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
    by_cases h2 : d 0 + d 1 ≤ 1
    · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h2 with h | h
      · exfalso
        apply hd
        have hd0 : d = 0 := Finsupp.ext fun i => by fin_cases i <;> simp <;> omega
        simp [hd0, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, F.2]
      · have h0 : d 0 ≤ 1 := by omega
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h0 with h0 | h0
        · right
          ext i
          fin_cases i <;> simp <;> omega
        · left
          ext i
          fin_cases i <;> simp <;> omega
    · exact absurd (by simp [h2]) hd

open MvPowerSeries Finsupp in

/- English proof (translation)
Introduce `R _ F`. Establish `hc` using `_root_.GlobalTheory.ConvSer.nMul_constantCoeff F`. Establish `hs : ∀ n, PowerSeries.HasSubst (_root_.GlobalTheory.ConvSer.nMul F n)` using `fun n => PowerSeries.HasSubst.of_constantCoeff_zero' (hc n)`. Establish `hX : PowerSeries.HasSubst (PowerSeries.X : PowerSeries R)` using `PowerSeries.HasSubst.of_constantCoeff_zero' PowerSeries.constantCoeff_X`. Establish `hadd : ∀ i j, MvPowerSeries.subst (![_root_.GlobalTheory.ConvSer.nMul F i, _root_.GlobalTheory.ConvSer.nMul F j] : Fin 2 → MvPowerSeries Unit R) F.toPowerSeries = _root_.GlobalTheory.ConvSer.nMul F (i + j)`.

Introduce `i j`. Proceed by induction on `j with`. Consider the case `zero`. Rewrite using `[_root_.GlobalTheory.ConvSer.nMul_zero, Nat.add_zero]`. Conclude with `F.add_zero (hs i)`.

Consider the case `succ j ih`. Rewrite using `[_root_.GlobalTheory.ConvSer.nMul_succ F j, show i + (j + 1) = (i + j) + 1 by omega, _root_.GlobalTheory.ConvSer.nMul_succ F (i + j), ← ih]`. Conclude with `(F.assoc' (hs i) (hs j) hX).symm`. Use `⟨fun n => ⟨hc n, ?_⟩, ?_, hadd, ?_, ?_⟩` and prove the remaining obligations. Proceed by induction on `n with`.

Consider the case `zero => simp [_root_.GlobalTheory.ConvSer.nMul_zero]`. Consider the case `succ n ih`. Rewrite using `[_root_.GlobalTheory.ConvSer.nMul_succ, coeff_one_subst_pair_X F (hc n), ih]`. Use `push_cast`. Both sides reduce to the same expression.

Rewrite using `[_root_.GlobalTheory.ConvSer.nMul_succ, _root_.GlobalTheory.ConvSer.nMul_zero]`. Conclude with `F.zero_add hX`. Introduce `i j`. Proceed by induction on `i with`. Consider the case `zero`.

Rewrite using `[_root_.GlobalTheory.ConvSer.nMul_zero, Nat.zero_mul, _root_.GlobalTheory.ConvSer.nMul_zero, ← PowerSeries.coe_substAlgHom (hs j), map_zero]`. Consider the case `succ i ih`. Rewrite using `[_root_.GlobalTheory.ConvSer.nMul_succ F i, Nat.succ_mul, ← hadd (i * j) j, ← ih]`. Use `show MvPowerSeries.subst (fun _ => _root_.GlobalTheory.ConvSer.nMul F j) _ = _`. Rewrite using `[MvPowerSeries.subst_comp_subst_apply (_root_.GlobalTheory.ConvSer.nMul_hasSubst_pair (hc i) PowerSeries.constantCoeff_X) (hasSubst_of_constantCoeff_zero fun _ => hc j)]`.

Use `congr 1`. Use function extensionality and compare the values at `s`. Use `fin_cases s`. Both sides reduce to the same expression. Conclude with `PowerSeries.subst_X (hs j)`.

Introduce `S _ φ n`. Proceed by induction on `n with`. Consider the case `zero => simp [_root_.GlobalTheory.ConvSer.nMul_zero]`. Consider the case `succ n ih`. Rewrite using `[_root_.GlobalTheory.ConvSer.nMul_succ, _root_.GlobalTheory.ConvSer.nMul_succ, FormalGroup.map_toPowerSeries, ← ih]`.

Use `show MvPowerSeries.map φ _ = _`. Rewrite using `[MvPowerSeries.map_subst (_root_.GlobalTheory.ConvSer.nMul_hasSubst_pair (hc n) PowerSeries.constantCoeff_X)]`. Use `congr 1`. Use function extensionality and compare the values at `s`. Use `fin_cases s`.

Both sides reduce to the same expression. Conclude with `PowerSeries.map_X φ`.
-/
theorem _root_.GlobalTheory.ConvSer.nMul_props : ∀ (R : Type) [CommRing R] (F : FormalGroup R), (∀ n, PowerSeries.constantCoeff (_root_.GlobalTheory.ConvSer.nMul F n) = 0 ∧ PowerSeries.coeff 1 (_root_.GlobalTheory.ConvSer.nMul F n) = (n : R)) ∧ _root_.GlobalTheory.ConvSer.nMul F 1 = PowerSeries.X ∧ (∀ i j, MvPowerSeries.subst (![_root_.GlobalTheory.ConvSer.nMul F i, _root_.GlobalTheory.ConvSer.nMul F j] : Fin 2 → MvPowerSeries Unit R) F.toPowerSeries = _root_.GlobalTheory.ConvSer.nMul F (i + j)) ∧ (∀ i j, (_root_.GlobalTheory.ConvSer.nMul F i).subst (_root_.GlobalTheory.ConvSer.nMul F j) = _root_.GlobalTheory.ConvSer.nMul F (i * j)) ∧ (∀ (S : Type) [CommRing S] (φ : R →+* S) (n : ℕ), PowerSeries.map φ (_root_.GlobalTheory.ConvSer.nMul F n) = _root_.GlobalTheory.ConvSer.nMul (F.map φ) n) := by
  intro R _ F
  have hc := _root_.GlobalTheory.ConvSer.nMul_constantCoeff F
  have hs : ∀ n, PowerSeries.HasSubst (_root_.GlobalTheory.ConvSer.nMul F n) :=
    fun n => PowerSeries.HasSubst.of_constantCoeff_zero' (hc n)
  have hX : PowerSeries.HasSubst (PowerSeries.X : PowerSeries R) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' PowerSeries.constantCoeff_X
  have hadd : ∀ i j, MvPowerSeries.subst (![_root_.GlobalTheory.ConvSer.nMul F i,
      _root_.GlobalTheory.ConvSer.nMul F j] : Fin 2 → MvPowerSeries Unit R) F.toPowerSeries =
      _root_.GlobalTheory.ConvSer.nMul F (i + j) := by
    intro i j
    induction j with
    | zero =>
      rw [_root_.GlobalTheory.ConvSer.nMul_zero, Nat.add_zero]
      exact F.add_zero (hs i)
    | succ j ih =>
      rw [_root_.GlobalTheory.ConvSer.nMul_succ F j, show i + (j + 1) = (i + j) + 1 by omega,
        _root_.GlobalTheory.ConvSer.nMul_succ F (i + j), ← ih]
      exact (F.assoc' (hs i) (hs j) hX).symm
  refine ⟨fun n => ⟨hc n, ?_⟩, ?_, hadd, ?_, ?_⟩
  · induction n with
    | zero => simp [_root_.GlobalTheory.ConvSer.nMul_zero]
    | succ n ih =>
      rw [_root_.GlobalTheory.ConvSer.nMul_succ, coeff_one_subst_pair_X F (hc n), ih]
      push_cast
      rfl
  · rw [_root_.GlobalTheory.ConvSer.nMul_succ, _root_.GlobalTheory.ConvSer.nMul_zero]
    exact F.zero_add hX
  · intro i j
    induction i with
    | zero =>
      rw [_root_.GlobalTheory.ConvSer.nMul_zero, Nat.zero_mul, _root_.GlobalTheory.ConvSer.nMul_zero,
        ← PowerSeries.coe_substAlgHom (hs j), map_zero]
    | succ i ih =>
      rw [_root_.GlobalTheory.ConvSer.nMul_succ F i, Nat.succ_mul, ← hadd (i * j) j, ← ih]
      show MvPowerSeries.subst (fun _ => _root_.GlobalTheory.ConvSer.nMul F j) _ = _
      rw [MvPowerSeries.subst_comp_subst_apply
        (_root_.GlobalTheory.ConvSer.nMul_hasSubst_pair (hc i) PowerSeries.constantCoeff_X)
        (hasSubst_of_constantCoeff_zero fun _ => hc j)]
      congr 1
      funext s
      fin_cases s
      · rfl
      · exact PowerSeries.subst_X (hs j)
  · intro S _ φ n
    induction n with
    | zero => simp [_root_.GlobalTheory.ConvSer.nMul_zero]
    | succ n ih =>
      rw [_root_.GlobalTheory.ConvSer.nMul_succ, _root_.GlobalTheory.ConvSer.nMul_succ, FormalGroup.map_toPowerSeries,
        ← ih]
      show MvPowerSeries.map φ _ = _
      rw [MvPowerSeries.map_subst
        (_root_.GlobalTheory.ConvSer.nMul_hasSubst_pair (hc n) PowerSeries.constantCoeff_X)]
      congr 1
      funext s
      fin_cases s
      · rfl
      · exact PowerSeries.map_X φ

end GlobalTheory.ConvSer
