import Formalism.LocalToGlobal.CharacterGerms.FirstStepSecondHalfCondition
import Formalism.LocalToGlobal.CharacterGerms.RowTiePGerm

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

namespace MaximalIdealCongruence

open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ PartialDerivEval

variable {C : Type} [Field C] {V : VF C}

/- English proof (translation)
Unfold `VF.MM at h ⊢`. Rewrite using `[AddValuation.map_neg]`. Conclude with `h`.
-/
theorem mm_neg {a : C} (h : V.MM a) : V.MM (-a) := by
  unfold VF.MM at h ⊢
  rw [AddValuation.map_neg]
  exact h

/- English proof (translation)
Rewrite using `[sub_eq_add_neg]`. Conclude with `mm_add ha (mm_neg hb)`.
-/
theorem mm_sub {a b : C} (ha : V.MM a) (hb : V.MM b) : V.MM (a - b) := by
  rw [sub_eq_add_neg]
  exact mm_add ha (mm_neg hb)

/- English proof (translation)
Rewrite using `[mul_comm]`. Conclude with `mm_mul_ge hb ha`.
-/
theorem mm_mul_ge' {a b : C} (ha : V.Ge 0 a) (hb : V.MM b) : V.MM (a * b) := by
  rw [mul_comm]
  exact mm_mul_ge hb ha

/- English proof (translation)
Unfold `VF.MM`. Unfold `VF.Ge at h`. Establish `h0 : (0 : WithTop ℝ) < ((1 : ℝ) : WithTop ℝ)` using `by exact_mod_cast (zero_lt_one : (0 : ℝ) < 1)`. Conclude with `lt_of_lt_of_le h0 h`.
-/
theorem maximal_of_valuation_ge_one {a : C} (h : V.Ge 1 a) : V.MM a := by
  unfold VF.MM
  unfold VF.Ge at h
  have h0 : (0 : WithTop ℝ) < ((1 : ℝ) : WithTop ℝ) := by exact_mod_cast (zero_lt_one : (0 : ℝ) < 1)
  exact lt_of_lt_of_le h0 h

/- English proof (translation)
Use `mm_mul_ge ?_ hx` and prove the remaining obligations. Unfold `VF.MM`. Rewrite using `[V.v_l]`. Conclude with `(zero_lt_one : (0 : ℝ) < 1)` after adjusting the coercions.
-/
theorem mm_l_mul {x : C} (hx : V.Ge 0 x) : V.MM ((V.l : C) * x) := by
  refine mm_mul_ge ?_ hx
  unfold VF.MM
  rw [V.v_l]
  exact_mod_cast (zero_lt_one : (0 : ℝ) < 1)

/- English proof (translation)
Take `⟨k, rfl⟩` from `h`. Use `push_cast`. Conclude with `mm_l_mul (ge_natCast k)`.
-/
theorem mm_natCast_of_dvd {n : ℕ} (h : V.l ∣ n) : V.MM (n : C) := by
  obtain ⟨k, rfl⟩ := h
  push_cast
  exact mm_l_mul (ge_natCast k)

/- English proof (translation)
Break down `Int.eq_nat_or_neg z with ⟨n, rfl | rfl⟩` into its components or cases. Rewrite using `[Int.cast_natCast]`. Conclude with `ge_natCast n`. Rewrite using `[Int.cast_neg, Int.cast_natCast]`. Conclude with `VF.Ge.neg (ge_natCast n)`.
-/
theorem ge_intCast (z : ℤ) : V.Ge 0 (z : C) := by
  rcases Int.eq_nat_or_neg z with ⟨n, rfl | rfl⟩
  · rw [Int.cast_natCast]
    exact ge_natCast n
  · rw [Int.cast_neg, Int.cast_natCast]
    exact VF.Ge.neg (ge_natCast n)

/- English proof (translation)
Establish `hcop : Nat.Coprime V.l n` using `(Nat.Prime.coprime_iff_not_dvd V.l_prime).2 h`. Establish `hb : ((V.l : ℤ) * Nat.gcdA V.l n + (n : ℤ) * Nat.gcdB V.l n) = 1`. Rewrite using `[← Nat.gcd_eq_gcd_ab, Nat.Coprime.gcd_eq_one hcop]`. Simplify using the standard rewrite rules. Establish `hbC : ((V.l : C) * (Nat.gcdA V.l n : C) + (n : C) * (Nat.gcdB V.l n : C)) = 1`.

Establish `h2` using `congrArg (fun z : ℤ => (z : C)) hb`. Move the coercions through the operations in `at h2`. Conclude with `h2`. Establish `hx' : x = (V.l : C) * ((Nat.gcdA V.l n : C) * x) + (Nat.gcdB V.l n : C) * ((n : C) * x)`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[hbC, one_mul]`. Use `_ = _ := by ring`. Rewrite using `[hx']`. Conclude with `mm_add (mm_l_mul (VF.Ge.mul_int (ge_intCast _) hx)) (mm_mul_ge' (ge_intCast _) hm)`.
-/
theorem mm_of_natCast_mul {n : ℕ} (h : ¬ V.l ∣ n) {x : C} (hx : V.Ge 0 x) (hm : V.MM ((n : C) * x)) :
    V.MM x := by
  have hcop : Nat.Coprime V.l n := (Nat.Prime.coprime_iff_not_dvd V.l_prime).2 h
  have hb : ((V.l : ℤ) * Nat.gcdA V.l n + (n : ℤ) * Nat.gcdB V.l n) = 1 := by
    rw [← Nat.gcd_eq_gcd_ab, Nat.Coprime.gcd_eq_one hcop]
    simp
  have hbC : ((V.l : C) * (Nat.gcdA V.l n : C) + (n : C) * (Nat.gcdB V.l n : C)) = 1 := by
    have h2 := congrArg (fun z : ℤ => (z : C)) hb
    push_cast at h2
    exact h2
  have hx' : x = (V.l : C) * ((Nat.gcdA V.l n : C) * x) + (Nat.gcdB V.l n : C) * ((n : C) * x) := by
    calc x = ((V.l : C) * (Nat.gcdA V.l n : C) + (n : C) * (Nat.gcdB V.l n : C)) * x := by
          rw [hbC, one_mul]
      _ = _ := by ring
  rw [hx']
  exact mm_add (mm_l_mul (VF.Ge.mul_int (ge_intCast _) hx)) (mm_mul_ge' (ge_intCast _) hm)

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero`. Rewrite using `[pow_zero]`. Conclude with `VF.Ge.one`. Consider the case `succ k ih`.

Rewrite using `[pow_succ]`. Conclude with `VF.Ge.mul_int ih hx`.
-/
private theorem ge_pow_lemma {x : C} (hx : V.Ge 0 x) (k : ℕ) : V.Ge 0 (x ^ k) := by
  induction k with
  | zero =>
    rw [pow_zero]
    exact VF.Ge.one
  | succ k ih =>
    rw [pow_succ]
    exact VF.Ge.mul_int ih hx

/- English proof (translation)
Take `⟨k, rfl⟩` from `Nat.exists_eq_succ_of_ne_zero hn`. Rewrite using `[pow_succ]`. Conclude with `mm_mul_ge' (ge_pow_lemma (le_of_lt hx) k) hx`.
-/
theorem mm_pow {x : C} (hx : V.MM x) {n : ℕ} (hn : n ≠ 0) : V.MM (x ^ n) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [pow_succ]
  exact mm_mul_ge' (ge_pow_lemma (le_of_lt hx) k) hx

/- English proof (translation)
Unfold `VF.MM at h ⊢`. Assume the negation of the conclusion as `hc`. Establish `hle : V.v x ≤ 0` using `not_lt.1 hc`. Establish `h2 : V.v (x ^ V.l) ≤ 0`. Rewrite using `[AddValuation.map_pow]`.

Conclude with `nsmul_nonpos hle V.l`. Conclude with `absurd h (not_lt.2 h2)`.
-/
theorem mm_of_pow {x : C} (h : V.MM (x ^ V.l)) : V.MM x := by
  unfold VF.MM at h ⊢
  by_contra hc
  have hle : V.v x ≤ 0 := not_lt.1 hc
  have h2 : V.v (x ^ V.l) ≤ 0 := by
    rw [AddValuation.map_pow]
    exact nsmul_nonpos hle V.l
  exact absurd h (not_lt.2 h2)

/- English proof (translation)
Unfold `VF.Ge at h ⊢`. Assume the negation of the conclusion as `hc`. Establish `hc' : V.v x < 0` using `not_le.1 hc`. Establish `hl : V.l = (V.l - 1) + 1` using `(Nat.sub_add_cancel V.l_prime.one_le).symm`. Rewrite `h` using `[AddValuation.map_pow, hl, succ_nsmul]`.

Establish `h1 : (V.l - 1) • V.v x ≤ 0` using `nsmul_nonpos hc'.le (V.l - 1)`. Establish `h2 : (V.l - 1) • V.v x + V.v x ≤ V.v x`. Combine the equalities or inequalities in the displayed calculation. Conclude with `absurd (le_trans h h2) (not_le.2 hc')`.
-/
theorem ge_of_pow {x : C} (h : V.Ge 0 (x ^ V.l)) : V.Ge 0 x := by
  unfold VF.Ge at h ⊢
  by_contra hc
  have hc' : V.v x < 0 := not_le.1 hc
  have hl : V.l = (V.l - 1) + 1 := (Nat.sub_add_cancel V.l_prime.one_le).symm
  rw [AddValuation.map_pow, hl, succ_nsmul] at h
  have h1 : (V.l - 1) • V.v x ≤ 0 := nsmul_nonpos hc'.le (V.l - 1)
  have h2 : (V.l - 1) • V.v x + V.v x ≤ V.v x := by
    calc (V.l - 1) • V.v x + V.v x ≤ 0 + V.v x := add_le_add h1 le_rfl
      _ = V.v x := zero_add _
  exact absurd (le_trans h h2) (not_le.2 hc')

/- English proof (translation)
Take `⟨k, hk⟩ : ∃ k, V.l = k + 2` from `⟨V.l - 2, by have := V.l_prime.two_le; omega⟩`. Establish `hdvd : ∀ i ∈ Finset.range (k + 1), V.l ∣ (k + 2).choose (i + 1)`. Introduce `i hi`. Rewrite `hi` using `[Finset.mem_range]`. Rewrite using `[hk]`.

Conclude with `Nat.Prime.dvd_choose_self (hk ▸ V.l_prime) (Nat.succ_ne_zero i) (by omega)`. Establish `hexp : (x + y) ^ V.l - x ^ V.l - y ^ V.l = ∑ i ∈ Finset.range (k + 1), x ^ (i + 1) * y ^ (k + 2 - (i + 1)) * ((k + 2).choose (i + 1) : C)`. Rewrite using `[hk, add_pow, Finset.sum_range_succ, Finset.sum_range_succ']`. Simplify using `only [pow_zero, one_mul, mul_one, Nat.choose_self, Nat.choose_zero_right, Nat.cast_one, Nat.sub_zero, Nat.sub_self]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hexp]`. Apply `mm_sum` to reduce the goal to its premises. Introduce `i hi`. Conclude with `mm_mul_ge' (VF.Ge.mul_int (ge_pow_lemma hx _) (ge_pow_lemma hy _)) (mm_natCast_of_dvd (hdvd i hi))`.
-/
theorem mm_add_pow {x y : C} (hx : V.Ge 0 x) (hy : V.Ge 0 y) : V.MM ((x + y) ^ V.l - x ^ V.l - y ^ V.l) := by
  obtain ⟨k, hk⟩ : ∃ k, V.l = k + 2 := ⟨V.l - 2, by have := V.l_prime.two_le; omega⟩
  have hdvd : ∀ i ∈ Finset.range (k + 1), V.l ∣ (k + 2).choose (i + 1) := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [hk]
    exact Nat.Prime.dvd_choose_self (hk ▸ V.l_prime) (Nat.succ_ne_zero i) (by omega)
  have hexp : (x + y) ^ V.l - x ^ V.l - y ^ V.l =
      ∑ i ∈ Finset.range (k + 1), x ^ (i + 1) * y ^ (k + 2 - (i + 1)) * ((k + 2).choose (i + 1) : C) := by
    rw [hk, add_pow, Finset.sum_range_succ, Finset.sum_range_succ']
    simp only [pow_zero, one_mul, mul_one, Nat.choose_self, Nat.choose_zero_right, Nat.cast_one,
      Nat.sub_zero, Nat.sub_self]
    ring
  rw [hexp]
  apply mm_sum
  intro i hi
  exact mm_mul_ge' (VF.Ge.mul_int (ge_pow_lemma hx _) (ge_pow_lemma hy _)) (mm_natCast_of_dvd (hdvd i hi))

def MMS {σ : Type} (V : VF C) (f : MvPowerSeries σ C) : Prop := ∀ μ, V.MM (MvPowerSeries.coeff μ f)

variable {σ τ : Type}

/- English proof (translation)
Introduce `μ`. Rewrite using `[map_zero]`. Conclude with `mm_zero`.
-/
theorem mms_zero : MMS V (0 : MvPowerSeries σ C) := by
  intro μ
  rw [map_zero]
  exact mm_zero

/- English proof (translation)
Introduce `μ`. Rewrite using `[map_add]`. Conclude with `mm_add (hf μ) (hg μ)`.
-/
theorem MMS.add {f g : MvPowerSeries σ C} (hf : MMS V f) (hg : MMS V g) : MMS V (f + g) := by
  intro μ
  rw [map_add]
  exact mm_add (hf μ) (hg μ)

/- English proof (translation)
Introduce `μ`. Rewrite using `[map_neg]`. Conclude with `mm_neg (hf μ)`.
-/
theorem MMS.neg {f : MvPowerSeries σ C} (hf : MMS V f) : MMS V (-f) := by
  intro μ
  rw [map_neg]
  exact mm_neg (hf μ)

/- English proof (translation)
Introduce `μ`. Rewrite using `[map_sub]`. Conclude with `mm_sub (hf μ) (hg μ)`.
-/
theorem MMS.sub {f g : MvPowerSeries σ C} (hf : MMS V f) (hg : MMS V g) : MMS V (f - g) := by
  intro μ
  rw [map_sub]
  exact mm_sub (hf μ) (hg μ)

/- English proof (translation)
Introduce `μ`. Rewrite using `[map_sum]`. Conclude with `mm_sum s _ (fun i hi => hf i hi μ)`.
-/
theorem mms_sum {ι : Type} (s : Finset ι) {f : ι → MvPowerSeries σ C} (hf : ∀ i ∈ s, MMS V (f i)) :
    MMS V (∑ i ∈ s, f i) := by
  intro μ
  rw [map_sum]
  exact mm_sum s _ (fun i hi => hf i hi μ)

/- English proof (translation)
Introduce `μ`. Rewrite using `[MvPowerSeries.coeff_mul]`. Conclude with `mm_sum _ _ (fun p _ => mm_mul_ge' (hf p.1) (hg p.2))`.
-/
theorem MMS.mul_left {f g : MvPowerSeries σ C} (hf : IntS V f) (hg : MMS V g) : MMS V (f * g) := by
  intro μ
  rw [MvPowerSeries.coeff_mul]
  exact mm_sum _ _ (fun p _ => mm_mul_ge' (hf p.1) (hg p.2))

/- English proof (translation)
Introduce `μ`. Rewrite using `[MvPowerSeries.coeff_mul]`. Conclude with `mm_sum _ _ (fun p _ => mm_mul_ge (hf p.1) (hg p.2))`.
-/
theorem MMS.mul_right {f g : MvPowerSeries σ C} (hf : MMS V f) (hg : IntS V g) : MMS V (f * g) := by
  intro μ
  rw [MvPowerSeries.coeff_mul]
  exact mm_sum _ _ (fun p _ => mm_mul_ge (hf p.1) (hg p.2))

/- English proof (translation)
Introduce `μ`. Rewrite using `[MvPowerSeries.coeff_pderiv]`. Use `mm_mul_ge (hf _) ?_` and prove the remaining obligations. Use `first`. Consider the case `exact ge_natCast _`.

Consider the case `exact VF.Ge.add (ge_natCast _) VF.Ge.one`. Consider the case `(push_cast; exact VF.Ge.add (ge_natCast _) VF.Ge.one)`.
-/
theorem MMS.pderiv {f : MvPowerSeries σ C} (hf : MMS V f) (i : σ) : MMS V (MvPowerSeries.pderiv C i f) := by
  intro μ
  rw [MvPowerSeries.coeff_pderiv]
  refine mm_mul_ge (hf _) ?_
  first
    | exact ge_natCast _
    | exact VF.Ge.add (ge_natCast _) VF.Ge.one
    | (push_cast; exact VF.Ge.add (ge_natCast _) VF.Ge.one)

/- English proof (translation)
Use `first`. Consider the case `exact MvPowerSeries.HasSubst.of_constantCoeff_zero ha0`. Consider the case `exact MvPowerSeries.hasSubst_of_constantCoeff_zero ha0`. Consider the case `exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun s => by rw [ha0 s]; exact IsNilpotent.zero)`. Consider the case `exact MvPowerSeries.hasSubst_of_constantCoeff_nilpotent (fun s => by rw [ha0 s]; exact IsNilpotent.zero)`.
-/
private theorem hasSubst_lemma_2 [Finite σ] {a : σ → MvPowerSeries τ C}
    (ha0 : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) : MvPowerSeries.HasSubst a := by
  first
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero ha0
    | exact MvPowerSeries.hasSubst_of_constantCoeff_zero ha0
    | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun s => by rw [ha0 s]; exact IsNilpotent.zero)
    | exact MvPowerSeries.hasSubst_of_constantCoeff_nilpotent (fun s => by rw [ha0 s]; exact IsNilpotent.zero)

/- English proof (translation)
Rewrite using `[finsum_def]`. Use `split_ifs`. Conclude with `mm_sum _ _ (fun i _ => h i)`. Conclude with `mm_zero`.
-/
private theorem mm_finsum_lemma_3 {ι : Type} {g : ι → C} (h : ∀ i, V.MM (g i)) : V.MM (∑ᶠ i, g i) := by
  rw [finsum_def]
  split_ifs
  · exact mm_sum _ _ (fun i _ => h i)
  · exact mm_zero

/- English proof (translation)
Rewrite using `[finsum_def]`. Use `split_ifs`. Conclude with `Finset.sum_induction _ (V.Ge 0) (fun _ _ ha hb => VF.Ge.add ha hb) (by unfold VF.Ge; rw [AddValuation.map_zero]; exact le_top) (fun i _ => h i)`. Unfold `VF.Ge`. Rewrite using `[AddValuation.map_zero]`.

Conclude with `le_top`.
-/
private theorem ge_finsum_lemma_8 {ι : Type} {g : ι → C} (h : ∀ i, V.Ge 0 (g i)) : V.Ge 0 (∑ᶠ i, g i) := by
  rw [finsum_def]
  split_ifs
  · exact Finset.sum_induction _ (V.Ge 0) (fun _ _ ha hb => VF.Ge.add ha hb)
      (by unfold VF.Ge; rw [AddValuation.map_zero]; exact le_top) (fun i _ => h i)
  · unfold VF.Ge
    rw [AddValuation.map_zero]
    exact le_top

/- English proof (translation)
Unfold `Finsupp.prod`. Conclude with `Finset.prod_induction _ (IntS V) (fun _ _ hx hy => intS_mul hx hy) intS_one (fun s _ => intS_pow (ha s) _)`.
-/
private theorem intS_fprod_lemma_4 {a : σ → MvPowerSeries τ C} (ha : ∀ s, IntS V (a s)) (d : σ →₀ ℕ) :
    IntS V (d.prod fun s e => a s ^ e) := by
  unfold Finsupp.prod
  exact Finset.prod_induction _ (IntS V) (fun _ _ hx hy => intS_mul hx hy) intS_one
    (fun s _ => intS_pow (ha s) _)

/- English proof (translation)
Establish `hs` using `hasSubst_lemma_2 ha0`. Introduce `μ`. Rewrite using `[MvPowerSeries.coeff_subst hs]`. Apply `mm_finsum_lemma_3` to reduce the goal to its premises. Introduce `d`.

Rewrite using `[smul_eq_mul]`. Conclude with `mm_mul_ge (hf d) (intS_fprod_lemma_4 ha d μ)`.
-/
theorem MMS.subst [Finite σ] {a : σ → MvPowerSeries τ C} (ha0 : ∀ s, MvPowerSeries.constantCoeff (a s) = 0)
    (ha : ∀ s, IntS V (a s)) {f : MvPowerSeries σ C} (hf : MMS V f) : MMS V (MvPowerSeries.subst a f) := by
  have hs := hasSubst_lemma_2 ha0
  intro μ
  rw [MvPowerSeries.coeff_subst hs]
  apply mm_finsum_lemma_3
  intro d
  rw [smul_eq_mul]
  exact mm_mul_ge (hf d) (intS_fprod_lemma_4 ha d μ)

/- English proof (translation)
Conclude with `MMS.subst (a := fun p : Fin m × Fin d => a p.1 p.2) (fun p => ha p.1 p.2) (fun p => hi p.1 p.2) hf`.
-/
theorem MMS.ev_of {d m n : ℕ} {a : Fin m → Pt C n d} (ha : Z0 a) (hi : ∀ k i, IntS V (a k i)) {f : PS C m d}
    (hf : MMS V f) : MMS V (ev a f) := by
  exact MMS.subst (a := fun p : Fin m × Fin d => a p.1 p.2) (fun p => ha p.1 p.2) (fun p => hi p.1 p.2) hf

def intSer (V : VF C) (σ : Type) : Subring (MvPowerSeries σ C) where
  carrier := {f | IntS V f}
  mul_mem' := fun ha hb => intS_mul ha hb
  one_mem' := intS_one
  add_mem' := fun ha hb => intS_add ha hb
  zero_mem' := intS_zero
  neg_mem' := fun ha => intS_neg ha

/- English proof (translation)
Introduce `μ`. Rewrite using `[← nsmul_eq_mul, map_nsmul, nsmul_eq_mul]`. Conclude with `mm_l_mul (hf μ)`.
-/
theorem mms_l_mul {f : MvPowerSeries σ C} (hf : IntS V f) : MMS V ((V.l : MvPowerSeries σ C) * f) := by
  intro μ
  rw [← nsmul_eq_mul, map_nsmul, nsmul_eq_mul]
  exact mm_l_mul (hf μ)

/- English proof (translation)
Introduce `μ`. Rewrite using `[mul_comm, ← nsmul_eq_mul, map_nsmul, nsmul_eq_mul]`. Conclude with `mm_mul_ge (mm_natCast_of_dvd hn) (hh μ)`.
-/
private theorem mms_mul_natCast_lemma_5 {h : MvPowerSeries σ C} (hh : IntS V h) {n : ℕ} (hn : V.l ∣ n) :
    MMS V (h * (n : MvPowerSeries σ C)) := by
  intro μ
  rw [mul_comm, ← nsmul_eq_mul, map_nsmul, nsmul_eq_mul]
  exact mm_mul_ge (mm_natCast_of_dvd hn) (hh μ)

/- English proof (translation)
Take `⟨k, hk⟩ : ∃ k, V.l = k + 2` from `⟨V.l - 2, by have := V.l_prime.two_le; omega⟩`. Establish `hdvd : ∀ i ∈ Finset.range (k + 1), V.l ∣ (k + 2).choose (i + 1)`. Introduce `i hi`. Rewrite `hi` using `[Finset.mem_range]`. Rewrite using `[hk]`.

Conclude with `Nat.Prime.dvd_choose_self (hk ▸ V.l_prime) (Nat.succ_ne_zero i) (by omega)`. Establish `hexp : (f + g) ^ V.l - f ^ V.l - g ^ V.l = ∑ i ∈ Finset.range (k + 1), f ^ (i + 1) * g ^ (k + 2 - (i + 1)) * ((k + 2).choose (i + 1) : MvPowerSeries σ C)`. Rewrite using `[hk, add_pow, Finset.sum_range_succ, Finset.sum_range_succ']`. Simplify using `only [pow_zero, one_mul, mul_one, Nat.choose_self, Nat.choose_zero_right, Nat.cast_one, Nat.sub_zero, Nat.sub_self]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hexp]`. Apply `mms_sum` to reduce the goal to its premises. Introduce `i hi`. Conclude with `mms_mul_natCast_lemma_5 (intS_mul (intS_pow hf _) (intS_pow hg _)) (hdvd i hi)`.
-/
theorem mms_add_pow {f g : MvPowerSeries σ C} (hf : IntS V f) (hg : IntS V g) :
    MMS V ((f + g) ^ V.l - f ^ V.l - g ^ V.l) := by
  obtain ⟨k, hk⟩ : ∃ k, V.l = k + 2 := ⟨V.l - 2, by have := V.l_prime.two_le; omega⟩
  have hdvd : ∀ i ∈ Finset.range (k + 1), V.l ∣ (k + 2).choose (i + 1) := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [hk]
    exact Nat.Prime.dvd_choose_self (hk ▸ V.l_prime) (Nat.succ_ne_zero i) (by omega)
  have hexp : (f + g) ^ V.l - f ^ V.l - g ^ V.l =
      ∑ i ∈ Finset.range (k + 1),
        f ^ (i + 1) * g ^ (k + 2 - (i + 1)) * ((k + 2).choose (i + 1) : MvPowerSeries σ C) := by
    rw [hk, add_pow, Finset.sum_range_succ, Finset.sum_range_succ']
    simp only [pow_zero, one_mul, mul_one, Nat.choose_self, Nat.choose_zero_right, Nat.cast_one,
      Nat.sub_zero, Nat.sub_self]
    ring
  rw [hexp]
  apply mms_sum
  intro i hi
  exact mms_mul_natCast_lemma_5 (intS_mul (intS_pow hf _) (intS_pow hg _)) (hdvd i hi)

/- English proof (translation)
Use `revert hf`. Use `Finset.induction_on s ?_ ?_` and prove the remaining obligations. Introduce `_`. Establish `e : ((∑ i ∈ (∅ : Finset ι), f i) ^ V.l - ∑ i ∈ (∅ : Finset ι), f i ^ V.l) = 0`. Simplify using `[zero_pow V.l_prime.ne_zero]`.

Rewrite using `[e]`. Conclude with `mms_zero`. Introduce `a s ha ih hf`. Establish `hfa : IntS V (f a)` using `hf a (Finset.mem_insert_self a s)`. Establish `hfs : ∀ i ∈ s, IntS V (f i)` using `fun i hi => hf i (Finset.mem_insert_of_mem hi)`.

Rewrite using `[Finset.sum_insert ha, Finset.sum_insert ha]`. Establish `e : (f a + ∑ i ∈ s, f i) ^ V.l - (f a ^ V.l + ∑ i ∈ s, f i ^ V.l) = ((f a + ∑ i ∈ s, f i) ^ V.l - f a ^ V.l - (∑ i ∈ s, f i) ^ V.l) + ((∑ i ∈ s, f i) ^ V.l - ∑ i ∈ s, f i ^ V.l)` using `by ring`. Rewrite using `[e]`. Conclude with `MMS.add (mms_add_pow hfa (intS_sum s hfs)) (ih hfs)`.
-/
theorem mms_sum_pow {ι : Type} (s : Finset ι) (f : ι → MvPowerSeries σ C) (hf : ∀ i ∈ s, IntS V (f i)) :
    MMS V ((∑ i ∈ s, f i) ^ V.l - ∑ i ∈ s, f i ^ V.l) := by
  revert hf
  refine Finset.induction_on s ?_ ?_
  · intro _
    have e : ((∑ i ∈ (∅ : Finset ι), f i) ^ V.l - ∑ i ∈ (∅ : Finset ι), f i ^ V.l) = 0 := by
      simp [zero_pow V.l_prime.ne_zero]
    rw [e]
    exact mms_zero
  · intro a s ha ih hf
    have hfa : IntS V (f a) := hf a (Finset.mem_insert_self a s)
    have hfs : ∀ i ∈ s, IntS V (f i) := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have e : (f a + ∑ i ∈ s, f i) ^ V.l - (f a ^ V.l + ∑ i ∈ s, f i ^ V.l) =
        ((f a + ∑ i ∈ s, f i) ^ V.l - f a ^ V.l - (∑ i ∈ s, f i) ^ V.l) +
          ((∑ i ∈ s, f i) ^ V.l - ∑ i ∈ s, f i ^ V.l) := by ring
    rw [e]
    exact MMS.add (mms_add_pow hfa (intS_sum s hfs)) (ih hfs)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coeff_frobTw (l : ℕ) (c : MvPowerSeries σ C) (μ : σ →₀ ℕ) :
    MvPowerSeries.coeff μ (frobTw l c) =
      if ∀ s, l ∣ μ s then (MvPowerSeries.coeff (μ.mapRange (fun n => n / l) (Nat.zero_div l)) c) ^ l else 0 := rfl

/- English proof (translation)
Use extensionality with `s`. Rewrite using `[Finsupp.mapRange_apply, Finsupp.smul_apply, smul_eq_mul, Nat.mul_div_cancel_left _ hl]`.
-/
theorem divl_smul {l : ℕ} (hl : 0 < l) (ν : σ →₀ ℕ) :
    (l • ν).mapRange (fun n => n / l) (Nat.zero_div l) = ν := by
  ext s
  rw [Finsupp.mapRange_apply, Finsupp.smul_apply, smul_eq_mul, Nat.mul_div_cancel_left _ hl]

/- English proof (translation)
Use extensionality with `s`. Rewrite using `[Finsupp.smul_apply, smul_eq_mul, Finsupp.mapRange_apply, Nat.mul_div_cancel' (h s)]`.
-/
theorem smul_divl {l : ℕ} {μ : σ →₀ ℕ} (h : ∀ s, l ∣ μ s) :
    l • μ.mapRange (fun n => n / l) (Nat.zero_div l) = μ := by
  ext s
  rw [Finsupp.smul_apply, smul_eq_mul, Finsupp.mapRange_apply, Nat.mul_div_cancel' (h s)]

/- English proof (translation)
Introduce `s`. Rewrite using `[Finsupp.mapRange_apply]`. Conclude with `Nat.div_le_self _ _`.
-/
theorem divl_le (l : ℕ) (μ : σ →₀ ℕ) : μ.mapRange (fun n => n / l) (Nat.zero_div l) ≤ μ := by
  intro s
  rw [Finsupp.mapRange_apply]
  exact Nat.div_le_self _ _

/- English proof (translation)
Introduce `μ`. Rewrite using `[coeff_frobTw]`. Use `split_ifs`. Conclude with `ge_pow_lemma (hc _) _`. Unfold `VF.Ge`.

Rewrite using `[AddValuation.map_zero]`. Conclude with `le_top`.
-/
theorem intS_frobTw {c : MvPowerSeries σ C} (hc : IntS V c) : IntS V (frobTw V.l c) := by
  intro μ
  rw [coeff_frobTw]
  split_ifs
  · exact ge_pow_lemma (hc _) _
  · unfold VF.Ge
    rw [AddValuation.map_zero]
    exact le_top

/- English proof (translation)
Introduce `μ`. Rewrite using `[map_sub, map_add, coeff_frobTw, coeff_frobTw, coeff_frobTw]`. Use `split_ifs`. Rewrite using `[map_add, ← sub_sub]`. Conclude with `mm_add_pow (hf _) (hg _)`.

Rewrite using `[add_zero, sub_zero]`. Conclude with `mm_zero`.
-/
theorem mms_frobTw_add {f g : MvPowerSeries σ C} (hf : IntS V f) (hg : IntS V g) :
    MMS V (frobTw V.l (f + g) - (frobTw V.l f + frobTw V.l g)) := by
  intro μ
  rw [map_sub, map_add, coeff_frobTw, coeff_frobTw, coeff_frobTw]
  split_ifs
  · rw [map_add, ← sub_sub]
    exact mm_add_pow (hf _) (hg _)
  · rw [add_zero, sub_zero]
    exact mm_zero

/- English proof (translation)
Establish `h` using `mm_neg (mm_add_pow (VF.Ge.neg ha) ha)`. Establish `e : -((-a + a) ^ V.l - (-a) ^ V.l - a ^ V.l) = (-a) ^ V.l + a ^ V.l`. Rewrite using `[show -a + a = 0 by ring, zero_pow V.l_prime.ne_zero]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `h` using `[e]`.

Conclude with `h`.
-/
private theorem mm_neg_pow_add_lemma_6 {a : C} (ha : V.Ge 0 a) : V.MM ((-a) ^ V.l + a ^ V.l) := by
  have h := mm_neg (mm_add_pow (VF.Ge.neg ha) ha)
  have e : -((-a + a) ^ V.l - (-a) ^ V.l - a ^ V.l) = (-a) ^ V.l + a ^ V.l := by
    rw [show -a + a = 0 by ring, zero_pow V.l_prime.ne_zero]
    ring
  rw [e] at h
  exact h

/- English proof (translation)
Introduce `μ`. Rewrite using `[map_add, coeff_frobTw, coeff_frobTw]`. Use `split_ifs`. Rewrite using `[map_neg]`. Conclude with `mm_neg_pow_add_lemma_6 (hf _)`.

Rewrite using `[add_zero]`. Conclude with `mm_zero`.
-/
theorem mms_frobTw_neg {f : MvPowerSeries σ C} (hf : IntS V f) :
    MMS V (frobTw V.l (-f) + frobTw V.l f) := by
  intro μ
  rw [map_add, coeff_frobTw, coeff_frobTw]
  split_ifs
  · rw [map_neg]
    exact mm_neg_pow_add_lemma_6 (hf _)
  · rw [add_zero]
    exact mm_zero

/- English proof (translation)
Introduce `ν`. Establish `h1` using `h (V.l • ν)`. Establish `hd : ∀ s, V.l ∣ (V.l • ν) s` using `fun s => by`. Rewrite using `[Finsupp.smul_apply, smul_eq_mul]`. Conclude with `dvd_mul_right _ _`.

Rewrite `h1` using `[coeff_frobTw, if_pos hd, divl_smul V.l_prime.pos]`. Conclude with `mm_of_pow h1`.
-/
theorem mms_of_frobTw {e : MvPowerSeries σ C} (h : MMS V (frobTw V.l e)) : MMS V e := by
  intro ν
  have h1 := h (V.l • ν)
  have hd : ∀ s, V.l ∣ (V.l • ν) s := fun s => by
    rw [Finsupp.smul_apply, smul_eq_mul]
    exact dvd_mul_right _ _
  rw [coeff_frobTw, if_pos hd, divl_smul V.l_prime.pos] at h1
  exact mm_of_pow h1

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp [MvPowerSeries.monomial_zero_one]`. Consider the case `succ k ih => rw [pow_succ, ih, MvPowerSeries.monomial_mul_monomial, succ_nsmul, pow_succ]`.
-/
private theorem monomial_pow_lemma_9 (ν : σ →₀ ℕ) (c : C) (k : ℕ) :
    (MvPowerSeries.monomial ν c) ^ k = MvPowerSeries.monomial (k • ν) (c ^ k) := by
  induction k with
  | zero => simp [MvPowerSeries.monomial_zero_one]
  | succ k ih => rw [pow_succ, ih, MvPowerSeries.monomial_mul_monomial, succ_nsmul, pow_succ]

/- English proof (translation)
Introduce `μ`. Rewrite using `[MvPowerSeries.coeff_monomial]`. Use `split_ifs`. Conclude with `hc`. Unfold `VF.Ge`.

Rewrite using `[AddValuation.map_zero]`. Conclude with `le_top`.
-/
private theorem intS_monomial_lemma_10 {ν : σ →₀ ℕ} {c : C} (hc : V.Ge 0 c) :
    IntS V (MvPowerSeries.monomial ν c) := by
  intro μ
  rw [MvPowerSeries.coeff_monomial]
  split_ifs
  · exact hc
  · unfold VF.Ge
    rw [AddValuation.map_zero]
    exact le_top

/- English proof (translation)
Introduce `μ`. Use `set S : Finset (σ →₀ ℕ) := Finset.Iic μ with hS`. Use `set P : MvPowerSeries σ C := ∑ ν ∈ S, MvPowerSeries.monomial ν (MvPowerSeries.coeff ν f) with hP`. Establish `hcoeffP : ∀ ν, MvPowerSeries.coeff ν P = if ν ∈ S then MvPowerSeries.coeff ν f else 0`. Introduce `ν`.

Rewrite using `[hP, map_sum]`. Simplify using `only [MvPowerSeries.coeff_monomial]`. Rewrite using `[Finset.sum_ite_eq]`. Establish `hlow : ∀ ν, ν ≤ μ → MvPowerSeries.coeff ν (f - P) = 0`. Introduce `ν hν`.

Rewrite using `[map_sub, hcoeffP, if_pos (Finset.mem_Iic.2 hν)]`. Conclude with `sub_self _`. Establish `h1 : MvPowerSeries.coeff μ (f ^ V.l) = MvPowerSeries.coeff μ (P ^ V.l)`. Take `⟨Q, hQ⟩` from `sub_dvd_pow_sub_pow f P V.l`. Establish `h2 : MvPowerSeries.coeff μ (f ^ V.l - P ^ V.l) = 0`.

Rewrite using `[hQ, MvPowerSeries.coeff_mul]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `p hp`. Use `first`. Consider the case `rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp`.

Consider the case `rw [Finset.mem_antidiagonal] at hp`. Consider the case `simp only [Finset.mem_antidiagonal] at hp`. Rewrite using `[hlow p.1 (by rw [← hp]; exact le_self_add), zero_mul]`. Rewrite `h2` using `[map_sub, sub_eq_zero]`. Conclude with `h2`.

Establish `h3 : MvPowerSeries.coeff μ (frobTw V.l f) = MvPowerSeries.coeff μ (frobTw V.l P)`. Rewrite using `[coeff_frobTw, coeff_frobTw]`. Use `split_ifs`. Rewrite using `[hcoeffP, if_pos (Finset.mem_Iic.2 (divl_le _ _))]`. Both sides reduce to the same expression.

Establish `h4 : frobTw V.l P = ∑ ν ∈ S, (MvPowerSeries.monomial ν (MvPowerSeries.coeff ν f)) ^ V.l`. Use extensionality with `μ'`. Rewrite using `[coeff_frobTw]`. Simplify using `only [hP, map_sum, monomial_pow_lemma_9, MvPowerSeries.coeff_monomial]`. Use `split_ifs with hd`.

Rewrite using `[Finset.sum_ite_eq]`. Establish `e : ∀ ν : σ →₀ ℕ, (μ' = V.l • ν) ↔ (ν = μ'.mapRange (fun n => n / V.l) (Nat.zero_div V.l))`. Introduce `ν`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `rfl`.

Conclude with `(divl_smul V.l_prime.pos ν).symm`. Introduce and unpack `rfl`. Conclude with `(smul_divl hd).symm`. Simplify using `only [e]`. Rewrite using `[Finset.sum_ite_eq']`.

Apply the tactic sequence `split_ifs <;> simp [zero_pow V.l_prime.ne_zero]`. Use `symm`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `ν _`. Rewrite using `[if_neg]`.

Introduce and unpack `rfl`. Apply `hd` to reduce the goal to its premises. Introduce `s`. Rewrite using `[Finsupp.smul_apply, smul_eq_mul]`. Conclude with `dvd_mul_right _ _`.

Establish `h5 : MMS V (P ^ V.l - ∑ ν ∈ S, (MvPowerSeries.monomial ν (MvPowerSeries.coeff ν f)) ^ V.l)` using `mms_sum_pow S _ (fun ν _ => intS_monomial_lemma_10 (hf ν))`. Establish `h6` using `h5 μ`. Rewrite `h6`, the goal using `[map_sub]`. Rewrite using `[h1, h3, h4]`. Conclude with `h6`.
-/
theorem mms_pow_frobTw [Finite σ] {f : MvPowerSeries σ C} (hf : IntS V f) : MMS V (f ^ V.l - frobTw V.l f) := by
  classical
  intro μ
  set S : Finset (σ →₀ ℕ) := Finset.Iic μ with hS
  set P : MvPowerSeries σ C := ∑ ν ∈ S, MvPowerSeries.monomial ν (MvPowerSeries.coeff ν f) with hP
  have hcoeffP : ∀ ν, MvPowerSeries.coeff ν P = if ν ∈ S then MvPowerSeries.coeff ν f else 0 := by
    intro ν
    rw [hP, map_sum]
    simp only [MvPowerSeries.coeff_monomial]
    rw [Finset.sum_ite_eq]
  have hlow : ∀ ν, ν ≤ μ → MvPowerSeries.coeff ν (f - P) = 0 := by
    intro ν hν
    rw [map_sub, hcoeffP, if_pos (Finset.mem_Iic.2 hν)]
    exact sub_self _
  have h1 : MvPowerSeries.coeff μ (f ^ V.l) = MvPowerSeries.coeff μ (P ^ V.l) := by
    obtain ⟨Q, hQ⟩ := sub_dvd_pow_sub_pow f P V.l
    have h2 : MvPowerSeries.coeff μ (f ^ V.l - P ^ V.l) = 0 := by
      rw [hQ, MvPowerSeries.coeff_mul]
      apply Finset.sum_eq_zero
      intro p hp
      first
        | rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
        | rw [Finset.mem_antidiagonal] at hp
        | simp only [Finset.mem_antidiagonal] at hp
      rw [hlow p.1 (by rw [← hp]; exact le_self_add), zero_mul]
    rw [map_sub, sub_eq_zero] at h2
    exact h2
  have h3 : MvPowerSeries.coeff μ (frobTw V.l f) = MvPowerSeries.coeff μ (frobTw V.l P) := by
    rw [coeff_frobTw, coeff_frobTw]
    split_ifs
    · rw [hcoeffP, if_pos (Finset.mem_Iic.2 (divl_le _ _))]
    · rfl
  have h4 : frobTw V.l P = ∑ ν ∈ S, (MvPowerSeries.monomial ν (MvPowerSeries.coeff ν f)) ^ V.l := by
    ext μ'
    rw [coeff_frobTw]
    simp only [hP, map_sum, monomial_pow_lemma_9, MvPowerSeries.coeff_monomial]
    split_ifs with hd
    · rw [Finset.sum_ite_eq]
      have e : ∀ ν : σ →₀ ℕ, (μ' = V.l • ν) ↔ (ν = μ'.mapRange (fun n => n / V.l) (Nat.zero_div V.l)) := by
        intro ν
        constructor
        · rintro rfl
          exact (divl_smul V.l_prime.pos ν).symm
        · rintro rfl
          exact (smul_divl hd).symm
      simp only [e]
      rw [Finset.sum_ite_eq']
      split_ifs <;> simp [zero_pow V.l_prime.ne_zero]
    · symm
      apply Finset.sum_eq_zero
      intro ν _
      rw [if_neg]
      rintro rfl
      apply hd
      intro s
      rw [Finsupp.smul_apply, smul_eq_mul]
      exact dvd_mul_right _ _
  have h5 : MMS V (P ^ V.l - ∑ ν ∈ S, (MvPowerSeries.monomial ν (MvPowerSeries.coeff ν f)) ^ V.l) :=
    mms_sum_pow S _ (fun ν _ => intS_monomial_lemma_10 (hf ν))
  have h6 := h5 μ
  rw [map_sub] at h6 ⊢
  rw [h1, h3, h4]
  exact h6

/- English proof (translation)
Establish `hs` using `hasSubst_lemma_2 ha0`. Introduce `μ`. Rewrite using `[MvPowerSeries.coeff_subst hs]`. Apply `ge_finsum_lemma_8` to reduce the goal to its premises. Introduce `d`.

Rewrite using `[smul_eq_mul]`. Conclude with `VF.Ge.mul_int (hf d) (intS_fprod_lemma_4 ha d μ)`.
-/
private theorem intS_subst_lemma_7 [Finite σ] {a : σ → MvPowerSeries τ C}
    (ha0 : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (ha : ∀ s, IntS V (a s)) {f : MvPowerSeries σ C}
    (hf : IntS V f) : IntS V (MvPowerSeries.subst a f) := by
  have hs := hasSubst_lemma_2 ha0
  intro μ
  rw [MvPowerSeries.coeff_subst hs]
  apply ge_finsum_lemma_8
  intro d
  rw [smul_eq_mul]
  exact VF.Ge.mul_int (hf d) (intS_fprod_lemma_4 ha d μ)

/- English proof (translation)
Establish `hs` using `hasSubst_lemma_2 ha0`. Establish `hpow : MvPowerSeries.subst a (f ^ V.l) = (MvPowerSeries.subst a f) ^ V.l` using `by first`. Consider the case `exact MvPowerSeries.subst_pow hs _ _`. Consider the case `(rw [← MvPowerSeries.coe_substAlgHom hs]; exact map_pow _ _ _)`. Establish `hsub : MvPowerSeries.subst a (f ^ V.l - frobTw V.l f) = MvPowerSeries.subst a (f ^ V.l) - MvPowerSeries.subst a (frobTw V.l f)` using `by first`.

Consider the case `exact MvPowerSeries.subst_sub hs _ _`. Consider the case `(rw [← MvPowerSeries.coe_substAlgHom hs]; exact map_sub _ _ _)`. Establish `e : MvPowerSeries.subst a (frobTw V.l f) - frobTw V.l (MvPowerSeries.subst a f) = -(MvPowerSeries.subst a (f ^ V.l - frobTw V.l f)) + ((MvPowerSeries.subst a f) ^ V.l - frobTw V.l (MvPowerSeries.subst a f))`. Rewrite using `[hsub, hpow]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e]`. Conclude with `MMS.add (MMS.neg (MMS.subst ha0 ha (mms_pow_frobTw hf))) (mms_pow_frobTw (intS_subst_lemma_7 ha0 ha hf))`.
-/
theorem mms_subst_frobTw [Finite σ] [Finite τ] {a : σ → MvPowerSeries τ C}
    (ha0 : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (ha : ∀ s, IntS V (a s)) {f : MvPowerSeries σ C}
    (hf : IntS V f) :
    MMS V (MvPowerSeries.subst a (frobTw V.l f) - frobTw V.l (MvPowerSeries.subst a f)) := by
  have hs := hasSubst_lemma_2 ha0
  have hpow : MvPowerSeries.subst a (f ^ V.l) = (MvPowerSeries.subst a f) ^ V.l := by
    first
      | exact MvPowerSeries.subst_pow hs _ _
      | (rw [← MvPowerSeries.coe_substAlgHom hs]; exact map_pow _ _ _)
  have hsub : MvPowerSeries.subst a (f ^ V.l - frobTw V.l f) =
      MvPowerSeries.subst a (f ^ V.l) - MvPowerSeries.subst a (frobTw V.l f) := by
    first
      | exact MvPowerSeries.subst_sub hs _ _
      | (rw [← MvPowerSeries.coe_substAlgHom hs]; exact map_sub _ _ _)
  have e : MvPowerSeries.subst a (frobTw V.l f) - frobTw V.l (MvPowerSeries.subst a f) =
      -(MvPowerSeries.subst a (f ^ V.l - frobTw V.l f)) +
        ((MvPowerSeries.subst a f) ^ V.l - frobTw V.l (MvPowerSeries.subst a f)) := by
    rw [hsub, hpow]
    ring
  rw [e]
  exact MMS.add (MMS.neg (MMS.subst ha0 ha (mms_pow_frobTw hf)))
    (mms_pow_frobTw (intS_subst_lemma_7 ha0 ha hf))

end MaximalIdealCongruence

end Formalism.L2.FormalSeriesBounds
