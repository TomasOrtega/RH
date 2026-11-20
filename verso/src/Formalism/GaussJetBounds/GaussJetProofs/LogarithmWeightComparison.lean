import Formalism.GaussJetBounds.GaussJetProofs.SubstitutionWeightBound
import Formalism.FormalGroupWitt.FormalGroupWittProofs.SolveV
import Formalism.FormalGroupWitt.FormalGroupWittProofs.EqSingleOfDegreeEqOne
import Formalism.IncomingBounds.FlowDegreeBounds.PadicValFactorialRatioProd

noncomputable section
open scoped BigOperators

universe u v w

namespace Formalism.DworkPowerSeriesWeights

open Formalism.IncomingBounds MvPowerSeries
open Formalism.FG.SolveVAux (Low low_mono low_add low_mul low_pow low_one_iff low_P)

/- English proof (translation)
Use `show (n.sum fun i k => (k : ℝ) * c) = ((∑ i ∈ n.support, n i : ℕ) : ℝ) * c`. Rewrite using `[Finsupp.sum, Nat.cast_sum, Finset.sum_mul]`.
-/
theorem dot_const {ι : Type v} (n : ι →₀ ℕ) (c : ℝ) :
    dot n (fun _ => c) = (n.degree : ℝ) * c := by
  show (n.sum fun i k => (k : ℝ) * c) = ((∑ i ∈ n.support, n i : ℕ) : ℝ) * c
  rw [Finsupp.sum, Nat.cast_sum, Finset.sum_mul]

def truncBelow {K : Type u} [Field K] {τ : Type v} (N : ℕ) (f : MvPowerSeries τ K) :
    MvPowerSeries τ K :=
  fun m => if m.degree < N then coeff m f else 0

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coeff_truncBelow {K : Type u} [Field K] {τ : Type v} (N : ℕ) (f : MvPowerSeries τ K)
    (m : τ →₀ ℕ) : coeff m (truncBelow N f) = if m.degree < N then coeff m f else 0 := rfl

/- English proof (translation)
Introduce `d hd`. Establish `hs : HasSubst k` using `hasSubst_of_constantCoeff_zero hk`. Rewrite using `[coeff_subst hs]`. Use `finsum_eq_zero_of_forall_eq_zero fun e => ?_` and prove the remaining obligations. Break down `lt_or_ge e.degree m with he | he` into its components or cases.

Rewrite using `[hf e he, zero_smul]`. Use `low_P (fun i => (low_one_iff _).2 (hk i)) e d (lt_of_lt_of_le hd he)` as an intermediate fact. Simplify using `only [Formalism.FG.SolveVAux.P] at this`. Rewrite using `[this, smul_zero]`.
-/
theorem low_subst_of_low {K : Type u} [Field K] {ι : Type v} [Finite ι] {τ : Type w}
    {k : ι → MvPowerSeries τ K} (hk : ∀ i, constantCoeff (k i) = 0) {m : ℕ}
    {f : MvPowerSeries ι K} (hf : Low m f) : Low m (subst k f) := by
  intro d hd
  have hs : HasSubst k := hasSubst_of_constantCoeff_zero hk
  rw [coeff_subst hs]
  refine finsum_eq_zero_of_forall_eq_zero fun e => ?_
  rcases lt_or_ge e.degree m with he | he
  · rw [hf e he, zero_smul]
  · have := low_P (fun i => (low_one_iff _).2 (hk i)) e d (lt_of_lt_of_le hd he)
    simp only [Formalism.FG.SolveVAux.P] at this
    rw [this, smul_zero]

section Shift

variable {K : Type u} [Field K] {τ : Type v} [DecidableEq τ]

/- English proof (translation)
Conclude with `Nat.lt_pow_self (by nlinarith)`.
-/
theorem lt_sq_pow {l : ℕ} (hl : 2 ≤ l) (e : ℕ) : e < (l ^ 2) ^ e := by
  exact Nat.lt_pow_self (by nlinarith)

/- English proof (translation)
Use `show (∑ e ∈ Finset.range (n.degree + 1), if n = Finsupp.single (p^[e] x) ((l ^ 2) ^ e) then ((l : K) ^ e)⁻¹ else 0) = _`. Apply `Finset.sum_subset (fun e he => by simp only [Finset.mem_range] at he ⊢; omega)` to reduce the goal to its premises. Introduce `e _ hne`. Rewrite using `[if_neg]`. Introduce `h`.

Apply `hne` to reduce the goal to its premises. Rewrite using `[Finset.mem_range]`. Establish `hd` using `congrArg Finsupp.degree h`. Rewrite `hd` using `[Finsupp.degree_single]`. Use `lt_sq_pow hl e` as an intermediate fact.

Use linear arithmetic over natural numbers and integers.
-/
theorem coeff_genLog {l : ℕ} (hl : 2 ≤ l) (p : τ → τ) (x : τ) (n : τ →₀ ℕ) {M : ℕ}
    (hM : n.degree < M) :
    coeff n (genLog (K := K) l p x) = ∑ e ∈ Finset.range M,
      if n = Finsupp.single (p^[e] x) ((l ^ 2) ^ e) then ((l : K) ^ e)⁻¹ else 0 := by
  show (∑ e ∈ Finset.range (n.degree + 1),
      if n = Finsupp.single (p^[e] x) ((l ^ 2) ^ e) then ((l : K) ^ e)⁻¹ else 0) = _
  apply Finset.sum_subset (fun e he => by simp only [Finset.mem_range] at he ⊢; omega)
  intro e _ hne
  rw [if_neg]
  intro h
  apply hne
  rw [Finset.mem_range]
  have hd := congrArg Finsupp.degree h
  rw [Finsupp.degree_single] at hd
  have := lt_sq_pow hl e
  omega

def genLogTrunc (l : ℕ) (p : τ → τ) (x : τ) (M : ℕ) : MvPowerSeries τ K :=
  ∑ e ∈ Finset.range M, ((l : K) ^ e)⁻¹ • (X (p^[e] x)) ^ ((l ^ 2) ^ e)

/- English proof (translation)
Simplify using `only [genLogTrunc, map_sum, MvPowerSeries.coeff_smul, MvPowerSeries.coeff_X_pow, mul_ite, mul_one, mul_zero]`.
-/
theorem coeff_genLogTrunc (l : ℕ) (p : τ → τ) (x : τ) (M : ℕ) (n : τ →₀ ℕ) :
    coeff n (genLogTrunc (K := K) l p x M) = ∑ e ∈ Finset.range M,
      if n = Finsupp.single (p^[e] x) ((l ^ 2) ^ e) then ((l : K) ^ e)⁻¹ else 0 := by
  simp only [genLogTrunc, map_sum, MvPowerSeries.coeff_smul, MvPowerSeries.coeff_X_pow, mul_ite, mul_one,
    mul_zero]

/- English proof (translation)
Introduce `d hd`. Rewrite using `[map_sub, coeff_genLog hl p x d hd, coeff_genLogTrunc, sub_self]`.
-/
theorem low_genLog_sub {l : ℕ} (hl : 2 ≤ l) (p : τ → τ) (x : τ) (M : ℕ) :
    Low M (genLog (K := K) l p x - genLogTrunc l p x M) := by
  intro d hd
  rw [map_sub, coeff_genLog hl p x d hd, coeff_genLogTrunc, sub_self]

/- English proof (translation)
Rewrite using `[← MvPowerSeries.coe_substAlgHom hs]`. Simplify using `only [genLogTrunc, map_sum, map_smul, map_pow, MvPowerSeries.coe_substAlgHom, MvPowerSeries.subst_X hs]`.
-/
theorem subst_genLogTrunc [Finite τ] {g : τ → MvPowerSeries τ K} (hs : HasSubst g) (l : ℕ)
    (p : τ → τ) (x : τ) (M : ℕ) :
    subst g (genLogTrunc (K := K) l p x M) =
      ∑ e ∈ Finset.range M, ((l : K) ^ e)⁻¹ • (g (p^[e] x)) ^ ((l ^ 2) ^ e) := by
  rw [← MvPowerSeries.coe_substAlgHom hs]
  simp only [genLogTrunc, map_sum, map_smul, map_pow, MvPowerSeries.coe_substAlgHom, MvPowerSeries.subst_X hs]

/- English proof (translation)
Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => intro n hn`. Use linear arithmetic over natural numbers and integers. Consider the case `succ m ih`.

Introduce `n hn`. Rewrite using `[pow_succ', MvPowerSeries.coeff_mul]`. Use `Finset.sum_eq_zero fun ab hab => ?_` and prove the remaining obligations. Use `replace hab : ab.1 + ab.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.1 hab`. Distinguish the cases in `ha : ab.1 = 0`.

Rewrite using `[ha, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h0, zero_mul]`. Establish `hdeg : ab.1.degree + ab.2.degree = n.degree` using `by rw [← hab, map_add]`. Establish `hpos : 0 < ab.1.degree`. Break down `Nat.eq_zero_or_pos ab.1.degree with h' | h'` into its components or cases. Conclude with `absurd ((Finsupp.degree_eq_zero_iff _).1 h') ha`.

Conclude with `h'`. Rewrite using `[ih ab.2 (by omega), mul_zero]`.
-/
private theorem coeff_pow_eq_zero_of_degree_lt' {h : MvPowerSeries τ K} (h0 : constantCoeff h = 0) :
    ∀ (m : ℕ) (n : τ →₀ ℕ), n.degree < m → coeff n (h ^ m) = 0 := by
  intro m
  induction m with
  | zero => intro n hn; omega
  | succ m ih =>
    intro n hn
    rw [pow_succ', MvPowerSeries.coeff_mul]
    refine Finset.sum_eq_zero fun ab hab => ?_
    replace hab : ab.1 + ab.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.1 hab
    by_cases ha : ab.1 = 0
    · rw [ha, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h0, zero_mul]
    · have hdeg : ab.1.degree + ab.2.degree = n.degree := by rw [← hab, map_add]
      have hpos : 0 < ab.1.degree := by
        rcases Nat.eq_zero_or_pos ab.1.degree with h' | h'
        · exact absurd ((Finsupp.degree_eq_zero_iff _).1 h') ha
        · exact h'
      rw [ih ab.2 (by omega), mul_zero]

/- English proof (translation)
Establish `hs : HasSubst g` using `by first`. Consider the case `exact hasSubst_of_constantCoeff_zero hg0`. Consider the case `exact HasSubst.of_constantCoeff_nilpotent (fun s => by rw [hg0 s]; exact IsNilpotent.zero)`. Establish `hcoef` using `congrArg (coeff n) hx`. Rewrite `hcoef` using `[coeff_subst hs]`.

Rewrite using `[← hcoef]`. Use `set D : ℕ → τ →₀ ℕ := fun e => Finsupp.single (p^[e] x) ((l ^ 2) ^ e) with hDdef`. Establish `hDdeg : ∀ e, (D e).degree = (l ^ 2) ^ e` using `fun e => by simp [hDdef, Finsupp.degree_single]`. Establish `hD_inj : ∀ e e', D e = D e' → e = e'`. Introduce `e e' h`.

Establish `h'` using `congrArg Finsupp.degree h`. Rewrite `h'` using `[hDdeg, hDdeg]`. Conclude with `Nat.pow_right_injective (by nlinarith) h'`. Establish `hcD : ∀ e, coeff (D e) (genLog (K` using `K) l p x) = ((l : K) ^ e)⁻¹ := by`. Introduce `e`.

Rewrite using `[coeff_genLog hl p x (D e) (M := (l ^ 2) ^ e + 1) (by rw [hDdeg]; omega)]`. Rewrite using `[Finset.sum_eq_single e]`. Rewrite using `[if_pos rfl]`. Introduce `e' _ hne`. Rewrite using `[if_neg]`.

Introduce `h`. Conclude with `hne (hD_inj e e' h).symm`. Introduce `he`. It suffices to derive a contradiction. Apply `he` to reduce the goal to its premises.

Rewrite using `[Finset.mem_range]`. Use `lt_sq_pow hl e` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite using `[finsum_eq_sum_of_support_subset _ (s := (Finset.range (n.degree + 1)).image D) ?_]`. Rewrite using `[Finset.sum_image (fun e _ e' _ h => hD_inj e e' h)]`.

Use `Finset.sum_congr rfl fun e _ => ?_` and prove the remaining obligations. Rewrite using `[hcD, smul_eq_mul, hDdef]`. Simplify using `only`. Rewrite using `[Finsupp.prod_single_index (h := fun s e => g s ^ e) (pow_zero _)]`. Introduce `d hd`.

Rewrite `hd` using `[Function.mem_support, smul_eq_mul]`. Establish `h1 : coeff d (genLog (K` using `K) l p x) ≠ 0 := left_ne_zero_of_mul hd`. Establish `h2` using `right_ne_zero_of_mul hd`. Establish `h1' : (∑ e ∈ Finset.range (d.degree + 1), if d = Finsupp.single (p^[e] x) ((l ^ 2) ^ e) then ((l : K) ^ e)⁻¹ else 0) ≠ 0` using `h1`. Take `⟨e, _, he⟩` from `Finset.exists_ne_zero_of_sum_ne_zero h1'`.

Establish `hde : d = D e`. Assume the negation of the conclusion as `hc`. Conclude with `he (if_neg hc)`. Rewrite `h2` using `[hde, hDdef]`. Simplify using `only at h2`.

Rewrite `h2` using `[Finsupp.prod_single_index (h := fun s e => g s ^ e) (pow_zero _)]`. Establish `hle : ¬ n.degree < (l ^ 2) ^ e` using `fun hlt => h2 (coeff_pow_eq_zero_of_degree_lt' (hg0 _) _ n hlt)`. Use `lt_sq_pow hl e` as an intermediate fact. Rewrite using `[Finset.coe_image]`. Conclude with `⟨e, by simp only [Finset.coe_range, Set.mem_Iio]; omega, hde.symm⟩`.
-/
theorem coeff_X_eq_sum [Finite τ] {l : ℕ} (hl : 2 ≤ l) (p : τ → τ) {g : τ → MvPowerSeries τ K}
    (hg0 : ∀ x, constantCoeff (g x) = 0) (x : τ)
    (hx : subst g (genLog (K := K) l p x) = X x) (n : τ →₀ ℕ) :
    coeff n (X x : MvPowerSeries τ K) = ∑ e ∈ Finset.range (n.degree + 1),
      ((l : K) ^ e)⁻¹ * coeff n (g (p^[e] x) ^ ((l ^ 2) ^ e)) := by
  have hs : HasSubst g := by
    first
      | exact hasSubst_of_constantCoeff_zero hg0
      | exact HasSubst.of_constantCoeff_nilpotent (fun s => by rw [hg0 s]; exact IsNilpotent.zero)
  have hcoef := congrArg (coeff n) hx
  rw [coeff_subst hs] at hcoef
  rw [← hcoef]

  set D : ℕ → τ →₀ ℕ := fun e => Finsupp.single (p^[e] x) ((l ^ 2) ^ e) with hDdef
  have hDdeg : ∀ e, (D e).degree = (l ^ 2) ^ e := fun e => by simp [hDdef, Finsupp.degree_single]
  have hD_inj : ∀ e e', D e = D e' → e = e' := by
    intro e e' h
    have h' := congrArg Finsupp.degree h
    rw [hDdeg, hDdeg] at h'
    exact Nat.pow_right_injective (by nlinarith) h'
  have hcD : ∀ e, coeff (D e) (genLog (K := K) l p x) = ((l : K) ^ e)⁻¹ := by
    intro e
    rw [coeff_genLog hl p x (D e) (M := (l ^ 2) ^ e + 1) (by rw [hDdeg]; omega)]
    rw [Finset.sum_eq_single e]
    · rw [if_pos rfl]
    · intro e' _ hne
      rw [if_neg]
      intro h
      exact hne (hD_inj e e' h).symm
    · intro he
      exfalso
      apply he
      rw [Finset.mem_range]
      have := lt_sq_pow hl e
      omega
  rw [finsum_eq_sum_of_support_subset _ (s := (Finset.range (n.degree + 1)).image D) ?_]
  · rw [Finset.sum_image (fun e _ e' _ h => hD_inj e e' h)]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [hcD, smul_eq_mul, hDdef]
    simp only
    rw [Finsupp.prod_single_index (h := fun s e => g s ^ e) (pow_zero _)]
  · intro d hd
    rw [Function.mem_support, smul_eq_mul] at hd
    have h1 : coeff d (genLog (K := K) l p x) ≠ 0 := left_ne_zero_of_mul hd
    have h2 := right_ne_zero_of_mul hd
    have h1' : (∑ e ∈ Finset.range (d.degree + 1),
        if d = Finsupp.single (p^[e] x) ((l ^ 2) ^ e) then ((l : K) ^ e)⁻¹ else 0) ≠ 0 := h1
    obtain ⟨e, _, he⟩ := Finset.exists_ne_zero_of_sum_ne_zero h1'
    have hde : d = D e := by
      by_contra hc
      exact he (if_neg hc)
    rw [hde, hDdef] at h2
    simp only at h2
    rw [Finsupp.prod_single_index (h := fun s e => g s ^ e) (pow_zero _)] at h2
    have hle : ¬ n.degree < (l ^ 2) ^ e := fun hlt => h2 (coeff_pow_eq_zero_of_degree_lt' (hg0 _) _ n hlt)
    have := lt_sq_pow hl e
    rw [Finset.coe_image]
    exact ⟨e, by simp only [Finset.coe_range, Set.mem_Iio]; omega, hde.symm⟩

/- English proof (translation)
Establish `hl0 : 0 < l` using `by omega`. Use `⟨fun j => ?_, fun j i => ?_⟩` and prove the remaining obligations. Rewrite using `[← MvPowerSeries.coeff_zero_eq_constantCoeff_apply] show (∑ e ∈ Finset.range ((0 : τ →₀ ℕ).degree + 1), if (0 : τ →₀ ℕ) = Finsupp.single (p^[e] j) ((l ^ 2) ^ e) then ((l : K) ^ e)⁻¹ else 0) = 0`. Use `Finset.sum_eq_zero fun e _ => if_neg ?_` and prove the remaining obligations. Introduce `h`.

Establish `hd` using `congrArg Finsupp.degree h`. Rewrite `hd` using `[map_zero, Finsupp.degree_single]`. Use `pow_pos (pow_pos hl0 2) e` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Use `show (∑ e ∈ Finset.range ((Finsupp.single i 1 : τ →₀ ℕ).degree + 1), if Finsupp.single i 1 = Finsupp.single (p^[e] j) ((l ^ 2) ^ e) then ((l : K) ^ e)⁻¹ else 0) = _`.

Rewrite using `[Finsupp.degree_single, Finset.sum_range_succ, Finset.sum_range_one]`. Establish `h1 : ¬ Finsupp.single i 1 = Finsupp.single (p^[1] j) ((l ^ 2) ^ 1)`. Introduce `h`. Establish `hd` using `congrArg Finsupp.degree h`. Rewrite `hd` using `[Finsupp.degree_single, Finsupp.degree_single]`.

Use the polynomial consequences of the given equalities and inequalities. Rewrite using `[if_neg h1, add_zero]`. Simplify using `only [Function.iterate_zero, id, pow_zero, inv_one]`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[hij, Finsupp.single_left_inj one_ne_zero]`.
-/
theorem isIdMod2_genLog {l : ℕ} (hl : 2 ≤ l) (p : τ → τ) :
    Formalism.FG.IsIdMod2 (genLog (K := K) l p) := by
  have hl0 : 0 < l := by omega
  refine ⟨fun j => ?_, fun j i => ?_⟩
  · rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    show (∑ e ∈ Finset.range ((0 : τ →₀ ℕ).degree + 1),
      if (0 : τ →₀ ℕ) = Finsupp.single (p^[e] j) ((l ^ 2) ^ e) then ((l : K) ^ e)⁻¹ else 0) = 0
    refine Finset.sum_eq_zero fun e _ => if_neg ?_
    intro h
    have hd := congrArg Finsupp.degree h
    rw [map_zero, Finsupp.degree_single] at hd
    have := pow_pos (pow_pos hl0 2) e
    omega
  · show (∑ e ∈ Finset.range ((Finsupp.single i 1 : τ →₀ ℕ).degree + 1),
      if Finsupp.single i 1 = Finsupp.single (p^[e] j) ((l ^ 2) ^ e) then ((l : K) ^ e)⁻¹ else 0) = _
    rw [Finsupp.degree_single, Finset.sum_range_succ, Finset.sum_range_one]
    have h1 : ¬ Finsupp.single i 1 = Finsupp.single (p^[1] j) ((l ^ 2) ^ 1) := by
      intro h
      have hd := congrArg Finsupp.degree h
      rw [Finsupp.degree_single, Finsupp.degree_single] at hd
      nlinarith
    rw [if_neg h1, add_zero]
    simp only [Function.iterate_zero, id, pow_zero, inv_one]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij, Finsupp.single_left_inj one_ne_zero]

end Shift

/- English proof (translation)
Proceed by induction on `e with`. Consider the case `zero => simp`. Consider the case `succ e ih`. Rewrite using `[Function.iterate_succ_apply', ih]`. Use `Prod.ext rfl ?_` and prove the remaining obligations.

Simplify using `only`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem iter_letter {d : ℕ} (x : V2 d) (e : ℕ) :
    (fun y : V2 d => (y.1, y.2 - 2))^[e] x = (x.1, x.2 - 2 * (e : ZMod d)) := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [Function.iterate_succ_apply', ih]
    refine Prod.ext rfl ?_
    simp only
    push_cast
    ring

/- English proof (translation)
Proceed by induction on `e with`. Consider the case `zero => simp`. Consider the case `succ e ih`. Rewrite using `[Function.iterate_succ_apply', ih]`. Use `Prod.ext ?_ rfl` and prove the remaining obligations.

Simplify using `only`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem iter_ent {d N0 N1 : ℕ} (x : ZV d N0 N1) (e : ℕ) :
    (fun y : ZV d N0 N1 => (y.1 - 2, y.2.1, y.2.2))^[e] x =
      (x.1 - 2 * (e : ZMod d), x.2.1, x.2.2) := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [Function.iterate_succ_apply', ih]
    refine Prod.ext ?_ rfl
    simp only
    push_cast
    ring

/- English proof (translation)
Introduce `K _ l d N0 N1`. Use `⟨fun x => ?_, fun x => ?_, fun x => ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `n`. Simplify using `only [letterLog, genLog, iter_letter]`. Use function extensionality and compare the values at `n`.

Simplify using `only [entLog, genLog, iter_ent]`. Use function extensionality and compare the values at `n`. Simplify using `only [oneLog, genLog, Function.iterate_id, id]`.
-/
theorem logarithm_weight_comparison : LogBridges.{u} := by
  intro K _ l d N0 N1
  refine ⟨fun x => ?_, fun x => ?_, fun x => ?_⟩
  · funext n
    simp only [letterLog, genLog, iter_letter]
  · funext n
    simp only [entLog, genLog, iter_ent]
  · funext n
    simp only [oneLog, genLog, Function.iterate_id, id]

/- English proof (translation)
Introduce `K _ _ l hl τ _ _ p`. Use `haveI := Fintype.ofFinite τ`. Establish `hf` using `isIdMod2_genLog (K := K) hl.two_le p`. Take `⟨g, hg0, hg⟩` from `Formalism.FG.solve_exists_vector K τ τ (genLog (K := K) l p) (fun j => X j) hf (fun j => constantCoeff_X j)`. Use `⟨g, hg0, hg, ?_⟩` and prove the remaining obligations.

Establish `hsg : HasSubst g` using `by first`. Consider the case `exact hasSubst_of_constantCoeff_zero hg0`. Consider the case `exact HasSubst.of_constantCoeff_zero' hg0`. Consider the case `exact HasSubst.of_constantCoeff_nilpotent (fun s => by rw [hg0 s]; exact IsNilpotent.zero)`. Establish `hsf : HasSubst (genLog (K` using `K) l p) := by first`.

Consider the case `exact hasSubst_of_constantCoeff_zero hf.1`. Consider the case `exact HasSubst.of_constantCoeff_zero' hf.1`. Consider the case `exact HasSubst.of_constantCoeff_nilpotent (fun s => by rw [hf.1 s]; exact IsNilpotent.zero)`. Establish `key` using `Formalism.FG.subst_injective_vector K τ τ (genLog (K := K) l p) (fun x => subst (genLog (K := K) l p) (g x)) X hf (fun x => constantCoeff_subst_eq_zero hsf hf.1 (hg0 x)) (fun x => constantCoeff_X x) (fun j => by`. Rewrite using `[← subst_comp_subst_apply hsg hsf, hg j, subst_X hsf, subst_self]`.

Use the proof step `rfl)`. Conclude with `fun x => congrFun key x`.
-/
theorem generalized_log_inverse : GenLogInverse.{u, v} := by
  intro K _ _ l hl τ _ _ p
  haveI := Fintype.ofFinite τ
  have hf := isIdMod2_genLog (K := K) hl.two_le p
  obtain ⟨g, hg0, hg⟩ := Formalism.FG.solve_exists_vector K τ τ (genLog (K := K) l p) (fun j => X j) hf
    (fun j => constantCoeff_X j)
  refine ⟨g, hg0, hg, ?_⟩
  have hsg : HasSubst g := by
    first
      | exact hasSubst_of_constantCoeff_zero hg0
      | exact HasSubst.of_constantCoeff_zero' hg0
      | exact HasSubst.of_constantCoeff_nilpotent (fun s => by rw [hg0 s]; exact IsNilpotent.zero)
  have hsf : HasSubst (genLog (K := K) l p) := by
    first
      | exact hasSubst_of_constantCoeff_zero hf.1
      | exact HasSubst.of_constantCoeff_zero' hf.1
      | exact HasSubst.of_constantCoeff_nilpotent (fun s => by rw [hf.1 s]; exact IsNilpotent.zero)

  have key := Formalism.FG.subst_injective_vector K τ τ (genLog (K := K) l p)
    (fun x => subst (genLog (K := K) l p) (g x)) X hf
    (fun x => constantCoeff_subst_eq_zero hsf hf.1 (hg0 x)) (fun x => constantCoeff_X x) (fun j => by
      rw [← subst_comp_subst_apply hsg hsf, hg j, subst_X hsf, subst_self]
      rfl)
  exact fun x => congrFun key x

/- English proof (translation)
Introduce `K _ _ _ l hl hπ τ _ _ p g hg0 hsub`. Establish `hl2` using `hl.two_le`. Establish `hπ0 : 0 < ‖(l : K)‖` using `norm_pos_iff.2 (Nat.cast_ne_zero.2 hl.ne_zero)`. Establish `hπ1 : ‖(l : K)‖ ≤ 1` using `hπ.le`. Establish `hg1 : ∀ z, Low 1 (g z)` using `fun z => (low_one_iff _).2 (hg0 z)`.

It suffices to establish `H : ∀ N, ∀ y, ∀ n : τ →₀ ℕ, n.degree = N → ‖coeff n (g y)‖ ≤ ‖(l : K)‖ ^ (rho l - (n.degree : ℝ) * rho l) by`. Introduce `x n`. Rewrite using `[monoWtGe_iff, dot_const]`. Conclude with `H _ x n rfl`. Introduce `N`.

Proceed by induction on `N using Nat.strong_induction_on with`. Consider the case `_ N ih`. Introduce `y n hn`. Establish `hw : ∀ z, WtGe ‖(l : K)‖ (fun _ => rho l) (rho l) (truncBelow N (g z))`. Introduce `z m`.

Rewrite using `[monoWtGe_iff, dot_const, coeff_truncBelow]`. Use `split_ifs with hm`. Conclude with `ih _ hm z m rfl`. Simplify using `using Real.rpow_nonneg hπ0.le _`. Establish `hlow : ∀ z, Low N (g z - truncBelow N (g z))`.

Introduce `z m hm`. Rewrite using `[map_sub, coeff_truncBelow, if_pos hm, sub_self]`. Establish `htr1 : ∀ z, Low 1 (truncBelow N (g z))`. Introduce `z m hm`. Rewrite using `[coeff_truncBelow]`.

Use `split_ifs`. Conclude with `hg1 z m hm`. Both sides reduce to the same expression. Establish `hpow : ∀ z k, Low (N + k) (g z ^ (k + 1) - truncBelow N (g z) ^ (k + 1))`. Introduce `z k`.

Proceed by induction on `k with`. Consider the case `zero => simpa using hlow z`. Consider the case `succ k ihk`. Establish `e : g z ^ (k + 1 + 1) - truncBelow N (g z) ^ (k + 1 + 1) = (g z ^ (k + 1) - truncBelow N (g z) ^ (k + 1)) * g z + truncBelow N (g z) ^ (k + 1) * (g z - truncBelow N (g z))` using `by ring`. Rewrite using `[e]`.

Conclude with `low_add (low_mono (le_of_eq (by omega)) (low_mul ihk (hg1 z))) (low_mono (le_of_eq (by omega)) (low_mul (low_pow (htr1 z) (k + 1)) (hlow z)))`. Establish `key` using `coeff_X_eq_sum hl2 p hg0 y (hsub y) n`. Rewrite `key` using `[Finset.sum_range_succ']`. Simplify using `only [pow_zero, inv_one, one_mul, pow_one, Function.iterate_zero, id_eq] at key`. Establish `hc : coeff n (g y) = coeff n (X y : MvPowerSeries τ K) + -∑ e ∈ Finset.range n.degree, ((l : K) ^ (e + 1))⁻¹ * coeff n (g (p^[e + 1] y) ^ ((l ^ 2) ^ (e + 1)))`.

Rewrite using `[key]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hc]`. Use `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)` and prove the remaining obligations. Rewrite using `[coeff_X] split_ifs with h`.

Substitute `h` using the available equality. Simplify using `[Finsupp.degree_single]`. Simplify using `using Real.rpow_nonneg hπ0.le _`. Rewrite using `[norm_neg]`. Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (Real.rpow_nonneg hπ0.le _) fun e _ => ?_` and prove the remaining obligations.

Use `set k := (l ^ 2) ^ (e + 1) with hk`. Establish `hk2 : 2 ≤ k` using `le_trans (by nlinarith) (Nat.le_self_pow (by omega) (l ^ 2))`. Establish `hce : coeff n (g (p^[e + 1] y) ^ k) = coeff n (truncBelow N (g (p^[e + 1] y)) ^ k)`. Use `hpow (p^[e + 1] y) (k - 1) n (by omega)` as an intermediate fact. Rewrite `this` using `[Nat.sub_add_cancel (by omega), map_sub, sub_eq_zero]`.

Conclude with `this`. Rewrite using `[hce, norm_mul, norm_inv, norm_pow]`. Establish `hb` using `wtGe_pow hπ0 (hw (p^[e + 1] y)) k n`. Rewrite `hb` using `[monoWtGe_iff, dot_const]`. Establish `hv` using `(padicValuationGain l hl).2 (e + 1)`.

Establish `hkr : ((k : ℕ) : ℝ) = ((l : ℝ) ^ 2) ^ (e + 1)` using `by rw [hk]; push_cast; ring`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Real.rpow_sub hπ0 ((k : ℝ) * rho l - (n.degree : ℝ) * rho l) ((e + 1 : ℕ) : ℝ), Real.rpow_natCast, div_eq_inv_mul]`. Use `_ ≤ ‖(l : K)‖ ^ (rho l - (n.degree : ℝ) * rho l) := by`. Apply `Real.rpow_le_rpow_of_exponent_ge hπ0 hπ1` to reduce the goal to its premises.

Rewrite using `[hkr]`. Move the coercions through the operations in `at hv ⊢`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem generalized_log_weight : GenLogWeight.{u, v} := by
  intro K _ _ _ l hl hπ τ _ _ p g hg0 hsub
  have hl2 := hl.two_le
  have hπ0 : 0 < ‖(l : K)‖ := norm_pos_iff.2 (Nat.cast_ne_zero.2 hl.ne_zero)
  have hπ1 : ‖(l : K)‖ ≤ 1 := hπ.le
  have hg1 : ∀ z, Low 1 (g z) := fun z => (low_one_iff _).2 (hg0 z)
  suffices H : ∀ N, ∀ y, ∀ n : τ →₀ ℕ, n.degree = N →
      ‖coeff n (g y)‖ ≤ ‖(l : K)‖ ^ (rho l - (n.degree : ℝ) * rho l) by
    intro x n
    rw [monoWtGe_iff, dot_const]
    exact H _ x n rfl
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro y n hn
  have hw : ∀ z, WtGe ‖(l : K)‖ (fun _ => rho l) (rho l) (truncBelow N (g z)) := by
    intro z m
    rw [monoWtGe_iff, dot_const, coeff_truncBelow]
    split_ifs with hm
    · exact ih _ hm z m rfl
    · simpa using Real.rpow_nonneg hπ0.le _
  have hlow : ∀ z, Low N (g z - truncBelow N (g z)) := by
    intro z m hm
    rw [map_sub, coeff_truncBelow, if_pos hm, sub_self]
  have htr1 : ∀ z, Low 1 (truncBelow N (g z)) := by
    intro z m hm
    rw [coeff_truncBelow]
    split_ifs
    · exact hg1 z m hm
    · rfl
  have hpow : ∀ z k, Low (N + k) (g z ^ (k + 1) - truncBelow N (g z) ^ (k + 1)) := by
    intro z k
    induction k with
    | zero => simpa using hlow z
    | succ k ihk =>
      have e : g z ^ (k + 1 + 1) - truncBelow N (g z) ^ (k + 1 + 1) =
          (g z ^ (k + 1) - truncBelow N (g z) ^ (k + 1)) * g z +
            truncBelow N (g z) ^ (k + 1) * (g z - truncBelow N (g z)) := by ring
      rw [e]
      exact low_add (low_mono (le_of_eq (by omega)) (low_mul ihk (hg1 z)))
        (low_mono (le_of_eq (by omega)) (low_mul (low_pow (htr1 z) (k + 1)) (hlow z)))
  have key := coeff_X_eq_sum hl2 p hg0 y (hsub y) n
  rw [Finset.sum_range_succ'] at key
  simp only [pow_zero, inv_one, one_mul, pow_one, Function.iterate_zero, id_eq] at key
  have hc : coeff n (g y) = coeff n (X y : MvPowerSeries τ K) + -∑ e ∈ Finset.range n.degree,
      ((l : K) ^ (e + 1))⁻¹ * coeff n (g (p^[e + 1] y) ^ ((l ^ 2) ^ (e + 1))) := by
    rw [key]; ring
  rw [hc]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [coeff_X]
    split_ifs with h
    · subst h
      simp [Finsupp.degree_single]
    · simpa using Real.rpow_nonneg hπ0.le _
  · rw [norm_neg]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (Real.rpow_nonneg hπ0.le _)
      fun e _ => ?_
    set k := (l ^ 2) ^ (e + 1) with hk
    have hk2 : 2 ≤ k := le_trans (by nlinarith) (Nat.le_self_pow (by omega) (l ^ 2))
    have hce : coeff n (g (p^[e + 1] y) ^ k) = coeff n (truncBelow N (g (p^[e + 1] y)) ^ k) := by
      have := hpow (p^[e + 1] y) (k - 1) n (by omega)
      rw [Nat.sub_add_cancel (by omega), map_sub, sub_eq_zero] at this
      exact this
    rw [hce, norm_mul, norm_inv, norm_pow]
    have hb := wtGe_pow hπ0 (hw (p^[e + 1] y)) k n
    rw [monoWtGe_iff, dot_const] at hb
    have hv := (padicValuationGain l hl).2 (e + 1)
    have hkr : ((k : ℕ) : ℝ) = ((l : ℝ) ^ 2) ^ (e + 1) := by rw [hk]; push_cast; ring
    calc (‖(l : K)‖ ^ (e + 1))⁻¹ * ‖coeff n (truncBelow N (g (p^[e + 1] y)) ^ k)‖
        ≤ (‖(l : K)‖ ^ (e + 1))⁻¹ * ‖(l : K)‖ ^ ((k : ℝ) * rho l - (n.degree : ℝ) * rho l) :=
          mul_le_mul_of_nonneg_left hb (inv_nonneg.2 (pow_nonneg hπ0.le _))
      _ = ‖(l : K)‖ ^ ((k : ℝ) * rho l - (n.degree : ℝ) * rho l - ((e + 1 : ℕ) : ℝ)) := by
          rw [Real.rpow_sub hπ0 ((k : ℝ) * rho l - (n.degree : ℝ) * rho l) ((e + 1 : ℕ) : ℝ),
            Real.rpow_natCast, div_eq_inv_mul]
      _ ≤ ‖(l : K)‖ ^ (rho l - (n.degree : ℝ) * rho l) := by
          apply Real.rpow_le_rpow_of_exponent_ge hπ0 hπ1
          rw [hkr]
          push_cast at hv ⊢
          linarith

end Formalism.DworkPowerSeriesWeights
