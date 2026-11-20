import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FontaineThetaEqZeroIffFontaineXiElementDvd
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

noncomputable section
namespace GlobalTheory.MemLoc.KerAll
open Ideal

/- English proof (translation)
Set `g : {z // P z} → A × {z // P z}` to `fun z => ((h z.1 z.2).choose, ⟨(h z.1 z.2).choose_spec.choose, (h z.1 z.2).choose_spec.choose_spec.2⟩)`. Establish `hg : ∀ z : {z // P z}, z.1 = a * (g z).1 + q * (g z).2.1` using `fun z => (h z.1 z.2).choose_spec.choose_spec.1`. Set `xs : ℕ → {z // P z}` to `fun n => Nat.rec ⟨x, hx⟩ (fun _ z => (g z).2) n`. Establish `hxs : ∀ n, xs (n + 1) = (g (xs n)).2` using `fun n => rfl`. Set `S : ℕ → A` to `fun n => ∑ k ∈ Finset.range n, q ^ k * (g (xs k)).1`.

Establish `hS : ∀ n, S (n + 1) = S n + q ^ n * (g (xs n)).1` using `fun n => Finset.sum_range_succ _ _`. Establish `hY : ∀ n, x = a * S n + q ^ n * (xs n).1`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => simp [S, xs]`.

Consider the case `succ n ih`. Rewrite using `[hS, hxs]`. Take the linear combination `ih + q ^ n * hg (xs n)`. Establish `hC : ∀ m n, m ≤ n → S n - S m ∈ span {q ^ m}`. Introduce `m n hmn`.

Proceed by induction on `n, hmn using Nat.le_induction with`. Consider the case `base => simp`. Consider the case `succ n hmn ih`. Rewrite using `[hS, show S n + q ^ n * (g (xs n)).1 - S m = (S n - S m) + q ^ n * (g (xs n)).1 by ring]`. Use `add_mem ih (mem_span_singleton.2 (Dvd.dvd.mul_right (pow_dvd_pow q hmn) _))` and prove the remaining obligations.

Take `⟨L, hL⟩` from `(inferInstance : IsPrecomplete (span {q}) A).prec' S (by`. Introduce `m n hmn`. Simplify using `only [Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top, SModEq.sub_mem]`. Rewrite using `[← neg_sub]`. Conclude with `neg_mem (hC m n hmn))`.

Establish `hxL : x - a * L = 0`. Use `(inferInstance : IsHausdorff (span {q}) A).haus' _ (fun n => ?_)` and prove the remaining obligations. Establish `hn` using `hL n`. Simplify using `only [Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top, SModEq.sub_mem] at hn ⊢`. Rewrite using `[sub_zero, show x - a * L = a * (S n - L) + q ^ n * (xs n).1 by`.

Take the linear combination `hY n]`. Conclude with `add_mem (mul_mem_left _ _ hn) (mul_mem_right _ _ (mem_span_singleton_self _))`. Conclude with `⟨L, sub_eq_zero.1 hxL⟩`.
-/
theorem dvd_of_step {A : Type*} [CommRing A] (q a : A)
    [IsAdicComplete (span {q}) A] (P : A → Prop)
    (h : ∀ x, P x → ∃ y x', x = a * y + q * x' ∧ P x') (x : A) (hx : P x) :
    a ∣ x := by
  classical
  let g : {z // P z} → A × {z // P z} := fun z =>
    ((h z.1 z.2).choose, ⟨(h z.1 z.2).choose_spec.choose, (h z.1 z.2).choose_spec.choose_spec.2⟩)
  have hg : ∀ z : {z // P z}, z.1 = a * (g z).1 + q * (g z).2.1 := fun z =>
    (h z.1 z.2).choose_spec.choose_spec.1
  let xs : ℕ → {z // P z} := fun n => Nat.rec ⟨x, hx⟩ (fun _ z => (g z).2) n
  have hxs : ∀ n, xs (n + 1) = (g (xs n)).2 := fun n => rfl
  let S : ℕ → A := fun n => ∑ k ∈ Finset.range n, q ^ k * (g (xs k)).1
  have hS : ∀ n, S (n + 1) = S n + q ^ n * (g (xs n)).1 := fun n => Finset.sum_range_succ _ _
  have hY : ∀ n, x = a * S n + q ^ n * (xs n).1 := by
    intro n
    induction n with
    | zero => simp [S, xs]
    | succ n ih =>
      rw [hS, hxs]
      linear_combination ih + q ^ n * hg (xs n)
  have hC : ∀ m n, m ≤ n → S n - S m ∈ span {q ^ m} := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      rw [hS, show S n + q ^ n * (g (xs n)).1 - S m = (S n - S m) + q ^ n * (g (xs n)).1 by ring]
      refine add_mem ih (mem_span_singleton.2 (Dvd.dvd.mul_right (pow_dvd_pow q hmn) _))
  obtain ⟨L, hL⟩ := (inferInstance : IsPrecomplete (span {q}) A).prec' S (by
    intro m n hmn
    simp only [Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top, SModEq.sub_mem]
    rw [← neg_sub]
    exact neg_mem (hC m n hmn))
  have hxL : x - a * L = 0 := by
    refine (inferInstance : IsHausdorff (span {q}) A).haus' _ (fun n => ?_)
    have hn := hL n
    simp only [Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top, SModEq.sub_mem] at hn ⊢
    rw [sub_zero, show x - a * L = a * (S n - L) + q ^ n * (xs n).1 by
      linear_combination hY n]
    exact add_mem (mul_mem_left _ _ hn) (mul_mem_right _ _ (mem_span_singleton_self _))
  exact ⟨L, sub_eq_zero.1 hxL⟩

variable {l : ℕ} [hl : Fact l.Prime]

def rt (x : Per.Fl l) (n : ℕ) : Per.Fl l := ((frobeniusEquiv (Per.Fl l) l).symm)^[n] x

/- English proof (translation)
The claim follows from `Function.iterate_succ_apply' _ _ _`.
-/
theorem rt_succ (x : Per.Fl l) (n : ℕ) :
    rt x (n + 1) = (frobeniusEquiv (Per.Fl l) l).symm (rt x n) := Function.iterate_succ_apply' _ _ _

/- English proof (translation)
Rewrite using `[rt_succ, frobeniusEquiv_symm_pow_p]`.
-/
theorem rt_succ_pow (x : Per.Fl l) (n : ℕ) : rt x (n + 1) ^ l = rt x n := by
  rw [rt_succ, frobeniusEquiv_symm_pow_p]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp [rt]`. Consider the case `succ n ih => rw [pow_succ', pow_mul, rt_succ_pow, ih]`.
-/
theorem rt_pow (x : Per.Fl l) (n : ℕ) : rt x n ^ l ^ n = x := by
  induction n with
  | zero => simp [rt]
  | succ n ih => rw [pow_succ', pow_mul, rt_succ_pow, ih]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem rootT_eq (x : Per.Fl l) (n : ℕ) : rootT x n = (rt x n).untilt := rfl

/- English proof (translation)
Rewrite using `[rootT, PreTilt.mk_untilt_eq_coeff_zero]`. Use `PreTilt.coeff_iterate_frobeniusEquiv_symm 0 n x` as an intermediate fact. Rewrite `this` using `[zero_add]`. Conclude with `this`.
-/
theorem mk_rootT (x : Per.Fl l) (n : ℕ) :
    Ideal.Quotient.mk (span {(l : Per.OC l)}) (rootT x n) = PreTilt.coeff n x := by
  rw [rootT, PreTilt.mk_untilt_eq_coeff_zero]
  have := PreTilt.coeff_iterate_frobeniusEquiv_symm 0 n x
  rw [zero_add] at this
  exact this

/- English proof (translation)
Rewrite using `[rootT_eq, ← map_pow, rt_pow]`.
-/
theorem rootT_pow (x : Per.Fl l) (n : ℕ) : rootT x n ^ l ^ n = x.untilt := by
  rw [rootT_eq, ← map_pow, rt_pow]

/- English proof (translation)
Rewrite using `[rootT_eq, rootT_eq, ← map_pow, rt_succ_pow]`.
-/
theorem rootT_succ_pow (x : Per.Fl l) (n : ℕ) : rootT x (n + 1) ^ l = rootT x n := by
  rw [rootT_eq, rootT_eq, ← map_pow, rt_succ_pow]

/- English proof (translation)
Use `Perfection.ext fun n => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `PreTilt.coeff n x = PreTilt.coeff n 0`. Establish `: rootT x n = 0` using `pow_eq_zero_iff (pow_ne_zero n hl.out.ne_zero) |>.1 (by rw [rootT_pow, h])`. Rewrite using `[← mk_rootT, this, map_zero, map_zero]`.
-/
theorem eq_zero_of_untilt {x : Per.Fl l} (h : x.untilt = 0) : x = 0 := by
  refine Perfection.ext fun n => ?_
  change PreTilt.coeff n x = PreTilt.coeff n 0
  have : rootT x n = 0 := pow_eq_zero_iff (pow_ne_zero n hl.out.ne_zero) |>.1 (by rw [rootT_pow, h])
  rw [← mk_rootT, this, map_zero, map_zero]

def nm (x : Per.Fl l) : ℝ := ‖(x.untilt : ℂ_[l])‖

/- English proof (translation)
Simplify using `[nm]`.
-/
theorem nm_mul (x y : Per.Fl l) : nm (x * y) = nm x * nm y := by
  simp [nm]

/- English proof (translation)
Simplify using `[nm]`.
-/
theorem nm_pow (x : Per.Fl l) (n : ℕ) : nm (x ^ n) = nm x ^ n := by
  simp [nm]

/- English proof (translation)
The claim follows from `norm_nonneg _`.
-/
theorem nm_nonneg (x : Per.Fl l) : 0 ≤ nm x := norm_nonneg _

/- English proof (translation)
The claim follows from `(GlobalTheory.RingBasics.mem_OC _).1 x.untilt.2`.
-/
theorem nm_le (x : Per.Fl l) : nm x ≤ 1 := (GlobalTheory.RingBasics.mem_OC _).1 x.untilt.2

/- English proof (translation)
Use `norm_pos_iff.2 fun h0 => h (eq_zero_of_untilt (Subtype.ext h0))` and prove the remaining obligations.
-/
theorem nm_pos {x : Per.Fl l} (h : x ≠ 0) : 0 < nm x := by
  refine norm_pos_iff.2 fun h0 => h (eq_zero_of_untilt (Subtype.ext h0))

/- English proof (translation)
Establish `hsne : ∀ n, rootT x n ≠ 0`. Introduce `n h0`. Apply `hx` to reduce the goal to its premises. Apply `eq_zero_of_untilt` to reduce the goal to its premises. Rewrite using `[← rootT_pow x n, h0, zero_pow (pow_ne_zero _ hl.out.ne_zero)]`.

Establish `hdvd : ∀ n, rootT x n ∣ rootT c n`. Introduce `n`. Establish `h1 : ‖(rootT c n : ℂ_[l])‖ ^ l ^ n ≤ ‖(rootT x n : ℂ_[l])‖ ^ l ^ n`. Rewrite using `[← norm_pow, ← norm_pow]`. Establish `a` using `congrArg Subtype.val (rootT_pow c n)`.

Establish `b` using `congrArg Subtype.val (rootT_pow x n)`. Move the coercions through the operations in `at a b`. Rewrite using `[a, b]`. Conclude with `h`. Establish `h2` using `(pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) (pow_ne_zero n hl.out.ne_zero)).1 h1`.

Establish `hne : (rootT x n : ℂ_[l]) ≠ 0` using `fun h0 => hsne n (Subtype.ext h0)`. Use `⟨⟨(rootT c n : ℂ_[l]) / rootT x n, (GlobalTheory.RingBasics.mem_OC _).2 ?_⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Rewrite using `[norm_div, div_le_one (norm_pos_iff.2 hne)]` and apply the resulting hypothesis. Use `push_cast`. Clear the denominators using the available nonvanishing facts.

Use `choose e he using hdvd`. Establish `hcomp : ∀ n, e (n + 1) ^ l = e n`. Introduce `n`. Establish `h2` using `rootT_succ_pow c n`. Rewrite `h2` using `[he (n + 1), he n, mul_pow, rootT_succ_pow]`.

Conclude with `mul_left_cancel₀ (hsne n) h2`. Set `d : Per.Fl l` to `⟨fun n => Ideal.Quotient.mk _ (e n), fun n => by`. Simplify using `only [← map_pow, hcomp]⟩`. Use `⟨d, Perfection.ext fun n => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `PreTilt.coeff n c = PreTilt.coeff n (x * d)`.

Rewrite using `[map_mul, ← mk_rootT, ← mk_rootT, he n, map_mul]`. Both sides reduce to the same expression.
-/
theorem dvd_of_nm_le {x c : Per.Fl l} (hx : x ≠ 0) (h : nm c ≤ nm x) : x ∣ c := by
  have hsne : ∀ n, rootT x n ≠ 0 := by
    intro n h0
    apply hx
    apply eq_zero_of_untilt
    rw [← rootT_pow x n, h0, zero_pow (pow_ne_zero _ hl.out.ne_zero)]
  have hdvd : ∀ n, rootT x n ∣ rootT c n := by
    intro n
    have h1 : ‖(rootT c n : ℂ_[l])‖ ^ l ^ n ≤ ‖(rootT x n : ℂ_[l])‖ ^ l ^ n := by
      rw [← norm_pow, ← norm_pow]
      have a := congrArg Subtype.val (rootT_pow c n)
      have b := congrArg Subtype.val (rootT_pow x n)
      push_cast at a b
      rw [a, b]
      exact h
    have h2 := (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) (pow_ne_zero n hl.out.ne_zero)).1 h1
    have hne : (rootT x n : ℂ_[l]) ≠ 0 := fun h0 => hsne n (Subtype.ext h0)
    refine ⟨⟨(rootT c n : ℂ_[l]) / rootT x n, (GlobalTheory.RingBasics.mem_OC _).2 ?_⟩, Subtype.ext ?_⟩
    · rwa [norm_div, div_le_one (norm_pos_iff.2 hne)]
    · push_cast
      field_simp
  choose e he using hdvd
  have hcomp : ∀ n, e (n + 1) ^ l = e n := by
    intro n
    have h2 := rootT_succ_pow c n
    rw [he (n + 1), he n, mul_pow, rootT_succ_pow] at h2
    exact mul_left_cancel₀ (hsne n) h2
  let d : Per.Fl l := ⟨fun n => Ideal.Quotient.mk _ (e n), fun n => by
    simp only [← map_pow, hcomp]⟩
  refine ⟨d, Perfection.ext fun n => ?_⟩
  change PreTilt.coeff n c = PreTilt.coeff n (x * d)
  rw [map_mul, ← mk_rootT, ← mk_rootT, he n, map_mul]
  rfl

/- English proof (translation)
Use `dvd_of_nm_le hx ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hlt`. Use `push Not at hlt`. Establish `hp` using `nm_pos hx`. Establish `hr : 1 < nm c / nm x` using `(one_lt_div hp).2 hlt`.

Take `⟨n, hn⟩` from `pow_unbounded_of_one_lt (nm x)⁻¹ hr`. Take `⟨d, hd⟩` from `h n`. Establish `h1 : nm c * nm (rt x n) ≤ nm x`. Rewrite using `[← nm_mul, hd, nm_mul]`. Conclude with `mul_le_of_le_one_right hp.le (nm_le d)`.

Establish `h2` using `pow_le_pow_left₀ (mul_nonneg (nm_nonneg _) (nm_nonneg _)) h1 (l ^ n)`. Rewrite `h2` using `[mul_pow, ← nm_pow (rt x n), rt_pow]`. Establish `h3 : (nm c / nm x) ^ n ≤ (nm c / nm x) ^ l ^ n` using `pow_le_pow_right₀ hr.le (Nat.lt_pow_self hl.out.one_lt).le`. Establish `h4 : (nm c / nm x) ^ l ^ n ≤ (nm x)⁻¹`. Rewrite using `[div_pow, div_le_iff₀ (pow_pos hp _), inv_mul_eq_div, le_div_iff₀ hp]`.

Conclude with `h2`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem dvd_of_forall {x c : Per.Fl l} (hx : x ≠ 0) (h : ∀ n, x ∣ c * rt x n) : x ∣ c := by
  refine dvd_of_nm_le hx ?_
  by_contra hlt
  push Not at hlt
  have hp := nm_pos hx
  have hr : 1 < nm c / nm x := (one_lt_div hp).2 hlt
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (nm x)⁻¹ hr
  obtain ⟨d, hd⟩ := h n
  have h1 : nm c * nm (rt x n) ≤ nm x := by
    rw [← nm_mul, hd, nm_mul]
    exact mul_le_of_le_one_right hp.le (nm_le d)
  have h2 := pow_le_pow_left₀ (mul_nonneg (nm_nonneg _) (nm_nonneg _)) h1 (l ^ n)
  rw [mul_pow, ← nm_pow (rt x n), rt_pow] at h2
  have h3 : (nm c / nm x) ^ n ≤ (nm c / nm x) ^ l ^ n :=
    pow_le_pow_right₀ hr.le (Nat.lt_pow_self hl.out.one_lt).le
  have h4 : (nm c / nm x) ^ l ^ n ≤ (nm x)⁻¹ := by
    rw [div_pow, div_le_iff₀ (pow_pos hp _), inv_mul_eq_div, le_div_iff₀ hp]
    exact h2
  linarith

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => ext i`. Simplify using the standard rewrite rules. Consider the case `succ n ih`. Rewrite using `[Function.iterate_succ_apply', ih]`.

Use `WittVector.ext fun i => ?_` and prove the remaining obligations. Rewrite using `[GlobalTheory.RingBasics.φA_apply, WittVector.coeff_frobenius_charP]`. Simplify using `[WittVector.map_coeff, iterateFrobenius_def, pow_succ, pow_mul]`.
-/
theorem iter_eq (n : ℕ) (a : Per.Ainf l) :
    (Per.φA l)^[n] a = WittVector.map (iterateFrobenius (Per.Fl l) l n) a := by
  induction n with
  | zero => ext i; simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    refine WittVector.ext fun i => ?_
    rw [GlobalTheory.RingBasics.φA_apply, WittVector.coeff_frobenius_charP]
    simp [WittVector.map_coeff, iterateFrobenius_def, pow_succ, pow_mul]

def ph (n : ℕ) : Per.Ainf l →+* Per.Ainf l := WittVector.map (iterateFrobenius (Per.Fl l) l n)

/- English proof (translation)
Simplify using `[ph, WittVector.map_teichmuller, iterateFrobenius_def]`.
-/
theorem ph_tm (n : ℕ) (x : Per.Fl l) : ph n (Per.tm x) = Per.tm (x ^ l ^ n) := by
  simp [ph, WittVector.map_teichmuller, iterateFrobenius_def]

/- English proof (translation)
Assemble the required witnesses or components as `⟨WittVector.map_injective _ (bijective_iterateFrobenius (Per.Fl l) l n).1, WittVector.map_surjective _ (bijective_iterateFrobenius (Per.Fl l) l n).2⟩`.
-/
theorem ph_bij (n : ℕ) : Function.Bijective (ph (l := l) n) :=
  ⟨WittVector.map_injective _ (bijective_iterateFrobenius (Per.Fl l) l n).1,
   WittVector.map_surjective _ (bijective_iterateFrobenius (Per.Fl l) l n).2⟩

/- English proof (translation)
Rewrite using `[xi, rt_succ]`.
-/
theorem xi_rt (e : Per.Fl l) (n : ℕ) :
    xi (rt e n) = ∑ i ∈ Finset.range l, (Per.tm (rt e (n + 1))) ^ i := by
  rw [xi, rt_succ]

/- English proof (translation)
Rewrite using `[xi_rt, mu, mu, geom_sum_mul, ← map_pow, rt_succ_pow]`.
-/
theorem mu_rt (e : Per.Fl l) (n : ℕ) : mu (rt e n) = xi (rt e n) * mu (rt e (n + 1)) := by
  rw [xi_rt, mu, mu, geom_sum_mul, ← map_pow, rt_succ_pow]

/- English proof (translation)
Establish `: rt e (n + 1) ^ l ^ n = (frobeniusEquiv (Per.Fl l) l).symm e`. Rewrite using `[rt_succ, ← map_pow, rt_pow]`. Rewrite using `[xi_rt, xi, map_sum]`. Simplify using `only [map_pow (ph n), ph_tm, this]`.
-/
theorem ph_xi (e : Per.Fl l) (n : ℕ) : ph n (xi (rt e n)) = xi e := by
  have : rt e (n + 1) ^ l ^ n = (frobeniusEquiv (Per.Fl l) l).symm e := by
    rw [rt_succ, ← map_pow, rt_pow]
  rw [xi_rt, xi, map_sum]
  simp only [map_pow (ph n), ph_tm, this]

/- English proof (translation)
Take `⟨k, rfl⟩` from `Nat.exists_eq_add_of_le h`. Establish `: rt e (n + 1) ^ l ^ (n + 1 + k) = e ^ l ^ k`. Rewrite using `[pow_add, pow_mul, rt_pow]`. Rewrite using `[xi_rt, map_sum, map_sum]`. Simplify using `only [map_pow (ph _), ph_tm, this, map_pow (Per.θ l), WittVector.fontaineTheta_teichmuller, map_pow PreTilt.untilt, he]`.

Simplify using the standard rewrite rules.
-/
theorem th_ph_xi {e : Per.Fl l} (he : e.untilt = 1) {n m : ℕ} (h : n + 1 ≤ m) :
    Per.θ l (ph m (xi (rt e n))) = l := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  have : rt e (n + 1) ^ l ^ (n + 1 + k) = e ^ l ^ k := by
    rw [pow_add, pow_mul, rt_pow]
  rw [xi_rt, map_sum, map_sum]
  simp only [map_pow (ph _), ph_tm, this, map_pow (Per.θ l), WittVector.fontaineTheta_teichmuller,
    map_pow PreTilt.untilt, he]
  simp

/- English proof (translation)
Conclude with `hl.out.ne_zero` after adjusting the coercions.
-/
theorem l_ne : (l : Per.OC l) ≠ 0 := by exact_mod_cast hl.out.ne_zero

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => exact ⟨1, a, by simp [rt], by simp, by simp⟩`. Consider the case `succ n ih`. Take `⟨c, b, h1, h2, h3⟩` from `ih`. Establish `h4 : Per.θ l (ph n b) = 0`.

Use `ha n` as an intermediate fact. Rewrite `this` using `[h2, map_mul, map_mul]`. Conclude with `(mul_eq_zero.1 this).resolve_left (h3 n le_rfl)`. Take `⟨y, hy⟩` from `(theta_eq_zero_iff_xi_dvd l e he _).1 h4`. Take `⟨y, rfl⟩` from `(ph_bij n).2 y`.

Rewrite `hy` using `[← ph_xi e n, ← map_mul]`. Establish `hb` using `(ph_bij n).1 hy`. Use `⟨c * xi (rt e n), y, by rw [h1, mu_rt, mul_assoc], by rw [h2, hb, mul_assoc], fun m hm => ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, map_mul, th_ph_xi he.1 hm]`. Conclude with `mul_ne_zero (h3 m (by omega)) l_ne`.
-/
theorem factor {e : Per.Fl l} (he : IsEps e) {a : Per.Ainf l} (ha : ∀ n, Per.θ l (ph n a) = 0) (n : ℕ) :
    ∃ c b, mu e = c * mu (rt e n) ∧ a = c * b ∧ ∀ m, n ≤ m → Per.θ l (ph m c) ≠ 0 := by
  induction n with
  | zero => exact ⟨1, a, by simp [rt], by simp, by simp⟩
  | succ n ih =>
    obtain ⟨c, b, h1, h2, h3⟩ := ih
    have h4 : Per.θ l (ph n b) = 0 := by
      have := ha n
      rw [h2, map_mul, map_mul] at this
      exact (mul_eq_zero.1 this).resolve_left (h3 n le_rfl)
    obtain ⟨y, hy⟩ := (theta_eq_zero_iff_xi_dvd l e he _).1 h4
    obtain ⟨y, rfl⟩ := (ph_bij n).2 y
    rw [← ph_xi e n, ← map_mul] at hy
    have hb := (ph_bij n).1 hy
    refine ⟨c * xi (rt e n), y, by rw [h1, mu_rt, mul_assoc], by rw [h2, hb, mul_assoc], fun m hm => ?_⟩
    rw [map_mul, map_mul, th_ph_xi he.1 hm]
    exact mul_ne_zero (h3 m (by omega)) l_ne

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => rfl`. Consider the case `succ n ih => rw [rt_succ, rt_succ, ih, map_sub, map_one]`.
-/
theorem rt_sub_one (e : Per.Fl l) (n : ℕ) : rt (e - 1) n = rt e n - 1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [rt_succ, rt_succ, ih, map_sub, map_one]

/- English proof (translation)
Rewrite using `[mu, map_sub, map_one]`. Use `congr 1`.
-/
theorem cc_mu (e : Per.Fl l) : WittVector.constantCoeff (mu e) = e - 1 := by
  rw [mu, map_sub, map_one]
  congr 1

/- English proof (translation)
Establish `hne : e - 1 ≠ 0`. Introduce `h`. Apply `he.2` to reduce the goal to its premises. Rewrite using `[sub_eq_zero.1 h, map_one, map_one]`. Establish `hd : e - 1 ∣ WittVector.constantCoeff a`.

Use `dvd_of_forall hne fun n => ?_` and prove the remaining obligations. Take `⟨c, b, h1, h2, -⟩` from `factor he ha n`. Use `⟨WittVector.constantCoeff b, ?_⟩` and prove the remaining obligations. Establish `h3 : a * mu (rt e n) = mu e * b` using `by linear_combination mu (rt e n) * h2 - b * h1`. Establish `h4` using `congrArg WittVector.constantCoeff h3`.

Rewrite `h4` using `[map_mul, map_mul, cc_mu, cc_mu]`. Rewrite using `[rt_sub_one, h4]`. Take `⟨d, hd⟩` from `hd`. Establish `hm : a - mu e * Per.tm d ∈ span {(l : Per.Ainf l)}`. Rewrite using `[← WittVector.ker_constantCoeff, RingHom.mem_ker, map_sub, map_mul, cc_mu, hd, sub_eq_zero]`.

Conclude with `congrArg (fun w => (e - 1) * w) (WittVector.teichmuller_coeff_zero l d).symm`. Take `⟨z, hz⟩` from `mem_span_singleton'.1 hm`. Use `⟨Per.tm d, z, by linear_combination -hz, fun n => ?_⟩` and prove the remaining obligations. Establish `h0 : Per.θ l (ph n (mu e)) = 0`. Rewrite using `[mu, map_sub, map_sub, ph_tm, WittVector.fontaineTheta_teichmuller, map_pow, he.1]`.

Simplify using the standard rewrite rules. Use `congrArg (fun w => Per.θ l (ph n w)) hz` as an intermediate fact. Simplify using `only [map_mul, map_sub, map_natCast, h0, ha n, zero_mul, sub_zero] at this`. Conclude with `(mul_eq_zero.1 this).resolve_right l_ne`.
-/
theorem step {e : Per.Fl l} (he : IsEps e) (a : Per.Ainf l) (ha : ∀ n, Per.θ l (ph n a) = 0) :
    ∃ y a', a = mu e * y + (l : Per.Ainf l) * a' ∧ ∀ n, Per.θ l (ph n a') = 0 := by
  have hne : e - 1 ≠ 0 := by
    intro h
    apply he.2
    rw [sub_eq_zero.1 h, map_one, map_one]
  have hd : e - 1 ∣ WittVector.constantCoeff a := by
    refine dvd_of_forall hne fun n => ?_
    obtain ⟨c, b, h1, h2, -⟩ := factor he ha n
    refine ⟨WittVector.constantCoeff b, ?_⟩
    have h3 : a * mu (rt e n) = mu e * b := by linear_combination mu (rt e n) * h2 - b * h1
    have h4 := congrArg WittVector.constantCoeff h3
    rw [map_mul, map_mul, cc_mu, cc_mu] at h4
    rw [rt_sub_one, h4]
  obtain ⟨d, hd⟩ := hd
  have hm : a - mu e * Per.tm d ∈ span {(l : Per.Ainf l)} := by
    rw [← WittVector.ker_constantCoeff, RingHom.mem_ker, map_sub, map_mul, cc_mu, hd, sub_eq_zero]
    exact congrArg (fun w => (e - 1) * w) (WittVector.teichmuller_coeff_zero l d).symm
  obtain ⟨z, hz⟩ := mem_span_singleton'.1 hm
  refine ⟨Per.tm d, z, by linear_combination -hz, fun n => ?_⟩
  have h0 : Per.θ l (ph n (mu e)) = 0 := by
    rw [mu, map_sub, map_sub, ph_tm, WittVector.fontaineTheta_teichmuller, map_pow, he.1]
    simp
  have := congrArg (fun w => Per.θ l (ph n w)) hz
  simp only [map_mul, map_sub, map_natCast, h0, ha n, zero_mul, sub_zero] at this
  exact (mul_eq_zero.1 this).resolve_right l_ne

end GlobalTheory.MemLoc.KerAll

/- English proof (translation)
Introduce `l _ e he a ha`. Use `KerAll.dvd_of_step (l : Per.Ainf l) (mu e) (fun a => ∀ n, Per.θ l (KerAll.ph n a) = 0) (KerAll.step he) a fun n => ?_` and prove the remaining obligations. Use `ha n` as an intermediate fact. Rewrite `this` using `[KerAll.iter_eq]`. Then use the resulting hypothesis.
-/
theorem GlobalTheory.MemLoc.mu_dvd_of_theta_frob : ∀ (l : ℕ) [Fact l.Prime], ∀ e : Per.Fl l, IsEps e → ∀ a : Per.Ainf l, (∀ n : ℕ, Per.θ l ((Per.φA l)^[n] a) = 0) → mu e ∣ a := by
  intro l _ e he a ha
  refine KerAll.dvd_of_step (l : Per.Ainf l) (mu e) (fun a => ∀ n, Per.θ l (KerAll.ph n a) = 0)
    (KerAll.step he) a fun n => ?_
  have := ha n
  rwa [KerAll.iter_eq] at this
