import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.BiextensionRelation
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.HomotheticLatticeIntegralS2

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.D

open Formalism.InvariantFactorPaths.G7 (UnrOK)
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension omegaK)

namespace GaussNormEstimates

variable {l : ℕ} [hl : Fact l.Prime]

/- English proof (translation)
Rewrite using `[← norm_algebraMap' ℂ_[l] (a : ℚ_[l]), map_intCast]`.
-/
lemma normZ_eq (a : ℤ) : ‖(a : ℂ_[l])‖ = ‖(a : ℚ_[l])‖ := by
  rw [← norm_algebraMap' ℂ_[l] (a : ℚ_[l]), map_intCast]

/- English proof (translation)
Rewrite using `[normZ_eq]`. Conclude with `Padic.norm_int_le_one a`.
-/
lemma normZ_le (a : ℤ) : ‖(a : ℂ_[l])‖ ≤ 1 := by
  rw [normZ_eq]; exact Padic.norm_int_le_one a

/- English proof (translation)
Rewrite using `[normZ_eq]`. Conclude with `Padic.norm_intCast_lt_one_iff`.
-/
lemma normZ_lt {a : ℤ} : ‖(a : ℂ_[l])‖ < 1 ↔ (l : ℤ) ∣ a := by
  rw [normZ_eq]; exact Padic.norm_intCast_lt_one_iff

/- English proof (translation)
The claim follows from `le_antisymm (normZ_le a) (not_lt.1 fun h' => h (normZ_lt.1 h'))`.
-/
lemma normZ_one {a : ℤ} (h : ¬ (l : ℤ) ∣ a) : ‖(a : ℂ_[l])‖ = 1 :=
  le_antisymm (normZ_le a) (not_lt.1 fun h' => h (normZ_lt.1 h'))

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Establish `h1 : ‖(a - b) + b‖ ≤ max ‖a - b‖ ‖b‖` using `IsUltrametricDist.norm_add_le_max _ _`. Rewrite `h1` using `[sub_add_cancel]`. Conclude with `h1.trans (max_le h.le hb.le)`. Assume the negation of the conclusion as `hlt`.

Rewrite `hlt` using `[not_le]`. Establish `h1 : ‖a + -(a - b)‖ ≤ max ‖a‖ ‖-(a - b)‖` using `IsUltrametricDist.norm_add_le_max _ _`. Rewrite `h1` using `[norm_neg, ← sub_eq_add_neg, sub_sub_cancel, hb]`. Conclude with `absurd h1 (not_le.2 (max_lt hlt h))`.
-/
lemma norm_one_of_close {K : Type*} [NormedField K] [IsUltrametricDist K] {a b : K}
    (h : ‖a - b‖ < 1) (hb : ‖b‖ = 1) : ‖a‖ = 1 := by
  apply le_antisymm
  · have h1 : ‖(a - b) + b‖ ≤ max ‖a - b‖ ‖b‖ := IsUltrametricDist.norm_add_le_max _ _
    rw [sub_add_cancel] at h1
    exact h1.trans (max_le h.le hb.le)
  · by_contra hlt
    rw [not_le] at hlt
    have h1 : ‖a + -(a - b)‖ ≤ max ‖a‖ ‖-(a - b)‖ := IsUltrametricDist.norm_add_le_max _ _
    rw [norm_neg, ← sub_eq_add_neg, sub_sub_cancel, hb] at h1
    exact absurd h1 (not_le.2 (max_lt hlt h))

/- English proof (translation)
The claim follows from `Subfield.le_topologicalClosure _ (Subfield.subset_closure ⟨n, hn, hln, h⟩)`.
-/
lemma mu_mem_Kur {z : ℂ_[l]} {n : ℕ} (hn : 0 < n) (hln : ¬ l ∣ n) (h : z ^ n = 1) : z ∈ MaximalUnramifiedExtension l :=
  Subfield.le_topologicalClosure _ (Subfield.subset_closure ⟨n, hn, hln, h⟩)

/- English proof (translation)
The claim follows from `Subfield.isClosed_topologicalClosure _`.
-/
lemma isClosed_Kur : IsClosed (MaximalUnramifiedExtension l : Set ℂ_[l]) := Subfield.isClosed_topologicalClosure _

/- English proof (translation)
Introduce `h`. Use `Int.le_of_dvd (by norm_num) h` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
lemma two_not_dvd (h2 : 2 < l) : ¬ (l : ℤ) ∣ 2 := by
  intro h
  have := Int.le_of_dvd (by norm_num) h
  omega

/- English proof (translation)
Use `normZ_one (two_not_dvd h2)` as an intermediate fact. Simplify using `using this`.
-/
lemma norm_two (h2 : 2 < l) : ‖(2 : ℂ_[l])‖ = 1 := by
  have := normZ_one (two_not_dvd h2)
  simpa using this

/- English proof (translation)
Establish `hl2 : 2 ≤ l` using `hl.out.two_le`. Establish `hpos : 0 < l ^ 2 - 1`. Establish `: 2 ^ 2 ≤ l ^ 2` using `Nat.pow_le_pow_left hl2 2`. Use linear arithmetic over natural numbers and integers. Establish `hnd : ¬ l ∣ l ^ 2 - 1`.

Introduce `hd`. Establish `h1 : l ∣ l ^ 2` using `dvd_pow_self l (by norm_num)`. Establish `h2 : l ∣ 1`. Use `(Nat.dvd_sub h1 hd)` as an intermediate fact. Rewrite `this` using `[Nat.sub_sub_self (by omega)]`. Then use the resulting hypothesis.

Conclude with `hl.out.one_lt.ne' (Nat.dvd_one.1 h2)`. Take `⟨ζ, hζ⟩` from `kurRoots l (l ^ 2 - 1) hpos hnd`. Establish `hζ' : IsPrimitiveRoot ((MaximalUnramifiedExtension l).subtype ζ) (l ^ 2 - 1)` using `hζ.map_of_injective (MaximalUnramifiedExtension l).subtype.injective`. Establish `hprod` using `Polynomial.X_pow_sub_one_eq_prod hpos hζ'`. Establish `hev` using `congrArg (Polynomial.eval r) hprod`.

Simplify using `only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_prod, Polynomial.eval_C] at hev`. Assume the negation of the conclusion as `hcon`. Establish `hcon : ∀ η : ℂ_[l], η ^ (l ^ 2 - 1) = 1 → 1 ≤ ‖r - η‖`. Introduce `η h1`. Assume the negation of the conclusion as `h2`.

Conclude with `hcon ⟨η, h1, not_le.1 h2⟩`. Establish `h1 : (1 : ℝ) ≤ ‖∏ η ∈ Polynomial.nthRootsFinset (l ^ 2 - 1) (1 : ℂ_[l]), (r - η)‖`. Rewrite using `[norm_prod]`. Combine the equalities or inequalities in the displayed calculation. Rewrite `h1` using `[← hev]`.

Conclude with `absurd h (not_lt.2 h1)`.
-/
lemma exists_root_close (r : ℂ_[l]) (h : ‖r ^ (l ^ 2 - 1) - 1‖ < 1) :
    ∃ η : ℂ_[l], η ^ (l ^ 2 - 1) = 1 ∧ ‖r - η‖ < 1 := by
  have hl2 : 2 ≤ l := hl.out.two_le
  have hpos : 0 < l ^ 2 - 1 := by
    have : 2 ^ 2 ≤ l ^ 2 := Nat.pow_le_pow_left hl2 2
    omega
  have hnd : ¬ l ∣ l ^ 2 - 1 := by
    intro hd
    have h1 : l ∣ l ^ 2 := dvd_pow_self l (by norm_num)
    have h2 : l ∣ 1 := by
      have := (Nat.dvd_sub h1 hd)
      rwa [Nat.sub_sub_self (by omega)] at this
    exact hl.out.one_lt.ne' (Nat.dvd_one.1 h2)
  obtain ⟨ζ, hζ⟩ := kurRoots l (l ^ 2 - 1) hpos hnd
  have hζ' : IsPrimitiveRoot ((MaximalUnramifiedExtension l).subtype ζ) (l ^ 2 - 1) :=
    hζ.map_of_injective (MaximalUnramifiedExtension l).subtype.injective
  have hprod := Polynomial.X_pow_sub_one_eq_prod hpos hζ'
  have hev := congrArg (Polynomial.eval r) hprod
  simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one,
    Polynomial.eval_prod, Polynomial.eval_C] at hev
  by_contra hcon
  have hcon : ∀ η : ℂ_[l], η ^ (l ^ 2 - 1) = 1 → 1 ≤ ‖r - η‖ := by
    intro η h1
    by_contra h2
    exact hcon ⟨η, h1, not_le.1 h2⟩
  have h1 : (1 : ℝ) ≤ ‖∏ η ∈ Polynomial.nthRootsFinset (l ^ 2 - 1) (1 : ℂ_[l]), (r - η)‖ := by
    rw [norm_prod]
    calc (1 : ℝ) = ∏ _η ∈ Polynomial.nthRootsFinset (l ^ 2 - 1) (1 : ℂ_[l]), (1 : ℝ) := by simp
      _ ≤ _ := Finset.prod_le_prod (fun _ _ => zero_le_one) (fun η hη =>
          hcon η ((Polynomial.mem_nthRootsFinset hpos 1).1 hη))
  rw [← hev] at h1
  exact absurd h (not_lt.2 h1)

/- English proof (translation)
Establish `hr1 : ‖r‖ = 1`. Establish `h1 : ‖r‖ ^ 2 = 1` using `by rw [← norm_pow, hr, normZ_one hc]`. Conclude with `(pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 h1`. Choose the witnesses or unpack the hypotheses as in `⟨k, hk⟩ : ∃ k, l = 2 * k + 1 := by`. Break down `hl.out.eq_two_or_odd' with h | h` into its components or cases.

Use linear arithmetic over natural numbers and integers. Conclude with `h`. Establish `hexp : l ^ 2 - 1 = 2 * ((l - 1) * (k + 1))`. Establish `h1 : l - 1 = 2 * k` using `by omega`. Rewrite using `[h1]`.

Apply `Nat.sub_eq_of_eq_add` to reduce the goal to its premises. Rewrite using `[hk]`. Expand and normalize the polynomial expressions, which then agree. Establish `hc0 : (c : ZMod l) ≠ 0`. Rewrite using `[Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]`.

Conclude with `hc`. Establish `hdvd : (l : ℤ) ∣ c ^ ((l - 1) * (k + 1)) - 1`. Rewrite using `[← ZMod.intCast_zmod_eq_zero_iff_dvd]`. Use `push_cast`. Rewrite using `[pow_mul, ZMod.pow_card_sub_one_eq_one hc0, one_pow, sub_self]`.

Establish `hclose : ‖r ^ (l ^ 2 - 1) - 1‖ < 1`. Rewrite using `[hexp, pow_mul, hr]`. Use `normZ_lt.2 hdvd` as an intermediate fact. Move the coercions through the operations in `at this`. Conclude with `this`.

Take `⟨η, hη, hηr⟩` from `exists_root_close r hclose`. Establish `hpos : 0 < l ^ 2 - 1`. Rewrite using `[hexp]; have : 0 < l - 1 := by omega`. Check the signs of the components of the expression. Establish `hnd : ¬ l ∣ l ^ 2 - 1`.

Introduce `hd`. Establish `h1 : l ∣ l ^ 2` using `dvd_pow_self l (by norm_num)`. Establish `h2 : l ∣ 1`. Use `(Nat.dvd_sub h1 hd)` as an intermediate fact. Rewrite `this` using `[Nat.sub_sub_self (by omega)]`. Then use the resulting hypothesis.

Conclude with `hl.out.one_lt.ne' (Nat.dvd_one.1 h2)`. Establish `hηK : η ∈ MaximalUnramifiedExtension l` using `mu_mem_Kur hpos hnd hη`. Use `set δ : ℝ := ‖η - r‖ with hδ`. Establish `hδ1 : δ < 1` using `by rw [hδ, norm_sub_rev]; exact hηr`. Establish `hδ0 : 0 ≤ δ` using `norm_nonneg _`.

Establish `key : ∀ n : ℕ, ∃ x ∈ MaximalUnramifiedExtension l, ‖x - r‖ ≤ δ ^ (n + 1)`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => exact ⟨η, hηK, by simp [hδ]⟩`. Consider the case `succ n ih`.

Take `⟨x, hx, hxr⟩` from `ih`. Establish `hlt : ‖x - r‖ < 1` using `lt_of_le_of_lt hxr (pow_lt_one₀ hδ0 hδ1 (by omega))`. Establish `hx1 : ‖x‖ = 1` using `norm_one_of_close hlt hr1`. Establish `hx0 : x ≠ 0`. Introduce `h`.

Rewrite `hx1` using `[h, norm_zero]`. Conclude with `zero_ne_one hx1`. Establish `h20 : (2 : ℂ_[l]) ≠ 0` using `two_ne_zero`. Use `⟨(x ^ 2 + (c : ℂ_[l])) / (2 * x), ?_, ?_⟩` and prove the remaining obligations. Use `(MaximalUnramifiedExtension l).div_mem ((MaximalUnramifiedExtension l).add_mem ((MaximalUnramifiedExtension l).pow_mem hx 2) (intCast_mem _ c)) ((MaximalUnramifiedExtension l).mul_mem ?_ hx)` and prove the remaining obligations.

Conclude with `natCast_mem (MaximalUnramifiedExtension l) 2` after adjusting the coercions. Establish `he : (x ^ 2 + (c : ℂ_[l])) / (2 * x) - r = (x - r) ^ 2 / (2 * x)`. Rewrite using `[← hr]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[he, norm_div, norm_mul, norm_two h2, hx1, norm_pow]`. Simplify using `only [mul_one, div_one]`. Combine the equalities or inequalities in the displayed calculation. Use `mul_le_mul hxr ?_ (norm_nonneg _) (pow_nonneg hδ0 _)` and prove the remaining obligations. Use `hxr.trans ?_` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation. Use `_ = δ ^ (n + 1 + 1) := (pow_succ _ _).symm`. Establish `hcl : r ∈ closure (MaximalUnramifiedExtension l : Set ℂ_[l])`. Rewrite using `[Metric.mem_closure_iff]`. Introduce `ε hε`.

Take `⟨n, hn⟩` from `exists_pow_lt_of_lt_one hε hδ1`. Take `⟨x, hx, hxr⟩` from `key n`. Use `⟨x, hx, ?_⟩` and prove the remaining obligations. Rewrite using `[dist_comm, dist_eq_norm]`. Use `lt_of_le_of_lt hxr (lt_of_le_of_lt ?_ hn)` and prove the remaining obligations.

Conclude with `pow_le_pow_of_le_one hδ0 hδ1.le (by omega)`. Rewrite `hcl` using `[isClosed_Kur.closure_eq]`. Then use the resulting hypothesis.
-/
lemma sqrt_mem (h2 : 2 < l) (r : ℂ_[l]) (c : ℤ) (hr : r ^ 2 = (c : ℂ_[l])) (hc : ¬ (l : ℤ) ∣ c) :
    r ∈ MaximalUnramifiedExtension l := by
  have hr1 : ‖r‖ = 1 := by
    have h1 : ‖r‖ ^ 2 = 1 := by rw [← norm_pow, hr, normZ_one hc]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 h1
  obtain ⟨k, hk⟩ : ∃ k, l = 2 * k + 1 := by
    rcases hl.out.eq_two_or_odd' with h | h
    · omega
    · exact h
  have hexp : l ^ 2 - 1 = 2 * ((l - 1) * (k + 1)) := by
    have h1 : l - 1 = 2 * k := by omega
    rw [h1]
    apply Nat.sub_eq_of_eq_add
    rw [hk]; ring
  have hc0 : (c : ZMod l) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hc
  have hdvd : (l : ℤ) ∣ c ^ ((l - 1) * (k + 1)) - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [pow_mul, ZMod.pow_card_sub_one_eq_one hc0, one_pow, sub_self]
  have hclose : ‖r ^ (l ^ 2 - 1) - 1‖ < 1 := by
    rw [hexp, pow_mul, hr]
    have := normZ_lt.2 hdvd
    push_cast at this
    exact this
  obtain ⟨η, hη, hηr⟩ := exists_root_close r hclose
  have hpos : 0 < l ^ 2 - 1 := by
    rw [hexp]; have : 0 < l - 1 := by omega
    positivity
  have hnd : ¬ l ∣ l ^ 2 - 1 := by
    intro hd
    have h1 : l ∣ l ^ 2 := dvd_pow_self l (by norm_num)
    have h2 : l ∣ 1 := by
      have := (Nat.dvd_sub h1 hd)
      rwa [Nat.sub_sub_self (by omega)] at this
    exact hl.out.one_lt.ne' (Nat.dvd_one.1 h2)
  have hηK : η ∈ MaximalUnramifiedExtension l := mu_mem_Kur hpos hnd hη
  set δ : ℝ := ‖η - r‖ with hδ
  have hδ1 : δ < 1 := by rw [hδ, norm_sub_rev]; exact hηr
  have hδ0 : 0 ≤ δ := norm_nonneg _
  have key : ∀ n : ℕ, ∃ x ∈ MaximalUnramifiedExtension l, ‖x - r‖ ≤ δ ^ (n + 1) := by
    intro n
    induction n with
    | zero => exact ⟨η, hηK, by simp [hδ]⟩
    | succ n ih =>
      obtain ⟨x, hx, hxr⟩ := ih
      have hlt : ‖x - r‖ < 1 := lt_of_le_of_lt hxr (pow_lt_one₀ hδ0 hδ1 (by omega))
      have hx1 : ‖x‖ = 1 := norm_one_of_close hlt hr1
      have hx0 : x ≠ 0 := by
        intro h; rw [h, norm_zero] at hx1; exact zero_ne_one hx1
      have h20 : (2 : ℂ_[l]) ≠ 0 := two_ne_zero
      refine ⟨(x ^ 2 + (c : ℂ_[l])) / (2 * x), ?_, ?_⟩
      · refine (MaximalUnramifiedExtension l).div_mem ((MaximalUnramifiedExtension l).add_mem ((MaximalUnramifiedExtension l).pow_mem hx 2) (intCast_mem _ c))
          ((MaximalUnramifiedExtension l).mul_mem ?_ hx)
        exact_mod_cast natCast_mem (MaximalUnramifiedExtension l) 2
      · have he : (x ^ 2 + (c : ℂ_[l])) / (2 * x) - r = (x - r) ^ 2 / (2 * x) := by
          rw [← hr]; field_simp; ring
        rw [he, norm_div, norm_mul, norm_two h2, hx1, norm_pow]
        simp only [mul_one, div_one]
        calc ‖x - r‖ ^ 2 = ‖x - r‖ * ‖x - r‖ := sq _
          _ ≤ δ ^ (n + 1) * δ := by
              refine mul_le_mul hxr ?_ (norm_nonneg _) (pow_nonneg hδ0 _)
              refine hxr.trans ?_
              calc δ ^ (n + 1) ≤ δ ^ 1 := pow_le_pow_of_le_one hδ0 hδ1.le (by omega)
                _ = δ := pow_one δ
          _ = δ ^ (n + 1 + 1) := (pow_succ _ _).symm
  have hcl : r ∈ closure (MaximalUnramifiedExtension l : Set ℂ_[l]) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hδ1
    obtain ⟨x, hx, hxr⟩ := key n
    refine ⟨x, hx, ?_⟩
    rw [dist_comm, dist_eq_norm]
    refine lt_of_le_of_lt hxr (lt_of_le_of_lt ?_ hn)
    exact pow_le_pow_of_le_one hδ0 hδ1.le (by omega)
  rwa [isClosed_Kur.closure_eq] at hcl

def rt (dK : ℕ) : ℂ := Complex.I * ((Real.sqrt dK : ℝ) : ℂ)

/- English proof (translation)
Unfold `rt`. Rewrite using `[mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]`. Simplify using the standard rewrite rules.
-/
lemma rt_sq (dK : ℕ) : rt dK ^ 2 = -(dK : ℂ) := by
  unfold rt
  rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  simp

/- English proof (translation)
Unfold `omegaK rt`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma omega_eq (dK : ℕ) : 2 * omegaK dK - 1 = rt dK := by
  unfold omegaK rt; ring

/- English proof (translation)
Introduce `h`. Apply `hin` to reduce the goal to its premises. Use `⟨0, ?_⟩` and prove the remaining obligations. Use `(ZMod.intCast_zmod_eq_zero_iff_dvd _ l).2 h` as an intermediate fact. Move the coercions through the operations in `at this`.

Rewrite using `[this]`. Simplify using the standard rewrite rules.
-/
lemma not_dvd_of_inert {dK : ℕ} (hin : ¬ ∃ a : ZMod l, a ^ 2 = -(dK : ZMod l)) :
    ¬ (l : ℤ) ∣ -(dK : ℤ) := by
  intro h
  apply hin
  refine ⟨0, ?_⟩
  have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ l).2 h
  push_cast at this
  rw [this]; simp

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma normK (x : MaximalUnramifiedExtension l) : ‖x‖ = ‖(x : ℂ_[l])‖ := rfl

/- English proof (translation)
Rewrite using `[normK]`. Use `push_cast`. Conclude with `normZ_lt`.
-/
lemma normKZ_lt {a : ℤ} : ‖(a : MaximalUnramifiedExtension l)‖ < 1 ↔ (l : ℤ) ∣ a := by
  rw [normK]; push_cast; exact normZ_lt

/- English proof (translation)
Rewrite using `[normK]`. Use `push_cast`. Conclude with `normZ_one h`.
-/
lemma normKZ_one {a : ℤ} (h : ¬ (l : ℤ) ∣ a) : ‖(a : MaximalUnramifiedExtension l)‖ = 1 := by
  rw [normK]; push_cast; exact normZ_one h

/- English proof (translation)
Take `⟨-, h2, hnl, -, hfr⟩` from `hσ`. Establish `hc0 : (c : ZMod l) ≠ 0`. Introduce `h; exact hin ⟨0, by rw [h]; simp⟩`. Establish `hc : ¬ (l : ℤ) ∣ c`. Rewrite using `[← ZMod.intCast_zmod_eq_zero_iff_dvd]` and apply the resulting hypothesis.

Establish `hR1 : ‖R‖ = 1`. Establish `h1 : ‖R‖ ^ 2 = 1` using `by rw [← norm_pow, hR, normKZ_one hc]`. Conclude with `(pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 h1`. Establish `hs : σ R ^ 2 = R ^ 2` using `by rw [← map_pow, hR, map_intCast]`. Break down `sq_eq_sq_iff_eq_or_eq_neg.1 hs with h | h` into its components or cases.

It suffices to derive a contradiction. Establish `hodd : l = 2 * (l / 2) + 1`. Apply the tactic sequence `rcases hl.out.eq_two_or_odd with h' | h' <;> omega`. Establish `heul : (c : ZMod l) ^ (l / 2) = -1`. Break down `ZMod.pow_div_two_eq_neg_one_or_one l hc0 with h' | h'` into its components or cases.

It suffices to derive a contradiction. Take `⟨a, ha⟩` from `(ZMod.euler_criterion l hc0).2 h'`. Conclude with `hin ⟨a, by rw [ha, sq]⟩`. Conclude with `h'`. Establish `hN : (l : ℤ) ∣ c ^ (l / 2) + 1`.

Rewrite using `[← ZMod.intCast_zmod_eq_zero_iff_dvd]`. Use `push_cast`. Rewrite using `[heul]`. Expand and normalize the polynomial expressions, which then agree. Establish `hN2 : ¬ (l : ℤ) ∣ 2 - (c ^ (l / 2) + 1)`.

Introduce `hd`. Conclude with `two_not_dvd h2 (by simpa using dvd_add hd hN)`. Establish `hpow : R ^ l = R * ((c ^ (l / 2) : ℤ) : MaximalUnramifiedExtension l)`. Establish `h0 : R ^ l = R ^ (2 * (l / 2) + 1)` using `congrArg (fun n => R ^ n) hodd`. Rewrite using `[h0, pow_succ, pow_mul, hR]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `he : σ R - R ^ l = R * ((2 - (c ^ (l / 2) + 1) : ℤ) : MaximalUnramifiedExtension l)`. Rewrite using `[h, hpow]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `h3` using `hfr R hR1.le`. Rewrite `h3` using `[he, norm_mul, hR1, normKZ_one hN2, one_mul]`. Establish `h4 : ((l : ℝ))⁻¹ < 1` using `KF.l_inv_lt_one l`. Combine the linear equalities and inequalities to obtain the conclusion.

Conclude with `h`.
-/
lemma sigma_neg (σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l) (hσ : UnrOK (MaximalUnramifiedExtension l) l σ) (c : ℤ)
    (hin : ¬ ∃ a : ZMod l, a ^ 2 = (c : ZMod l)) (R : MaximalUnramifiedExtension l) (hR : R ^ 2 = (c : MaximalUnramifiedExtension l)) :
    σ R = -R := by
  obtain ⟨-, h2, hnl, -, hfr⟩ := hσ
  have hc0 : (c : ZMod l) ≠ 0 := by
    intro h; exact hin ⟨0, by rw [h]; simp⟩
  have hc : ¬ (l : ℤ) ∣ c := by
    rwa [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hR1 : ‖R‖ = 1 := by
    have h1 : ‖R‖ ^ 2 = 1 := by rw [← norm_pow, hR, normKZ_one hc]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 h1
  have hs : σ R ^ 2 = R ^ 2 := by rw [← map_pow, hR, map_intCast]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 hs with h | h
  · exfalso
    have hodd : l = 2 * (l / 2) + 1 := by
      rcases hl.out.eq_two_or_odd with h' | h' <;> omega
    have heul : (c : ZMod l) ^ (l / 2) = -1 := by
      rcases ZMod.pow_div_two_eq_neg_one_or_one l hc0 with h' | h'
      · exfalso
        obtain ⟨a, ha⟩ := (ZMod.euler_criterion l hc0).2 h'
        exact hin ⟨a, by rw [ha, sq]⟩
      · exact h'
    have hN : (l : ℤ) ∣ c ^ (l / 2) + 1 := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [heul]; ring
    have hN2 : ¬ (l : ℤ) ∣ 2 - (c ^ (l / 2) + 1) := by
      intro hd
      exact two_not_dvd h2 (by simpa using dvd_add hd hN)
    have hpow : R ^ l = R * ((c ^ (l / 2) : ℤ) : MaximalUnramifiedExtension l) := by
      have h0 : R ^ l = R ^ (2 * (l / 2) + 1) := congrArg (fun n => R ^ n) hodd
      rw [h0, pow_succ, pow_mul, hR]; push_cast; ring
    have he : σ R - R ^ l = R * ((2 - (c ^ (l / 2) + 1) : ℤ) : MaximalUnramifiedExtension l) := by
      rw [h, hpow]; push_cast; ring
    have h3 := hfr R hR1.le
    rw [he, norm_mul, hR1, normKZ_one hN2, one_mul] at h3
    have h4 : ((l : ℝ))⁻¹ < 1 := KF.l_inv_lt_one l
    linarith
  · exact h

end GaussNormEstimates

open GaussNormEstimates

/- English proof (translation)
Introduce `dK _ _ l _ h5 hin ι`. Establish `h2 : 2 < l` using `by omega`. Establish `hr : (ι (rt dK)) ^ 2 = ((-(dK : ℤ) : ℤ) : ℂ_[l])`. Rewrite using `[← map_pow, rt_sq]`. Simplify using the standard rewrite rules.

Establish `hmem : ι (rt dK) ∈ MaximalUnramifiedExtension l` using `sqrt_mem h2 _ _ hr (not_dvd_of_inert hin)`. Establish `hom : ι (omegaK dK) = (1 + ι (rt dK)) / 2`. Establish `h0 : 2 * ι (omegaK dK) - 1 = ι (rt dK)`. Rewrite using `[← omega_eq, map_sub, map_mul, map_ofNat, map_one]`. Rewrite using `[← h0]`.

Expand and normalize the polynomial expressions, which then agree. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hom]`. Use `(MaximalUnramifiedExtension l).div_mem ((MaximalUnramifiedExtension l).add_mem (MaximalUnramifiedExtension l).one_mem hmem) ?_` and prove the remaining obligations. Conclude with `natCast_mem (MaximalUnramifiedExtension l) 2` after adjusting the coercions.

Introduce `σ hσ w hw`. Establish `hR : (w + w - 1) ^ 2 = ((-(dK : ℤ) : ℤ) : MaximalUnramifiedExtension l)`. Apply `Subtype.ext` to reduce the goal to its premises. Use `push_cast`. Rewrite using `[hw, hom]`.

Use `hr` as an intermediate fact. Move the coercions through the operations in `at this`. Rewrite using `[← this]`. Expand and normalize the polynomial expressions, which then agree. Establish `hin' : ¬ ∃ a : ZMod l, a ^ 2 = ((-(dK : ℤ) : ℤ) : ZMod l)` using `by push_cast; exact hin`.

Establish `h` using `sigma_neg σ hσ _ hin' _ hR`. Simplify using `only [map_sub, map_add, map_one] at h`. Establish `h20 : (2 : MaximalUnramifiedExtension l) ≠ 0` using `two_ne_zero`. Apply `mul_left_cancel₀ h20` to reduce the goal to its premises. Take the linear combination `h`.
-/
theorem sqrt_in_unramified_completion : SqrtKur := by
  intro dK _ _ l _ h5 hin ι
  have h2 : 2 < l := by omega
  have hr : (ι (rt dK)) ^ 2 = ((-(dK : ℤ) : ℤ) : ℂ_[l]) := by
    rw [← map_pow, rt_sq]; simp
  have hmem : ι (rt dK) ∈ MaximalUnramifiedExtension l := sqrt_mem h2 _ _ hr (not_dvd_of_inert hin)
  have hom : ι (omegaK dK) = (1 + ι (rt dK)) / 2 := by
    have h0 : 2 * ι (omegaK dK) - 1 = ι (rt dK) := by
      rw [← omega_eq, map_sub, map_mul, map_ofNat, map_one]
    rw [← h0]; ring
  refine ⟨?_, ?_⟩
  · rw [hom]
    refine (MaximalUnramifiedExtension l).div_mem ((MaximalUnramifiedExtension l).add_mem (MaximalUnramifiedExtension l).one_mem hmem) ?_
    exact_mod_cast natCast_mem (MaximalUnramifiedExtension l) 2
  · intro σ hσ w hw
    have hR : (w + w - 1) ^ 2 = ((-(dK : ℤ) : ℤ) : MaximalUnramifiedExtension l) := by
      apply Subtype.ext
      push_cast
      rw [hw, hom]
      have := hr
      push_cast at this
      rw [← this]; ring
    have hin' : ¬ ∃ a : ZMod l, a ^ 2 = ((-(dK : ℤ) : ℤ) : ZMod l) := by
      push_cast; exact hin
    have h := sigma_neg σ hσ _ hin' _ hR
    simp only [map_sub, map_add, map_one] at h
    have h20 : (2 : MaximalUnramifiedExtension l) ≠ 0 := two_ne_zero
    apply mul_left_cancel₀ h20
    linear_combination h

/- English proof (translation)
Introduce `dK hsq h4 l _ h5 hin ι σ hσ α hα hfix ε hε`. Establish `h2 : 2 < l` using `by omega`. Take `⟨hwm, hws⟩` from `sqrt_in_unramified_completion dK hsq h4 l h5 hin ι`. Use `set w : MaximalUnramifiedExtension l := ⟨ι (omegaK dK), hwm⟩ with hwdef`. Establish `hw : σ w = 1 - w` using `hws σ hσ w rfl`.

Establish `hiso : ∀ a : MaximalUnramifiedExtension l, ‖σ a‖ = ‖a‖` using `sigmaIsom (MaximalUnramifiedExtension l) l σ hσ`. Establish `hR2 : (w + w - 1) ^ 2 = ((-(dK : ℤ) : ℤ) : MaximalUnramifiedExtension l)`. Apply `Subtype.ext` to reduce the goal to its premises. Use `push_cast`. Establish `h0 : ι (omegaK dK) + ι (omegaK dK) - 1 = ι (rt dK)`.

Rewrite using `[← omega_eq, map_sub, map_mul, map_ofNat, map_one]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hwdef]`. Simplify using `only`. Rewrite using `[h0, ← map_pow, rt_sq]`.

Simplify using the standard rewrite rules. Use `set R : MaximalUnramifiedExtension l := w + w - 1 with hRdef`. Establish `hσR : σ R = -R`. Rewrite using `[hRdef]`. Simplify using `only [map_sub, map_add, map_one, hw]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hR1 : ‖R‖ = 1`. Establish `h1 : ‖R‖ ^ 2 = 1` using `by rw [← norm_pow, hR2, normKZ_one (not_dvd_of_inert hin)]`. Conclude with `(pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 h1`. Establish `hR0 : R ≠ 0`.

Introduce `h`. Rewrite `hR1` using `[h, norm_zero]`. Conclude with `zero_ne_one hR1`. Establish `hn2 : ‖(2 : MaximalUnramifiedExtension l)‖ = 1`. Use `normKZ_one (l := l) (two_not_dvd h2)` as an intermediate fact.

Simplify using `using this`. Establish `hw1 : ‖w‖ ≤ 1`. Establish `h0 : w = (1 + R) / 2` using `by rw [hRdef]; ring`. Rewrite using `[h0, norm_div, hn2, div_one]`. Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le (by simp) hR1.le)`.

Use `set n0 : MaximalUnramifiedExtension l := (α - σ α) / R with hn0`. Use `set m0 : MaximalUnramifiedExtension l := α - n0 * w with hm0`. Establish `hn0R : n0 * R = α - σ α` using `by rw [hn0]; field_simp`. Establish `hσn0 : σ n0 = n0`. Rewrite using `[hn0, map_div₀, map_sub, hfix, hσR]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `hσm0 : σ m0 = m0`. Rewrite using `[hm0, map_sub, map_mul, hσn0, hw]`. Establish `: R = w + w - 1` using `hRdef`.

Rewrite `hn0R` using `[this]`. Take the linear combination `hn0R`. Establish `hn01 : ‖n0‖ ≤ 1`. Rewrite using `[hn0, norm_div, hR1, div_one, sub_eq_add_neg]`. Use `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le hα.le ?_)` and prove the remaining obligations.

Rewrite using `[norm_neg, hiso, hα]`. Establish `hm01 : ‖m0‖ ≤ 1`. Rewrite using `[hm0, sub_eq_add_neg]`. Use `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le hα.le ?_)` and prove the remaining obligations. Rewrite using `[norm_neg, norm_mul]`.

Conclude with `mul_le_one₀ hn01 (norm_nonneg _) hw1`. Take `⟨k, hk⟩` from `exists_pow_lt_of_lt_one (lt_min hε zero_lt_one) (KF.l_inv_lt_one l)`. Rewrite `hk` using `[inv_pow]`. Take `⟨m, hm⟩` from `fixedIsLimit (MaximalUnramifiedExtension l) l σ hσ m0 hm01 hσm0 k`. Take `⟨n, hn⟩` from `fixedIsLimit (MaximalUnramifiedExtension l) l σ hσ n0 hn01 hσn0 k`.

Use `set β : MaximalUnramifiedExtension l := (m : MaximalUnramifiedExtension l) + (n : MaximalUnramifiedExtension l) * w with hβ`. Establish `hβα : ‖β - α‖ ≤ ((l : ℝ) ^ k)⁻¹`. Establish `h0 : β - α = -(m0 - m) + -(n0 - n) * w` using `by rw [hβ, hm0]; ring`. Rewrite using `[h0]`. Use `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le (by rwa [norm_neg]) ?_)` and prove the remaining obligations.

Rewrite using `[norm_mul, norm_neg]`. Combine the equalities or inequalities in the displayed calculation. Establish `hβ1 : ‖β‖ = 1` using `norm_one_of_close (lt_of_le_of_lt hβα (lt_of_lt_of_le hk (min_le_right _ _))) hα`. Establish `hσβ : σ β = (m : MaximalUnramifiedExtension l) + (n : MaximalUnramifiedExtension l) * (1 - w)`. Rewrite using `[hβ, map_add, map_mul, map_natCast, map_natCast, hw]`.

Take `⟨q, hq⟩ : ∃ q : ℤ, (dK : ℤ) + 1 = 4 * q` from `⟨((dK : ℤ) + 1) / 4, by omega⟩`. Establish `hq' : ((dK : ℤ) + 1) / 4 = q` using `by omega`. Establish `hwq : w * (1 - w) = (q : MaximalUnramifiedExtension l)`. Establish `h40 : (4 : MaximalUnramifiedExtension l) ≠ 0` using `by norm_num`. Apply `mul_left_cancel₀ h40` to reduce the goal to its premises.

Establish `h1 : ((dK : MaximalUnramifiedExtension l)) + 1 = 4 * (q : MaximalUnramifiedExtension l)` using `by exact_mod_cast congrArg (fun z : ℤ => (z : MaximalUnramifiedExtension l)) hq`. Establish `h3` using `hR2`. Rewrite `h3` using `[hRdef]`. Move the coercions through the operations in `at h3`. Take the linear combination `(-1 : MaximalUnramifiedExtension l) * h3 + h1`.

Establish `hnorm : β * σ β = ((normInt dK m n : ℤ) : MaximalUnramifiedExtension l)`. Rewrite using `[hσβ, hβ]`. Unfold `normInt`. Rewrite using `[hq']`. Use `push_cast`.

Take the linear combination `((n : MaximalUnramifiedExtension l)) ^ 2 * hwq`. Use `⟨(m : ℤ), (n : ℤ), ?_, ?_⟩` and prove the remaining obligations. Introduce `hd`. Establish `h1` using `normKZ_lt.2 hd`. Rewrite `h1` using `[← hnorm, norm_mul, hiso, hβ1]`.

Evaluate the numerical expressions using `at h1`. Establish `h0 : ι (((m : ℤ) : ℂ) + ((n : ℤ) : ℂ) * omegaK dK) - (α : ℂ_[l]) = ((β - α : MaximalUnramifiedExtension l) : ℂ_[l])`. Rewrite using `[hβ, hwdef]`. Use `push_cast`. Simplify using the standard rewrite rules.

Rewrite using `[h0, ← normK]`. Conclude with `lt_of_le_of_lt hβα (lt_of_lt_of_le hk (min_le_left _ _))`.
-/
theorem dense_criterion : DenseOK := by
  intro dK hsq h4 l _ h5 hin ι σ hσ α hα hfix ε hε
  have h2 : 2 < l := by omega
  obtain ⟨hwm, hws⟩ := sqrt_in_unramified_completion dK hsq h4 l h5 hin ι
  set w : MaximalUnramifiedExtension l := ⟨ι (omegaK dK), hwm⟩ with hwdef
  have hw : σ w = 1 - w := hws σ hσ w rfl
  have hiso : ∀ a : MaximalUnramifiedExtension l, ‖σ a‖ = ‖a‖ := sigmaIsom (MaximalUnramifiedExtension l) l σ hσ

  have hR2 : (w + w - 1) ^ 2 = ((-(dK : ℤ) : ℤ) : MaximalUnramifiedExtension l) := by
    apply Subtype.ext
    push_cast
    have h0 : ι (omegaK dK) + ι (omegaK dK) - 1 = ι (rt dK) := by
      rw [← omega_eq, map_sub, map_mul, map_ofNat, map_one]; ring
    rw [hwdef]
    simp only
    rw [h0, ← map_pow, rt_sq]; simp
  set R : MaximalUnramifiedExtension l := w + w - 1 with hRdef
  have hσR : σ R = -R := by
    rw [hRdef]; simp only [map_sub, map_add, map_one, hw]; ring
  have hR1 : ‖R‖ = 1 := by
    have h1 : ‖R‖ ^ 2 = 1 := by rw [← norm_pow, hR2, normKZ_one (not_dvd_of_inert hin)]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 h1
  have hR0 : R ≠ 0 := by
    intro h; rw [h, norm_zero] at hR1; exact zero_ne_one hR1
  have hn2 : ‖(2 : MaximalUnramifiedExtension l)‖ = 1 := by
    have := normKZ_one (l := l) (two_not_dvd h2)
    simpa using this
  have hw1 : ‖w‖ ≤ 1 := by
    have h0 : w = (1 + R) / 2 := by rw [hRdef]; ring
    rw [h0, norm_div, hn2, div_one]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (by simp) hR1.le)

  set n0 : MaximalUnramifiedExtension l := (α - σ α) / R with hn0
  set m0 : MaximalUnramifiedExtension l := α - n0 * w with hm0
  have hn0R : n0 * R = α - σ α := by rw [hn0]; field_simp
  have hσn0 : σ n0 = n0 := by
    rw [hn0, map_div₀, map_sub, hfix, hσR]
    field_simp
    ring
  have hσm0 : σ m0 = m0 := by
    rw [hm0, map_sub, map_mul, hσn0, hw]
    have : R = w + w - 1 := hRdef
    rw [this] at hn0R
    linear_combination hn0R
  have hn01 : ‖n0‖ ≤ 1 := by
    rw [hn0, norm_div, hR1, div_one, sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hα.le ?_)
    rw [norm_neg, hiso, hα]
  have hm01 : ‖m0‖ ≤ 1 := by
    rw [hm0, sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hα.le ?_)
    rw [norm_neg, norm_mul]
    exact mul_le_one₀ hn01 (norm_nonneg _) hw1

  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (lt_min hε zero_lt_one) (KF.l_inv_lt_one l)
  rw [inv_pow] at hk
  obtain ⟨m, hm⟩ := fixedIsLimit (MaximalUnramifiedExtension l) l σ hσ m0 hm01 hσm0 k
  obtain ⟨n, hn⟩ := fixedIsLimit (MaximalUnramifiedExtension l) l σ hσ n0 hn01 hσn0 k
  set β : MaximalUnramifiedExtension l := (m : MaximalUnramifiedExtension l) + (n : MaximalUnramifiedExtension l) * w with hβ
  have hβα : ‖β - α‖ ≤ ((l : ℝ) ^ k)⁻¹ := by
    have h0 : β - α = -(m0 - m) + -(n0 - n) * w := by rw [hβ, hm0]; ring
    rw [h0]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (by rwa [norm_neg]) ?_)
    rw [norm_mul, norm_neg]
    calc ‖n0 - n‖ * ‖w‖ ≤ ((l : ℝ) ^ k)⁻¹ * 1 :=
          mul_le_mul hn hw1 (norm_nonneg _) (by positivity)
      _ = _ := mul_one _
  have hβ1 : ‖β‖ = 1 :=
    norm_one_of_close (lt_of_le_of_lt hβα (lt_of_lt_of_le hk (min_le_right _ _))) hα
  have hσβ : σ β = (m : MaximalUnramifiedExtension l) + (n : MaximalUnramifiedExtension l) * (1 - w) := by
    rw [hβ, map_add, map_mul, map_natCast, map_natCast, hw]
  obtain ⟨q, hq⟩ : ∃ q : ℤ, (dK : ℤ) + 1 = 4 * q := ⟨((dK : ℤ) + 1) / 4, by omega⟩
  have hq' : ((dK : ℤ) + 1) / 4 = q := by omega
  have hwq : w * (1 - w) = (q : MaximalUnramifiedExtension l) := by
    have h40 : (4 : MaximalUnramifiedExtension l) ≠ 0 := by norm_num
    apply mul_left_cancel₀ h40
    have h1 : ((dK : MaximalUnramifiedExtension l)) + 1 = 4 * (q : MaximalUnramifiedExtension l) := by exact_mod_cast congrArg (fun z : ℤ => (z : MaximalUnramifiedExtension l)) hq
    have h3 := hR2
    rw [hRdef] at h3
    push_cast at h3
    linear_combination (-1 : MaximalUnramifiedExtension l) * h3 + h1
  have hnorm : β * σ β = ((normInt dK m n : ℤ) : MaximalUnramifiedExtension l) := by
    rw [hσβ, hβ]
    unfold normInt
    rw [hq']
    push_cast
    linear_combination ((n : MaximalUnramifiedExtension l)) ^ 2 * hwq
  refine ⟨(m : ℤ), (n : ℤ), ?_, ?_⟩
  · intro hd
    have h1 := normKZ_lt.2 hd
    rw [← hnorm, norm_mul, hiso, hβ1] at h1
    norm_num at h1
  · have h0 : ι (((m : ℤ) : ℂ) + ((n : ℤ) : ℂ) * omegaK dK) - (α : ℂ_[l]) = ((β - α : MaximalUnramifiedExtension l) : ℂ_[l]) := by
      rw [hβ, hwdef]; push_cast
      simp
    rw [h0, ← normK]
    exact lt_of_le_of_lt hβα (lt_of_lt_of_le hk (min_le_left _ _))

end Formalism.L2.Th1.D
