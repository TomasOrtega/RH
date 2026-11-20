import Mathlib

namespace ReciprocityTheory.ChartRestriction.G.Sh

open MvPowerSeries

noncomputable section

section PowerSeriesAgreement

variable {R : Type*} [CommRing R] {τ : Type*} {ι : Type*}

def PTAgree (k : ℕ) (A A' : ι → MvPowerSeries τ R) : Prop :=
  ∀ i (e : τ →₀ ℕ), e.degree < k → coeff e (A i) = coeff e (A' i)

/- English proof (translation)
Introduce `i e he` and use `h i e (lt_of_lt_of_le he hl)`.
-/
theorem PTAgree.mono {k l : ℕ} {A A' : ι → MvPowerSeries τ R} (h : PTAgree k A A') (hl : l ≤ k) :
    PTAgree l A A' := fun i e he => h i e (lt_of_lt_of_le he hl)

/- English proof (translation)
Introduce `i e he` and use `(h i e he).trans (h' i e he)`.
-/
theorem PTAgree.trans {k : ℕ} {A B D : ι → MvPowerSeries τ R} (h : PTAgree k A B)
    (h' : PTAgree k B D) : PTAgree k A D := fun i e he => (h i e he).trans (h' i e he)

/- English proof (translation)
Introduce `i e he` and use `(h i e he).symm`.
-/
theorem PTAgree.symm {k : ℕ} {A B : ι → MvPowerSeries τ R} (h : PTAgree k A B) :
    PTAgree k B A := fun i e he => (h i e he).symm

/- English proof (translation)
Introduce `_ _ he` and use `absurd he (Nat.not_lt_zero _)`.
-/
theorem ptAgree_zero (A A' : ι → MvPowerSeries τ R) : PTAgree 0 A A' :=
  fun _ _ he => absurd he (Nat.not_lt_zero _)

/- English proof (translation)
The claim follows from `funext fun i => MvPowerSeries.ext fun e => h (e.degree + 1) i e (Nat.lt_succ_self _)`.
-/
theorem PTAgree.eq {A A' : ι → MvPowerSeries τ R} (h : ∀ k, PTAgree k A A') : A = A' :=
  funext fun i => MvPowerSeries.ext fun e => h (e.degree + 1) i e (Nat.lt_succ_self _)

section Fixed

variable (T : (ι → MvPowerSeries τ R) → (ι → MvPowerSeries τ R))
  (P : (ι → MvPowerSeries τ R) → Prop)

/- English proof (translation)
Use `ReciprocityTheory.ChartRestriction.G.Sh.PTAgree.eq fun k => ?_` and prove the remaining obligations. Proceed by induction on `k with`. Consider the case `zero => exact ptAgree_zero _ _`. Consider the case `succ k ih`. Establish `h` using `hT k x y hx hy ih`.

Rewrite `h` using `[hTx, hTy]`. Then use the resulting hypothesis.
-/
theorem pt_unique
    (hT : ∀ k x y, P x → P y → PTAgree k x y → PTAgree (k + 1) (T x) (T y))
    {x y : ι → MvPowerSeries τ R} (hx : P x) (hy : P y) (hTx : T x = x) (hTy : T y = y) :
    x = y := by
  refine ReciprocityTheory.ChartRestriction.G.Sh.PTAgree.eq fun k => ?_
  induction k with
  | zero => exact ptAgree_zero _ _
  | succ k ih =>
    have h := hT k x y hx hy ih
    rwa [hTx, hTy] at h

end Fixed

section Order

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h _ hd => coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast hd) h), nat_le_order⟩`.
-/
private theorem natCast_le_order_iff_coeff_eq_zero {f : MvPowerSeries τ R} {n : ℕ} :
    (n : ℕ∞) ≤ f.order ↔ ∀ d : τ →₀ ℕ, d.degree < n → coeff d f = 0 :=
  ⟨fun h _ hd => coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast hd) h), nat_le_order⟩

/- English proof (translation)
The claim follows from `natCast_le_order_iff_coeff_eq_zero.2 fun d hd => by rw [map_add, natCast_le_order_iff_coeff_eq_zero.1 hf d hd, natCast_le_order_iff_coeff_eq_zero.1 hg d hd, add_zero]`.
-/
private theorem natCast_le_order_add {f g : MvPowerSeries τ R} {n : ℕ}
    (hf : (n : ℕ∞) ≤ f.order) (hg : (n : ℕ∞) ≤ g.order) : (n : ℕ∞) ≤ (f + g).order :=
  natCast_le_order_iff_coeff_eq_zero.2 fun d hd => by
    rw [map_add, natCast_le_order_iff_coeff_eq_zero.1 hf d hd, natCast_le_order_iff_coeff_eq_zero.1 hg d hd, add_zero]

/- English proof (translation)
The claim follows from `le_trans (by rw [Nat.cast_add]; exact add_le_add hf hg) le_order_mul`.
-/
private theorem natCast_add_le_order_mul {f g : MvPowerSeries τ R} {a b : ℕ}
    (hf : (a : ℕ∞) ≤ f.order) (hg : (b : ℕ∞) ≤ g.order) : ((a + b : ℕ) : ℕ∞) ≤ (f * g).order :=
  le_trans (by rw [Nat.cast_add]; exact add_le_add hf hg) le_order_mul

/- English proof (translation)
The claim follows from `le_trans (Nat.cast_le.mpr hab) h`.
-/
private theorem natCast_le_order_of_le {f : MvPowerSeries τ R} {a b : ℕ} (hab : a ≤ b)
    (h : (b : ℕ∞) ≤ f.order) : (a : ℕ∞) ≤ f.order :=
  le_trans (Nat.cast_le.mpr hab) h

/- English proof (translation)
Use `nat_le_order fun d hd => ?_` and prove the remaining obligations. Establish `hd0 : d = 0` using `(Finsupp.degree_eq_zero_iff d).1 (by omega)`. Substitute `hd0` using the available equality. Simplify using `using hf`.
-/
private theorem one_le_order_of_constantCoeff_eq_zero {f : MvPowerSeries τ R} (hf : constantCoeff f = 0) :
    ((1 : ℕ) : ℕ∞) ≤ f.order := by
  refine nat_le_order fun d hd => ?_
  have hd0 : d = 0 := (Finsupp.degree_eq_zero_iff d).1 (by omega)
  subst hd0
  simpa using hf

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simp`. Consider the case `succ m ih`. Rewrite using `[pow_succ]`. Conclude with `natCast_add_le_order_mul ih (one_le_order_of_constantCoeff_eq_zero hf)`.
-/
private theorem natCast_le_order_pow_of_constantCoeff_eq_zero {f : MvPowerSeries τ R} (hf : constantCoeff f = 0) (m : ℕ) :
    (m : ℕ∞) ≤ (f ^ m).order := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ]
    exact natCast_add_le_order_mul ih (one_le_order_of_constantCoeff_eq_zero hf)

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simp [MvPowerSeries.order_zero]`. Consider the case `succ m ih`. Establish `key : f ^ (m + 1) - g ^ (m + 1) = f ^ m * (f - g) + (f ^ m - g ^ m) * g` using `by ring`. Rewrite using `[key]`.

Use `natCast_le_order_add ?_ ?_` and prove the remaining obligations. Conclude with `natCast_le_order_of_le (by omega) (natCast_add_le_order_mul (natCast_le_order_pow_of_constantCoeff_eq_zero hf m) hfg)`. Conclude with `natCast_le_order_of_le (by omega) (natCast_add_le_order_mul ih (one_le_order_of_constantCoeff_eq_zero hg))`.
-/
theorem pt_order_pow_sub {f g : MvPowerSeries τ R} {j : ℕ}
    (hfg : ((j + 1 : ℕ) : ℕ∞) ≤ (f - g).order) (hf : constantCoeff f = 0)
    (hg : constantCoeff g = 0) (m : ℕ) : ((j + m : ℕ) : ℕ∞) ≤ (f ^ m - g ^ m).order := by
  induction m with
  | zero => simp [MvPowerSeries.order_zero]
  | succ m ih =>
    have key : f ^ (m + 1) - g ^ (m + 1) = f ^ m * (f - g) + (f ^ m - g ^ m) * g := by ring
    rw [key]
    refine natCast_le_order_add ?_ ?_
    · exact natCast_le_order_of_le (by omega) (natCast_add_le_order_mul (natCast_le_order_pow_of_constantCoeff_eq_zero hf m) hfg)
    · exact natCast_le_order_of_le (by omega)
        (natCast_add_le_order_mul ih (one_le_order_of_constantCoeff_eq_zero hg))

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `@insert a S ha ih`. Rewrite using `[Finset.sum_insert ha, Finset.prod_insert ha]`. Conclude with `natCast_add_le_order_mul (natCast_le_order_pow_of_constantCoeff_eq_zero (hA a) (α a)) ih`.
-/
theorem pt_order_prod_pow {σ : Type*} (A : σ → MvPowerSeries τ R)
    (hA : ∀ s, constantCoeff (A s) = 0) (α : σ →₀ ℕ) (S : Finset σ) :
    ((∑ s ∈ S, α s : ℕ) : ℕ∞) ≤ (∏ s ∈ S, A s ^ α s).order := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact natCast_add_le_order_mul (natCast_le_order_pow_of_constantCoeff_eq_zero (hA a) (α a)) ih

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty => simp [MvPowerSeries.order_zero]`. Consider the case `@insert a S ha ih`. Rewrite using `[Finset.sum_insert ha, Finset.prod_insert ha, Finset.prod_insert ha]`. Establish `key : A a ^ α a * ∏ s ∈ S, A s ^ α s - A' a ^ α a * ∏ s ∈ S, A' s ^ α s = (A a ^ α a - A' a ^ α a) * ∏ s ∈ S, A s ^ α s + A' a ^ α a * (∏ s ∈ S, A s ^ α s - ∏ s ∈ S, A' s ^ α s)` using `by ring`.

Rewrite using `[key]`. Use `natCast_le_order_add ?_ ?_` and prove the remaining obligations. Conclude with `natCast_le_order_of_le (by omega) (natCast_add_le_order_mul (pt_order_pow_sub (hAA a) (hA a) (hA' a) (α a)) (pt_order_prod_pow A hA α S))`. Conclude with `natCast_le_order_of_le (by omega) (natCast_add_le_order_mul (natCast_le_order_pow_of_constantCoeff_eq_zero (hA' a) (α a)) ih)`.
-/
theorem pt_order_prod_sub {σ : Type*} {A A' : σ → MvPowerSeries τ R} {j : ℕ}
    (hA : ∀ s, constantCoeff (A s) = 0) (hA' : ∀ s, constantCoeff (A' s) = 0)
    (hAA : ∀ s, ((j + 1 : ℕ) : ℕ∞) ≤ (A s - A' s).order) (α : σ →₀ ℕ) (S : Finset σ) :
    ((j + ∑ s ∈ S, α s : ℕ) : ℕ∞) ≤
      (∏ s ∈ S, A s ^ α s - ∏ s ∈ S, A' s ^ α s).order := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [MvPowerSeries.order_zero]
  | @insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, Finset.prod_insert ha]
    have key : A a ^ α a * ∏ s ∈ S, A s ^ α s - A' a ^ α a * ∏ s ∈ S, A' s ^ α s =
        (A a ^ α a - A' a ^ α a) * ∏ s ∈ S, A s ^ α s +
          A' a ^ α a * (∏ s ∈ S, A s ^ α s - ∏ s ∈ S, A' s ^ α s) := by ring
    rw [key]
    refine natCast_le_order_add ?_ ?_
    · exact natCast_le_order_of_le (by omega)
        (natCast_add_le_order_mul (pt_order_pow_sub (hAA a) (hA a) (hA' a) (α a))
          (pt_order_prod_pow A hA α S))
    · exact natCast_le_order_of_le (by omega) (natCast_add_le_order_mul (natCast_le_order_pow_of_constantCoeff_eq_zero (hA' a) (α a)) ih)

/- English proof (translation)
Introduce `e he`. Rewrite using `[coeff_subst hA K e, coeff_subst hA' K e]`. Use `finsum_congr fun α => ?_` and prove the remaining obligations. Distinguish the cases in `hα : coeff α K = 0`. Simplify using `[hα]`.

Use `congr 1`. Simplify using `only [Finsupp.prod]`. Break down `hK α hα with h2 | hsame` into its components or cases. Establish `hdeg : α.degree = ∑ s ∈ α.support, α s` using `Finsupp.degree_apply α`. Break down `Nat.eq_zero_or_pos k with hk | hk` into its components or cases.

Substitute `hk` using the available equality. Establish `h1` using `pt_order_prod_pow A hA0 α α.support`. Establish `h1'` using `pt_order_prod_pow A' hA0' α α.support`. Establish `hlt : ((e.degree : ℕ) : ℕ∞) < ((∑ s ∈ α.support, α s : ℕ) : ℕ∞)`. Conclude with `(by omega : e.degree < ∑ s ∈ α.support, α s)` after adjusting the coercions.

Rewrite using `[coeff_of_lt_order (lt_of_lt_of_le hlt h1), coeff_of_lt_order (lt_of_lt_of_le hlt h1')]`. Take `⟨j, rfl⟩ : ∃ j, k = j + 1` from `⟨k - 1, by omega⟩`. Establish `hAA' : ∀ s, ((j + 1 : ℕ) : ℕ∞) ≤ (A s - A' s).order` using `fun s => nat_le_order fun d hd => by rw [map_sub, hAA s d hd, sub_self]`. Establish `h` using `pt_order_prod_sub hA0 hA0' hAA' α α.support`. Establish `hlt : ((e.degree : ℕ) : ℕ∞) < ((j + ∑ s ∈ α.support, α s : ℕ) : ℕ∞)`.

Conclude with `(by omega : e.degree < j + ∑ s ∈ α.support, α s)` after adjusting the coercions. Establish `hz` using `coeff_of_lt_order (lt_of_lt_of_le hlt h)`. Rewrite `hz` using `[map_sub, sub_eq_zero]`. Conclude with `hz`. Establish `hprod : ∏ s ∈ α.support, A s ^ α s = ∏ s ∈ α.support, A' s ^ α s` using `Finset.prod_congr rfl fun s hs => by rw [hsame s hs]`.

Rewrite using `[hprod]`.
-/
theorem pt_subst_agree {σ : Type*} {A A' : σ → MvPowerSeries τ R} (hA : HasSubst A)
    (hA' : HasSubst A') (hA0 : ∀ s, constantCoeff (A s) = 0)
    (hA0' : ∀ s, constantCoeff (A' s) = 0) (K : MvPowerSeries σ R) (k : ℕ)
    (hAA : ∀ s (e : τ →₀ ℕ), e.degree < k → coeff e (A s) = coeff e (A' s))
    (hK : ∀ α, coeff α K ≠ 0 → 2 ≤ α.degree ∨ ∀ s ∈ α.support, A s = A' s) :
    ∀ e : τ →₀ ℕ, e.degree < k + 1 → coeff e (subst A K) = coeff e (subst A' K) := by
  intro e he
  rw [coeff_subst hA K e, coeff_subst hA' K e]
  refine finsum_congr fun α => ?_
  by_cases hα : coeff α K = 0
  · simp [hα]
  congr 1
  simp only [Finsupp.prod]
  rcases hK α hα with h2 | hsame
  · have hdeg : α.degree = ∑ s ∈ α.support, α s := Finsupp.degree_apply α
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      have h1 := pt_order_prod_pow A hA0 α α.support
      have h1' := pt_order_prod_pow A' hA0' α α.support
      have hlt : ((e.degree : ℕ) : ℕ∞) < ((∑ s ∈ α.support, α s : ℕ) : ℕ∞) := by
        exact_mod_cast (by omega : e.degree < ∑ s ∈ α.support, α s)
      rw [coeff_of_lt_order (lt_of_lt_of_le hlt h1), coeff_of_lt_order (lt_of_lt_of_le hlt h1')]
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      have hAA' : ∀ s, ((j + 1 : ℕ) : ℕ∞) ≤ (A s - A' s).order := fun s =>
        nat_le_order fun d hd => by rw [map_sub, hAA s d hd, sub_self]
      have h := pt_order_prod_sub hA0 hA0' hAA' α α.support
      have hlt : ((e.degree : ℕ) : ℕ∞) < ((j + ∑ s ∈ α.support, α s : ℕ) : ℕ∞) := by
        exact_mod_cast (by omega : e.degree < j + ∑ s ∈ α.support, α s)
      have hz := coeff_of_lt_order (lt_of_lt_of_le hlt h)
      rw [map_sub, sub_eq_zero] at hz
      exact hz
  · have hprod : ∏ s ∈ α.support, A s ^ α s = ∏ s ∈ α.support, A' s ^ α s :=
      Finset.prod_congr rfl fun s hs => by rw [hsame s hs]
    rw [hprod]

end Order

end PowerSeriesAgreement

end

end ReciprocityTheory.ChartRestriction.G.Sh
