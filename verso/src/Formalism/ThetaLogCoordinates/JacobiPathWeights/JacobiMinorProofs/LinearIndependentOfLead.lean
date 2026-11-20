import Mathlib
import Formalism.ThetaLogCoordinates.JacobiPathWeights.StatementA
import Lemmata.GeneralBFactRightFurther.Imports

noncomputable section

open scoped BigOperators
open Finset MvPolynomial

namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases

namespace leadingTermLemmas

section Lex

variable {σ τ : Type*} [LinearOrder τ] (κ : σ → τ)

def LL (e e' : σ →₀ ℕ) : Prop := ∃ x, e x < e' x ∧ ∀ y, κ y < κ x → e y = e' y

/- English proof (translation)
Introduce and unpack `⟨x, hx, -⟩`. Conclude with `lt_irrefl _ hx`.
-/
theorem LL_irrefl (e : σ →₀ ℕ) : ¬ LL κ e e := by
  rintro ⟨x, hx, -⟩
  exact lt_irrefl _ hx

variable {κ}

/- English proof (translation)
Take `⟨x, hx, hxy⟩` from `h`. Take `⟨x', hx', hxy'⟩` from `h'`. Break down `lt_trichotomy (κ x) (κ x') with hlt | heq | hgt` into its components or cases. Use `⟨x, ?_, fun y hy => ?_⟩` and prove the remaining obligations. Rewrite using `[← hxy' x hlt]`.

Conclude with `hx`. Rewrite using `[hxy y hy, hxy' y (hy.trans hlt)]`. Establish `: x = x'` using `hκ heq`. Substitute `this` using the available equality. Conclude with `⟨x, hx.trans hx', fun y hy => by rw [hxy y hy, hxy' y hy]⟩`.

Use `⟨x', ?_, fun y hy => ?_⟩` and prove the remaining obligations. Rewrite using `[hxy x' hgt]`. Conclude with `hx'`. Rewrite using `[hxy y (hy.trans hgt), hxy' y hy]`.
-/
theorem LL_trans (hκ : Function.Injective κ) {e e' e'' : σ →₀ ℕ} (h : LL κ e e') (h' : LL κ e' e'') :
    LL κ e e'' := by
  obtain ⟨x, hx, hxy⟩ := h
  obtain ⟨x', hx', hxy'⟩ := h'
  rcases lt_trichotomy (κ x) (κ x') with hlt | heq | hgt
  · refine ⟨x, ?_, fun y hy => ?_⟩
    · rw [← hxy' x hlt]; exact hx
    · rw [hxy y hy, hxy' y (hy.trans hlt)]
  · have : x = x' := hκ heq
    subst this
    exact ⟨x, hx.trans hx', fun y hy => by rw [hxy y hy, hxy' y hy]⟩
  · refine ⟨x', ?_, fun y hy => ?_⟩
    · rw [hxy x' hgt]; exact hx'
    · rw [hxy y (hy.trans hgt), hxy' y hy]

/- English proof (translation)
Take `⟨x, hx, hxy⟩` from `h`. Use `⟨x, ?_, fun y hy => ?_⟩` and prove the remaining obligations. Simplify using `only [Finsupp.add_apply]`. Use linear arithmetic over natural numbers and integers. Simplify using `only [Finsupp.add_apply]`.

Rewrite using `[hxy y hy]`.
-/
theorem LL_add_right {e e' : σ →₀ ℕ} (h : LL κ e e') (f : σ →₀ ℕ) : LL κ (e + f) (e' + f) := by
  obtain ⟨x, hx, hxy⟩ := h
  refine ⟨x, ?_, fun y hy => ?_⟩
  · simp only [Finsupp.add_apply]; omega
  · simp only [Finsupp.add_apply]; rw [hxy y hy]

/- English proof (translation)
Rewrite using `[add_comm f e, add_comm f e']`. Conclude with `LL_add_right h f`.
-/
theorem LL_add_left {e e' : σ →₀ ℕ} (h : LL κ e e') (f : σ →₀ ℕ) : LL κ (f + e) (f + e') := by
  rw [add_comm f e, add_comm f e']; exact LL_add_right h f

/- English proof (translation)
The claim follows from `LL_trans hκ (LL_add_right h f) (LL_add_left h' e')`.
-/
theorem LL_add (hκ : Function.Injective κ) {e e' f f' : σ →₀ ℕ} (h : LL κ e e') (h' : LL κ f f') :
    LL κ (e + f) (e' + f') :=
  LL_trans hκ (LL_add_right h f) (LL_add_left h' e')

/- English proof (translation)
Use `set S := (e.support ∪ e'.support).filter fun x => e x ≠ e' x with hS`. Establish `hne : S.Nonempty`. Assume the negation of the conclusion as `hemp`. Rewrite `hemp` using `[Finset.not_nonempty_iff_eq_empty]`. Apply `h` to reduce the goal to its premises.

Use extensionality with `x`. Assume the negation of the conclusion as `hx`. Establish `: x ∈ S`. Rewrite using `[hS, Finset.mem_filter, Finset.mem_union, Finsupp.mem_support_iff, Finsupp.mem_support_iff]`. Use `⟨?_, hx⟩` and prove the remaining obligations.

Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Conclude with `hx (by rw [hc.1, hc.2])`. Rewrite `this` using `[hemp]`. Conclude with `absurd this (Finset.notMem_empty _)`.

Take `⟨x, hxS, hmin⟩` from `Finset.exists_min_image S κ hne`. Establish `hxne : e x ≠ e' x` using `(Finset.mem_filter.1 hxS).2`. Establish `hbefore : ∀ y, κ y < κ x → e y = e' y`. Introduce `y hy`. Assume the negation of the conclusion as `hne'`.

Establish `: y ∈ S`. Rewrite using `[hS, Finset.mem_filter, Finset.mem_union, Finsupp.mem_support_iff, Finsupp.mem_support_iff]`. Use `⟨?_, hne'⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hc`. Use `push Not at hc`.

Conclude with `hne' (by rw [hc.1, hc.2])`. Conclude with `absurd (hmin y this) (not_le.2 hy)`. Break down `lt_or_gt_of_ne hxne with hlt | hgt` into its components or cases. Conclude with `Or.inl ⟨x, hlt, hbefore⟩`. Conclude with `Or.inr ⟨x, hgt, fun y hy => (hbefore y hy).symm⟩`.
-/
theorem LL_total {e e' : σ →₀ ℕ} (h : e ≠ e') : LL κ e e' ∨ LL κ e' e := by
  classical
  set S := (e.support ∪ e'.support).filter fun x => e x ≠ e' x with hS
  have hne : S.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    apply h
    ext x
    by_contra hx
    have : x ∈ S := by
      rw [hS, Finset.mem_filter, Finset.mem_union, Finsupp.mem_support_iff, Finsupp.mem_support_iff]
      refine ⟨?_, hx⟩
      by_contra hc
      push Not at hc
      exact hx (by rw [hc.1, hc.2])
    rw [hemp] at this
    exact absurd this (Finset.notMem_empty _)
  obtain ⟨x, hxS, hmin⟩ := Finset.exists_min_image S κ hne
  have hxne : e x ≠ e' x := (Finset.mem_filter.1 hxS).2
  have hbefore : ∀ y, κ y < κ x → e y = e' y := by
    intro y hy
    by_contra hne'
    have : y ∈ S := by
      rw [hS, Finset.mem_filter, Finset.mem_union, Finsupp.mem_support_iff, Finsupp.mem_support_iff]
      refine ⟨?_, hne'⟩
      by_contra hc
      push Not at hc
      exact hne' (by rw [hc.1, hc.2])
    exact absurd (hmin y this) (not_le.2 hy)
  rcases lt_or_gt_of_ne hxne with hlt | hgt
  · exact Or.inl ⟨x, hlt, hbefore⟩
  · exact Or.inr ⟨x, hgt, fun y hy => (hbefore y hy).symm⟩

/- English proof (translation)
Proceed by induction on `hs using Finset.Nonempty.cons_induction with`. Consider the case `singleton a`. Conclude with `⟨a, Finset.mem_singleton_self a, fun j hj hne => absurd (Finset.mem_singleton.1 hj) hne⟩`. Consider the case `cons a s ha hs ih`. Take `⟨i, his, hi⟩` from `ih`.

Establish `hai : a ≠ i` using `fun h => ha (h ▸ his)`. Break down `LL_total (κ := κ) (fun h => hai (hd h) : d a ≠ d i) with h1 | h1` into its components or cases. Use `⟨i, Finset.mem_cons.2 (Or.inr his), fun j hj hne => ?_⟩` and prove the remaining obligations. Break down `Finset.mem_cons.1 hj with rfl | hj` into its components or cases. Conclude with `h1`.

Conclude with `hi j hj hne`. Use `⟨a, Finset.mem_cons_self a s, fun j hj hne => ?_⟩` and prove the remaining obligations. Break down `Finset.mem_cons.1 hj with rfl | hj` into its components or cases. Conclude with `absurd rfl hne`. Distinguish the cases in `hji : j = i`.

Rewrite using `[hji]`. Conclude with `h1`. Conclude with `LL_trans hκ (hi j hj hji) h1`.
-/
theorem exists_LL_max (hκ : Function.Injective κ) {ι : Type*} (d : ι → σ →₀ ℕ) (hd : Function.Injective d)
    (s : Finset ι) (hs : s.Nonempty) : ∃ i ∈ s, ∀ j ∈ s, j ≠ i → LL κ (d j) (d i) := by
  classical
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a =>
    exact ⟨a, Finset.mem_singleton_self a, fun j hj hne => absurd (Finset.mem_singleton.1 hj) hne⟩
  | cons a s ha hs ih =>
    obtain ⟨i, his, hi⟩ := ih
    have hai : a ≠ i := fun h => ha (h ▸ his)
    rcases LL_total (κ := κ) (fun h => hai (hd h) : d a ≠ d i) with h1 | h1
    · refine ⟨i, Finset.mem_cons.2 (Or.inr his), fun j hj hne => ?_⟩
      rcases Finset.mem_cons.1 hj with rfl | hj
      · exact h1
      · exact hi j hj hne
    · refine ⟨a, Finset.mem_cons_self a s, fun j hj hne => ?_⟩
      rcases Finset.mem_cons.1 hj with rfl | hj
      · exact absurd rfl hne
      · by_cases hji : j = i
        · rw [hji]; exact h1
        · exact LL_trans hκ (hi j hj hji) h1

variable {R : Type*} [CommRing R] (κ)

def Lead (f : MvPolynomial σ R) (d : σ →₀ ℕ) : Prop :=
  coeff d f = 1 ∧ ∀ e ∈ f.support, e ≠ d → LL κ e d

variable {κ}

/- English proof (translation)
Use `⟨by simp, fun e he hne => ?_⟩` and prove the remaining obligations. Rewrite `he` using `[MvPolynomial.mem_support_iff, MvPolynomial.coeff_one, if_neg (Ne.symm hne)]`. Conclude with `absurd rfl he`.
-/
theorem Lead_one : Lead κ (1 : MvPolynomial σ R) 0 := by
  classical
  refine ⟨by simp, fun e he hne => ?_⟩
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_one, if_neg (Ne.symm hne)] at he
  exact absurd rfl he

/- English proof (translation)
Establish `key : ∀ e e' : σ →₀ ℕ, e ∈ f.support → e' ∈ g.support → (e ≠ d ∨ e' ≠ d') → LL κ (e + e') (d + d')`. Introduce `e e' he he' hne`. Distinguish the cases in `h1 : e = d`. Substitute `h1` using the available equality. Establish `h2 : e' ≠ d'`.

Break down `hne with h | h` into its components or cases. Conclude with `absurd rfl h`. Conclude with `h`. Conclude with `LL_add_left (hg.2 e' he' h2) e`. Distinguish the cases in `h2 : e' = d'`.

Substitute `h2` using the available equality. Conclude with `LL_add_right (hf.2 e he h1) e'`. Conclude with `LL_add hκ (hf.2 e he h1) (hg.2 e' he' h2)`. Prove the components needed by the constructor for the conclusion. Rewrite using `[MvPolynomial.coeff_mul, Finset.sum_eq_single (d, d')]`.

Rewrite using `[hf.1, hg.1, one_mul]`. Introduce and unpack `⟨e, e'⟩ hmem hne`. Rewrite `hmem` using `[Finset.HasAntidiagonal.mem_antidiagonal]`. Simplify using `only at hmem`. Assume the negation of the conclusion as `hc`.

Establish `he : e ∈ f.support`. Rewrite using `[MvPolynomial.mem_support_iff]; intro h0; exact hc (by simp [h0])`. Establish `he' : e' ∈ g.support`. Rewrite using `[MvPolynomial.mem_support_iff]; intro h0; exact hc (by simp [h0])`. Establish `hne' : e ≠ d ∨ e' ≠ d'`.

Assume the negation of the conclusion as `hcc`. Use `push Not at hcc`. Conclude with `hne (by rw [hcc.1, hcc.2])`. Use `key e e' he he' hne'` as an intermediate fact. Rewrite `this` using `[hmem]`.

Conclude with `LL_irrefl κ _ this`. Introduce `h`. Conclude with `absurd (Finset.HasAntidiagonal.mem_antidiagonal.2 (show (d, d').1 + (d, d').2 = d + d' from rfl)) h`. Introduce `e he hne`. Take `⟨a, ha, b, hb, rfl⟩` from `Finset.mem_add.1 (MvPolynomial.support_mul f g he)`.

Apply `key a b ha hb` to reduce the goal to its premises. Assume the negation of the conclusion as `hcc`. Use `push Not at hcc`. Conclude with `hne (by rw [hcc.1, hcc.2])`.
-/
theorem Lead_mul (hκ : Function.Injective κ) {f g : MvPolynomial σ R} {d d' : σ →₀ ℕ}
    (hf : Lead κ f d) (hg : Lead κ g d') : Lead κ (f * g) (d + d') := by
  classical
  have key : ∀ e e' : σ →₀ ℕ, e ∈ f.support → e' ∈ g.support → (e ≠ d ∨ e' ≠ d') →
      LL κ (e + e') (d + d') := by
    intro e e' he he' hne
    by_cases h1 : e = d
    · subst h1
      have h2 : e' ≠ d' := by
        rcases hne with h | h
        · exact absurd rfl h
        · exact h
      exact LL_add_left (hg.2 e' he' h2) e
    · by_cases h2 : e' = d'
      · subst h2
        exact LL_add_right (hf.2 e he h1) e'
      · exact LL_add hκ (hf.2 e he h1) (hg.2 e' he' h2)
  constructor
  · rw [MvPolynomial.coeff_mul, Finset.sum_eq_single (d, d')]
    · rw [hf.1, hg.1, one_mul]
    · rintro ⟨e, e'⟩ hmem hne
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hmem
      simp only at hmem
      by_contra hc
      have he : e ∈ f.support := by
        rw [MvPolynomial.mem_support_iff]; intro h0; exact hc (by simp [h0])
      have he' : e' ∈ g.support := by
        rw [MvPolynomial.mem_support_iff]; intro h0; exact hc (by simp [h0])
      have hne' : e ≠ d ∨ e' ≠ d' := by
        by_contra hcc
        push Not at hcc
        exact hne (by rw [hcc.1, hcc.2])
      have := key e e' he he' hne'
      rw [hmem] at this
      exact LL_irrefl κ _ this
    · intro h
      exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.2 (show (d, d').1 + (d, d').2 = d + d' from rfl)) h
  · intro e he hne
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.1 (MvPolynomial.support_mul f g he)
    apply key a b ha hb
    by_contra hcc
    push Not at hcc
    exact hne (by rw [hcc.1, hcc.2])

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using (Lead_one : Lead κ (1 : MvPolynomial σ R) 0)`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.prod_insert ha, Finset.sum_insert ha]`. Conclude with `Lead_mul hκ (h a (Finset.mem_insert_self a s)) (ih fun c hc => h c (Finset.mem_insert_of_mem hc))`.
-/
theorem Lead_prod (hκ : Function.Injective κ) {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ R)
    (d : ι → σ →₀ ℕ) (h : ∀ c ∈ s, Lead κ (f c) (d c)) : Lead κ (∏ c ∈ s, f c) (∑ c ∈ s, d c) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (Lead_one : Lead κ (1 : MvPolynomial σ R) 0)
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact Lead_mul hκ (h a (Finset.mem_insert_self a s))
      (ih fun c hc => h c (Finset.mem_insert_of_mem hc))

/- English proof (translation)
Rewrite using `[linearIndependent_iff']`. Introduce `s g hsum`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Take `⟨i₁, hi₁, hg₁⟩` from `hcon`.

Establish `hne : (s.filter fun i => g i ≠ 0).Nonempty` using `⟨i₁, Finset.mem_filter.2 ⟨hi₁, hg₁⟩⟩`. Take `⟨i₀, hi₀, hmax⟩` from `exists_LL_max hκ d hd _ hne`. Establish `hc : coeff (d i₀) (∑ i ∈ s, g i • v i) = 0` using `by rw [hsum]; simp`. Rewrite `hc` using `[MvPolynomial.coeff_sum, Finset.sum_eq_single i₀]`. Rewrite `hc` using `[MvPolynomial.coeff_smul, (hv i₀).1, smul_eq_mul, mul_one]`.

Conclude with `(Finset.mem_filter.1 hi₀).2 hc`. Introduce `j hj hji`. Rewrite using `[MvPolynomial.coeff_smul, smul_eq_mul]`. Distinguish the cases in `hgj : g j = 0`. Rewrite using `[hgj, zero_mul]`.

Establish `h1` using `hmax j (Finset.mem_filter.2 ⟨hj, hgj⟩) hji`. Assume the negation of the conclusion as `hc'`. Establish `hsup : d i₀ ∈ (v j).support`. Rewrite using `[MvPolynomial.mem_support_iff]; intro h0; exact hc' (by rw [h0, mul_zero])`. Establish `h2` using `(hv j).2 (d i₀) hsup (fun h => hji (hd h).symm)`.

Conclude with `LL_irrefl κ _ (LL_trans hκ h1 h2)`. Introduce `h`. Conclude with `absurd (Finset.mem_filter.1 hi₀).1 h`.
-/
theorem linearIndependent_of_Lead (hκ : Function.Injective κ) {k : Type*} [Field k] {ι : Type*}
    (v : ι → MvPolynomial σ k) (d : ι → σ →₀ ℕ) (hd : Function.Injective d)
    (hv : ∀ i, Lead κ (v i) (d i)) : LinearIndependent k v := by
  classical
  rw [linearIndependent_iff']
  intro s g hsum
  by_contra hcon
  push Not at hcon
  obtain ⟨i₁, hi₁, hg₁⟩ := hcon
  have hne : (s.filter fun i => g i ≠ 0).Nonempty := ⟨i₁, Finset.mem_filter.2 ⟨hi₁, hg₁⟩⟩
  obtain ⟨i₀, hi₀, hmax⟩ := exists_LL_max hκ d hd _ hne
  have hc : coeff (d i₀) (∑ i ∈ s, g i • v i) = 0 := by rw [hsum]; simp
  rw [MvPolynomial.coeff_sum, Finset.sum_eq_single i₀] at hc
  · rw [MvPolynomial.coeff_smul, (hv i₀).1, smul_eq_mul, mul_one] at hc
    exact (Finset.mem_filter.1 hi₀).2 hc
  · intro j hj hji
    rw [MvPolynomial.coeff_smul, smul_eq_mul]
    by_cases hgj : g j = 0
    · rw [hgj, zero_mul]
    · have h1 := hmax j (Finset.mem_filter.2 ⟨hj, hgj⟩) hji
      by_contra hc'
      have hsup : d i₀ ∈ (v j).support := by
        rw [MvPolynomial.mem_support_iff]; intro h0; exact hc' (by rw [h0, mul_zero])
      have h2 := (hv j).2 (d i₀) hsup (fun h => hji (hd h).symm)
      exact LL_irrefl κ _ (LL_trans hκ h1 h2)
  · intro h
    exact absurd (Finset.mem_filter.1 hi₀).1 h

end Lex

section Det

variable {n : ℕ}

def key (x : Fin n × Fin n) : Fin n ×ₗ Fin n := toLex x

/- English proof (translation)
The claim follows from `toLex.injective`.
-/
theorem key_inj : Function.Injective (key (n := n)) := toLex.injective

/- English proof (translation)
The claim follows from `Prod.Lex.toLex_lt_toLex`.
-/
theorem key_lt {x y : Fin n × Fin n} :
    key y < key x ↔ (y.1 < x.1 ∨ (y.1 = x.1 ∧ y.2 < x.2)) := Prod.Lex.toLex_lt_toLex

def mon {m : ℕ} (r c : Fin m → Fin n) (π : Equiv.Perm (Fin m)) : Fin n × Fin n →₀ ℕ :=
  ∑ i, Finsupp.single (r i, c (π i)) 1

/- English proof (translation)
Unfold `mon`. Rewrite using `[Finsupp.finsetSum_apply]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finsupp.single_apply]`. Conclude with `if_congr Prod.ext_iff rfl rfl`.
-/
theorem mon_apply {m : ℕ} (r c : Fin m → Fin n) (π : Equiv.Perm (Fin m)) (x : Fin n × Fin n) :
    mon r c π x = ∑ i, if (r i = x.1 ∧ c (π i) = x.2) then 1 else 0 := by
  classical
  unfold mon
  rw [Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finsupp.single_apply]
  exact if_congr Prod.ext_iff rfl rfl

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨a, ha, hmin⟩ : ∃ a, π a ≠ a ∧ ∀ i, i < a → π i = i := by`. Establish `hne : (univ.filter fun a => π a ≠ a).Nonempty`. Assume the negation of the conclusion as `h`. Rewrite `h` using `[Finset.not_nonempty_iff_eq_empty]`. Apply `hπ` to reduce the goal to its premises.

Use `ext1 a`. Assume the negation of the conclusion as `hc'`. Establish `: a ∈ univ.filter fun a => π a ≠ a` using `Finset.mem_filter.2 ⟨Finset.mem_univ a, hc'⟩`. Rewrite `this` using `[h]`. Conclude with `absurd this (Finset.notMem_empty _)`.

Take `⟨a, haS, hmin⟩` from `Finset.exists_min_image _ id hne`. Use `⟨a, (Finset.mem_filter.1 haS).2, fun i hi => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hc'`. Conclude with `absurd (hmin i (Finset.mem_filter.2 ⟨Finset.mem_univ i, hc'⟩)) (not_le.2 hi)`. Establish `hgt : a < π a`.

Break down `lt_or_gt_of_ne ha with h | h` into its components or cases. Conclude with `absurd (π.injective (hmin _ h)) ha`. Conclude with `h`. Use `⟨(r a, c a), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[mon_apply, mon_apply]`.

Establish `h0 : (∑ i, if (r i = (r a, c a).1 ∧ c (π i) = (r a, c a).2) then 1 else 0) = 0`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `i _`. Rewrite using `[if_neg]`. Introduce and unpack `⟨h1, h2⟩`.

Use `hr.injective h1` as an intermediate fact. Substitute `this` using the available equality. Conclude with `ha (hc.injective h2)`. Rewrite using `[h0]`. Establish `h1` using `Finset.single_le_sum (f := fun i => if (r i = (r a, c a).1 ∧ c ((1 : Equiv.Perm (Fin m)) i) = (r a, c a).2) then 1 else 0) (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)`.

Simplify using `only [Equiv.Perm.coe_one, id_eq, and_self, if_true] at h1`. Simplify using `only [Equiv.Perm.coe_one, id_eq]`. Use linear arithmetic over natural numbers and integers. Introduce `y hy`. Rewrite `hy` using `[key_lt]`.

Simplify using `only at hy`. Rewrite using `[mon_apply, mon_apply]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Use `if_congr ?_ rfl rfl` and prove the remaining obligations. Rewrite using `[Equiv.Perm.one_apply]`.

Break down `lt_trichotomy i a with h | h | h` into its components or cases. Rewrite using `[hmin i h]`. Substitute `h` using the available equality. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`.

It suffices to derive a contradiction. Break down `hy with hy | ⟨_, hy⟩` into its components or cases. Rewrite `hy` using `[← h1]`. Conclude with `lt_irrefl _ hy`. Rewrite `hy` using `[← h2]`.

Conclude with `absurd (hc hgt) (not_lt.2 hy.le)`. Introduce and unpack `⟨h1, h2⟩`. It suffices to derive a contradiction. Break down `hy with hy | ⟨_, hy⟩` into its components or cases. Rewrite `hy` using `[← h1]`.

Conclude with `lt_irrefl _ hy`. Rewrite `hy` using `[← h2]`. Conclude with `lt_irrefl _ hy`. Establish `hlt : y.1 < r i`. Break down `hy with hy | ⟨hy, _⟩` into its components or cases.

Conclude with `hy.trans (hr h)`. Rewrite using `[hy]`. Conclude with `hr h`. Apply the tactic sequence `constructor <;> rintro ⟨h1, _⟩ <;> exact absurd h1 hlt.ne'`.
-/
theorem mon_LL {m : ℕ} {r c : Fin m → Fin n} (hr : StrictMono r) (hc : StrictMono c)
    (π : Equiv.Perm (Fin m)) (hπ : π ≠ 1) : LL key (mon r c π) (mon r c 1) := by
  classical
  obtain ⟨a, ha, hmin⟩ : ∃ a, π a ≠ a ∧ ∀ i, i < a → π i = i := by
    have hne : (univ.filter fun a => π a ≠ a).Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty] at h
      apply hπ
      ext1 a
      by_contra hc'
      have : a ∈ univ.filter fun a => π a ≠ a := Finset.mem_filter.2 ⟨Finset.mem_univ a, hc'⟩
      rw [h] at this
      exact absurd this (Finset.notMem_empty _)
    obtain ⟨a, haS, hmin⟩ := Finset.exists_min_image _ id hne
    refine ⟨a, (Finset.mem_filter.1 haS).2, fun i hi => ?_⟩
    by_contra hc'
    exact absurd (hmin i (Finset.mem_filter.2 ⟨Finset.mem_univ i, hc'⟩)) (not_le.2 hi)
  have hgt : a < π a := by
    rcases lt_or_gt_of_ne ha with h | h
    · exact absurd (π.injective (hmin _ h)) ha
    · exact h
  refine ⟨(r a, c a), ?_, ?_⟩
  · rw [mon_apply, mon_apply]
    have h0 : (∑ i, if (r i = (r a, c a).1 ∧ c (π i) = (r a, c a).2) then 1 else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      rw [if_neg]
      rintro ⟨h1, h2⟩
      have := hr.injective h1
      subst this
      exact ha (hc.injective h2)
    rw [h0]
    have h1 := Finset.single_le_sum
      (f := fun i => if (r i = (r a, c a).1 ∧ c ((1 : Equiv.Perm (Fin m)) i) = (r a, c a).2) then 1 else 0)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)
    simp only [Equiv.Perm.coe_one, id_eq, and_self, if_true] at h1
    simp only [Equiv.Perm.coe_one, id_eq]
    omega
  · intro y hy
    rw [key_lt] at hy
    simp only at hy
    rw [mon_apply, mon_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine if_congr ?_ rfl rfl
    rw [Equiv.Perm.one_apply]
    rcases lt_trichotomy i a with h | h | h
    · rw [hmin i h]
    · subst h
      constructor
      · rintro ⟨h1, h2⟩
        exfalso
        rcases hy with hy | ⟨_, hy⟩
        · rw [← h1] at hy; exact lt_irrefl _ hy
        · rw [← h2] at hy; exact absurd (hc hgt) (not_lt.2 hy.le)
      · rintro ⟨h1, h2⟩
        exfalso
        rcases hy with hy | ⟨_, hy⟩
        · rw [← h1] at hy; exact lt_irrefl _ hy
        · rw [← h2] at hy; exact lt_irrefl _ hy
    · have hlt : y.1 < r i := by
        rcases hy with hy | ⟨hy, _⟩
        · exact hy.trans (hr h)
        · rw [hy]; exact hr h
      constructor <;> rintro ⟨h1, _⟩ <;> exact absurd h1 hlt.ne'

/- English proof (translation)
Establish `hdet : ((genX k n).submatrix r c).det = ∑ π : Equiv.Perm (Fin m), C (((Equiv.Perm.sign π : ℤ) : k)) * monomial (mon r c π) (1 : k)`. Rewrite using `[← Matrix.det_transpose, Matrix.det_apply']`. Use `Finset.sum_congr rfl fun π _ => ?_` and prove the remaining obligations. Rewrite using `[map_intCast]`. Use `congr 1`.

Unfold `mon`. Rewrite using `[MvPolynomial.monomial_sum_one]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `[genX, Matrix.transpose_apply, Matrix.submatrix_apply, MvPolynomial.X]`. Establish `hcoeff : ∀ e, coeff e (((genX k n).submatrix r c).det) = ∑ π : Equiv.Perm (Fin m), ((Equiv.Perm.sign π : ℤ) : k) * (if mon r c π = e then (1 : k) else 0)`.

Introduce `e`. Rewrite using `[hdet, MvPolynomial.coeff_sum]`. Use `Finset.sum_congr rfl fun π _ => ?_` and prove the remaining obligations. Rewrite using `[MvPolynomial.coeff_C_mul, MvPolynomial.coeff_monomial]`. Prove the components needed by the constructor for the conclusion.

Rewrite using `[hcoeff, Finset.sum_eq_single 1]`. Simplify using the standard rewrite rules. Introduce `π _ hπ`. Rewrite using `[if_neg, mul_zero]`. Introduce `h`.

Use `mon_LL hr hc π hπ` as an intermediate fact. Rewrite `this` using `[h]`. Conclude with `LL_irrefl _ _ this`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.

Introduce `e he hne`. Rewrite `he` using `[MvPolynomial.mem_support_iff, hcoeff]`. Take `⟨π, -, hπ⟩` from `Finset.exists_ne_zero_of_sum_ne_zero he`. Establish `hπe : mon r c π = e`. Assume the negation of the conclusion as `h`.

Conclude with `hπ (by rw [if_neg h, mul_zero])`. Substitute `hπe` using the available equality. Apply `mon_LL hr hc π` to reduce the goal to its premises. Introduce and unpack `rfl`. Conclude with `hne rfl`.
-/
theorem Lead_det (k : Type*) [CommRing k] {m : ℕ} (r c : Fin m → Fin n) (hr : StrictMono r)
    (hc : StrictMono c) : Lead key (((genX k n).submatrix r c).det) (mon r c 1) := by
  classical
  have hdet : ((genX k n).submatrix r c).det =
      ∑ π : Equiv.Perm (Fin m), C (((Equiv.Perm.sign π : ℤ) : k)) * monomial (mon r c π) (1 : k) := by
    rw [← Matrix.det_transpose, Matrix.det_apply']
    refine Finset.sum_congr rfl fun π _ => ?_
    rw [map_intCast]
    congr 1
    unfold mon
    rw [MvPolynomial.monomial_sum_one]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp [genX, Matrix.transpose_apply, Matrix.submatrix_apply, MvPolynomial.X]
  have hcoeff : ∀ e, coeff e (((genX k n).submatrix r c).det) =
      ∑ π : Equiv.Perm (Fin m), ((Equiv.Perm.sign π : ℤ) : k) * (if mon r c π = e then (1 : k) else 0) := by
    intro e
    rw [hdet, MvPolynomial.coeff_sum]
    refine Finset.sum_congr rfl fun π _ => ?_
    rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_monomial]
  constructor
  · rw [hcoeff, Finset.sum_eq_single 1]
    · simp
    · intro π _ hπ
      rw [if_neg, mul_zero]
      intro h
      have := mon_LL hr hc π hπ
      rw [h] at this
      exact LL_irrefl _ _ this
    · intro h
      exact absurd (Finset.mem_univ _) h
  · intro e he hne
    rw [MvPolynomial.mem_support_iff, hcoeff] at he
    obtain ⟨π, -, hπ⟩ := Finset.exists_ne_zero_of_sum_ne_zero he
    have hπe : mon r c π = e := by
      by_contra h
      exact hπ (by rw [if_neg h, mul_zero])
    subst hπe
    apply mon_LL hr hc π
    rintro rfl
    exact hne rfl

/- English proof (translation)
Unfold `initSeg`. Rewrite using `[Fin.card_filter_val_lt]`. Conclude with `min_eq_right hh`.
-/
theorem card_initSeg {h : ℕ} (hh : h ≤ n) : (initSeg n h).card = h := by
  unfold initSeg
  rw [Fin.card_filter_val_lt]
  exact min_eq_right hh

/- English proof (translation)
Establish `hkh : k = h` using `by rw [← hk, card_initSeg hh]`. Establish `hlt : ∀ j : Fin k, j.val < n` using `fun j => by have := j.2; omega`. Use `Finset.orderEmbOfFin_unique hk (f := fun j : Fin k => (⟨j.val, hlt j⟩ : Fin n)) (fun j => by` as an intermediate fact. Unfold `initSeg`. Rewrite using `[Finset.mem_filter]`.

Conclude with `⟨Finset.mem_univ _, by have := j.2; simp only; omega⟩)`. Use the proof step `(fun j j' hjj => hjj)`. Rewrite using `[← congr_fun this i]`.
-/
theorem initSeg_emb {h k : ℕ} (hh : h ≤ n) (hk : (initSeg n h).card = k) (i : Fin k) :
    ((initSeg n h).orderEmbOfFin hk i).val = i.val := by
  have hkh : k = h := by rw [← hk, card_initSeg hh]
  have hlt : ∀ j : Fin k, j.val < n := fun j => by have := j.2; omega
  have := Finset.orderEmbOfFin_unique hk (f := fun j : Fin k => (⟨j.val, hlt j⟩ : Fin n))
    (fun j => by
      unfold initSeg
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by have := j.2; simp only; omega⟩)
    (fun j j' hjj => hjj)
  rw [← congr_fun this i]

/- English proof (translation)
Unfold `nthElt`. Rewrite using `[Finset.orderEmbOfFin_apply, List.getD_eq_getElem _ _ (by simp [h])]`. Simplify using the standard rewrite rules.
-/
theorem nthElt_emb {J : Finset (Fin n)} {k : ℕ} (h : J.card = k) (i : Fin k) :
    nthElt J i.val = (J.orderEmbOfFin h i).val := by
  unfold nthElt
  rw [Finset.orderEmbOfFin_apply, List.getD_eq_getElem _ _ (by simp [h])]
  simp

/- English proof (translation)
Unfold `nthElt`. Rewrite using `[List.getD_eq_default _ _ (by simpa using h)]`.
-/
theorem nthElt_ge {J : Finset (Fin n)} {a : ℕ} (h : J.card ≤ a) : nthElt J a = n := by
  unfold nthElt
  rw [List.getD_eq_default _ _ (by simpa using h)]

/- English proof (translation)
Distinguish the cases in `h : a < J.card`. Rewrite using `[show a = (⟨a, h⟩ : Fin J.card).val from rfl, nthElt_emb rfl]`. Conclude with `(Fin.is_lt _).le`. Rewrite using `[nthElt_ge (not_lt.1 h)]`.
-/
theorem nthElt_le (J : Finset (Fin n)) (a : ℕ) : nthElt J a ≤ n := by
  by_cases h : a < J.card
  · rw [show a = (⟨a, h⟩ : Fin J.card).val from rfl, nthElt_emb rfl]
    exact (Fin.is_lt _).le
  · rw [nthElt_ge (not_lt.1 h)]

/- English proof (translation)
Assume the negation of the conclusion as `hc`. Rewrite `h` using `[nthElt_ge (not_lt.1 hc)]`. Conclude with `lt_irrefl _ h`.
-/
theorem lt_card_of_nthElt {J : Finset (Fin n)} {a : ℕ} (h : nthElt J a < n) : a < J.card := by
  by_contra hc
  rw [nthElt_ge (not_lt.1 hc)] at h
  exact lt_irrefl _ h

/- English proof (translation)
Establish `hle : J.card ≤ n` using `by simpa using Finset.card_le_univ J`. Prove the components needed by the constructor for the conclusion. Introduce `hb`. Establish `: b ∈ Set.range (J.orderEmbOfFin rfl)` using `by rw [Finset.range_orderEmbOfFin]; exact hb`. Take `⟨i, hi⟩` from `this`.

Use `⟨⟨i.val, lt_of_lt_of_le i.2 hle⟩, ?_⟩` and prove the remaining obligations. Simplify using `only`. Rewrite using `[nthElt_emb rfl i, hi]`. Introduce and unpack `⟨a, ha⟩`. Establish `hlt : a.val < J.card` using `lt_card_of_nthElt (by rw [ha]; exact b.2)`.

Establish `h1` using `nthElt_emb (J := J) rfl ⟨a.val, hlt⟩`. Simplify using `only at h1`. Rewrite `h1` using `[ha]`. Rewrite using `[Fin.ext h1]`. Conclude with `Finset.orderEmbOfFin_mem _ _ _`.
-/
theorem mem_iff_nthElt (J : Finset (Fin n)) (b : Fin n) : b ∈ J ↔ ∃ a : Fin n, nthElt J a.val = b.val := by
  have hle : J.card ≤ n := by simpa using Finset.card_le_univ J
  constructor
  · intro hb
    have : b ∈ Set.range (J.orderEmbOfFin rfl) := by rw [Finset.range_orderEmbOfFin]; exact hb
    obtain ⟨i, hi⟩ := this
    refine ⟨⟨i.val, lt_of_lt_of_le i.2 hle⟩, ?_⟩
    simp only
    rw [nthElt_emb rfl i, hi]
  · rintro ⟨a, ha⟩
    have hlt : a.val < J.card := lt_card_of_nthElt (by rw [ha]; exact b.2)
    have h1 := nthElt_emb (J := J) rfl ⟨a.val, hlt⟩
    simp only at h1
    rw [ha] at h1
    rw [Fin.ext h1]
    exact Finset.orderEmbOfFin_mem _ _ _

def colDiag (J : Finset (Fin n)) : Fin n × Fin n →₀ ℕ :=
  ∑ b ∈ J, ∑ a : Fin n, if a.val = (J.filter (· < b)).card then Finsupp.single (a, b) 1 else 0

/- English proof (translation)
Use `conv_lhs => rw [← Finset.map_orderEmbOfFin_univ J h]`. Rewrite using `[Finset.sum_map]`. Both sides reduce to the same expression.
-/
theorem sum_emb {M : Type*} [AddCommMonoid M] (J : Finset (Fin n)) {k : ℕ} (h : J.card = k) (F : Fin n → M) :
    ∑ b ∈ J, F b = ∑ i : Fin k, F (J.orderEmbOfFin h i) := by
  conv_lhs => rw [← Finset.map_orderEmbOfFin_univ J h]
  rw [Finset.sum_map]
  rfl

/- English proof (translation)
Apply the tactic sequence `first | exact Bl.general_b_fact_right_further.goal1 .. | (apply Bl.general_b_fact_right_further.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_right_further.goal1 <;> assumption) | (apply @Bl.general_b_fact_right_further.goal1 <;> assumption) | (intros; apply @Bl.genera …`.
-/
theorem card_filter_lt_emb (J : Finset (Fin n)) {k : ℕ} (h : J.card = k) (i : Fin k) :
    (J.filter (· < J.orderEmbOfFin h i)).card = i.val := by
  first | exact Bl.general_b_fact_right_further.goal1 .. | (apply Bl.general_b_fact_right_further.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_right_further.goal1 <;> assumption) | (apply @Bl.general_b_fact_right_further.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_right_further.goal1 <;> assumption) | (apply @Bl.general_b_fact_right_further.goal1 <;> first | assumption | infer_instance) | exact @Bl.general_b_fact_right_further.goal1 n J k h i | exact @Bl.general_b_fact_right_further.goal1 n J k h | exact @Bl.general_b_fact_right_further.goal1 n J k | exact @Bl.general_b_fact_right_further.goal1 n J | exact @Bl.general_b_fact_right_further.goal1 n

/- English proof (translation)
Unfold `colDiag mon`. Rewrite using `[sum_emb J h]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[card_filter_lt_emb, Finset.sum_eq_single (r i)]`. Rewrite using `[if_pos (hr i), Equiv.Perm.one_apply]`.

Introduce `a _ ha`. Rewrite using `[if_neg]`. Introduce `hc`. Conclude with `ha (Fin.ext (by rw [hc, hr i]))`. Introduce `hc`.

Conclude with `absurd (Finset.mem_univ _) hc`.
-/
theorem colDiag_eq (J : Finset (Fin n)) {k : ℕ} (h : J.card = k) (r : Fin k → Fin n)
    (hr : ∀ i, (r i).val = i.val) : colDiag J = mon r (J.orderEmbOfFin h) 1 := by
  unfold colDiag mon
  rw [sum_emb J h]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [card_filter_lt_emb, Finset.sum_eq_single (r i)]
  · rw [if_pos (hr i), Equiv.Perm.one_apply]
  · intro a _ ha
    rw [if_neg]
    intro hc
    exact ha (Fin.ext (by rw [hc, hr i]))
  · intro hc
    exact absurd (Finset.mem_univ _) hc

/- English proof (translation)
Establish `hle : J.card ≤ n` using `by simpa using Finset.card_le_univ J`. Rewrite using `[colDiag_eq J rfl (fun i => (⟨i.val, lt_of_lt_of_le i.2 hle⟩ : Fin n)) (fun _ => rfl), mon_apply]`. Distinguish the cases in `hab : nthElt J a.val = b.val`. Rewrite using `[if_pos hab]`. Establish `ha : a.val < J.card` using `lt_card_of_nthElt (by rw [hab]; exact b.2)`.

Rewrite using `[Finset.sum_eq_single ⟨a.val, ha⟩]`. Rewrite using `[if_pos]`. Use `⟨Fin.ext rfl, ?_⟩` and prove the remaining obligations. Apply `Fin.ext` to reduce the goal to its premises. Rewrite using `[Equiv.Perm.one_apply]`.

Simplify using `only`. Rewrite using `[← hab]`. Conclude with `(nthElt_emb rfl ⟨a.val, ha⟩).symm`. Introduce `i _ hi`. Rewrite using `[if_neg]`.

Introduce and unpack `⟨h1, _⟩`. Establish `h3` using `congrArg Fin.val h1`. Conclude with `hi (Fin.ext h3)`. Introduce `hc`. Conclude with `absurd (Finset.mem_univ _) hc`.

Rewrite using `[if_neg hab]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `i _`. Rewrite using `[if_neg]`. Introduce and unpack `⟨h1, h2⟩`.

Apply `hab` to reduce the goal to its premises. Establish `h3 : a.val = i.val` using `(congrArg Fin.val h1).symm`. Rewrite using `[h3, nthElt_emb rfl i]`. Conclude with `congrArg Fin.val h2`.
-/
theorem colDiag_apply (J : Finset (Fin n)) (a b : Fin n) :
    colDiag J (a, b) = if nthElt J a.val = b.val then 1 else 0 := by
  have hle : J.card ≤ n := by simpa using Finset.card_le_univ J
  rw [colDiag_eq J rfl (fun i => (⟨i.val, lt_of_lt_of_le i.2 hle⟩ : Fin n)) (fun _ => rfl), mon_apply]
  by_cases hab : nthElt J a.val = b.val
  · rw [if_pos hab]
    have ha : a.val < J.card := lt_card_of_nthElt (by rw [hab]; exact b.2)
    rw [Finset.sum_eq_single ⟨a.val, ha⟩]
    · rw [if_pos]
      refine ⟨Fin.ext rfl, ?_⟩
      apply Fin.ext
      rw [Equiv.Perm.one_apply]
      simp only
      rw [← hab]
      exact (nthElt_emb rfl ⟨a.val, ha⟩).symm
    · intro i _ hi
      rw [if_neg]
      rintro ⟨h1, _⟩
      have h3 := congrArg Fin.val h1
      exact hi (Fin.ext h3)
    · intro hc
      exact absurd (Finset.mem_univ _) hc
  · rw [if_neg hab]
    apply Finset.sum_eq_zero
    intro i _
    rw [if_neg]
    rintro ⟨h1, h2⟩
    apply hab
    have h3 : a.val = i.val := (congrArg Fin.val h1).symm
    rw [h3, nthElt_emb rfl i]
    exact congrArg Fin.val h2

/- English proof (translation)
Establish `hle : J.card ≤ n` using `by simpa using Finset.card_le_univ J`. Establish `hcard : J.card = (initSeg n J.card).card` using `(card_initSeg hle).symm`. Unfold `minorF`. Rewrite using `[dif_pos hcard, colDiag_eq J hcard ((initSeg n J.card).orderEmbOfFin rfl) (fun i => initSeg_emb hle rfl i)]`. Conclude with `Lead_det k _ _ (OrderEmbedding.strictMono _) (OrderEmbedding.strictMono _)`.
-/
theorem Lead_minor (k : Type*) [CommRing k] (J : Finset (Fin n)) :
    Lead key (minorF (genX k n) (initSeg n J.card) J) (colDiag J) := by
  have hle : J.card ≤ n := by simpa using Finset.card_le_univ J
  have hcard : J.card = (initSeg n J.card).card := (card_initSeg hle).symm
  unfold minorF
  rw [dif_pos hcard, colDiag_eq J hcard ((initSeg n J.card).orderEmbOfFin rfl)
    (fun i => initSeg_emb hle rfl i)]
  exact Lead_det k _ _ (OrderEmbedding.strictMono _) (OrderEmbedding.strictMono _)

end Det

section Inj

variable {n C : ℕ}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem tabDiag_eq (T : Fin C → Finset (Fin n)) : tabDiag T = ∑ c, colDiag (T c) := rfl

/- English proof (translation)
Rewrite using `[tabDiag_eq, Finsupp.finsetSum_apply, Finset.card_filter]`. Conclude with `Finset.sum_congr rfl fun c _ => colDiag_apply _ _ _`.
-/
theorem tabDiag_apply (T : Fin C → Finset (Fin n)) (a b : Fin n) :
    tabDiag T (a, b) = (univ.filter fun c => nthElt (T c) a.val = b.val).card := by
  rw [tabDiag_eq, Finsupp.finsetSum_apply, Finset.card_filter]
  exact Finset.sum_congr rfl fun c _ => colDiag_apply _ _ _

/- English proof (translation)
Establish `step : ∀ c c' : Fin C, c.val + 1 = c'.val → nthElt (T c) a ≤ nthElt (T c') a`. Introduce `c c' h`. Distinguish the cases in `ha : a < (T c').card`. Conclude with `hT c c' h a ha`. Rewrite using `[nthElt_ge (not_lt.1 ha)]`.

Conclude with `nthElt_le _ _`. Establish `all : ∀ d : ℕ, ∀ c c' : Fin C, c.val + d = c'.val → nthElt (T c) a ≤ nthElt (T c') a`. Introduce `d`. Proceed by induction on `d with`. Consider the case `zero`.

Introduce `c c' h`. Establish `: c = c'` using `Fin.ext (by omega)`. Rewrite using `[this]`. Consider the case `succ d ih`. Introduce `c c' h`.

Establish `hlt : c.val + d < C` using `by have := c'.2; omega`. Conclude with `(ih c ⟨c.val + d, hlt⟩ rfl).trans (step ⟨c.val + d, hlt⟩ c' (by simp only; omega))`. Introduce `c c' hcc`. Establish `hle : c.val ≤ c'.val` using `hcc`. Conclude with `all (c'.val - c.val) c c' (by omega)`.
-/
theorem semi_mono {T : Fin C → Finset (Fin n)} (hT : SemiStd T) (a : ℕ) :
    Monotone fun c => nthElt (T c) a := by
  have step : ∀ c c' : Fin C, c.val + 1 = c'.val → nthElt (T c) a ≤ nthElt (T c') a := by
    intro c c' h
    by_cases ha : a < (T c').card
    · exact hT c c' h a ha
    · rw [nthElt_ge (not_lt.1 ha)]; exact nthElt_le _ _
  have all : ∀ d : ℕ, ∀ c c' : Fin C, c.val + d = c'.val → nthElt (T c) a ≤ nthElt (T c') a := by
    intro d
    induction d with
    | zero =>
      intro c c' h
      have : c = c' := Fin.ext (by omega)
      rw [this]
    | succ d ih =>
      intro c c' h
      have hlt : c.val + d < C := by have := c'.2; omega
      exact (ih c ⟨c.val + d, hlt⟩ rfl).trans (step ⟨c.val + d, hlt⟩ c' (by simp only; omega))
  intro c c' hcc
  have hle : c.val ≤ c'.val := hcc
  exact all (c'.val - c.val) c c' (by omega)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hc`. Establish `: Finset.Iic c ⊆ S` using `fun c' hc' => hS c hc c' (Finset.mem_Iic.1 hc')`. Use `Finset.card_le_card this` as an intermediate fact. Rewrite `this` using `[Fin.card_Iic]`.

Use linear arithmetic over natural numbers and integers. Introduce `hlt`. Assume the negation of the conclusion as `hc`. Establish `: S ⊆ Finset.Iio c`. Introduce `s hs`.

Rewrite using `[Finset.mem_Iio]`. Assume the negation of the conclusion as `hcs`. Conclude with `hc (hS s hs c (not_lt.1 hcs))`. Use `Finset.card_le_card this` as an intermediate fact. Rewrite `this` using `[Fin.card_Iio]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem lower_card (S : Finset (Fin C)) (hS : ∀ c ∈ S, ∀ c' ≤ c, c' ∈ S) (c : Fin C) :
    c ∈ S ↔ c.val < S.card := by
  constructor
  · intro hc
    have : Finset.Iic c ⊆ S := fun c' hc' => hS c hc c' (Finset.mem_Iic.1 hc')
    have := Finset.card_le_card this
    rw [Fin.card_Iic] at this
    omega
  · intro hlt
    by_contra hc
    have : S ⊆ Finset.Iio c := by
      intro s hs
      rw [Finset.mem_Iio]
      by_contra hcs
      exact hc (hS s hs c (not_lt.1 hcs))
    have := Finset.card_le_card this
    rw [Fin.card_Iio] at this
    omega

/- English proof (translation)
Establish `h1 : (univ.filter fun c => f c ≤ v).card = ∑ w ∈ Finset.range (v + 1), (univ.filter fun c => f c = w).card`. Rewrite using `[Finset.card_eq_sum_card_fiberwise (f := f) (t := Finset.range (v + 1))]`. Use `Finset.sum_congr rfl fun w hw => ?_` and prove the remaining obligations. Use `congr 1`. Use extensionality with `c`.

Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and]`. Prove the components needed by the constructor for the conclusion. Conclude with `fun h => h.2`. Introduce `h`. Conclude with `⟨by have := Finset.mem_range.1 hw; omega, h⟩`.

Introduce `c hc`. Simplify using `only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hc`. Simplify using `only [Finset.coe_range, Set.mem_Iio]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[← h1, ← lower_card]`.

Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and]`. Introduce `c hc c' hcc`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢`. Conclude with `(hf hcc).trans hc`.
-/
theorem mono_le_iff (f : Fin C → ℕ) (hf : Monotone f) (v : ℕ) (c : Fin C) :
    f c ≤ v ↔ c.val < ∑ w ∈ Finset.range (v + 1), (univ.filter fun c => f c = w).card := by
  classical
  have h1 : (univ.filter fun c => f c ≤ v).card =
      ∑ w ∈ Finset.range (v + 1), (univ.filter fun c => f c = w).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := f) (t := Finset.range (v + 1))]
    · refine Finset.sum_congr rfl fun w hw => ?_
      congr 1
      ext c
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · exact fun h => h.2
      · intro h
        exact ⟨by have := Finset.mem_range.1 hw; omega, h⟩
    · intro c hc
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hc
      simp only [Finset.coe_range, Set.mem_Iio]
      omega
  rw [← h1, ← lower_card]
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  · intro c hc c' hcc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
    exact (hf hcc).trans hc

/- English proof (translation)
Establish `hiff : ∀ v < n, ∀ c, f c ≤ v ↔ g c ≤ v`. Introduce `v hv c`. Rewrite using `[mono_le_iff f hf, mono_le_iff g hg]`. Rewrite using `[Finset.sum_congr rfl fun w hw => h w (by have := Finset.mem_range.1 hw; omega)]`. Use function extensionality and compare the values at `c`.

Establish `h1` using `hfn c`. Establish `h2` using `hgn c`. Distinguish the cases in `hfc : f c < n`. Establish `h3` using `(hiff (f c) hfc c).1 le_rfl`. Establish `h4` using `(hiff (g c) (by omega) c).2 le_rfl`.

Use linear arithmetic over natural numbers and integers. Distinguish the cases in `hgc : g c < n`. Establish `h4` using `(hiff (g c) hgc c).2 le_rfl`. Use linear arithmetic over natural numbers and integers. Use linear arithmetic over natural numbers and integers.
-/
theorem mono_eq_of_counts (f g : Fin C → ℕ) (hf : Monotone f) (hg : Monotone g) (hfn : ∀ c, f c ≤ n)
    (hgn : ∀ c, g c ≤ n)
    (h : ∀ v < n, (univ.filter fun c => f c = v).card = (univ.filter fun c => g c = v).card) : f = g := by
  have hiff : ∀ v < n, ∀ c, f c ≤ v ↔ g c ≤ v := by
    intro v hv c
    rw [mono_le_iff f hf, mono_le_iff g hg]
    rw [Finset.sum_congr rfl fun w hw => h w (by have := Finset.mem_range.1 hw; omega)]
  funext c
  have h1 := hfn c
  have h2 := hgn c
  by_cases hfc : f c < n
  · have h3 := (hiff (f c) hfc c).1 le_rfl
    have h4 := (hiff (g c) (by omega) c).2 le_rfl
    omega
  · by_cases hgc : g c < n
    · have h4 := (hiff (g c) hgc c).2 le_rfl
      omega
    · omega

/- English proof (translation)
Establish `hrow : ∀ a : Fin n, (fun c => nthElt (T c) a.val) = fun c => nthElt (T' c) a.val`. Introduce `a`. Apply `mono_eq_of_counts (n := n) _ _ (semi_mono hT a.val) (semi_mono hT' a.val) (fun c => nthElt_le _ _) (fun c => nthElt_le _ _)` to reduce the goal to its premises. Introduce `v hv`. Establish `h1` using `tabDiag_apply T a ⟨v, hv⟩`.

Establish `h2` using `tabDiag_apply T' a ⟨v, hv⟩`. Rewrite `h1` using `[h, h2]`. Conclude with `h1.symm`. Use function extensionality and compare the values at `c`. Use extensionality with `b`.

Rewrite using `[mem_iff_nthElt, mem_iff_nthElt]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, ha⟩`. Conclude with `⟨a, by rw [← ha]; exact (congr_fun (hrow a) c).symm⟩`. Introduce and unpack `⟨a, ha⟩`.

Conclude with `⟨a, by rw [← ha]; exact congr_fun (hrow a) c⟩`.
-/
theorem tab_inj {T T' : Fin C → Finset (Fin n)} (hT : SemiStd T) (hT' : SemiStd T')
    (h : tabDiag T = tabDiag T') : T = T' := by
  have hrow : ∀ a : Fin n, (fun c => nthElt (T c) a.val) = fun c => nthElt (T' c) a.val := by
    intro a
    apply mono_eq_of_counts (n := n) _ _ (semi_mono hT a.val) (semi_mono hT' a.val)
      (fun c => nthElt_le _ _) (fun c => nthElt_le _ _)
    intro v hv
    have h1 := tabDiag_apply T a ⟨v, hv⟩
    have h2 := tabDiag_apply T' a ⟨v, hv⟩
    rw [h, h2] at h1
    exact h1.symm
  funext c
  ext b
  rw [mem_iff_nthElt, mem_iff_nthElt]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, by rw [← ha]; exact (congr_fun (hrow a) c).symm⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, by rw [← ha]; exact congr_fun (hrow a) c⟩

/- English proof (translation)
Rewrite using `[tabDiag_eq]`. Unfold `tabMinors`. Conclude with `Lead_prod key_inj _ _ _ fun c _ => Lead_minor k (T c)`.
-/
theorem Lead_tab (k : Type*) [CommRing k] (T : Fin C → Finset (Fin n)) :
    Lead key (tabMinors k T) (tabDiag T) := by
  rw [tabDiag_eq]
  unfold tabMinors
  exact Lead_prod key_inj _ _ _ fun c _ => Lead_minor k (T c)

end Inj

end leadingTermLemmas

open leadingTermLemmas in
/- English proof (translation)
Introduce `k _ n C`. Use `linearIndependent_of_Lead key_inj _ (fun T => tabDiag T.1) ?_ (fun T => Lead_tab k T.1)` and prove the remaining obligations. Introduce `T T' h`. Conclude with `Subtype.ext (tab_inj T.2 T'.2 h)`.
-/
theorem path_basis_lemma : LemmaA := by
  intro k _ n C
  refine linearIndependent_of_Lead key_inj _ (fun T => tabDiag T.1) ?_ (fun T => Lead_tab k T.1)
  intro T T' h
  exact Subtype.ext (tab_inj T.2 T'.2 h)

end Formalism.InvariantFactorPaths.GelfandTsetlinBases
