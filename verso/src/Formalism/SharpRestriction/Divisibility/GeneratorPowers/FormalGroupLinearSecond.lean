import Formalism.SharpRestriction.Divisibility.GeneratorPowers.AevalDiagMonomial
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndFrFix
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThetaSwapFirstTwo
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GaugeBilinearTermEqNegDoubleSum

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp2

open MvPolynomial Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt FGLaw)

variable {S : Type} [CommRing S] {d : ℕ}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem jetSubstP_mk {κ κ' : Type} (m : ℕ) (φ : κ → MvPolynomial κ' S) (P : MvPolynomial κ S) :
    jetSubstP m φ (Ideal.Quotient.mk (orig S κ ^ (m + 1)) P) =
      Ideal.Quotient.mk (orig S κ' ^ (m + 1)) (aeval (fun i => φ i - C (constantCoeff (φ i))) P) := rfl

/- English proof (translation)
Rewrite using `[Ideal.Quotient.eq]`. Conclude with `Iff.rfl`.
-/
theorem mk_eq_iff {κ : Type} (m : ℕ) (a b : MvPolynomial κ S) :
    Ideal.Quotient.mk (orig S κ ^ (m + 1)) a = Ideal.Quotient.mk (orig S κ ^ (m + 1)) b ↔
      a - b ∈ Io S κ ^ (m + 1) := by
  rw [Ideal.Quotient.eq]
  exact Iff.rfl

/- English proof (translation)
Introduce `x hx`. Rewrite using `[MvPowerSeries.coeff_mul]`. Use `Finset.sum_eq_zero fun p hp => ?_` and prove the remaining obligations. Use `replace hp : p.1 + p.2 = x := by first`. Consider the case `exact Finset.HasAntidiagonal.mem_antidiagonal.1 hp`.

Consider the case `exact Finset.mem_antidiagonal.1 hp`. Consider the case `simpa using hp`. Establish `hdeg : p.1.degree + p.2.degree = x.degree`. Rewrite using `[← hp]`. Establish `e : ∀ y : τ →₀ ℕ, y.degree = y.sum (fun _ k => k)` using `fun y => by first`.

Consider the case `rfl`. Consider the case `simp [Finsupp.degree, Finsupp.sum]`. Rewrite using `[e, e, e, Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]`. Distinguish the cases in `h1 : p.1.degree < a`. Rewrite using `[hA _ h1, zero_mul]`.

Rewrite using `[hB _ (by omega), mul_zero]`.
-/
private theorem coeff_mul_eq_zero_lemma_4 {τ : Type} (A B : MvPowerSeries τ S) (a b : ℕ)
    (hA : ∀ x : τ →₀ ℕ, x.degree < a → MvPowerSeries.coeff x A = 0)
    (hB : ∀ x : τ →₀ ℕ, x.degree < b → MvPowerSeries.coeff x B = 0) :
    ∀ x : τ →₀ ℕ, x.degree < a + b → MvPowerSeries.coeff x (A * B) = 0 := by
  classical
  intro x hx
  rw [MvPowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun p hp => ?_
  replace hp : p.1 + p.2 = x := by
    first
      | exact Finset.HasAntidiagonal.mem_antidiagonal.1 hp
      | exact Finset.mem_antidiagonal.1 hp
      | simpa using hp
  have hdeg : p.1.degree + p.2.degree = x.degree := by
    rw [← hp]
    have e : ∀ y : τ →₀ ℕ, y.degree = y.sum (fun _ k => k) := fun y => by
      first
        | rfl
        | simp [Finsupp.degree, Finsupp.sum]
    rw [e, e, e, Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]
  by_cases h1 : p.1.degree < a
  · rw [hA _ h1, zero_mul]
  · rw [hB _ (by omega), mul_zero]

/- English proof (translation)
Establish `hpow : ∀ s (n : ℕ) (y : τ →₀ ℕ), y.degree < n → MvPowerSeries.coeff y (σ' s ^ n) = 0`. Introduce `s n`. Proceed by induction on `n with`. Consider the case `zero => intro y hy`. Use linear arithmetic over natural numbers and integers.

Consider the case `succ n ih`. Introduce `y hy`. Rewrite using `[pow_succ]`. Use `coeff_mul_eq_zero_lemma_4 _ _ n 1 ih ?_ y (by omega)` and prove the remaining obligations. Introduce `z hz`.

Establish `hz0 : z = 0` using `by first`. Consider the case `exact (Finsupp.degree_eq_zero_iff z).1 (by omega)`. Consider the case `exact Finsupp.degree_eq_zero_iff.1 (by omega)`. Rewrite using `[hz0, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hσ]`. Establish `hprod : ∀ (t : Finset τ') (y : τ →₀ ℕ), y.degree < ∑ s ∈ t, e s → MvPowerSeries.coeff y (∏ s ∈ t, σ' s ^ e s) = 0`.

Introduce `t`. Use `Finset.induction_on t ?_ ?_` and prove the remaining obligations. Introduce `y hy`. Simplify using `at hy`. Introduce `a t ha ih y hy`.

Rewrite using `[Finset.prod_insert ha]`. Rewrite `hy` using `[Finset.sum_insert ha]`. Conclude with `coeff_mul_eq_zero_lemma_4 _ _ (e a) (∑ s ∈ t, e s) (hpow a (e a)) ih y hy`. Establish `he : e.degree = ∑ s ∈ e.support, e s` using `by first`. Consider the case `rfl`.

Consider the case `simp [Finsupp.degree]`. Conclude with `hprod e.support x (he ▸ hx)`.
-/
private theorem order_prod_lemma_5 {τ τ' : Type} (σ' : τ' → MvPowerSeries τ S)
    (hσ : ∀ s, MvPowerSeries.constantCoeff (σ' s) = 0) (e : τ' →₀ ℕ) (x : τ →₀ ℕ)
    (hx : x.degree < e.degree) : MvPowerSeries.coeff x (e.prod fun s n => σ' s ^ n) = 0 := by
  classical
  have hpow : ∀ s (n : ℕ) (y : τ →₀ ℕ), y.degree < n → MvPowerSeries.coeff y (σ' s ^ n) = 0 := by
    intro s n
    induction n with
    | zero => intro y hy; omega
    | succ n ih =>
      intro y hy
      rw [pow_succ]
      refine coeff_mul_eq_zero_lemma_4 _ _ n 1 ih ?_ y (by omega)
      intro z hz
      have hz0 : z = 0 := by
        first
          | exact (Finsupp.degree_eq_zero_iff z).1 (by omega)
          | exact Finsupp.degree_eq_zero_iff.1 (by omega)
      rw [hz0, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hσ]
  have hprod : ∀ (t : Finset τ') (y : τ →₀ ℕ), y.degree < ∑ s ∈ t, e s →
      MvPowerSeries.coeff y (∏ s ∈ t, σ' s ^ e s) = 0 := by
    intro t
    refine Finset.induction_on t ?_ ?_
    · intro y hy
      simp at hy
    · intro a t ha ih y hy
      rw [Finset.prod_insert ha]
      rw [Finset.sum_insert ha] at hy
      exact coeff_mul_eq_zero_lemma_4 _ _ (e a) (∑ s ∈ t, e s) (hpow a (e a)) ih y hy
  have he : e.degree = ∑ s ∈ e.support, e s := by
    first
      | rfl
      | simp [Finsupp.degree]
  exact hprod e.support x (he ▸ hx)

/- English proof (translation)
Establish `h1 : ∑ i ∈ e.support, e i = 1` using `by first`. Consider the case `exact he`. Consider the case `simpa [Finsupp.degree] using he`. Choose the witnesses or unpack the hypotheses as in `⟨q, hq⟩ : e.support.Nonempty := by`. Rewrite using `[Finset.nonempty_iff_ne_empty]`.

Introduce `h`. Rewrite `h1` using `[h, Finset.sum_empty]`. Conclude with `zero_ne_one h1`. Establish `h2` using `Finset.add_sum_erase e.support e hq`. Rewrite `h2` using `[h1]`.

Establish `hq0 : e q ≠ 0` using `Finsupp.mem_support_iff.1 hq`. Establish `h3s : ∑ i ∈ e.support.erase q, e i = 0` using `by omega`. Establish `h3` using `Finset.sum_eq_zero_iff.1 h3s`. Use `⟨q, ?_⟩` and prove the remaining obligations. Use extensionality with `i`.

Distinguish the cases in `hi : i = q`. Substitute `hi` using the available equality. Rewrite using `[Finsupp.single_eq_same]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[Finsupp.single_apply, if_neg (Ne.symm hi)]`.

Assume the negation of the conclusion as `hne`. Conclude with `hne (h3 i (Finset.mem_erase.2 ⟨hi, Finsupp.mem_support_iff.2 hne⟩))`.
-/
private theorem eq_single_lemma_6 {κ : Type} (e : κ →₀ ℕ) (he : e.degree = 1) : ∃ q, e = Finsupp.single q 1 := by
  classical
  have h1 : ∑ i ∈ e.support, e i = 1 := by
    first
      | exact he
      | simpa [Finsupp.degree] using he
  obtain ⟨q, hq⟩ : e.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    rw [h, Finset.sum_empty] at h1
    exact zero_ne_one h1
  have h2 := Finset.add_sum_erase e.support e hq
  rw [h1] at h2
  have hq0 : e q ≠ 0 := Finsupp.mem_support_iff.1 hq
  have h3s : ∑ i ∈ e.support.erase q, e i = 0 := by omega
  have h3 := Finset.sum_eq_zero_iff.1 h3s
  refine ⟨q, ?_⟩
  ext i
  by_cases hi : i = q
  · subst hi
    rw [Finsupp.single_eq_same]
    omega
  · rw [Finsupp.single_apply, if_neg (Ne.symm hi)]
    by_contra hne
    exact hne (h3 i (Finset.mem_erase.2 ⟨hi, Finsupp.mem_support_iff.2 hne⟩))

/- English proof (translation)
Establish `key : ∀ f : PS S 2 d, MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1) (ev (n` using `1) ![0, pt S d 0] f) = MvPowerSeries.coeff (Finsupp.single ((1 : Fin 2), j) 1) f := by`. Introduce `f`. Unfold `ev`. Establish `hσ : ∀ s : Fin 2 × Fin d, MvPowerSeries.constantCoeff ((![0, pt S d 0] : Fin 2 → Pt S 1 d) s.1 s.2) = 0`. Introduce and unpack `⟨a, l⟩`.

Apply the tactic sequence `obtain rfl | rfl : a = 0 ∨ a = 1 := by fin_cases a <;> simp`. Simplify using the standard rewrite rules. Simplify using `[pt]`. Establish `hS : MvPowerSeries.HasSubst (fun s : Fin 2 × Fin d => (![0, pt S d 0] : Fin 2 → Pt S 1 d) s.1 s.2)` using `by first`. Consider the case `exact MvPowerSeries.HasSubst.of_constantCoeff_zero hσ`.

Consider the case `exact MvPowerSeries.hasSubst_of_constantCoeff_zero hσ`. Consider the case `exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent fun s => by rw [hσ s]; exact IsNilpotent.zero`. Consider the case `exact MvPowerSeries.hasSubst_of_constantCoeff_nilpotent fun s => by rw [hσ s]; exact IsNilpotent.zero`. Consider the case `exact ⟨fun s => by rw [hσ s]; exact IsNilpotent.zero, fun _ => Set.toFinite _⟩`. Rewrite using `[MvPowerSeries.coeff_subst hS]`.

Establish `hd1 : (Finsupp.single ((0 : Fin 1), j) 1).degree = 1` using `by first`. Consider the case `simp`. Consider the case `simp [Finsupp.degree]`. Rewrite using `[finsum_eq_single _ (Finsupp.single ((1 : Fin 2), j) 1)]`. Rewrite using `[Finsupp.prod_single_index (by simp)]`.

Simplify using `[pt, MvPowerSeries.coeff_X]`. Introduce `e he`. Break down `lt_trichotomy e.degree 1 with hlt | heq | hgt` into its components or cases. Establish `he0 : e = 0` using `by first`. Consider the case `exact (Finsupp.degree_eq_zero_iff e).1 (by omega)`.

Consider the case `exact Finsupp.degree_eq_zero_iff.1 (by omega)`. Substitute `he0` using the available equality. Simplify using `[MvPowerSeries.coeff_one]`. Take `⟨⟨q1, q2⟩, rfl⟩` from `eq_single_lemma_6 e heq`. Rewrite using `[Finsupp.prod_single_index (by simp)]`.

Apply the tactic sequence `obtain rfl | rfl : q1 = 0 ∨ q1 = 1 := by fin_cases q1 <;> simp`. Simplify using the standard rewrite rules. Establish `hq : q2 ≠ j` using `fun h => he (by rw [h])`. Simplify using `[pt, MvPowerSeries.coeff_X, Finsupp.single_left_inj one_ne_zero, hq, Ne.symm hq]`. Establish `h0` using `order_prod_lemma_5 _ hσ e (Finsupp.single ((0 : Fin 1), j) 1) (by omega) first`.

Consider the case `simp only [h0, smul_zero]`. Consider the case `rw [h0, smul_zero]`. Consider the case `erw [h0, smul_zero]`. Establish `hu` using `congrArg (MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1)) (G.unit i)`. Rewrite `hu` using `[key, MvPowerSeries.coeff_X]`.

Rewrite using `[hu]`. Distinguish the cases in `h : j = i`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Finsupp.single_left_inj one_ne_zero, h]`.
-/
theorem formal_group_linear_second (G : FGLaw S d) (i j : Fin d) :
    MvPowerSeries.coeff (Finsupp.single ((1 : Fin 2), j) 1) (G.F i) = if j = i then 1 else 0 := by
  have key : ∀ f : PS S 2 d, MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1)
      (ev (n := 1) ![0, pt S d 0] f) = MvPowerSeries.coeff (Finsupp.single ((1 : Fin 2), j) 1) f := by
    intro f
    unfold ev
    have hσ : ∀ s : Fin 2 × Fin d, MvPowerSeries.constantCoeff
        ((![0, pt S d 0] : Fin 2 → Pt S 1 d) s.1 s.2) = 0 := by
      rintro ⟨a, l⟩
      obtain rfl | rfl : a = 0 ∨ a = 1 := by fin_cases a <;> simp
      · simp
      · simp [pt]
    have hS : MvPowerSeries.HasSubst
        (fun s : Fin 2 × Fin d => (![0, pt S d 0] : Fin 2 → Pt S 1 d) s.1 s.2) := by
      first
        | exact MvPowerSeries.HasSubst.of_constantCoeff_zero hσ
        | exact MvPowerSeries.hasSubst_of_constantCoeff_zero hσ
        | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent fun s => by rw [hσ s]; exact IsNilpotent.zero
        | exact MvPowerSeries.hasSubst_of_constantCoeff_nilpotent fun s => by rw [hσ s]; exact IsNilpotent.zero
        | exact ⟨fun s => by rw [hσ s]; exact IsNilpotent.zero, fun _ => Set.toFinite _⟩
    rw [MvPowerSeries.coeff_subst hS]
    have hd1 : (Finsupp.single ((0 : Fin 1), j) 1).degree = 1 := by
      first
        | simp
        | simp [Finsupp.degree]
    rw [finsum_eq_single _ (Finsupp.single ((1 : Fin 2), j) 1)]
    · rw [Finsupp.prod_single_index (by simp)]
      simp [pt, MvPowerSeries.coeff_X]
    · intro e he
      rcases lt_trichotomy e.degree 1 with hlt | heq | hgt
      · have he0 : e = 0 := by
          first
            | exact (Finsupp.degree_eq_zero_iff e).1 (by omega)
            | exact Finsupp.degree_eq_zero_iff.1 (by omega)
        subst he0
        simp [MvPowerSeries.coeff_one]
      · obtain ⟨⟨q1, q2⟩, rfl⟩ := eq_single_lemma_6 e heq
        rw [Finsupp.prod_single_index (by simp)]
        obtain rfl | rfl : q1 = 0 ∨ q1 = 1 := by fin_cases q1 <;> simp
        · simp
        · have hq : q2 ≠ j := fun h => he (by rw [h])
          simp [pt, MvPowerSeries.coeff_X, Finsupp.single_left_inj one_ne_zero, hq, Ne.symm hq]
      · have h0 := order_prod_lemma_5 _ hσ e (Finsupp.single ((0 : Fin 1), j) 1) (by omega)
        first
          | simp only [h0, smul_zero]
          | rw [h0, smul_zero]
          | erw [h0, smul_zero]
  have hu := congrArg (MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1)) (G.unit i)
  rw [key, MvPowerSeries.coeff_X] at hu
  rw [hu]
  by_cases h : j = i
  · subst h
    simp
  · simp [Finsupp.single_left_inj one_ne_zero, h]

/- English proof (translation)
Establish `key : ∀ f : PS S 2 d, MvPowerSeries.coeff (Finsupp.single ((0 : Fin 2), j) 1) (ev (n` using `2) ![pt S d 1, pt S d 0] f) = MvPowerSeries.coeff (Finsupp.single ((1 : Fin 2), j) 1) f := by`. Introduce `f`. Unfold `ev`. Establish `hσ : ∀ s : Fin 2 × Fin d, MvPowerSeries.constantCoeff ((![pt S d 1, pt S d 0] : Fin 2 → Pt S 2 d) s.1 s.2) = 0`. Introduce and unpack `⟨a, l⟩`.

Apply the tactic sequence `obtain rfl | rfl : a = 0 ∨ a = 1 := by fin_cases a <;> simp`. Simplify using `[pt]`. Simplify using `[pt]`. Establish `hS : MvPowerSeries.HasSubst (fun s : Fin 2 × Fin d => (![pt S d 1, pt S d 0] : Fin 2 → Pt S 2 d) s.1 s.2)` using `by first`. Consider the case `exact MvPowerSeries.HasSubst.of_constantCoeff_zero hσ`.

Consider the case `exact MvPowerSeries.hasSubst_of_constantCoeff_zero hσ`. Consider the case `exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent fun s => by rw [hσ s]; exact IsNilpotent.zero`. Consider the case `exact MvPowerSeries.hasSubst_of_constantCoeff_nilpotent fun s => by rw [hσ s]; exact IsNilpotent.zero`. Consider the case `exact ⟨fun s => by rw [hσ s]; exact IsNilpotent.zero, fun _ => Set.toFinite _⟩`. Rewrite using `[MvPowerSeries.coeff_subst hS]`.

Establish `hd1 : (Finsupp.single ((0 : Fin 2), j) 1).degree = 1` using `by first`. Consider the case `simp`. Consider the case `simp [Finsupp.degree]`. Rewrite using `[finsum_eq_single _ (Finsupp.single ((1 : Fin 2), j) 1)]`. Rewrite using `[Finsupp.prod_single_index (by simp)]`.

Simplify using `[pt, MvPowerSeries.coeff_X]`. Introduce `e he`. Break down `lt_trichotomy e.degree 1 with hlt | heq | hgt` into its components or cases. Establish `he0 : e = 0` using `by first`. Consider the case `exact (Finsupp.degree_eq_zero_iff e).1 (by omega)`.

Consider the case `exact Finsupp.degree_eq_zero_iff.1 (by omega)`. Substitute `he0` using the available equality. Simplify using `[MvPowerSeries.coeff_one]`. Take `⟨⟨q1, q2⟩, rfl⟩` from `eq_single_lemma_6 e heq`. Rewrite using `[Finsupp.prod_single_index (by simp)]`.

Apply the tactic sequence `obtain rfl | rfl : q1 = 0 ∨ q1 = 1 := by fin_cases q1 <;> simp`. Simplify using `[pt, MvPowerSeries.coeff_X, Finsupp.single_left_inj one_ne_zero]`. Establish `hq : q2 ≠ j` using `fun h => he (by rw [h])`. Simplify using `[pt, MvPowerSeries.coeff_X, Finsupp.single_left_inj one_ne_zero, hq, Ne.symm hq]`. Establish `h0` using `order_prod_lemma_5 _ hσ e (Finsupp.single ((0 : Fin 2), j) 1) (by omega) first`.

Consider the case `simp only [h0, smul_zero]`. Consider the case `rw [h0, smul_zero]`. Consider the case `erw [h0, smul_zero]`. Establish `hc` using `congrArg (MvPowerSeries.coeff (Finsupp.single ((0 : Fin 2), j) 1)) (G.comm i)`. Rewrite `hc` using `[key]`.

Rewrite using `[← hc]`. Conclude with `formal_group_linear_second G i j`.
-/
theorem formal_group_linear_first (G : FGLaw S d) (i j : Fin d) :
    MvPowerSeries.coeff (Finsupp.single ((0 : Fin 2), j) 1) (G.F i) = if j = i then 1 else 0 := by
  have key : ∀ f : PS S 2 d, MvPowerSeries.coeff (Finsupp.single ((0 : Fin 2), j) 1)
      (ev (n := 2) ![pt S d 1, pt S d 0] f) = MvPowerSeries.coeff (Finsupp.single ((1 : Fin 2), j) 1) f := by
    intro f
    unfold ev
    have hσ : ∀ s : Fin 2 × Fin d, MvPowerSeries.constantCoeff
        ((![pt S d 1, pt S d 0] : Fin 2 → Pt S 2 d) s.1 s.2) = 0 := by
      rintro ⟨a, l⟩
      obtain rfl | rfl : a = 0 ∨ a = 1 := by fin_cases a <;> simp
      · simp [pt]
      · simp [pt]
    have hS : MvPowerSeries.HasSubst
        (fun s : Fin 2 × Fin d => (![pt S d 1, pt S d 0] : Fin 2 → Pt S 2 d) s.1 s.2) := by
      first
        | exact MvPowerSeries.HasSubst.of_constantCoeff_zero hσ
        | exact MvPowerSeries.hasSubst_of_constantCoeff_zero hσ
        | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent fun s => by rw [hσ s]; exact IsNilpotent.zero
        | exact MvPowerSeries.hasSubst_of_constantCoeff_nilpotent fun s => by rw [hσ s]; exact IsNilpotent.zero
        | exact ⟨fun s => by rw [hσ s]; exact IsNilpotent.zero, fun _ => Set.toFinite _⟩
    rw [MvPowerSeries.coeff_subst hS]
    have hd1 : (Finsupp.single ((0 : Fin 2), j) 1).degree = 1 := by
      first
        | simp
        | simp [Finsupp.degree]
    rw [finsum_eq_single _ (Finsupp.single ((1 : Fin 2), j) 1)]
    · rw [Finsupp.prod_single_index (by simp)]
      simp [pt, MvPowerSeries.coeff_X]
    · intro e he
      rcases lt_trichotomy e.degree 1 with hlt | heq | hgt
      · have he0 : e = 0 := by
          first
            | exact (Finsupp.degree_eq_zero_iff e).1 (by omega)
            | exact Finsupp.degree_eq_zero_iff.1 (by omega)
        subst he0
        simp [MvPowerSeries.coeff_one]
      · obtain ⟨⟨q1, q2⟩, rfl⟩ := eq_single_lemma_6 e heq
        rw [Finsupp.prod_single_index (by simp)]
        obtain rfl | rfl : q1 = 0 ∨ q1 = 1 := by fin_cases q1 <;> simp
        · simp [pt, MvPowerSeries.coeff_X, Finsupp.single_left_inj one_ne_zero]
        · have hq : q2 ≠ j := fun h => he (by rw [h])
          simp [pt, MvPowerSeries.coeff_X, Finsupp.single_left_inj one_ne_zero, hq, Ne.symm hq]
      · have h0 := order_prod_lemma_5 _ hσ e (Finsupp.single ((0 : Fin 2), j) 1) (by omega)
        first
          | simp only [h0, smul_zero]
          | rw [h0, smul_zero]
          | erw [h0, smul_zero]
  have hc := congrArg (MvPowerSeries.coeff (Finsupp.single ((0 : Fin 2), j) 1)) (G.comm i)
  rw [key] at hc
  rw [← hc]
  exact formal_group_linear_second G i j

/- English proof (translation)
Establish `h1 : ∑ i ∈ e.support, e i = 1` using `by first`. Consider the case `exact he`. Consider the case `simpa [Finsupp.degree] using he`. Choose the witnesses or unpack the hypotheses as in `⟨q, hq⟩ : e.support.Nonempty := by`. Rewrite using `[Finset.nonempty_iff_ne_empty]`.

Introduce `h`. Rewrite `h1` using `[h, Finset.sum_empty]`. Conclude with `zero_ne_one h1`. Establish `h2` using `Finset.add_sum_erase e.support e hq`. Rewrite `h2` using `[h1]`.

Establish `hq0 : e q ≠ 0` using `Finsupp.mem_support_iff.1 hq`. Establish `h3s : ∑ i ∈ e.support.erase q, e i = 0` using `by omega`. Establish `h3` using `Finset.sum_eq_zero_iff.1 h3s`. Use `⟨q, ?_⟩` and prove the remaining obligations. Use extensionality with `i`.

Distinguish the cases in `hi : i = q`. Substitute `hi` using the available equality. Rewrite using `[Finsupp.single_eq_same]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[Finsupp.single_apply, if_neg (Ne.symm hi)]`.

Assume the negation of the conclusion as `hne`. Conclude with `hne (h3 i (Finset.mem_erase.2 ⟨hi, Finsupp.mem_support_iff.2 hne⟩))`.
-/
theorem eq_single_of_degree_one {κ : Type} (e : κ →₀ ℕ) (he : e.degree = 1) : ∃ q, e = Finsupp.single q 1 := by
  classical
  have h1 : ∑ i ∈ e.support, e i = 1 := by
    first
      | exact he
      | simpa [Finsupp.degree] using he
  obtain ⟨q, hq⟩ : e.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    rw [h, Finset.sum_empty] at h1
    exact zero_ne_one h1
  have h2 := Finset.add_sum_erase e.support e hq
  rw [h1] at h2
  have hq0 : e q ≠ 0 := Finsupp.mem_support_iff.1 hq
  have h3s : ∑ i ∈ e.support.erase q, e i = 0 := by omega
  have h3 := Finset.sum_eq_zero_iff.1 h3s
  refine ⟨q, ?_⟩
  ext i
  by_cases hi : i = q
  · subst hi
    rw [Finsupp.single_eq_same]
    omega
  · rw [Finsupp.single_apply, if_neg (Ne.symm hi)]
    by_contra hne
    exact hne (h3 i (Finset.mem_erase.2 ⟨hi, Finsupp.mem_support_iff.2 hne⟩))

/- English proof (translation)
Establish `hle : ∀ i, x i ≤ n`. Introduce `i`. Distinguish the cases in `hi : x i = 0`. Rewrite using `[hi]`. Conclude with `Nat.zero_le n`.

Conclude with `le_trans (Finset.single_le_sum (f := fun j => x j) (fun j _ => Nat.zero_le (x j)) (Finsupp.mem_support_iff.2 hi)) hx`. Unfold `degLE`. Rewrite using `[Finset.mem_filter, Finset.mem_image]`. Use `⟨⟨fun i => ⟨x i, Nat.lt_succ_of_le (hle i)⟩, Finset.mem_univ _, ?_⟩, hx⟩` and prove the remaining obligations. Use extensionality with `i`.

Simplify using the standard rewrite rules.
-/
private theorem mem_degLE_lemma {κ : Type} [Fintype κ] [DecidableEq κ] {n : ℕ} {x : κ →₀ ℕ}
    (hx : x.degree ≤ n) : x ∈ degLE n := by
  have hle : ∀ i, x i ≤ n := by
    intro i
    by_cases hi : x i = 0
    · rw [hi]
      exact Nat.zero_le n
    · exact le_trans (Finset.single_le_sum (f := fun j => x j) (fun j _ => Nat.zero_le (x j))
        (Finsupp.mem_support_iff.2 hi)) hx
  unfold degLE
  rw [Finset.mem_filter, Finset.mem_image]
  refine ⟨⟨fun i => ⟨x i, Nat.lt_succ_of_le (hle i)⟩, Finset.mem_univ _, ?_⟩, hx⟩
  ext i
  simp

/- English proof (translation)
Unfold `psTrunc`. Rewrite using `[coeff_sum]`. Simplify using `only [coeff_monomial, Finset.sum_ite_eq', Finset.sum_ite_eq]`. Distinguish the cases in `h : x.degree ≤ n`. Rewrite using `[if_pos (mem_degLE_lemma h), if_pos h]`.

Establish `h' : x ∉ degLE n`. Introduce `h'`. Unfold `degLE at h'`. Conclude with `h (Finset.mem_filter.1 h').2`. Rewrite using `[if_neg h', if_neg h]`.
-/
private theorem coeff_psTrunc_lemma_2 {κ : Type} [Fintype κ] [DecidableEq κ] (f : MvPowerSeries κ S) (n : ℕ)
    (x : κ →₀ ℕ) : coeff x (psTrunc n f) = if x.degree ≤ n then MvPowerSeries.coeff x f else 0 := by
  unfold psTrunc
  rw [coeff_sum]
  simp only [coeff_monomial, Finset.sum_ite_eq', Finset.sum_ite_eq]
  by_cases h : x.degree ≤ n
  · rw [if_pos (mem_degLE_lemma h), if_pos h]
  · have h' : x ∉ degLE n := by
      intro h'
      unfold degLE at h'
      exact h (Finset.mem_filter.1 h').2
    rw [if_neg h', if_neg h]

/- English proof (translation)
Establish `hX : ∀ i, (X i : MvPolynomial κ S) ∈ Io S κ` using `fun i => Ideal.subset_span ⟨i, rfl⟩`. Rewrite using `[p.as_sum]`. Use `Ideal.sum_mem _ fun x hx => ?_` and prove the remaining obligations. Rewrite using `[monomial_eq]`. Use `Ideal.mul_mem_left _ _ ?_` and prove the remaining obligations.

Establish `h2 : x.degree = ∑ a ∈ x.support, x a` using `by first`. Consider the case `rfl`. Consider the case `simp [Finsupp.degree]`. Establish `h1 : (x.prod fun n e => (X n : MvPolynomial κ S) ^ e) ∈ Io S κ ^ x.degree`. Unfold `Finsupp.prod`.

Rewrite using `[h2, ← Finset.prod_pow_eq_pow_sum]`. Conclude with `Ideal.prod_mem_prod fun a _ => Ideal.pow_mem_pow (hX a) _`. Conclude with `Ideal.pow_le_pow_right (hp x hx) h1`.
-/
private theorem mem_pow_Io_lemma_3 {κ : Type} (k : ℕ) (p : MvPolynomial κ S)
    (hp : ∀ x ∈ p.support, k ≤ x.degree) : p ∈ Io S κ ^ k := by
  have hX : ∀ i, (X i : MvPolynomial κ S) ∈ Io S κ := fun i => Ideal.subset_span ⟨i, rfl⟩
  rw [p.as_sum]
  refine Ideal.sum_mem _ fun x hx => ?_
  rw [monomial_eq]
  refine Ideal.mul_mem_left _ _ ?_
  have h2 : x.degree = ∑ a ∈ x.support, x a := by
    first
      | rfl
      | simp [Finsupp.degree]
  have h1 : (x.prod fun n e => (X n : MvPolynomial κ S) ^ e) ∈ Io S κ ^ x.degree := by
    unfold Finsupp.prod
    rw [h2, ← Finset.prod_pow_eq_pow_sum]
    exact Ideal.prod_mem_prod fun a _ => Ideal.pow_mem_pow (hX a) _
  exact Ideal.pow_le_pow_right (hp x hx) h1

/- English proof (translation)
Apply `mem_pow_Io_lemma_3` to reduce the goal to its premises. Introduce `x hx`. Rewrite `hx` using `[mem_support_iff, coeff_sub, coeff_psTrunc_lemma_2]`. Assume the negation of the conclusion as `hlt`. Establish `h1 : x.degree ≤ 1` using `by omega`.

Rewrite `hx` using `[if_pos (h1.trans hm)]`. Apply `hx` to reduce the goal to its premises. Break down `Nat.le_one_iff_eq_zero_or_eq_one.1 h1 with h0 | h0` into its components or cases. Establish `hx0 : x = 0` using `by first`. Consider the case `exact (Finsupp.degree_eq_zero_iff x).1 h0`.

Consider the case `exact Finsupp.degree_eq_zero_iff.1 h0`. Substitute `hx0` using the available equality. Simplify using `[coeff_X', MvPowerSeries.coeff_zero_eq_constantCoeff_apply, G.const]`. Take `⟨⟨q1, q2⟩, rfl⟩` from `eq_single_of_degree_one x h0`. Apply the tactic sequence `obtain rfl | rfl : q1 = 0 ∨ q1 = 1 := by fin_cases q1 <;> simp`.

Distinguish the cases in `hq : q2 = j`. Substitute `hq` using the available equality. Simplify using `[coeff_X', formal_group_linear_first, Finsupp.single_left_inj one_ne_zero]`. Simplify using `[coeff_X', formal_group_linear_first, Finsupp.single_left_inj one_ne_zero, hq, Ne.symm hq]`. Distinguish the cases in `hq : q2 = j`.

Substitute `hq` using the available equality. Simplify using `[coeff_X', formal_group_linear_second, Finsupp.single_left_inj one_ne_zero]`. Simplify using `[coeff_X', formal_group_linear_second, Finsupp.single_left_inj one_ne_zero, hq, Ne.symm hq]`.
-/
theorem psTrunc_law_sub_mem (G : FGLaw S d) {m : ℕ} (hm : 1 ≤ m) (j : Fin d) :
    psTrunc m (G.F j) - (X ((0 : Fin 2), j) + X ((1 : Fin 2), j)) ∈ Io S (Fin 2 × Fin d) ^ 2 := by
  apply mem_pow_Io_lemma_3
  intro x hx
  rw [mem_support_iff, coeff_sub, coeff_psTrunc_lemma_2] at hx
  by_contra hlt
  have h1 : x.degree ≤ 1 := by omega
  rw [if_pos (h1.trans hm)] at hx
  apply hx
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 h1 with h0 | h0
  · have hx0 : x = 0 := by
      first
        | exact (Finsupp.degree_eq_zero_iff x).1 h0
        | exact Finsupp.degree_eq_zero_iff.1 h0
    subst hx0
    simp [coeff_X', MvPowerSeries.coeff_zero_eq_constantCoeff_apply, G.const]
  · obtain ⟨⟨q1, q2⟩, rfl⟩ := eq_single_of_degree_one x h0
    obtain rfl | rfl : q1 = 0 ∨ q1 = 1 := by fin_cases q1 <;> simp
    · by_cases hq : q2 = j
      · subst hq
        simp [coeff_X', formal_group_linear_first, Finsupp.single_left_inj one_ne_zero]
      · simp [coeff_X', formal_group_linear_first, Finsupp.single_left_inj one_ne_zero, hq, Ne.symm hq]
    · by_cases hq : q2 = j
      · subst hq
        simp [coeff_X', formal_group_linear_second, Finsupp.single_left_inj one_ne_zero]
      · simp [coeff_X', formal_group_linear_second, Finsupp.single_left_inj one_ne_zero, hq, Ne.symm hq]

def bil (M : Fin d → Fin d → S) : MvPolynomial (Fin 2 × Fin d) S :=
  ∑ i, ∑ l, C (M i l) * (X ((0 : Fin 2), i) * X ((1 : Fin 2), l))

abbrev sil (i l : Fin d) : Fin 2 × Fin d →₀ ℕ := Finsupp.single ((0 : Fin 2), i) 1 + Finsupp.single ((1 : Fin 2), l) 1

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h1` using `DFunLike.congr_fun h ((0 : Fin 2), i)`. Establish `h2` using `DFunLike.congr_fun h ((1 : Fin 2), l)`. Prove the components needed by the constructor for the conclusion.

Assume the negation of the conclusion as `hne`. Simplify using `[sil, Finsupp.single_apply, hne, Ne.symm hne] at h1`. Assume the negation of the conclusion as `hne`. Simplify using `[sil, Finsupp.single_apply, hne, Ne.symm hne] at h2`. Introduce and unpack `⟨rfl, rfl⟩`.

Both sides reduce to the same expression.
-/
theorem sil_inj {i l i0 l0 : Fin d} : sil i l = sil i0 l0 ↔ i = i0 ∧ l = l0 := by
  constructor
  · intro h
    have h1 := DFunLike.congr_fun h ((0 : Fin 2), i)
    have h2 := DFunLike.congr_fun h ((1 : Fin 2), l)
    constructor
    · by_contra hne
      simp [sil, Finsupp.single_apply, hne, Ne.symm hne] at h1
    · by_contra hne
      simp [sil, Finsupp.single_apply, hne, Ne.symm hne] at h2
  · rintro ⟨rfl, rfl⟩
    rfl

/- English proof (translation)
Rewrite using `[MvPolynomial.X, MvPolynomial.X, MvPolynomial.monomial_mul, one_mul, MvPolynomial.coeff_monomial]`.
-/
theorem coeff_XX (e : Fin 2 × Fin d →₀ ℕ) (i l : Fin d) :
    coeff e (X ((0 : Fin 2), i) * X ((1 : Fin 2), l) : MvPolynomial (Fin 2 × Fin d) S) =
      if sil i l = e then 1 else 0 := by
  rw [MvPolynomial.X, MvPolynomial.X, MvPolynomial.monomial_mul, one_mul, MvPolynomial.coeff_monomial]

/- English proof (translation)
Simplify using `only [bil, coeff_sum, coeff_C_mul, coeff_XX, sil_inj]`. Rewrite using `[Finset.sum_eq_single i0]`. Rewrite using `[Finset.sum_eq_single l0]`. Rewrite using `[if_pos ⟨rfl, rfl⟩, mul_one]`. Introduce `l _ hl`.

Simplify using `[hl]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Introduce `i _ hi`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises.

Introduce `l _`. Simplify using `[hi]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
theorem coeff_bil (M : Fin d → Fin d → S) (i0 l0 : Fin d) : coeff (sil i0 l0) (bil M) = M i0 l0 := by
  simp only [bil, coeff_sum, coeff_C_mul, coeff_XX, sil_inj]
  rw [Finset.sum_eq_single i0]
  · rw [Finset.sum_eq_single l0]
    · rw [if_pos ⟨rfl, rfl⟩, mul_one]
    · intro l _ hl
      simp [hl]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · intro i _ hi
    apply Finset.sum_eq_zero
    intro l _
    simp [hi]
  · intro h
    exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Use function extensionality and compare the values at `i l`. Establish `h'` using `congrArg (coeff (sil i l)) h`. Rewrite `h'` using `[coeff_bil, coeff_bil]`. Conclude with `h'`.
-/
theorem bil_ext {M M' : Fin d → Fin d → S} (h : bil M = bil M') : M = M' := by
  funext i l
  have h' := congrArg (coeff (sil i l)) h
  rw [coeff_bil, coeff_bil] at h'
  exact h'

/- English proof (translation)
Establish `hX : ∀ p, (X p : MvPolynomial (Fin 2 × Fin d) S) ∈ Io S (Fin 2 × Fin d)` using `fun p => Ideal.subset_span ⟨p, rfl⟩`. Use `Ideal.sum_mem _ fun i _ => Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ ?_` and prove the remaining obligations. Rewrite using `[pow_two]`. Conclude with `Ideal.mul_mem_mul (hX _) (hX _)`.
-/
theorem bil_mem (M : Fin d → Fin d → S) : bil M ∈ Io S (Fin 2 × Fin d) ^ 2 := by
  have hX : ∀ p, (X p : MvPolynomial (Fin 2 × Fin d) S) ∈ Io S (Fin 2 × Fin d) :=
    fun p => Ideal.subset_span ⟨p, rfl⟩
  refine Ideal.sum_mem _ fun i _ => Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ ?_
  rw [pow_two]
  exact Ideal.mul_mem_mul (hX _) (hX _)

/- English proof (translation)
Unfold `bil`. Use `IsHomogeneous.sum _ _ _ fun i _ => IsHomogeneous.sum _ _ _ fun l _ => ?_` and prove the remaining obligations. Establish `h0 : (C (M i l) : MvPolynomial (Fin 2 × Fin d) S).IsHomogeneous 0` using `by first`. Consider the case `exact isHomogeneous_C _ _`. Consider the case `exact isHomogeneous_C _`.

Establish `h1 : (X ((0 : Fin 2), i) : MvPolynomial (Fin 2 × Fin d) S).IsHomogeneous 1` using `by first`. Consider the case `exact isHomogeneous_X _ _`. Consider the case `exact isHomogeneous_X _`. Establish `h2 : (X ((1 : Fin 2), l) : MvPolynomial (Fin 2 × Fin d) S).IsHomogeneous 1` using `by first`. Consider the case `exact isHomogeneous_X _ _`.

Consider the case `exact isHomogeneous_X _`. Simplify using `using h0.mul (h1.mul h2)`.
-/
theorem bil_hom (M : Fin d → Fin d → S) : (bil M).IsHomogeneous 2 := by
  unfold bil
  refine IsHomogeneous.sum _ _ _ fun i _ => IsHomogeneous.sum _ _ _ fun l _ => ?_
  have h0 : (C (M i l) : MvPolynomial (Fin 2 × Fin d) S).IsHomogeneous 0 := by
    first
      | exact isHomogeneous_C _ _
      | exact isHomogeneous_C _
  have h1 : (X ((0 : Fin 2), i) : MvPolynomial (Fin 2 × Fin d) S).IsHomogeneous 1 := by
    first
      | exact isHomogeneous_X _ _
      | exact isHomogeneous_X _
  have h2 : (X ((1 : Fin 2), l) : MvPolynomial (Fin 2 × Fin d) S).IsHomogeneous 1 := by
    first
      | exact isHomogeneous_X _ _
      | exact isHomogeneous_X _
  simpa using h0.mul (h1.mul h2)

/- English proof (translation)
Apply `mem_pow_Io_lemma_3` to reduce the goal to its premises. Introduce `x hx`. Rewrite `hx` using `[mem_support_iff, coeff_sub, coeff_psTrunc_lemma_2, coeff_psTrunc_lemma_2]`. Assume the negation of the conclusion as `hlt`. Establish `h1 : x.degree ≤ k` using `by omega`.

Rewrite `hx` using `[if_pos (h1.trans hkm), if_pos h1, sub_self]`. Conclude with `hx rfl`.
-/
theorem psTrunc_sub_mem {κ : Type} [Fintype κ] [DecidableEq κ] (f : MvPowerSeries κ S) {k m : ℕ} (hkm : k ≤ m) :
    psTrunc m f - psTrunc k f ∈ Io S κ ^ (k + 1) := by
  apply mem_pow_Io_lemma_3
  intro x hx
  rw [mem_support_iff, coeff_sub, coeff_psTrunc_lemma_2, coeff_psTrunc_lemma_2] at hx
  by_contra hlt
  have h1 : x.degree ≤ k := by omega
  rw [if_pos (h1.trans hkm), if_pos h1, sub_self] at hx
  exact hx rfl

section Poly

variable [Algebra ℚ S]

open Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp1

/- English proof (translation)
Simplify using `[ev2, bil, map_sum, map_mul, aeval_C, aeval_X, algebraMap_eq]`.
-/
theorem eval_pair_bilinear {τ : Type} (M : Fin d → Fin d → S) (u v : Fin d → MvPolynomial τ S) :
    ev2 (bil M) u v = ∑ i, ∑ l, C (M i l) * (u i * v l) := by
  simp [ev2, bil, map_sum, map_mul, aeval_C, aeval_X, algebraMap_eq]

/- English proof (translation)
Establish `h1` using `const_one fF hF hph1 hu`. Establish `h2 : P - 1 ∈ Io S _ ^ 2` using `stepNo2 le_rfl (by omega) (by omega) fF hF hph1 hsym h1`. Take `⟨hA1, hs⟩` from `lead_biadd (j := 2) (by omega) hm fF hF hph1 hsym h2`. Establish `hb` using `bilin_of_biadd hA1 hs`. Use `set B := fun i l => coeff (sil i l) (homogeneousComponent 2 (P - 1)) with hB`.

Establish `hbB : homogeneousComponent 2 (P - 1) = bil B` using `hb`. Use `⟨h2, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← hbB]`. Conclude with `sub_homogeneousComponent_mem h2`. Establish `e1 : ev2 (bil B) (xs S d 1) (xs S d 0) = bil (fun i l => B l i)`.

Rewrite using `[eval_pair_bilinear, bil, Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Simplify using `only [xs]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `e1` using `[← hbB, hs, hbB]`.

Introduce `i l`. Use `congrFun (congrFun (bil_ext e1) i) l` as an intermediate fact. Conclude with `this`.
-/
theorem lead_bil {P : MvPolynomial (Fin 2 × Fin d) S} {m : ℕ} (hm : 2 ≤ m)
    (fF : Fin d → MvPolynomial (Fin 3 × Fin d) S)
    (hF : ∀ i, fF i - (xs S d 0 i + xs S d 1 i) ∈ Io S (Fin 3 × Fin d) ^ 2)
    (hph1 : ev2 P fF (xs S d 2) - ev2 P (xs S d 0) (xs S d 2) * ev2 P (xs S d 1) (xs S d 2) ∈
      Io S (Fin 3 × Fin d) ^ (m + 1))
    (hsym : ev2 P (xs S d 1) (xs S d 0) - P ∈ Io S (Fin 2 × Fin d) ^ (m + 1))
    (hu : IsUnit (coeff 0 P)) :
    P - 1 ∈ Io S (Fin 2 × Fin d) ^ 2 ∧
      P - 1 - bil (fun i l => coeff (sil i l) (homogeneousComponent 2 (P - 1))) ∈ Io S (Fin 2 × Fin d) ^ 3 ∧
      ∀ i l, coeff (sil i l) (homogeneousComponent 2 (P - 1)) = coeff (sil l i) (homogeneousComponent 2 (P - 1)) := by
  have h1 := const_one fF hF hph1 hu
  have h2 : P - 1 ∈ Io S _ ^ 2 := stepNo2 le_rfl (by omega) (by omega) fF hF hph1 hsym h1
  obtain ⟨hA1, hs⟩ := lead_biadd (j := 2) (by omega) hm fF hF hph1 hsym h2
  have hb := bilin_of_biadd hA1 hs
  set B := fun i l => coeff (sil i l) (homogeneousComponent 2 (P - 1)) with hB
  have hbB : homogeneousComponent 2 (P - 1) = bil B := hb
  refine ⟨h2, ?_, ?_⟩
  · rw [← hbB]; exact sub_homogeneousComponent_mem h2
  · have e1 : ev2 (bil B) (xs S d 1) (xs S d 0) = bil (fun i l => B l i) := by
      rw [eval_pair_bilinear, bil, Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
      simp only [xs]; ring
    rw [← hbB, hs, hbB] at e1
    intro i l
    have := congrFun (congrFun (bil_ext e1) i) l
    exact this

/- English proof (translation)
Establish `key : ∀ i l j, coeff (sil i0 l0) (C (B i l) * (C (A i j) * X ((0 : Fin 2), j) * X ((1 : Fin 2), l)) : MvPolynomial (Fin 2 × Fin d) S) = if j = i0 ∧ l = l0 then B i l * A i j else 0`. Introduce `i l j`. Rewrite using `[show (C (B i l) * (C (A i j) * X ((0 : Fin 2), j) * X ((1 : Fin 2), l)) : MvPolynomial (Fin 2 × Fin d) S) = C (B i l * A i j) * (X ((0 : Fin 2), j) * X ((1 : Fin 2), l)) by rw [map_mul]; ring]`. Rewrite using `[coeff_C_mul, coeff_XX]`. Distinguish the cases in `h : j = i0 ∧ l = l0`.

Rewrite using `[if_pos (sil_inj.2 h), if_pos h, mul_one]`. Rewrite using `[if_neg (fun h' => h (sil_inj.1 h')), if_neg h, mul_zero]`. Simplify using `only [PairEvaluation.lin, xs, Finset.sum_mul, Finset.mul_sum, coeff_sum, key]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_eq_single l0 (fun l _ hl => Finset.sum_eq_zero fun j _ => by simp [hl]) (by simp)]`.

Rewrite using `[Finset.sum_eq_single i0 (fun j _ hj => by simp [hj]) (by simp), if_pos ⟨rfl, rfl⟩, mul_comm]`.
-/
theorem coeff_linL (A B : Fin d → Fin d → S) (i0 l0 : Fin d) :
    coeff (sil i0 l0) (∑ i, ∑ l, C (B i l) * (PairEvaluation.lin A (0 : Fin 2) i * xs S d (1 : Fin 2) l)) =
      ∑ i, A i i0 * B i l0 := by
  have key : ∀ i l j, coeff (sil i0 l0) (C (B i l) * (C (A i j) * X ((0 : Fin 2), j) * X ((1 : Fin 2), l)) :
      MvPolynomial (Fin 2 × Fin d) S) = if j = i0 ∧ l = l0 then B i l * A i j else 0 := by
    intro i l j
    rw [show (C (B i l) * (C (A i j) * X ((0 : Fin 2), j) * X ((1 : Fin 2), l)) : MvPolynomial (Fin 2 × Fin d) S) =
      C (B i l * A i j) * (X ((0 : Fin 2), j) * X ((1 : Fin 2), l)) by rw [map_mul]; ring]
    rw [coeff_C_mul, coeff_XX]
    by_cases h : j = i0 ∧ l = l0
    · rw [if_pos (sil_inj.2 h), if_pos h, mul_one]
    · rw [if_neg (fun h' => h (sil_inj.1 h')), if_neg h, mul_zero]
  simp only [PairEvaluation.lin, xs, Finset.sum_mul, Finset.mul_sum, coeff_sum, key]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single l0 (fun l _ hl => Finset.sum_eq_zero fun j _ => by simp [hl]) (by simp)]
  rw [Finset.sum_eq_single i0 (fun j _ hj => by simp [hj]) (by simp), if_pos ⟨rfl, rfl⟩, mul_comm]

/- English proof (translation)
Establish `key : ∀ i l j, coeff (sil i0 l0) (C (B i l) * (X ((0 : Fin 2), i) * (C (Ab l j) * X ((1 : Fin 2), j))) : MvPolynomial (Fin 2 × Fin d) S) = if i = i0 ∧ j = l0 then B i l * Ab l j else 0`. Introduce `i l j`. Rewrite using `[show (C (B i l) * (X ((0 : Fin 2), i) * (C (Ab l j) * X ((1 : Fin 2), j))) : MvPolynomial (Fin 2 × Fin d) S) = C (B i l * Ab l j) * (X ((0 : Fin 2), i) * X ((1 : Fin 2), j)) by rw [map_mul]; ring]`. Rewrite using `[coeff_C_mul, coeff_XX]`. Distinguish the cases in `h : i = i0 ∧ j = l0`.

Rewrite using `[if_pos (sil_inj.2 h), if_pos h, mul_one]`. Rewrite using `[if_neg (fun h' => h (sil_inj.1 h')), if_neg h, mul_zero]`. Simplify using `only [PairEvaluation.lin, xs, Finset.sum_mul, Finset.mul_sum, coeff_sum, key]`. Rewrite using `[Finset.sum_eq_single i0 (fun i _ hi => Finset.sum_eq_zero fun l _ => Finset.sum_eq_zero fun j _ => by simp [hi]) (by simp)]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.sum_eq_single l0 (fun j _ hj => by simp [hj]) (by simp), if_pos ⟨rfl, rfl⟩]`.
-/
theorem coeff_linR (Ab B : Fin d → Fin d → S) (i0 l0 : Fin d) :
    coeff (sil i0 l0) (∑ i, ∑ l, C (B i l) * (xs S d (0 : Fin 2) i * PairEvaluation.lin Ab (1 : Fin 2) l)) =
      ∑ l, B i0 l * Ab l l0 := by
  have key : ∀ i l j, coeff (sil i0 l0) (C (B i l) * (X ((0 : Fin 2), i) * (C (Ab l j) * X ((1 : Fin 2), j))) :
      MvPolynomial (Fin 2 × Fin d) S) = if i = i0 ∧ j = l0 then B i l * Ab l j else 0 := by
    intro i l j
    rw [show (C (B i l) * (X ((0 : Fin 2), i) * (C (Ab l j) * X ((1 : Fin 2), j))) : MvPolynomial (Fin 2 × Fin d) S) =
      C (B i l * Ab l j) * (X ((0 : Fin 2), i) * X ((1 : Fin 2), j)) by rw [map_mul]; ring]
    rw [coeff_C_mul, coeff_XX]
    by_cases h : i = i0 ∧ j = l0
    · rw [if_pos (sil_inj.2 h), if_pos h, mul_one]
    · rw [if_neg (fun h' => h (sil_inj.1 h')), if_neg h, mul_zero]
  simp only [PairEvaluation.lin, xs, Finset.sum_mul, Finset.mul_sum, coeff_sum, key]
  rw [Finset.sum_eq_single i0 (fun i _ hi => Finset.sum_eq_zero fun l _ => Finset.sum_eq_zero fun j _ => by simp [hi]) (by simp)]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_eq_single l0 (fun j _ hj => by simp [hj]) (by simp), if_pos ⟨rfl, rfl⟩]

end Poly

section Act

open ReciprocityTheory.ChartRestriction.G.TB (dLin)

/- English proof (translation)
Apply `mem_pow_Io_lemma_3` to reduce the goal to its premises. Introduce `x hx`. Rewrite `hx` using `[mem_support_iff, coeff_sub, coeff_psTrunc_lemma_2]`. Assume the negation of the conclusion as `hlt`. Establish `h1 : x.degree ≤ 1` using `by omega`.

Rewrite `hx` using `[if_pos (h1.trans hm)]`. Apply `hx` to reduce the goal to its premises. Rewrite using `[coeff_sum]`. Break down `Nat.le_one_iff_eq_zero_or_eq_one.1 h1 with h0 | h0` into its components or cases. Establish `hx0 : x = 0` using `by first`.

Consider the case `exact (Finsupp.degree_eq_zero_iff x).1 h0`. Consider the case `exact Finsupp.degree_eq_zero_iff.1 h0`. Substitute `hx0` using the available equality. Simplify using `[coeff_C_mul, coeff_X', MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hφ]`. Take `⟨⟨q1, q2⟩, rfl⟩` from `eq_single_of_degree_one x h0`.

Establish `hq1 : q1 = 0` using `Subsingleton.elim _ _`. Substitute `hq1` using the available equality. Rewrite using `[Finset.sum_eq_single q2]`. Simplify using `[coeff_C_mul, coeff_X', dLin]`. Introduce `j _ hj`.

Simplify using `[coeff_C_mul, coeff_X', Finsupp.single_left_inj one_ne_zero, hj]`. Simplify using the standard rewrite rules.
-/
theorem psTrunc_act_sub_mem (φ : Fin d → PS S 1 d) (hφ : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0) {m : ℕ}
    (hm : 1 ≤ m) (i : Fin d) :
    psTrunc m (φ i) - ∑ j, C (dLin φ i j) * X ((0 : Fin 1), j) ∈ Io S (Fin 1 × Fin d) ^ 2 := by
  apply mem_pow_Io_lemma_3
  intro x hx
  rw [mem_support_iff, coeff_sub, coeff_psTrunc_lemma_2] at hx
  by_contra hlt
  have h1 : x.degree ≤ 1 := by omega
  rw [if_pos (h1.trans hm)] at hx
  apply hx
  rw [coeff_sum]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 h1 with h0 | h0
  · have hx0 : x = 0 := by
      first
        | exact (Finsupp.degree_eq_zero_iff x).1 h0
        | exact Finsupp.degree_eq_zero_iff.1 h0
    subst hx0
    simp [coeff_C_mul, coeff_X', MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hφ]
  · obtain ⟨⟨q1, q2⟩, rfl⟩ := eq_single_of_degree_one x h0
    have hq1 : q1 = 0 := Subsingleton.elim _ _
    subst hq1
    rw [Finset.sum_eq_single q2]
    · simp [coeff_C_mul, coeff_X', dLin]
    · intro j _ hj
      simp [coeff_C_mul, coeff_X', Finsupp.single_left_inj one_ne_zero, hj]
    · simp

/- English proof (translation)
Establish `hmap : ∀ q ∈ Io S (Fin 1 × Fin d) ^ 2, rename (fun p : Fin 1 × Fin d => ((![k] : Fin 1 → Fin 2) p.1, p.2)) q ∈ Io S (Fin 2 × Fin d) ^ 2`. Introduce `q hq`. Establish `hle : Ideal.map (rename (fun p : Fin 1 × Fin d => ((![k] : Fin 1 → Fin 2) p.1, p.2)) : MvPolynomial (Fin 1 × Fin d) S →ₐ[S] MvPolynomial (Fin 2 × Fin d) S) (Io S (Fin 1 × Fin d)) ≤ Io S (Fin 2 × Fin d)`. Rewrite using `[Ideal.map_le_iff_le_comap]`. Use `Ideal.span_le.2 ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨s, rfl⟩`. Rewrite using `[SetLike.mem_coe, Ideal.mem_comap, rename_X]`. Conclude with `Ideal.subset_span ⟨_, rfl⟩`. Establish `h2` using `Ideal.mem_map_of_mem (rename (fun p : Fin 1 × Fin d => ((![k] : Fin 1 → Fin 2) p.1, p.2)) : MvPolynomial (Fin 1 × Fin d) S →ₐ[S] MvPolynomial (Fin 2 × Fin d) S) hq`. Rewrite `h2` using `[Ideal.map_pow]`.

Conclude with `Ideal.pow_right_mono hle 2 h2`. Establish `h3` using `hmap _ (psTrunc_act_sub_mem φ hφ hm i)`. Establish `hc0 : constantCoeff (psIn d m ![k] (φ i)) = 0`. Rewrite using `[psIn, constantCoeff_rename]`. Establish `h0 : constantCoeff (psTrunc m (φ i)) = coeff 0 (psTrunc m (φ i))` using `by first`.

Consider the case `rfl`. Consider the case `simp [constantCoeff_eq]`. Rewrite using `[h0, coeff_psTrunc_lemma_2]`. Simplify using `[MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hφ]`. Use `h3 using 1` and compare the differences between its conclusion and the goal.

Rewrite using `[hc0, map_zero, sub_zero, map_sub]`. Use `congr 1`. Apply the tactic sequence `all_goals first`. Consider the case `rfl`. Consider the case `simp [PairEvaluation.lin, map_sum, rename_X, rename_C]`.
-/
theorem psIn_act_sub_mem (φ : Fin d → PS S 1 d) (hφ : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0) {m : ℕ}
    (hm : 1 ≤ m) (k : Fin 2) (i : Fin d) :
    psIn d m ![k] (φ i) - C (constantCoeff (psIn d m ![k] (φ i))) - PairEvaluation.lin (dLin φ) k i ∈
      Io S (Fin 2 × Fin d) ^ 2 := by
  have hmap : ∀ q ∈ Io S (Fin 1 × Fin d) ^ 2,
      rename (fun p : Fin 1 × Fin d => ((![k] : Fin 1 → Fin 2) p.1, p.2)) q ∈ Io S (Fin 2 × Fin d) ^ 2 := by
    intro q hq
    have hle : Ideal.map (rename (fun p : Fin 1 × Fin d => ((![k] : Fin 1 → Fin 2) p.1, p.2)) :
        MvPolynomial (Fin 1 × Fin d) S →ₐ[S] MvPolynomial (Fin 2 × Fin d) S) (Io S (Fin 1 × Fin d)) ≤
          Io S (Fin 2 × Fin d) := by
      rw [Ideal.map_le_iff_le_comap]
      refine Ideal.span_le.2 ?_
      rintro _ ⟨s, rfl⟩
      rw [SetLike.mem_coe, Ideal.mem_comap, rename_X]
      exact Ideal.subset_span ⟨_, rfl⟩
    have h2 := Ideal.mem_map_of_mem (rename (fun p : Fin 1 × Fin d => ((![k] : Fin 1 → Fin 2) p.1, p.2)) :
        MvPolynomial (Fin 1 × Fin d) S →ₐ[S] MvPolynomial (Fin 2 × Fin d) S) hq
    rw [Ideal.map_pow] at h2
    exact Ideal.pow_right_mono hle 2 h2
  have h3 := hmap _ (psTrunc_act_sub_mem φ hφ hm i)
  have hc0 : constantCoeff (psIn d m ![k] (φ i)) = 0 := by
    rw [psIn, constantCoeff_rename]
    have h0 : constantCoeff (psTrunc m (φ i)) = coeff 0 (psTrunc m (φ i)) := by
      first
        | rfl
        | simp [constantCoeff_eq]
    rw [h0, coeff_psTrunc_lemma_2]
    simp [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hφ]
  convert h3 using 1
  rw [hc0, map_zero, sub_zero, map_sub]
  congr 1
  all_goals first
    | rfl
    | simp [PairEvaluation.lin, map_sum, rename_X, rename_C]

end Act

end Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp2
