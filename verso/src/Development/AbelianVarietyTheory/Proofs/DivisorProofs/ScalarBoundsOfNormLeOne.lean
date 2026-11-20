import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ModelDdcForms
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms MeasureTheory
open scoped ContDiff

namespace GlobalTheory.Proof.ScalarPart

/- English proof (translation)
Proceed by induction on `hs using Finset.Nonempty.cons_induction with`. Consider the case `singleton a => simp`. Consider the case `cons a t ha ht ih`. Rewrite using `[Finset.sum_cons, Finset.prod_cons]`. Establish `hxa : 2 ≤ x a` using `hx a (Finset.mem_cons_self a t)`.

Establish `ht' : ∀ i ∈ t, 2 ≤ x i` using `fun i hi => hx i (Finset.mem_cons_of_mem hi)`. Establish `h1` using `ih ht'`. Take `⟨j, hj⟩` from `ht`. Establish `h2 : x j ≤ ∑ i ∈ t, x i` using `Finset.single_le_sum (fun i hi => by linarith [ht' i hi]) hj`. Establish `h3 : 2 ≤ ∏ i ∈ t, x i` using `by linarith [ht' j hj]`.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem sum_le_prod_of_two_le {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (x : ι → ℝ)
    (hx : ∀ i ∈ s, 2 ≤ x i) : ∑ i ∈ s, x i ≤ ∏ i ∈ s, x i := by
  classical
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a => simp
  | cons a t ha ht ih =>
    rw [Finset.sum_cons, Finset.prod_cons]
    have hxa : 2 ≤ x a := hx a (Finset.mem_cons_self a t)
    have ht' : ∀ i ∈ t, 2 ≤ x i := fun i hi => hx i (Finset.mem_cons_of_mem hi)
    have h1 := ih ht'
    obtain ⟨j, hj⟩ := ht
    have h2 : x j ≤ ∑ i ∈ t, x i :=
      Finset.single_le_sum (fun i hi => by linarith [ht' i hi]) hj
    have h3 : 2 ≤ ∏ i ∈ t, x i := by linarith [ht' j hj]
    nlinarith

end GlobalTheory.Proof.ScalarPart

open GlobalTheory.Proof.ScalarPart in

/- English proof (translation)
Introduce `X _ m L s D hle hne y hy`. Use `set n : Fin m → ℝ := fun i => normSec (L i) (s i) y with hn`. Establish `n0 : ∀ i, 0 ≤ n i` using `fun i => by`. Simplify using `only [hn, normSec]`. Check the signs of the components of the expression.

Establish `n1 : ∀ i, n i ≤ 1` using `fun i => hle i y`. Establish `nne : ∀ i, n i ≠ 0` using `hne y hy`. Use `set a : Fin m → ℝ := fun i => Real.log (n i ^ 2) with ha`. Establish `a0 : ∀ i, a i ≤ 0` using `fun i => Real.log_nonpos (sq_nonneg _) (pow_le_one₀ (n0 i) (n1 i))`. Establish `hrc : ∀ i, rComp L s i y = Real.exp 1 - a i` using `fun i => rfl`.

Establish `hrt : rTot L s y = Real.exp 1 - ∑ i, a i`. Simplify using `only [rTot, ha]`. Rewrite using `[← Finset.prod_pow, Real.log_prod]`. Introduce `i _`. Conclude with `pow_ne_zero _ (nne i)`.

Establish `he : (2 : ℝ) ≤ Real.exp 1`. Use `Real.add_one_le_exp (1 : ℝ)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hge : ∀ i, Real.exp 1 ≤ rComp L s i y` using `fun i => by rw [hrc]; linarith [a0 i]`. Establish `hle' : ∀ i, rComp L s i y ≤ rTot L s y` using `fun i => by`.

Rewrite using `[hrc, hrt]`. Establish `: ∑ l, a l ≤ a i`. Establish `h` using `Finset.single_le_sum (f := fun l => -a l) (fun l _ => by linarith [a0 l]) (Finset.mem_univ i)`. Simplify using `only [Finset.sum_neg_distrib] at h`. Combine the linear equalities and inequalities to obtain the conclusion.

Combine the linear equalities and inequalities to obtain the conclusion. Use `⟨hge, ?_, hle', ?_⟩` and prove the remaining obligations. Rewrite using `[hrt]`. Simplify using `only [hrc, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.

Introduce `hm`. Establish `hpos : ∀ i, 0 < rComp L s i y` using `fun i => by linarith [hge i]`. Establish `hrpos : 0 < rTot L s y`. Establish `i0 : Fin m` using `⟨0, hm⟩`. Combine the linear relations using `[hle' i0, hpos i0]`.

Prove the components needed by the constructor for the conclusion. Rewrite using `[← Real.log_prod (fun i _ => (hpos i).ne')]`. Apply `Real.log_le_log hrpos` to reduce the goal to its premises. Establish `hsum : rTot L s y ≤ ∑ i, rComp L s i y`. Rewrite using `[hrt]`.

Simplify using `only [hrc, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]`. Establish `: (1 : ℝ) ≤ m` using `by exact_mod_cast hm`. Use polynomial arithmetic with `[Real.exp_pos 1]`. Establish `hne' : (Finset.univ : Finset (Fin m)).Nonempty` using `⟨⟨0, hm⟩, Finset.mem_univ _⟩`. Conclude with `hsum.trans (sum_le_prod_of_two_le _ hne' _ (fun i _ => he.trans (hge i)))`.

Establish `: ∀ i ∈ (Finset.univ : Finset (Fin m)), Real.log (rComp L s i y) ≤ Real.log (rTot L s y)` using `fun i _ => Real.log_le_log (hpos i) (hle' i)`. Establish `h` using `Finset.sum_le_sum this`. Simplify `h` using `[Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]`.
-/
theorem GlobalTheory.Proof.scalarBounds_of_norm_le_one :
    ∀ {X : Type} [TopologicalSpace X] {m : ℕ} (L : Fin m → LocPot X) (s : Fin m → X → X → ℂ)
      (D : Fin m → Set X), (∀ i y, normSec (L i) (s i) y ≤ 1) →
      (∀ y, y ∉ ⋃ i, D i → ∀ i, normSec (L i) (s i) y ≠ 0) → ScalarBounds L s D := by
  intro X _ m L s D hle hne y hy
  set n : Fin m → ℝ := fun i => normSec (L i) (s i) y with hn
  have n0 : ∀ i, 0 ≤ n i := fun i => by
    simp only [hn, normSec]; positivity
  have n1 : ∀ i, n i ≤ 1 := fun i => hle i y
  have nne : ∀ i, n i ≠ 0 := hne y hy
  set a : Fin m → ℝ := fun i => Real.log (n i ^ 2) with ha
  have a0 : ∀ i, a i ≤ 0 := fun i =>
    Real.log_nonpos (sq_nonneg _) (pow_le_one₀ (n0 i) (n1 i))
  have hrc : ∀ i, rComp L s i y = Real.exp 1 - a i := fun i => rfl
  have hrt : rTot L s y = Real.exp 1 - ∑ i, a i := by
    simp only [rTot, ha]
    rw [← Finset.prod_pow, Real.log_prod]
    intro i _; exact pow_ne_zero _ (nne i)
  have he : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ); linarith
  have hge : ∀ i, Real.exp 1 ≤ rComp L s i y := fun i => by rw [hrc]; linarith [a0 i]
  have hle' : ∀ i, rComp L s i y ≤ rTot L s y := fun i => by
    rw [hrc, hrt]
    have : ∑ l, a l ≤ a i := by
      have h := Finset.single_le_sum (f := fun l => -a l) (fun l _ => by linarith [a0 l])
        (Finset.mem_univ i)
      simp only [Finset.sum_neg_distrib] at h
      linarith
    linarith
  refine ⟨hge, ?_, hle', ?_⟩
  · rw [hrt]; simp only [hrc, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    ring
  · intro hm
    have hpos : ∀ i, 0 < rComp L s i y := fun i => by linarith [hge i]
    have hrpos : 0 < rTot L s y := by
      have i0 : Fin m := ⟨0, hm⟩
      linarith [hle' i0, hpos i0]
    constructor
    · rw [← Real.log_prod (fun i _ => (hpos i).ne')]
      apply Real.log_le_log hrpos
      have hsum : rTot L s y ≤ ∑ i, rComp L s i y := by
        rw [hrt]; simp only [hrc, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul]
        have : (1 : ℝ) ≤ m := by exact_mod_cast hm
        nlinarith [Real.exp_pos 1]
      have hne' : (Finset.univ : Finset (Fin m)).Nonempty := ⟨⟨0, hm⟩, Finset.mem_univ _⟩
      exact hsum.trans (sum_le_prod_of_two_le _ hne' _ (fun i _ => he.trans (hge i)))
    · have : ∀ i ∈ (Finset.univ : Finset (Fin m)),
          Real.log (rComp L s i y) ≤ Real.log (rTot L s y) :=
        fun i _ => Real.log_le_log (hpos i) (hle' i)
      have h := Finset.sum_le_sum this
      simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using h
