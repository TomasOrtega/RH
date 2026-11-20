import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial

variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]

variable (ι) in

def blkW : (Σ k, ι k) → (K → ℕ) := fun p => Pi.single p.1 1

/- English proof (translation)
Rewrite using `[Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply, Fintype.sum_sigma]`. Simplify using `[blkW, Pi.single_apply]`.
-/
theorem weight_blkW (β : (Σ k, ι k) →₀ ℕ) (k : K) :
    Finsupp.weight (blkW ι) β k = ∑ i, β ⟨k, i⟩ := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply, Fintype.sum_sigma]
  simp [blkW, Pi.single_apply]

/- English proof (translation)
Introduce `d hd`. Rewrite `hd` using `[coeff_map]`. Establish `hs' : d ∈ s.support`. Rewrite using `[mem_support_iff]`. Introduce `h0`.

Apply `hd` to reduce the goal to its premises. Simplify using `[h0]`. Use function extensionality and compare the values at `k`. Rewrite using `[weight_blkW]`. Conclude with `hs d hs' k`.
-/
theorem isWeightedHomogeneous_map_of_isMultiHomog {s : MRing ι} {a : K → ℕ} (hs : IsMultiHomog s a) :
    IsWeightedHomogeneous (blkW ι) (map (Int.castRingHom ℂ) s) a := by
  intro d hd
  rw [coeff_map] at hd
  have hs' : d ∈ s.support := by
    rw [mem_support_iff]
    intro h0
    apply hd
    simp [h0]
  funext k
  rw [weight_blkW]
  exact hs d hs' k

/- English proof (translation)
Proceed by induction on `d with`. Consider the case `zero`. Introduce `e he`. Use `⟨1, by simp, fun z => ?_⟩` and prove the remaining obligations. Establish `h0 : ∀ p, e p = 0`.

Introduce `p`. Use `he p.1` as an intermediate fact. Rewrite `this` using `[Finset.sum_eq_zero_iff]`. Conclude with `this p.2 (Finset.mem_univ _)`. Simplify using `[h0]`.

Consider the case `succ d ih`. Introduce `e he`. Establish `hex : ∀ k, ∃ i, 0 < e ⟨k, i⟩`. Introduce `k`. Assume the negation of the conclusion as `hne`.

Use `push_neg at hne`. Establish `h1` using `he k`. Rewrite `h1` using `[Finset.sum_eq_zero (fun i _ => Nat.le_zero.1 (hne i))]`. Use linear arithmetic over natural numbers and integers. Use `choose i0 hi0 using hex`.

Set `e' : (Σ k, ι k) → ℕ` to `fun p => if p.2 = i0 p.1 then e p - 1 else e p`. Establish `hblk : ∀ k, ∑ i, e' ⟨k, i⟩ = d`. Introduce `k`. Establish `h1` using `he k`. Rewrite `h1`, the goal using `[← Finset.add_sum_erase _ _ (Finset.mem_univ (i0 k))]`.

Establish `h2 : ∑ i ∈ Finset.univ.erase (i0 k), e' ⟨k, i⟩ = ∑ i ∈ Finset.univ.erase (i0 k), e ⟨k, i⟩`. Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations. Establish `hne : i ≠ i0 k` using `Finset.ne_of_mem_erase hi`. Simplify using `[e', hne]`. Rewrite using `[h2]`.

Establish `h3 : e' ⟨k, i0 k⟩ = e ⟨k, i0 k⟩ - 1` using `by simp [e']`. Rewrite using `[h3]`. Use `hi0 k` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Take `⟨G', hG'deg, hG'⟩` from `ih e' hblk`.

Use `⟨X i0 * G', ?_, fun z => ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[eval_mul, eval_X, ← hG', segre, Fintype.prod_sigma, Fintype.prod_sigma, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.mul_prod_erase _ _ (Finset.mem_univ (i0 k)), ← Finset.mul_prod_erase _ _ (Finset.mem_univ (i0 k))]`.

Establish `h2 : ∏ i ∈ Finset.univ.erase (i0 k), z ⟨k, i⟩ ^ e' ⟨k, i⟩ = ∏ i ∈ Finset.univ.erase (i0 k), z ⟨k, i⟩ ^ e ⟨k, i⟩`. Use `Finset.prod_congr rfl fun i hi => ?_` and prove the remaining obligations. Establish `hne : i ≠ i0 k` using `Finset.ne_of_mem_erase hi`. Simplify using `[e', hne]`. Rewrite using `[h2]`.

Establish `h3 : e' ⟨k, i0 k⟩ = e ⟨k, i0 k⟩ - 1` using `by simp [e']`. Rewrite using `[h3]`. Establish `h4 : e ⟨k, i0 k⟩ = e ⟨k, i0 k⟩ - 1 + 1` using `by have := hi0 k; omega`. Use `conv_lhs => rw [h4, pow_succ]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem diag_prod (d : ℕ) : ∀ e : (Σ k, ι k) → ℕ, (∀ k, ∑ i, e ⟨k, i⟩ = d) →
    ∃ G : MvPolynomial ((k : K) → ι k) ℂ, G.totalDegree ≤ d ∧
      ∀ z : (Σ k, ι k) → ℂ, ∏ p, z p ^ e p = eval (segre z) G := by
  induction d with
  | zero =>
    intro e he
    refine ⟨1, by simp, fun z => ?_⟩
    have h0 : ∀ p, e p = 0 := by
      intro p
      have := he p.1
      rw [Finset.sum_eq_zero_iff] at this
      exact this p.2 (Finset.mem_univ _)
    simp [h0]
  | succ d ih =>
    intro e he
    have hex : ∀ k, ∃ i, 0 < e ⟨k, i⟩ := by
      intro k
      by_contra hne
      push_neg at hne
      have h1 := he k
      rw [Finset.sum_eq_zero (fun i _ => Nat.le_zero.1 (hne i))] at h1
      omega
    choose i0 hi0 using hex
    classical
    let e' : (Σ k, ι k) → ℕ := fun p => if p.2 = i0 p.1 then e p - 1 else e p
    have hblk : ∀ k, ∑ i, e' ⟨k, i⟩ = d := by
      intro k
      have h1 := he k
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (i0 k))] at h1 ⊢
      have h2 : ∑ i ∈ Finset.univ.erase (i0 k), e' ⟨k, i⟩ = ∑ i ∈ Finset.univ.erase (i0 k), e ⟨k, i⟩ := by
        refine Finset.sum_congr rfl fun i hi => ?_
        have hne : i ≠ i0 k := Finset.ne_of_mem_erase hi
        simp [e', hne]
      rw [h2]
      have h3 : e' ⟨k, i0 k⟩ = e ⟨k, i0 k⟩ - 1 := by simp [e']
      rw [h3]
      have := hi0 k
      omega
    obtain ⟨G', hG'deg, hG'⟩ := ih e' hblk
    refine ⟨X i0 * G', ?_, fun z => ?_⟩
    · calc (X i0 * G').totalDegree ≤ (X i0 : MvPolynomial ((k : K) → ι k) ℂ).totalDegree + G'.totalDegree :=
            totalDegree_mul _ _
        _ ≤ 1 + d := by rw [totalDegree_X]; omega
        _ = d + 1 := by ring
    · rw [eval_mul, eval_X, ← hG', segre, Fintype.prod_sigma, Fintype.prod_sigma, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ (i0 k)),
        ← Finset.mul_prod_erase _ _ (Finset.mem_univ (i0 k))]
      have h2 : ∏ i ∈ Finset.univ.erase (i0 k), z ⟨k, i⟩ ^ e' ⟨k, i⟩ =
          ∏ i ∈ Finset.univ.erase (i0 k), z ⟨k, i⟩ ^ e ⟨k, i⟩ := by
        refine Finset.prod_congr rfl fun i hi => ?_
        have hne : i ≠ i0 k := Finset.ne_of_mem_erase hi
        simp [e', hne]
      rw [h2]
      have h3 : e' ⟨k, i0 k⟩ = e ⟨k, i0 k⟩ - 1 := by simp [e']
      rw [h3]
      have h4 : e ⟨k, i0 k⟩ = e ⟨k, i0 k⟩ - 1 + 1 := by have := hi0 k; omega
      conv_lhs => rw [h4, pow_succ]
      ring

/- English proof (translation)
Establish `hG : ∀ m : (Σ k, ι k) →₀ ℕ, ∃ G : MvPolynomial ((k : K) → ι k) ℂ, m ∈ f.support → G.totalDegree ≤ d ∧ ∀ z : (Σ k, ι k) → ℂ, ∏ p, z p ^ m p = eval (segre z) G`. Introduce `m`. Distinguish the cases in `hm : m ∈ f.support`. Establish `hw` using `hf (mem_support_iff.1 hm)`. Take `⟨G, h1, h2⟩` from `diag_prod d (fun p => m p) (fun k => by`.

Use `congrFun hw k` as an intermediate fact. Rewrite using `[weight_blkW] at this)` and apply the resulting hypothesis. Conclude with `⟨G, fun _ => ⟨h1, h2⟩⟩`. Conclude with `⟨0, fun h => absurd h hm⟩`. Use `choose Gf hGf using hG`.

Use `⟨∑ m ∈ f.support, C (coeff m f) * Gf m, ?_, fun z => ?_⟩` and prove the remaining obligations. Use `(totalDegree_finset_sum _ _).trans (Finset.sup_le fun m hm => ?_)` and prove the remaining obligations. Use `(totalDegree_mul _ _).trans ?_` and prove the remaining obligations. Rewrite using `[totalDegree_C, zero_add]`. Conclude with `(hGf m hm).1`.

Rewrite using `[eval_eq', map_sum]`. Use `Finset.sum_congr rfl fun m hm => ?_` and prove the remaining obligations. Rewrite using `[eval_mul, eval_C, (hGf m hm).2 z]`.
-/
theorem diag_of_homog (d : ℕ) {f : MvPolynomial (Σ k, ι k) ℂ}
    (hf : IsWeightedHomogeneous (blkW ι) f (fun _ => d)) :
    ∃ G : MvPolynomial ((k : K) → ι k) ℂ, G.totalDegree ≤ d ∧
      ∀ z : (Σ k, ι k) → ℂ, eval z f = eval (segre z) G := by
  classical
  have hG : ∀ m : (Σ k, ι k) →₀ ℕ, ∃ G : MvPolynomial ((k : K) → ι k) ℂ,
      m ∈ f.support → G.totalDegree ≤ d ∧ ∀ z : (Σ k, ι k) → ℂ, ∏ p, z p ^ m p = eval (segre z) G := by
    intro m
    by_cases hm : m ∈ f.support
    · have hw := hf (mem_support_iff.1 hm)
      obtain ⟨G, h1, h2⟩ := diag_prod d (fun p => m p) (fun k => by
        have := congrFun hw k
        rwa [weight_blkW] at this)
      exact ⟨G, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨0, fun h => absurd h hm⟩
  choose Gf hGf using hG
  refine ⟨∑ m ∈ f.support, C (coeff m f) * Gf m, ?_, fun z => ?_⟩
  · refine (totalDegree_finset_sum _ _).trans (Finset.sup_le fun m hm => ?_)
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, zero_add]
    exact (hGf m hm).1
  · rw [eval_eq', map_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [eval_mul, eval_C, (hGf m hm).2 z]

attribute [local instance] MvPolynomial.weightedGradedAlgebra

/- English proof (translation)
Use extensionality with `x`. Rewrite using `[coeff_weightedHomogeneousComponent, coeff_mul, coeff_mul]`. Use `split_ifs with hx`. Use `Finset.sum_congr rfl fun ab hab => ?_` and prove the remaining obligations. Rewrite using `[coeff_weightedHomogeneousComponent]`.

Distinguish the cases in `hb : coeff ab.2 ψ = 0`. Simplify using `[hb]`. Establish `hwb` using `hψ hb`. Establish `hsum : Finsupp.weight w ab.1 + Finsupp.weight w ab.2 = Finsupp.weight w x`. Establish `hab' : ab.1 + ab.2 = x` using `by simpa using hab`.

Rewrite using `[← map_add, hab']`. Establish `ha : Finsupp.weight w ab.1 = n`. Rewrite `hsum` using `[hwb, hx]`. Conclude with `add_right_cancel hsum`. Rewrite using `[if_pos ha]`.

Use `symm`. Use `Finset.sum_eq_zero fun ab hab => ?_` and prove the remaining obligations. Rewrite using `[coeff_weightedHomogeneousComponent]`. Use `split_ifs with ha`. Distinguish the cases in `hb : coeff ab.2 ψ = 0`.

Simplify using `[hb]`. It suffices to derive a contradiction. Apply `hx` to reduce the goal to its premises. Establish `hwb` using `hψ hb`. Establish `hab' : ab.1 + ab.2 = x` using `by simpa using hab`.

Rewrite using `[← hab', map_add, ha, hwb]`. Simplify using the standard rewrite rules.
-/
theorem comp_mul_homog {σ : Type*} {M : Type*} [AddCancelCommMonoid M] [DecidableEq M] {w : σ → M}
    {ψ : MvPolynomial σ ℂ} {δ : M} (hψ : IsWeightedHomogeneous w ψ δ) (g : MvPolynomial σ ℂ) (n : M) :
    weightedHomogeneousComponent w (n + δ) (g * ψ) = weightedHomogeneousComponent w n g * ψ := by
  classical
  ext x
  rw [coeff_weightedHomogeneousComponent, coeff_mul, coeff_mul]
  split_ifs with hx
  · refine Finset.sum_congr rfl fun ab hab => ?_
    rw [coeff_weightedHomogeneousComponent]
    by_cases hb : coeff ab.2 ψ = 0
    · simp [hb]
    · have hwb := hψ hb
      have hsum : Finsupp.weight w ab.1 + Finsupp.weight w ab.2 = Finsupp.weight w x := by
        have hab' : ab.1 + ab.2 = x := by simpa using hab
        rw [← map_add, hab']
      have ha : Finsupp.weight w ab.1 = n := by
        rw [hwb, hx] at hsum
        exact add_right_cancel hsum
      rw [if_pos ha]
  · symm
    refine Finset.sum_eq_zero fun ab hab => ?_
    rw [coeff_weightedHomogeneousComponent]
    split_ifs with ha
    · by_cases hb : coeff ab.2 ψ = 0
      · simp [hb]
      · exfalso
        apply hx
        have hwb := hψ hb
        have hab' : ab.1 + ab.2 = x := by simpa using hab
        rw [← hab', map_add, ha, hwb]
    · simp

end ReciprocityTheory.ChartRestriction.G.Geo
