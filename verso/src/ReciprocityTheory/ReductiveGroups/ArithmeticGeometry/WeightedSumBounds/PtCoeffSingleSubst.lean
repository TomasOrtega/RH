import Mathlib
import ReciprocityTheory.DualLattices.VEqZeroOfPowEqOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PtOrderProdSub

namespace ReciprocityTheory.ChartRestriction.G.Sh

open MvPowerSeries ReciprocityTheory.PGsh

open Classical

noncomputable section

section Int

variable {C : Type} [Field C] (v : AddValuation C (WithTop ℝ))

def ptIntSub : Subring C where
  carrier := {x | 0 ≤ v x}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, v.map_mul] at *
    exact add_nonneg ha hb
  one_mem' := by simp [v.map_one]
  add_mem' {a b} ha hb := le_trans (le_min ha hb) (v.map_add _ _)
  zero_mem' := by simp [v.map_zero]
  neg_mem' {a} ha := by simpa [Set.mem_ofPred_eq, v.map_neg] using ha

def ptIntSer (σ : Type*) : Subring (MvPowerSeries σ C) where
  carrier := {f | ∀ α, coeff α f ∈ ptIntSub v}
  mul_mem' {f g} hf hg α := by
    rw [coeff_mul]
    exact Subring.sum_mem _ fun x _ => Subring.mul_mem _ (hf _) (hg _)
  one_mem' α := by
    rw [coeff_one]
    split_ifs
    · exact Subring.one_mem _
    · exact Subring.zero_mem _
  add_mem' {f g} hf hg α := by rw [map_add]; exact Subring.add_mem _ (hf α) (hg α)
  zero_mem' α := by rw [map_zero]; exact Subring.zero_mem _
  neg_mem' {f} hf α := by rw [map_neg]; exact Subring.neg_mem _ (hf α)

variable {v}

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem ptMvIsInt_iff {σ : Type*} (f : MvPowerSeries σ C) : MvIsInt v f ↔ f ∈ ptIntSer v σ := Iff.rfl

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem ptIsIntV_iff (x : C) : IsIntV v x ↔ x ∈ ptIntSub v := Iff.rfl

/- English proof (translation)
Unfold `PsIsInt`. Prove the components needed by the constructor for the conclusion. Introduce `h α`. Establish `hα : α = Finsupp.single () (α ())`. Use `ext`.

Conclude with `Finsupp.single_eq_same.symm`. Establish `h1` using `h (α ())`. Rewrite using `[hα]`. Conclude with `h1`. Introduce `h n`.

Conclude with `h (Finsupp.single () n)`.
-/
theorem ptPsIsInt_iff (f : PowerSeries C) : PsIsInt v f ↔ f ∈ ptIntSer v Unit := by
  unfold PsIsInt
  constructor
  · intro h α
    have hα : α = Finsupp.single () (α ()) := by
      ext
      exact Finsupp.single_eq_same.symm
    have h1 := h (α ())
    rw [hα]
    exact h1
  · intro h n
    exact h (Finsupp.single () n)

/- English proof (translation)
Introduce `α`. Rewrite using `[coeff_X]`. Use `split_ifs`. Conclude with `Subring.one_mem _`. Conclude with `Subring.zero_mem _`.
-/
theorem ptIntSer_X {σ : Type*} (s : σ) : (X s : MvPowerSeries σ C) ∈ ptIntSer v σ := by
  intro α
  rw [coeff_X]
  split_ifs
  · exact Subring.one_mem _
  · exact Subring.zero_mem _

/- English proof (translation)
Introduce `α`. Rewrite using `[map_smul, smul_eq_mul]`. Conclude with `Subring.mul_mem _ hc (hf α)`.
-/
theorem ptIntSer_smul {σ : Type*} {c : C} (hc : c ∈ ptIntSub v) {f : MvPowerSeries σ C}
    (hf : f ∈ ptIntSer v σ) : c • f ∈ ptIntSer v σ := by
  intro α
  rw [map_smul, smul_eq_mul]
  exact Subring.mul_mem _ hc (hf α)

/- English proof (translation)
Introduce `e`. Rewrite using `[MvPowerSeries.coeff_subst hA f e]`. Establish `hmem : ∀ d : σ →₀ ℕ, coeff d f • coeff e (d.prod fun s n => A s ^ n) ∈ ptIntSub v`. Introduce `d`. Rewrite using `[smul_eq_mul]`.

Use `Subring.mul_mem _ (hf d) ?_` and prove the remaining obligations. Establish `hp : (d.prod fun s n => A s ^ n) ∈ ptIntSer v τ` using `Subring.prod_mem _ fun s _ => Subring.pow_mem _ (hAi s) _`. Conclude with `hp e`. Establish `key : ∀ g : (σ →₀ ℕ) → C, (∀ i, g i ∈ ptIntSub v) → ∑ᶠ i, g i ∈ ptIntSub v`. Introduce `g hg`.

Distinguish the cases in `hfin : (Function.support g).Finite`. Rewrite using `[finsum_eq_sum g hfin]`. Conclude with `Subring.sum_mem _ fun i _ => hg i`. Rewrite using `[finsum_of_infinite_support hfin]`. Conclude with `Subring.zero_mem _`.

Conclude with `key _ hmem`.
-/
theorem ptIntSer_subst {σ τ : Type*} {A : σ → MvPowerSeries τ C} (hA : HasSubst A)
    (hAi : ∀ s, A s ∈ ptIntSer v τ) {f : MvPowerSeries σ C} (hf : f ∈ ptIntSer v σ) :
    subst A f ∈ ptIntSer v τ := by
  intro e
  rw [MvPowerSeries.coeff_subst hA f e]
  have hmem : ∀ d : σ →₀ ℕ, coeff d f • coeff e (d.prod fun s n => A s ^ n) ∈ ptIntSub v := by
    intro d
    rw [smul_eq_mul]
    refine Subring.mul_mem _ (hf d) ?_
    have hp : (d.prod fun s n => A s ^ n) ∈ ptIntSer v τ :=
      Subring.prod_mem _ fun s _ => Subring.pow_mem _ (hAi s) _
    exact hp e
  have key : ∀ g : (σ →₀ ℕ) → C, (∀ i, g i ∈ ptIntSub v) → ∑ᶠ i, g i ∈ ptIntSub v := by
    intro g hg
    by_cases hfin : (Function.support g).Finite
    · rw [finsum_eq_sum g hfin]
      exact Subring.sum_mem _ fun i _ => hg i
    · rw [finsum_of_infinite_support hfin]
      exact Subring.zero_mem _
  exact key _ hmem

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => rw [Nat.cast_zero, v.map_zero]`. Conclude with `le_top`. Consider the case `succ n ih`. Rewrite using `[Nat.cast_succ]`.

Conclude with `le_trans (le_min ih (by rw [v.map_one])) (v.map_add _ _)`.
-/
theorem pt_v_natCast_nonneg (n : ℕ) : (0 : WithTop ℝ) ≤ v (n : C) := by
  induction n with
  | zero => rw [Nat.cast_zero, v.map_zero]; exact le_top
  | succ n ih =>
    rw [Nat.cast_succ]
    exact le_trans (le_min ih (by rw [v.map_one])) (v.map_add _ _)

/- English proof (translation)
Consider the cases of `n with`. Consider the case `ofNat m => rw [Int.ofNat_eq_coe, Int.cast_natCast]`. Conclude with `pt_v_natCast_nonneg m`. Consider the case `negSucc m => rw [Int.cast_negSucc, v.map_neg]`. Conclude with `pt_v_natCast_nonneg (m + 1)`.
-/
theorem pt_v_intCast_nonneg (n : ℤ) : (0 : WithTop ℝ) ≤ v (n : C) := by
  cases n with
  | ofNat m => rw [Int.ofNat_eq_coe, Int.cast_natCast]; exact pt_v_natCast_nonneg m
  | negSucc m => rw [Int.cast_negSucc, v.map_neg]; exact pt_v_natCast_nonneg (m + 1)

/- English proof (translation)
Establish `h0 : (0 : WithTop ℝ) ≤ v (n : C)` using `pt_v_natCast_nonneg n`. Use `(h0.lt_or_eq.resolve_left fun hlt => ?_).symm` and prove the remaining obligations. Establish `hcop : Nat.Coprime n p` using `Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).mpr hn)`. Establish `hz : ((1 : ℤ) : C) = ((n * Nat.gcdA n p + p * Nat.gcdB n p : ℤ) : C)`. Rewrite using `[← Nat.gcd_eq_gcd_ab, hcop.gcd_eq_one, Nat.cast_one]`.

Move the coercions through the operations in `at hz`. Establish `h1 : v (1 : C) = 0` using `v.map_one`. Rewrite `h1` using `[hz]`. Establish `hmin` using `v.map_add ((n : C) * (Nat.gcdA n p : C)) ((p : C) * (Nat.gcdB n p : C))`. Rewrite `hmin` using `[h1, v.map_mul, v.map_mul, hvp]`.

Establish `ha : (0 : WithTop ℝ) < v (n : C) + v (Nat.gcdA n p : C)` using `add_pos_of_pos_of_nonneg hlt (pt_v_intCast_nonneg _)`. Establish `hb : (0 : WithTop ℝ) < 1 + v (Nat.gcdB n p : C)` using `add_pos_of_pos_of_nonneg zero_lt_one (pt_v_intCast_nonneg _)`. Conclude with `absurd hmin (not_le.mpr (lt_min ha hb))`.
-/
theorem pt_v_natCast_eq_zero {p : ℕ} (hp : p.Prime) (hvp : v (p : C) = 1) {n : ℕ}
    (hn : ¬ p ∣ n) : v (n : C) = 0 := by
  have h0 : (0 : WithTop ℝ) ≤ v (n : C) := pt_v_natCast_nonneg n
  refine (h0.lt_or_eq.resolve_left fun hlt => ?_).symm
  have hcop : Nat.Coprime n p :=
    Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).mpr hn)
  have hz : ((1 : ℤ) : C) = ((n * Nat.gcdA n p + p * Nat.gcdB n p : ℤ) : C) := by
    rw [← Nat.gcd_eq_gcd_ab, hcop.gcd_eq_one, Nat.cast_one]
  push_cast at hz
  have h1 : v (1 : C) = 0 := v.map_one
  rw [hz] at h1
  have hmin := v.map_add ((n : C) * (Nat.gcdA n p : C)) ((p : C) * (Nat.gcdB n p : C))
  rw [h1, v.map_mul, v.map_mul, hvp] at hmin
  have ha : (0 : WithTop ℝ) < v (n : C) + v (Nat.gcdA n p : C) :=
    add_pos_of_pos_of_nonneg hlt (pt_v_intCast_nonneg _)
  have hb : (0 : WithTop ℝ) < 1 + v (Nat.gcdB n p : C) :=
    add_pos_of_pos_of_nonneg zero_lt_one (pt_v_intCast_nonneg _)
  exact absurd hmin (not_le.mpr (lt_min ha hb))

/- English proof (translation)
Establish `hv : v (n : C) = 0` using `pt_v_natCast_eq_zero hp hvp hn`. Establish `hne : (n : C) ≠ 0`. Introduce `h`. Rewrite `hv` using `[h, v.map_zero]`. Conclude with `absurd hv WithTop.top_ne_zero`.

Use `show (0 : WithTop ℝ) ≤ v ((n : C)⁻¹)`. Establish `h1` using `v.map_mul (n : C) ((n : C)⁻¹)`. Rewrite `h1` using `[mul_inv_cancel₀ hne, v.map_one, hv, zero_add]`. Rewrite using `[← h1]`.
-/
theorem pt_inv_natCast_mem {p : ℕ} (hp : p.Prime) (hvp : v (p : C) = 1) {n : ℕ}
    (hn : ¬ p ∣ n) : ((n : C))⁻¹ ∈ ptIntSub v := by
  have hv : v (n : C) = 0 := pt_v_natCast_eq_zero hp hvp hn
  have hne : (n : C) ≠ 0 := by
    intro h
    rw [h, v.map_zero] at hv
    exact absurd hv WithTop.top_ne_zero
  show (0 : WithTop ℝ) ≤ v ((n : C)⁻¹)
  have h1 := v.map_mul (n : C) ((n : C)⁻¹)
  rw [mul_inv_cancel₀ hne, v.map_one, hv, zero_add] at h1
  rw [← h1]

end Int

section Lin

variable {R : Type*} [CommRing R]

/- English proof (translation)
Establish `hsum : ∑ i ∈ α.support, α i = 1` using `h`. Choose the witnesses or unpack the hypotheses as in `⟨s, hs⟩ : α.support.Nonempty := by`. Rewrite using `[Finset.nonempty_iff_ne_empty]`. Introduce `he`. Rewrite `hsum` using `[he, Finset.sum_empty]`.

Conclude with `zero_ne_one hsum`. Use `⟨s, ?_⟩` and prove the remaining obligations. Establish `hs0 : α s ≠ 0` using `Finsupp.mem_support_iff.mp hs`. Use extensionality with `t`. Distinguish the cases in `hts : t = s`.

Substitute `hts` using the available equality. Rewrite using `[Finsupp.single_eq_same]`. Establish `h1 : α t ≤ ∑ i ∈ α.support, α i` using `Finset.single_le_sum (f := fun i => α i) (fun _ _ => Nat.zero_le _) hs`. Use linear arithmetic over natural numbers and integers. Establish `hst : s ≠ t` using `Ne.symm hts`.

Simplify using `only [Finsupp.single_apply, hst, hts, if_false]`. Assume the negation of the conclusion as `hne`. Establish `ht : t ∈ α.support` using `Finsupp.mem_support_iff.mpr hne`. Establish `hsub : ({s, t} : Finset _) ⊆ α.support`. Introduce `x hx`.

Simplify using `only [Finset.mem_insert, Finset.mem_singleton] at hx`. Apply the tactic sequence `rcases hx with rfl | rfl <;> assumption`. Establish `h2` using `Finset.sum_le_sum_of_subset (f := fun i => α i) hsub`. Rewrite `h2` using `[Finset.sum_pair hst]`. Use linear arithmetic over natural numbers and integers.
-/
theorem pt_degree_eq_one {σ : Type*} {α : σ →₀ ℕ} (h : α.degree = 1) :
    ∃ s, α = Finsupp.single s 1 := by
  classical
  have hsum : ∑ i ∈ α.support, α i = 1 := h
  obtain ⟨s, hs⟩ : α.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    rw [he, Finset.sum_empty] at hsum
    exact zero_ne_one hsum
  refine ⟨s, ?_⟩
  have hs0 : α s ≠ 0 := Finsupp.mem_support_iff.mp hs
  ext t
  by_cases hts : t = s
  · subst hts
    rw [Finsupp.single_eq_same]
    have h1 : α t ≤ ∑ i ∈ α.support, α i :=
      Finset.single_le_sum (f := fun i => α i) (fun _ _ => Nat.zero_le _) hs
    omega
  · have hst : s ≠ t := Ne.symm hts
    simp only [Finsupp.single_apply, hst, hts, if_false]
    by_contra hne
    have ht : t ∈ α.support := Finsupp.mem_support_iff.mpr hne
    have hsub : ({s, t} : Finset _) ⊆ α.support := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    have h2 := Finset.sum_le_sum_of_subset (f := fun i => α i) hsub
    rw [Finset.sum_pair hst] at h2
    omega

/- English proof (translation)
Introduce `e he`. Rewrite using `[coeff_mul]`. Use `Finset.sum_eq_zero fun x hx => ?_` and prove the remaining obligations. Establish `hx' : x.1 + x.2 = e` using `Finset.HasAntidiagonal.mem_antidiagonal.mp hx`. Establish `hdeg : (x.1 + x.2).degree = x.1.degree + x.2.degree` using `by first`.

Consider the case `exact Finsupp.degree_add _ _`. Consider the case `exact map_add _ _ _`. Rewrite `hdeg` using `[hx']`. Distinguish the cases in `h1 : x.1.degree < m`. Rewrite using `[hP _ h1, zero_mul]`.

Rewrite using `[hQ _ (by omega), mul_zero]`.
-/
private theorem vmul_lemma {ρ K : Type*} [CommRing K] {P Q : MvPowerSeries ρ K} {m n : ℕ}
    (hP : ∀ e : ρ →₀ ℕ, e.degree < m → coeff e P = 0)
    (hQ : ∀ e : ρ →₀ ℕ, e.degree < n → coeff e Q = 0) :
    ∀ e : ρ →₀ ℕ, e.degree < m + n → coeff e (P * Q) = 0 := by
  intro e he
  rw [coeff_mul]
  refine Finset.sum_eq_zero fun x hx => ?_
  have hx' : x.1 + x.2 = e := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
  have hdeg : (x.1 + x.2).degree = x.1.degree + x.2.degree := by
    first
    | exact Finsupp.degree_add _ _
    | exact map_add _ _ _
  rw [hx'] at hdeg
  by_cases h1 : x.1.degree < m
  · rw [hP _ h1, zero_mul]
  · rw [hQ _ (by omega), mul_zero]

/- English proof (translation)
Use `first`. Consider the case `exact (Finsupp.degree_eq_zero_iff _).mp h`. Consider the case `exact Finsupp.degree_eq_zero_iff.mp h`.
-/
private theorem vzero_lemma_2 {ρ : Type*} {e : ρ →₀ ℕ} (h : e.degree = 0) : e = 0 := by
  first
  | exact (Finsupp.degree_eq_zero_iff _).mp h
  | exact Finsupp.degree_eq_zero_iff.mp h

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => intro e he`. Use linear arithmetic over natural numbers and integers. Consider the case `succ k ih`. Rewrite using `[pow_succ]`.

Use `vmul_lemma ih ?_` and prove the remaining obligations. Introduce `e he`. Establish `h0 : e = 0` using `vzero_lemma_2 (by omega)`. Rewrite using `[h0, coeff_zero_eq_constantCoeff_apply, hA]`.
-/
private theorem vpow_lemma_3 {ρ K : Type*} [CommRing K] {A : MvPowerSeries ρ K}
    (hA : constantCoeff A = 0) (k : ℕ) :
    ∀ e : ρ →₀ ℕ, e.degree < k → coeff e (A ^ k) = 0 := by
  induction k with
  | zero => intro e he; omega
  | succ k ih =>
    rw [pow_succ]
    refine vmul_lemma ih ?_
    intro e he
    have h0 : e = 0 := vzero_lemma_2 (by omega)
    rw [h0, coeff_zero_eq_constantCoeff_apply, hA]

/- English proof (translation)
Use `Finset.induction_on T (fun e he => by simp at he) (fun a T ha ih => ?_)` and prove the remaining obligations. Rewrite using `[Finset.prod_insert ha, Finset.sum_insert ha]`. Conclude with `vmul_lemma (vpow_lemma_3 (hA a) (d a)) ih`.
-/
private theorem vprod_lemma_4 {ι ρ K : Type*} [CommRing K] {A : ι → MvPowerSeries ρ K}
    (hA : ∀ s, constantCoeff (A s) = 0) (d : ι →₀ ℕ) (T : Finset ι) :
    ∀ e : ρ →₀ ℕ, e.degree < ∑ s ∈ T, d s → coeff e (∏ s ∈ T, A s ^ d s) = 0 := by
  classical
  refine Finset.induction_on T (fun e he => by simp at he) (fun a T ha ih => ?_)
  rw [Finset.prod_insert ha, Finset.sum_insert ha]
  exact vmul_lemma (vpow_lemma_3 (hA a) (d a)) ih

/- English proof (translation)
Rewrite using `[MvPowerSeries.coeff_subst hA f (Finsupp.single i 1)]`. Establish `hi1 : (Finsupp.single i 1 : τ →₀ ℕ).degree = 1` using `by first`. Consider the case `exact Finsupp.degree_single i 1`. Consider the case `simp [Finsupp.degree]`. Establish `hsupp : (Function.support fun d : σ →₀ ℕ => coeff d f • coeff (Finsupp.single i 1) (d.prod fun s e => A s ^ e)) ⊆ ↑(Finset.univ.image fun s : σ => Finsupp.single s 1)`.

Introduce `d hd`. Simplify using `only [Function.mem_support, ne_eq] at hd`. Assume the negation of the conclusion as `hns`. Apply `hd` to reduce the goal to its premises. Distinguish the cases in `hd0 : d = 0`.

Rewrite using `[hd0, coeff_zero_eq_constantCoeff_apply, hf, zero_smul]`. Establish `hdeg : 2 ≤ d.degree`. Assume the negation of the conclusion as `hlt`. Establish `hne : d.degree ≠ 0` using `fun h0 => hd0 (vzero_lemma_2 h0)`. Establish `h1 : d.degree = 1` using `by omega`.

Take `⟨s, hs⟩` from `pt_degree_eq_one h1`. Apply `hns` to reduce the goal to its premises. Rewrite using `[hs]`. Conclude with `Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (Finset.mem_univ s))`. Establish `hlt : (Finsupp.single i 1 : τ →₀ ℕ).degree < d.degree` using `by omega`.

Establish `hz : coeff (Finsupp.single i 1) (d.prod fun s e => A s ^ e) = 0` using `vprod_lemma_4 hA0 d d.support _ hlt`. Rewrite using `[hz, smul_zero]`. Rewrite using `[finsum_eq_sum_of_support_subset _ hsupp, Finset.sum_image]`. Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Rewrite using `[Finsupp.prod_single_index (by simp)]`.

Simplify using `only [pow_one, smul_eq_mul]`. Introduce `s _ t _ hst`. Conclude with `(Finsupp.single_left_inj one_ne_zero).mp hst`.
-/
theorem pt_coeff_single_subst {σ τ : Type*} [Fintype σ]
    {A : σ → MvPowerSeries τ R} (hA : HasSubst A) (hA0 : ∀ s, constantCoeff (A s) = 0)
    {f : MvPowerSeries σ R} (hf : constantCoeff f = 0) (i : τ) :
    coeff (Finsupp.single i 1) (subst A f) =
      ∑ s, coeff (Finsupp.single s 1) f * coeff (Finsupp.single i 1) (A s) := by
  classical
  rw [MvPowerSeries.coeff_subst hA f (Finsupp.single i 1)]
  have hi1 : (Finsupp.single i 1 : τ →₀ ℕ).degree = 1 := by
    first
    | exact Finsupp.degree_single i 1
    | simp [Finsupp.degree]
  have hsupp : (Function.support fun d : σ →₀ ℕ =>
      coeff d f • coeff (Finsupp.single i 1) (d.prod fun s e => A s ^ e)) ⊆
      ↑(Finset.univ.image fun s : σ => Finsupp.single s 1) := by
    intro d hd
    simp only [Function.mem_support, ne_eq] at hd
    by_contra hns
    apply hd
    by_cases hd0 : d = 0
    · rw [hd0, coeff_zero_eq_constantCoeff_apply, hf, zero_smul]
    · have hdeg : 2 ≤ d.degree := by
        by_contra hlt
        have hne : d.degree ≠ 0 := fun h0 => hd0 (vzero_lemma_2 h0)
        have h1 : d.degree = 1 := by omega
        obtain ⟨s, hs⟩ := pt_degree_eq_one h1
        apply hns
        rw [hs]
        exact Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (Finset.mem_univ s))
      have hlt : (Finsupp.single i 1 : τ →₀ ℕ).degree < d.degree := by omega
      have hz : coeff (Finsupp.single i 1) (d.prod fun s e => A s ^ e) = 0 :=
        vprod_lemma_4 hA0 d d.support _ hlt
      rw [hz, smul_zero]
  rw [finsum_eq_sum_of_support_subset _ hsupp, Finset.sum_image]
  · refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finsupp.prod_single_index (by simp)]
    simp only [pow_one, smul_eq_mul]
  · intro s _ t _ hst
    exact (Finsupp.single_left_inj one_ne_zero).mp hst

/- English proof (translation)
Rewrite using `[coeff_X]`. Distinguish the cases in `h : s = t`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[if_neg h, if_neg]`.

Introduce `h'`. Conclude with `h ((Finsupp.single_left_inj one_ne_zero).mp h')`.
-/
theorem pt_coeff_single_X {σ : Type*} (s t : σ) :
    coeff (Finsupp.single s 1) (X t : MvPowerSeries σ R) = if s = t then 1 else 0 := by
  rw [coeff_X]
  by_cases h : s = t
  · subst h
    simp
  · rw [if_neg h, if_neg]
    intro h'
    exact h ((Finsupp.single_left_inj one_ne_zero).mp h')

/- English proof (translation)
Introduce `α hα`. Use `left`. Assume the negation of the conclusion as `h`. Conclude with `hα (hK α (by omega))`.
-/
theorem pt_hK_of_low {σ τ : Type*} {K : MvPowerSeries σ R}
    (hK : ∀ α : σ →₀ ℕ, α.degree ≤ 1 → coeff α K = 0) (A A' : σ → MvPowerSeries τ R) :
    ∀ α, coeff α K ≠ 0 → 2 ≤ α.degree ∨ ∀ s ∈ α.support, A s = A' s := by
  intro α hα
  left
  by_contra h
  exact hα (hK α (by omega))

end Lin

section Law

variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d : ℕ}

/- English proof (translation)
Establish `hF : HasSubst G.F` using `by first`. Consider the case `exact HasSubst.of_constantCoeff_zero G.F_const`. Consider the case `exact hasSubst_of_constantCoeff_zero G.F_const`. Establish `hX : ∀ e : Fin d → Fin d ⊕ Fin d, HasSubst (fun b => (X (e b) : MvPowerSeries (Fin d ⊕ Fin d) C))`. Introduce `e`.

Use `first`. Consider the case `exact HasSubst.of_constantCoeff_zero fun b => constantCoeff_X _`. Consider the case `exact hasSubst_of_constantCoeff_zero fun b => constantCoeff_X _`. Establish `key` using `congrArg (coeff (Finsupp.single i 1)) (G.lg_F a)`. Rewrite `key` using `[map_add, pt_coeff_single_subst hF G.F_const (G.lg_const a), pt_coeff_single_subst (hX Sum.inl) (fun b => constantCoeff_X _) (G.lg_const a), pt_coeff_single_subst (hX Sum.inr) (fun b => constantCoeff_X _) (G.lg_const a)]`.

Simplify using `only [G.lg_lin, pt_coeff_single_X, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true] at key`. Use `key` and compare the differences between its conclusion and the goal.
-/
theorem pt_F_lin (G : LogFGL v d) (a : Fin d) (i : Fin d ⊕ Fin d) :
    coeff (Finsupp.single i 1) (G.F a) =
      (if i = Sum.inl a then 1 else 0) + (if i = Sum.inr a then 1 else 0) := by
  have hF : HasSubst G.F := by
    first
    | exact HasSubst.of_constantCoeff_zero G.F_const
    | exact hasSubst_of_constantCoeff_zero G.F_const
  have hX : ∀ e : Fin d → Fin d ⊕ Fin d,
      HasSubst (fun b => (X (e b) : MvPowerSeries (Fin d ⊕ Fin d) C)) := by
    intro e
    first
    | exact HasSubst.of_constantCoeff_zero fun b => constantCoeff_X _
    | exact hasSubst_of_constantCoeff_zero fun b => constantCoeff_X _
  have key := congrArg (coeff (Finsupp.single i 1)) (G.lg_F a)
  rw [map_add, pt_coeff_single_subst hF G.F_const (G.lg_const a),
    pt_coeff_single_subst (hX Sum.inl) (fun b => constantCoeff_X _) (G.lg_const a),
    pt_coeff_single_subst (hX Sum.inr) (fun b => constantCoeff_X _) (G.lg_const a)] at key
  simp only [G.lg_lin, pt_coeff_single_X, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] at key
  convert key

end Law

end

end ReciprocityTheory.ChartRestriction.G.Sh
