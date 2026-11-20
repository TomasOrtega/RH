import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterPC
import ReciprocityTheory.AnalyticForms.RegularLocalRings.MemConePtsIffChartIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterMinorA

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial MultiHomogZ
open scoped Pointwise

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

/- English proof (translation)
Introduce `m hm k`. Take `⟨m1, hm1, m2, hm2, rfl⟩` from `Finset.mem_add.mp (MvPolynomial.support_mul f g hm)`. Simplify using `only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply]`. Rewrite using `[hf m1 hm1 k, hg m2 hm2 k]`.
-/
private theorem isMultiHomog_mul_birational_geometry {f g : MRing ι} {a b : K → ℕ} (hf : IsMultiHomog f a)
    (hg : IsMultiHomog g b) : IsMultiHomog (f * g) (a + b) := by
  classical
  intro m hm k
  obtain ⟨m1, hm1, m2, hm2, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul f g hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply]
  rw [hf m1 hm1 k, hg m2 hm2 k]

/- English proof (translation)
Take `⟨S, hS, rfl⟩` from `hI`. Take `⟨S', hS', rfl⟩` from `hI'`. Use `⟨S * S', ?_, Ideal.span_mul_span' S S'⟩` and prove the remaining obligations. Introduce and unpack `f ⟨x, hx, y, hy, rfl⟩`. Take `⟨a, ha⟩` from `hS x hx`.

Take `⟨b, hb⟩` from `hS' y hy`. Apply the tactic sequence `exact ⟨a + b, isMultiHomog_mul_birational_geometry ha hb⟩`.
-/
theorem isMultiHomogIdeal_mul {I I' : Ideal (MRing ι)} (hI : IsMultiHomogIdeal I)
    (hI' : IsMultiHomogIdeal I') : IsMultiHomogIdeal (I * I') := by
  obtain ⟨S, hS, rfl⟩ := hI
  obtain ⟨S', hS', rfl⟩ := hI'
  refine ⟨S * S', ?_, Ideal.span_mul_span' S S'⟩
  rintro f ⟨x, hx, y, hy, rfl⟩
  obtain ⟨a, ha⟩ := hS x hx
  obtain ⟨b, hb⟩ := hS' y hy
  exact ⟨a + b, isMultiHomog_mul_birational_geometry ha hb⟩

/- English proof (translation)
Use `revert h`. Use `Finset.induction_on s ?_ ?_` and prove the remaining obligations. Introduce `_ m hm k`. Rewrite `hm` using `[Finset.prod_empty]`. Establish `hm0 : m = 0`.

Assume the negation of the conclusion as `hne`. Rewrite `hm` using `[MvPolynomial.mem_support_iff, MvPolynomial.coeff_one, if_neg (Ne.symm hne)]`. Conclude with `hm rfl`. Substitute `hm0` using the available equality. Simplify using the standard rewrite rules.

Introduce `x s hx ih h`. Rewrite using `[Finset.prod_insert hx, Finset.sum_insert hx]`. Apply the tactic sequence `exact isMultiHomog_mul_birational_geometry (h x (Finset.mem_insert_self x s)) (ih fun y hy => h y (Finset.mem_insert_of_mem hy))`.
-/
private theorem isMultiHomog_finset_prod' {β : Type} (s : Finset β) (f : β → MRing ι) (a : β → K → ℕ)
    (h : ∀ x ∈ s, IsMultiHomog (f x) (a x)) : IsMultiHomog (∏ x ∈ s, f x) (∑ x ∈ s, a x) := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _ m hm k
    rw [Finset.prod_empty] at hm
    have hm0 : m = 0 := by
      by_contra hne
      rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_one, if_neg (Ne.symm hne)] at hm
      exact hm rfl
    subst hm0
    simp
  · intro x s hx ih h
    rw [Finset.prod_insert hx, Finset.sum_insert hx]
    exact isMultiHomog_mul_birational_geometry (h x (Finset.mem_insert_self x s))
      (ih fun y hy => h y (Finset.mem_insert_of_mem hy))

/- English proof (translation)
Introduce `m hm k`. Take `⟨x, hx, hm'⟩` from `Finset.mem_biUnion.mp (MvPolynomial.support_sum hm)`. Conclude with `h x hx m hm' k`.
-/
private theorem isMultiHomog_finset_sum {β : Type} (s : Finset β) (f : β → MRing ι) (a : K → ℕ)
    (h : ∀ x ∈ s, IsMultiHomog (f x) a) : IsMultiHomog (∑ x ∈ s, f x) a := by
  classical
  intro m hm k
  obtain ⟨x, hx, hm'⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hm)
  exact h x hx m hm' k

/- English proof (translation)
Introduce `m hm k` and use `h m (MvPolynomial.support_smul hm) k`.
-/
private theorem isMultiHomog_zsmul (c : ℤ) {f : MRing ι} {a : K → ℕ} (h : IsMultiHomog f a) :
    IsMultiHomog (c • f) a := fun m hm k => h m (MvPolynomial.support_smul hm) k

/- English proof (translation)
Establish `key : ∀ m, m ∈ (pderiv v p).support → ∀ k, ∑ i, m ⟨k, i⟩ + (if k = v.1 then 1 else 0) = d k`. Introduce `m hm k`. Rewrite `hm` using `[MvPolynomial.mem_support_iff, MvPolynomial.coeff_pderiv]`. Establish `hm' : m + Finsupp.single v 1 ∈ p.support`. Rewrite using `[MvPolynomial.mem_support_iff]`.

Introduce `h0`. Conclude with `hm (by rw [h0, zero_mul])`. Rewrite using `[← h _ hm' k]`. Simplify using `only [Finsupp.add_apply, Finset.sum_add_distrib]`. Use `congr 1`.

Take `⟨k0, i0⟩` from `v`. Distinguish the cases in `hk : k = k0`. Substitute `hk` using the available equality. Simplify using `[Finsupp.single_apply, Sigma.mk.inj_iff]`. Simplify using `[Finsupp.single_apply, Sigma.mk.inj_iff, Ne.symm hk, hk]`.

Use `⟨fun m hm k => ?_, fun hne => ?_⟩` and prove the remaining obligations. Use `key m hm k beta_reduce` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Take `⟨m, hm⟩` from `MvPolynomial.ne_zero_iff.mp hne`. Use `key m (MvPolynomial.mem_support_iff.mpr hm) v.1` as an intermediate fact.

Rewrite `this` using `[if_pos rfl]`. Use linear arithmetic over natural numbers and integers.
-/
private theorem isMultiHomog_pderiv_and_one_le_of_pderiv_ne_zero [DecidableEq K] (v : Σ k, ι k) {p : MRing ι} {d : K → ℕ}
    (h : IsMultiHomog p d) :
    IsMultiHomog (pderiv v p) (fun k => d k - if k = v.1 then 1 else 0) ∧
      (pderiv v p ≠ 0 → 1 ≤ d v.1) := by
  classical
  have key : ∀ m, m ∈ (pderiv v p).support → ∀ k, ∑ i, m ⟨k, i⟩ + (if k = v.1 then 1 else 0) = d k := by
    intro m hm k
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_pderiv] at hm
    have hm' : m + Finsupp.single v 1 ∈ p.support := by
      rw [MvPolynomial.mem_support_iff]
      intro h0
      exact hm (by rw [h0, zero_mul])
    rw [← h _ hm' k]
    simp only [Finsupp.add_apply, Finset.sum_add_distrib]
    congr 1
    obtain ⟨k0, i0⟩ := v
    by_cases hk : k = k0
    · subst hk
      simp [Finsupp.single_apply, Sigma.mk.inj_iff]
    · simp [Finsupp.single_apply, Sigma.mk.inj_iff, Ne.symm hk, hk]
  refine ⟨fun m hm k => ?_, fun hne => ?_⟩
  · have := key m hm k
    beta_reduce
    omega
  · obtain ⟨m, hm⟩ := MvPolynomial.ne_zero_iff.mp hne
    have := key m (MvPolynomial.mem_support_iff.mpr hm) v.1
    rw [if_pos rfl] at this
    omega

/- English proof (translation)
Use `choose d hd using hG`. Use `⟨fun k => (∑ i, d (a i) k) - ∑ j, (if k = (b j).1 then 1 else 0), ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.det_apply]`. Use `isMultiHomog_finset_sum _ _ _ fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[Units.smul_def]`.

Use `isMultiHomog_zsmul _ ?_` and prove the remaining obligations. Simplify using `only [Matrix.of_apply]`. Distinguish the cases in `h0 : ∃ i, pderiv (b i) (G (a (σ i))) = 0`. Take `⟨i, hi⟩` from `h0`. Rewrite using `[Finset.prod_eq_zero (Finset.mem_univ i) hi]`.

Introduce `m hm`. Simplify using `at hm`. Use `push_neg at h0`. Establish `hle : ∀ i ∈ (Finset.univ : Finset (Fin c)), ∀ k, (if k = (b i).1 then 1 else 0) ≤ d (a (σ i)) k`. Introduce `i _ k`.

Use `split_ifs with hk`. Substitute `hk` using the available equality. Conclude with `(isMultiHomog_pderiv_and_one_le_of_pderiv_ne_zero (b i) (hd (a (σ i)))).2 (h0 i)`. Conclude with `Nat.zero_le _`. Establish `hp` using `isMultiHomog_finset_prod' Finset.univ (fun i => pderiv (b i) (G (a (σ i)))) (fun i k => d (a (σ i)) k - if k = (b i).1 then 1 else 0) (fun i _ => (isMultiHomog_pderiv_and_one_le_of_pderiv_ne_zero (b i) (hd (a (σ i)))).1)`.

Use `hp using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `k`. Rewrite using `[Finset.sum_apply, Finset.sum_tsub_distrib _ (fun i hi => hle i hi k)]`. Use `congr 1`. Conclude with `(Equiv.sum_comp σ (fun i => d (a i) k)).symm`.
-/
theorem isMultiHomog_det_pderiv {s c : ℕ} (G : Fin s → MRing ι) (hG : ∀ i, ∃ a, IsMultiHomog (G i) a)
    (a : Fin c → Fin s) (b : Fin c → Σ k, ι k) :
    ∃ d, IsMultiHomog (Matrix.det (Matrix.of fun i j => pderiv (b j) (G (a i)))) d := by
  classical
  choose d hd using hG
  refine ⟨fun k => (∑ i, d (a i) k) - ∑ j, (if k = (b j).1 then 1 else 0), ?_⟩
  rw [Matrix.det_apply]
  refine isMultiHomog_finset_sum _ _ _ fun σ _ => ?_
  rw [Units.smul_def]
  refine isMultiHomog_zsmul _ ?_
  simp only [Matrix.of_apply]
  by_cases h0 : ∃ i, pderiv (b i) (G (a (σ i))) = 0
  · obtain ⟨i, hi⟩ := h0
    rw [Finset.prod_eq_zero (Finset.mem_univ i) hi]
    intro m hm
    simp at hm
  · push_neg at h0
    have hle : ∀ i ∈ (Finset.univ : Finset (Fin c)), ∀ k,
        (if k = (b i).1 then 1 else 0) ≤ d (a (σ i)) k := by
      intro i _ k
      split_ifs with hk
      · subst hk
        exact (isMultiHomog_pderiv_and_one_le_of_pderiv_ne_zero (b i) (hd (a (σ i)))).2 (h0 i)
      · exact Nat.zero_le _
    have hp := isMultiHomog_finset_prod' Finset.univ (fun i => pderiv (b i) (G (a (σ i))))
      (fun i k => d (a (σ i)) k - if k = (b i).1 then 1 else 0)
      (fun i _ => (isMultiHomog_pderiv_and_one_le_of_pderiv_ne_zero (b i) (hd (a (σ i)))).1)
    convert hp using 1
    funext k
    rw [Finset.sum_apply, Finset.sum_tsub_distrib _ (fun i hi => hle i hi k)]
    congr 1
    exact (Equiv.sum_comp σ (fun i => d (a i) k)).symm

/- English proof (translation)
Take `⟨S, hS, rfl⟩` from `hP`. Use `⟨map (Int.castRingHom ℂ) '' S, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨f, hf, rfl⟩`. Take `⟨a, ha⟩` from `hS f hf`. Conclude with `⟨a, fun m hm k => ha m (MvPolynomial.support_map_subset _ _ hm) k⟩`.

Conclude with `Ideal.map_span (map (Int.castRingHom ℂ)) S`.
-/
theorem isMultiHomogIdeal_pC {P : Ideal (MRing ι)} (hP : IsMultiHomogIdeal P) :
    ReciprocityTheory.AnForm.R.IsMultiHomogIdeal (pC P) := by
  obtain ⟨S, hS, rfl⟩ := hP
  refine ⟨map (Int.castRingHom ℂ) '' S, ?_, ?_⟩
  · rintro _ ⟨f, hf, rfl⟩
    obtain ⟨a, ha⟩ := hS f hf
    exact ⟨a, fun m hm k => ha m (MvPolynomial.support_map_subset _ _ hm) k⟩
  · exact Ideal.map_span (map (Int.castRingHom ℂ)) S

end ReciprocityTheory.ChartRestriction.G.Geo
