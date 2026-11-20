import Mathlib

namespace GlobalTheory.OrdMul

open MvPolynomial

/- English proof (translation)
Establish `key : ∀ n : ℕ, ∀ m : ι →₀ ℕ, m q + 2 * (m.erase q).degree = n → m.degree < N → (∀ j ∈ K, m j = 0) → F.coeff m ∈ I`. Introduce `n`. Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Introduce `m hμ hm hK`.

Use `set m' : ι →₀ ℕ := m + Finsupp.single q 1 with hm'`. Establish `hdeg' : m'.degree < N + 1`. Rewrite using `[hm', map_add, Finsupp.degree_single]`. Use linear arithmetic over natural numbers and integers. Establish `hK' : ∀ j ∈ K, m' j = 0`.

Introduce `j hj`. Establish `hqj : q ≠ j` using `fun h => hq (h ▸ hj)`. Simplify using `[hm', hK j hj, Finsupp.single_apply, hqj]`. Establish `hH` using `H m' hdeg' hK'`. Rewrite `hH` using `[MvPolynomial.coeff_mul]`.

Establish `hmem : (Finsupp.single q 1, m) ∈ Finset.HasAntidiagonal.antidiagonal m'`. Rewrite using `[Finset.HasAntidiagonal.mem_antidiagonal, hm']`. Conclude with `add_comm _ _`. Rewrite `hH` using `[← Finset.add_sum_erase _ _ hmem]`. Establish `hrest : ∑ x ∈ (Finset.HasAntidiagonal.antidiagonal m').erase (Finsupp.single q 1, m), a.coeff x.1 * F.coeff x.2 ∈ I`.

Use `Ideal.sum_mem _ (fun x hx => ?_)` and prove the remaining obligations. Take `⟨hne, hx⟩` from `Finset.mem_erase.mp hx`. Rewrite `hx` using `[Finset.HasAntidiagonal.mem_antidiagonal]`. Distinguish the cases in `hi : x.1 = 0`. Rewrite using `[hi, h0, zero_mul]`.

Conclude with `I.zero_mem`. Apply `I.mul_mem_left` to reduce the goal to its premises. Establish `hiq : x.1 ≠ Finsupp.single q 1`. Introduce `h`. Apply `hne` to reduce the goal to its premises.

Use `Prod.ext h ?_` and prove the remaining obligations. Rewrite `hx` using `[h, hm', add_comm m]`. Conclude with `add_left_cancel hx`. Establish `hxq : x.1 q + x.2 q = m q + 1`. Use `congrArg (fun f : ι →₀ ℕ => f q) hx` as an intermediate fact.

Simplify `this` using `[hm']`. Establish `hxe : x.1.erase q + x.2.erase q = m.erase q`. Use `congrArg (Finsupp.erase q) hx` as an intermediate fact. Simplify `this` using `[hm', Finsupp.erase_add]`. Establish `hD : (x.1.erase q).degree + (x.2.erase q).degree = (m.erase q).degree`.

Rewrite using `[← map_add, hxe]`. Establish `hdx : x.1.degree + x.2.degree = m.degree + 1`. Use `congrArg Finsupp.degree hx` as an intermediate fact. Simplify `this` using `[hm']`. Establish `hd1 : x.1.degree ≠ 0` using `fun h => hi ((Finsupp.degree_eq_zero_iff _).mp h)`.

Establish `hw : 2 ≤ x.1 q + 2 * (x.1.erase q).degree`. Distinguish the cases in `he : x.1.erase q = 0`. Establish `hs : Finsupp.single q (x.1 q) = x.1`. Simplify `Finsupp.single_add_erase q x.1` using `[he]`. Establish `h0' : x.1 q ≠ 0`.

Introduce `h`. Apply `hi` to reduce the goal to its premises. Rewrite using `[← hs, h, Finsupp.single_zero]`. Establish `h1' : x.1 q ≠ 1`. Introduce `h`.

Apply `hiq` to reduce the goal to its premises. Rewrite using `[← hs, h]`. Use linear arithmetic over natural numbers and integers. Establish `: (x.1.erase q).degree ≠ 0` using `fun h => he ((Finsupp.degree_eq_zero_iff _).mp h)`. Use linear arithmetic over natural numbers and integers.

Use `ih (x.2 q + 2 * (x.2.erase q).degree) (by omega) x.2 rfl (by omega) ?_` and prove the remaining obligations. Introduce `j hj`. Establish `h1` using `hK' j hj`. Rewrite `h1` using `[← hx]`. Simplify using `only [Finsupp.add_apply] at h1`.

Use linear arithmetic over natural numbers and integers. Establish `hmain : a.coeff (Finsupp.single q 1) * F.coeff m ∈ I` using `(Ideal.add_mem_iff_left I hrest).mp hH`. Conclude with `(Ideal.unit_mul_mem_iff_mem I hu).mp hmain`. Conclude with `fun m hm hK => key _ m rfl hm hK`.
-/
theorem coeff_mem_of_mul {O : Type} [CommRing O] (I : Ideal O) {ι : Type} (K : Set ι) (q : ι)
    (hq : q ∉ K) (a F : MvPolynomial ι O) (N : ℕ) (h0 : a.coeff 0 = 0)
    (hu : IsUnit (a.coeff (Finsupp.single q 1)))
    (H : ∀ m : ι →₀ ℕ, m.degree < N + 1 → (∀ j ∈ K, m j = 0) → (a * F).coeff m ∈ I) :
    ∀ m : ι →₀ ℕ, m.degree < N → (∀ j ∈ K, m j = 0) → F.coeff m ∈ I := by
  classical

  have key : ∀ n : ℕ, ∀ m : ι →₀ ℕ, m q + 2 * (m.erase q).degree = n → m.degree < N →
      (∀ j ∈ K, m j = 0) → F.coeff m ∈ I := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro m hμ hm hK
      set m' : ι →₀ ℕ := m + Finsupp.single q 1 with hm'
      have hdeg' : m'.degree < N + 1 := by
        rw [hm', map_add, Finsupp.degree_single]; omega
      have hK' : ∀ j ∈ K, m' j = 0 := by
        intro j hj
        have hqj : q ≠ j := fun h => hq (h ▸ hj)
        simp [hm', hK j hj, Finsupp.single_apply, hqj]
      have hH := H m' hdeg' hK'
      rw [MvPolynomial.coeff_mul] at hH
      have hmem : (Finsupp.single q 1, m) ∈ Finset.HasAntidiagonal.antidiagonal m' := by
        rw [Finset.HasAntidiagonal.mem_antidiagonal, hm']; exact add_comm _ _
      rw [← Finset.add_sum_erase _ _ hmem] at hH
      have hrest : ∑ x ∈ (Finset.HasAntidiagonal.antidiagonal m').erase (Finsupp.single q 1, m),
          a.coeff x.1 * F.coeff x.2 ∈ I := by
        refine Ideal.sum_mem _ (fun x hx => ?_)
        obtain ⟨hne, hx⟩ := Finset.mem_erase.mp hx
        rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
        by_cases hi : x.1 = 0
        · rw [hi, h0, zero_mul]; exact I.zero_mem
        · apply I.mul_mem_left
          have hiq : x.1 ≠ Finsupp.single q 1 := by
            intro h
            apply hne
            refine Prod.ext h ?_
            rw [h, hm', add_comm m] at hx
            exact add_left_cancel hx
          have hxq : x.1 q + x.2 q = m q + 1 := by
            have := congrArg (fun f : ι →₀ ℕ => f q) hx
            simpa [hm'] using this
          have hxe : x.1.erase q + x.2.erase q = m.erase q := by
            have := congrArg (Finsupp.erase q) hx
            simpa [hm', Finsupp.erase_add] using this
          have hD : (x.1.erase q).degree + (x.2.erase q).degree = (m.erase q).degree := by
            rw [← map_add, hxe]
          have hdx : x.1.degree + x.2.degree = m.degree + 1 := by
            have := congrArg Finsupp.degree hx
            simpa [hm'] using this
          have hd1 : x.1.degree ≠ 0 := fun h => hi ((Finsupp.degree_eq_zero_iff _).mp h)

          have hw : 2 ≤ x.1 q + 2 * (x.1.erase q).degree := by
            by_cases he : x.1.erase q = 0
            · have hs : Finsupp.single q (x.1 q) = x.1 := by
                simpa [he] using Finsupp.single_add_erase q x.1
              have h0' : x.1 q ≠ 0 := by
                intro h; apply hi; rw [← hs, h, Finsupp.single_zero]
              have h1' : x.1 q ≠ 1 := by
                intro h; apply hiq; rw [← hs, h]
              omega
            · have : (x.1.erase q).degree ≠ 0 := fun h => he ((Finsupp.degree_eq_zero_iff _).mp h)
              omega
          refine ih (x.2 q + 2 * (x.2.erase q).degree) (by omega) x.2 rfl (by omega) ?_
          intro j hj
          have h1 := hK' j hj
          rw [← hx] at h1
          simp only [Finsupp.add_apply] at h1
          omega
      have hmain : a.coeff (Finsupp.single q 1) * F.coeff m ∈ I :=
        (Ideal.add_mem_iff_left I hrest).mp hH
      exact (Ideal.unit_mul_mem_iff_mem I hu).mp hmain
  exact fun m hm hK => key _ m rfl hm hK

/- English proof (translation)
Introduce `O _ I ι K q hq a F N k h0 hu H`. Proceed by induction on `k generalizing F N with`. Consider the case `zero`. Introduce `m hm hK`. Simplify `hm) hK` using `using H m (by simpa`.

Consider the case `succ k ih`. Use `coeff_mem_of_mul I K q hq a F N h0 hu ?_` and prove the remaining obligations. Use `ih (a * F) (N + 1) ?_` and prove the remaining obligations. Introduce `m hm hK`. Use `H m (by omega) hK` as an intermediate fact.

Rewrite `this` using `[pow_succ, mul_assoc]`. Then use the resulting hypothesis.
-/
theorem coeff_mem_of_pow_mul : ∀ (O : Type) [CommRing O] (I : Ideal O) (ι : Type) (K : Set ι) (q : ι), q ∉ K → ∀ (a F : MvPolynomial ι O) (N k : ℕ), a.coeff 0 = 0 → IsUnit (a.coeff (Finsupp.single q 1)) → (∀ m : ι →₀ ℕ, m.degree < N + k → (∀ j ∈ K, m j = 0) → (a ^ k * F).coeff m ∈ I) → ∀ m : ι →₀ ℕ, m.degree < N → (∀ j ∈ K, m j = 0) → F.coeff m ∈ I := by
  intro O _ I ι K q hq a F N k h0 hu H
  induction k generalizing F N with
  | zero =>
    intro m hm hK
    simpa using H m (by simpa using hm) hK
  | succ k ih =>
    refine coeff_mem_of_mul I K q hq a F N h0 hu ?_
    refine ih (a * F) (N + 1) ?_
    intro m hm hK
    have := H m (by omega) hK
    rwa [pow_succ, mul_assoc] at this

end GlobalTheory.OrdMul
