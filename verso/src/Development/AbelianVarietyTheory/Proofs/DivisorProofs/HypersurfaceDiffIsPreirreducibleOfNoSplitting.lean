import Mathlib

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory

/- English proof (translation)
Proceed by induction on `a using UniqueFactorizationMonoid.induction_on_prime with`. Consider the case `h₁ => exact absurd rfl ha`. Consider the case `h₂ x hx => exact absurd (I.eq_top_of_isUnit_mem haI hx) hI.ne_top`. Consider the case `h₃ a p ha' hp ih`. Break down `hI.mem_or_mem haI with h | h` into its components or cases.

Conclude with `⟨p, hp, dvd_mul_right _ _, h⟩`. Take `⟨u, hu, hua, huI⟩` from `ih (right_ne_zero_of_mul ha) h`. Conclude with `⟨u, hu, dvd_mul_of_dvd_right hua _, huI⟩`.
-/
theorem exists_prime_factor_mem_prime_ideal_ufd {R : Type} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] (I : Ideal R) [hI : I.IsPrime] (a : R) (ha : a ≠ 0)
    (haI : a ∈ I) : ∃ u : R, Prime u ∧ u ∣ a ∧ u ∈ I := by
  induction a using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact absurd rfl ha
  | h₂ x hx => exact absurd (I.eq_top_of_isUnit_mem haI hx) hI.ne_top
  | h₃ a p ha' hp ih =>
    rcases hI.mem_or_mem haI with h | h
    · exact ⟨p, hp, dvd_mul_right _ _, h⟩
    · obtain ⟨u, hu, hua, huI⟩ := ih (right_ne_zero_of_mul ha) h
      exact ⟨u, hu, dvd_mul_of_dvd_right hua _, huI⟩

/- English proof (translation)
Introduce `U V hU hV ⟨p, hpS, hpU⟩ ⟨q, hqS, hqV⟩`. Establish `hfp : f ∈ p.asIdeal` using `by simpa using hpS.1`. Establish `hgp : g ∉ p.asIdeal` using `by simpa using hpS.2`. Take `⟨u, hu, huf, hup⟩` from `exists_prime_factor_mem_prime_ideal_ufd p.asIdeal f hf0 hfp`. Take `⟨v, rfl⟩` from `huf`.

Establish `hu0 : u ≠ 0` using `hu.ne_zero`. Establish `hv0 : v ≠ 0` using `right_ne_zero_of_mul hf0`. Establish `hdeg` using `MvPolynomial.totalDegree_mul_of_isDomain hu0 hv0`. Establish `hgrad : g ∉ (Ideal.span {u}).radical`. Introduce `hg`.

Apply `hgp` to reduce the goal to its premises. Establish `: (Ideal.span {u}).radical ≤ p.asIdeal` using `(Ideal.radical_mono ((Ideal.span_singleton_le_iff_mem _).mpr hup)).trans p.isPrime.radical.le`. Conclude with `this hg`. Rewrite `hgrad` using `[← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := Ω)]`. Simplify using `only [MvPolynomial.mem_vanishingIdeal_iff, not_forall] at hgrad`.

Take `⟨P, hP, hPg⟩` from `hgrad`. Establish `hPu : MvPolynomial.eval P u = 0`. Use `hP u (Ideal.mem_span_singleton_self u)` as an intermediate fact. Simplify `this` using `[MvPolynomial.aeval_eq_eval]`. Establish `hPg' : MvPolynomial.eval P g ≠ 0` using `by simpa [MvPolynomial.aeval_eq_eval] using hPg`.

Establish `hvg : g ∈ (Ideal.span {v}).radical`. Rewrite using `[← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := Ω)]`. Introduce `Q hQ`. Establish `hQv : MvPolynomial.eval Q v = 0`. Use `hQ v (Ideal.mem_span_singleton_self v)` as an intermediate fact.

Simplify `this` using `[MvPolynomial.aeval_eq_eval]`. Assume the negation of the conclusion as `hQg`. Apply `hno` to reduce the goal to its premises. Use `⟨u, v, by omega, by omega, rfl, P, Q, hPu, hPg', hQv, ?_⟩` and prove the remaining obligations. Simplify `hQg` using `[MvPolynomial.aeval_eq_eval]`.

Establish `hprime : (Ideal.span {u}).IsPrime` using `(Ideal.span_singleton_prime hu0).mpr hu`. Set `x : PrimeSpectrum (MvPolynomial σ Ω)` to `⟨Ideal.span {u}, hprime⟩`. Establish `key : ∀ y ∈ PrimeSpectrum.zeroLocus {u * v} \ PrimeSpectrum.zeroLocus {g}, y ∈ closure ({x} : Set _)`. Introduce `y hy`. Establish `hfy : u * v ∈ y.asIdeal` using `by simpa using hy.1`.

Establish `hgy : g ∉ y.asIdeal` using `by simpa using hy.2`. Rewrite using `[← PrimeSpectrum.le_iff_mem_closure]`. Use `show Ideal.span {u} ≤ y.asIdeal`. Rewrite using `[Ideal.span_singleton_le_iff_mem]`. Break down `y.isPrime.mem_or_mem hfy with h | h` into its components or cases.

Conclude with `h`. It suffices to derive a contradiction. Apply `hgy` to reduce the goal to its premises. Establish `: (Ideal.span {v}).radical ≤ y.asIdeal` using `(Ideal.radical_mono ((Ideal.span_singleton_le_iff_mem _).mpr h)).trans y.isPrime.radical.le`. Conclude with `this hvg`.

Establish `hxS : x ∈ PrimeSpectrum.zeroLocus {u * v} \ PrimeSpectrum.zeroLocus {g}`. Prove the components needed by the constructor for the conclusion. Simplify using `only [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff, SetLike.mem_coe]`. Conclude with `Ideal.mem_span_singleton.mpr (dvd_mul_right u v)`. Simplify using `only [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff, SetLike.mem_coe]`.

Introduce `hg`. Conclude with `hgp (((Ideal.span_singleton_le_iff_mem _).mpr hup) hg)`. Establish `hxU : x ∈ U`. Use `key p hpS` as an intermediate fact. Rewrite `this` using `[mem_closure_iff]`.

Take `⟨z, hzU, hz⟩` from `this U hU hpU`. Rewrite `hzU` using `[Set.mem_singleton_iff.mp hz]`. Conclude with `hzU`. Establish `hxV : x ∈ V`. Use `key q hqS` as an intermediate fact.

Rewrite `this` using `[mem_closure_iff]`. Take `⟨z, hzV, hz⟩` from `this V hV hqV`. Rewrite `hzV` using `[Set.mem_singleton_iff.mp hz]`. Conclude with `hzV`. Conclude with `⟨x, hxS, hxU, hxV⟩`.
-/
theorem hypersurface_diff_isPreirreducible (Ω : Type) [Field Ω] [IsAlgClosed Ω] (σ : Type) [Finite σ]
    (f g : MvPolynomial σ Ω) (D : ℕ) (hf0 : f ≠ 0) (hfD : f.totalDegree ≤ D)
    (hno : ¬ (∃ u v : MvPolynomial σ Ω, u.totalDegree ≤ D ∧ v.totalDegree ≤ D ∧ u * v = f ∧
      ∃ P Q : σ → Ω, MvPolynomial.eval P u = 0 ∧ MvPolynomial.eval P g ≠ 0 ∧
        MvPolynomial.eval Q v = 0 ∧ MvPolynomial.eval Q g ≠ 0)) :
    IsPreirreducible (PrimeSpectrum.zeroLocus {f} \ PrimeSpectrum.zeroLocus {g}) := by
  intro U V hU hV ⟨p, hpS, hpU⟩ ⟨q, hqS, hqV⟩
  have hfp : f ∈ p.asIdeal := by simpa using hpS.1
  have hgp : g ∉ p.asIdeal := by simpa using hpS.2
  obtain ⟨u, hu, huf, hup⟩ := exists_prime_factor_mem_prime_ideal_ufd p.asIdeal f hf0 hfp
  obtain ⟨v, rfl⟩ := huf
  have hu0 : u ≠ 0 := hu.ne_zero
  have hv0 : v ≠ 0 := right_ne_zero_of_mul hf0
  have hdeg := MvPolynomial.totalDegree_mul_of_isDomain hu0 hv0

  have hgrad : g ∉ (Ideal.span {u}).radical := by
    intro hg
    apply hgp
    have : (Ideal.span {u}).radical ≤ p.asIdeal :=
      (Ideal.radical_mono ((Ideal.span_singleton_le_iff_mem _).mpr hup)).trans
        p.isPrime.radical.le
    exact this hg
  rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := Ω)] at hgrad
  simp only [MvPolynomial.mem_vanishingIdeal_iff, not_forall] at hgrad
  obtain ⟨P, hP, hPg⟩ := hgrad
  have hPu : MvPolynomial.eval P u = 0 := by
    have := hP u (Ideal.mem_span_singleton_self u)
    simpa [MvPolynomial.aeval_eq_eval] using this
  have hPg' : MvPolynomial.eval P g ≠ 0 := by simpa [MvPolynomial.aeval_eq_eval] using hPg

  have hvg : g ∈ (Ideal.span {v}).radical := by
    rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := Ω)]
    intro Q hQ
    have hQv : MvPolynomial.eval Q v = 0 := by
      have := hQ v (Ideal.mem_span_singleton_self v)
      simpa [MvPolynomial.aeval_eq_eval] using this
    by_contra hQg
    apply hno
    refine ⟨u, v, by omega, by omega, rfl, P, Q, hPu, hPg', hQv, ?_⟩
    simpa [MvPolynomial.aeval_eq_eval] using hQg

  have hprime : (Ideal.span {u}).IsPrime := (Ideal.span_singleton_prime hu0).mpr hu
  let x : PrimeSpectrum (MvPolynomial σ Ω) := ⟨Ideal.span {u}, hprime⟩
  have key : ∀ y ∈ PrimeSpectrum.zeroLocus {u * v} \ PrimeSpectrum.zeroLocus {g},
      y ∈ closure ({x} : Set _) := by
    intro y hy
    have hfy : u * v ∈ y.asIdeal := by simpa using hy.1
    have hgy : g ∉ y.asIdeal := by simpa using hy.2
    rw [← PrimeSpectrum.le_iff_mem_closure]
    show Ideal.span {u} ≤ y.asIdeal
    rw [Ideal.span_singleton_le_iff_mem]
    rcases y.isPrime.mem_or_mem hfy with h | h
    · exact h
    · exfalso; apply hgy
      have : (Ideal.span {v}).radical ≤ y.asIdeal :=
        (Ideal.radical_mono ((Ideal.span_singleton_le_iff_mem _).mpr h)).trans
          y.isPrime.radical.le
      exact this hvg
  have hxS : x ∈ PrimeSpectrum.zeroLocus {u * v} \ PrimeSpectrum.zeroLocus {g} := by
    constructor
    · simp only [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff, SetLike.mem_coe]
      exact Ideal.mem_span_singleton.mpr (dvd_mul_right u v)
    · simp only [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff, SetLike.mem_coe]
      intro hg
      exact hgp (((Ideal.span_singleton_le_iff_mem _).mpr hup) hg)
  have hxU : x ∈ U := by
    have := key p hpS
    rw [mem_closure_iff] at this
    obtain ⟨z, hzU, hz⟩ := this U hU hpU
    rw [Set.mem_singleton_iff.mp hz] at hzU; exact hzU
  have hxV : x ∈ V := by
    have := key q hqS
    rw [mem_closure_iff] at this
    obtain ⟨z, hzV, hz⟩ := this V hV hqV
    rw [Set.mem_singleton_iff.mp hz] at hzV; exact hzV
  exact ⟨x, hxS, hxU, hxV⟩

end GlobalTheory
