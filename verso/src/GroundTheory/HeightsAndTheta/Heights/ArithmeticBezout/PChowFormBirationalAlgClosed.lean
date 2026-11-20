import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsChowFormBirationalAlgClosed
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.RenameProdMapMul
import GroundTheory.HeightsAndTheta.Heights.ChowForms.Assembly
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

/- English proof (translation)
Introduce and unpack `⟨q, hq⟩`. Establish `hi : 0 < degreeOf i g`. Take `⟨m, hm⟩` from `support_nonempty.2 hne`. Rewrite `hm` using `[mem_support_iff, coeff_pderiv]`. Establish `h1 : m + Finsupp.single i 1 ∈ g.support` using `mem_support_iff.2 (left_ne_zero_of_mul hm)`.

Use `monomial_le_degreeOf i h1` as an intermediate fact. Simplify using `only [Finsupp.add_apply, Finsupp.single_eq_same] at this`. Use linear arithmetic over natural numbers and integers. Establish `hlt : degreeOf i (pderiv i g) < degreeOf i g`. Rewrite using `[degreeOf_lt_iff hi]`.

Introduce `m hm`. Rewrite `hm` using `[mem_support_iff, coeff_pderiv]`. Establish `h1 : m + Finsupp.single i 1 ∈ g.support` using `mem_support_iff.2 (left_ne_zero_of_mul hm)`. Use `monomial_le_degreeOf i h1` as an intermediate fact. Simplify using `only [Finsupp.add_apply, Finsupp.single_eq_same] at this`.

Use linear arithmetic over natural numbers and integers. Rewrite `hlt` using `[hq, degreeOf_mul_eq hg (right_ne_zero_of_mul (hq ▸ hne))]`. Use linear arithmetic over natural numbers and integers.
-/
theorem not_dvd_pderiv_of_pderiv_ne_zero {F σ : Type*} [Field F] {g : MvPolynomial σ F}
    (hg : g ≠ 0) {i : σ} (hne : pderiv i g ≠ 0) : ¬ g ∣ pderiv i g := by
  classical
  rintro ⟨q, hq⟩
  have hi : 0 < degreeOf i g := by
    obtain ⟨m, hm⟩ := support_nonempty.2 hne
    rw [mem_support_iff, coeff_pderiv] at hm
    have h1 : m + Finsupp.single i 1 ∈ g.support := mem_support_iff.2 (left_ne_zero_of_mul hm)
    have := monomial_le_degreeOf i h1
    simp only [Finsupp.add_apply, Finsupp.single_eq_same] at this
    omega
  have hlt : degreeOf i (pderiv i g) < degreeOf i g := by
    rw [degreeOf_lt_iff hi]
    intro m hm
    rw [mem_support_iff, coeff_pderiv] at hm
    have h1 : m + Finsupp.single i 1 ∈ g.support := mem_support_iff.2 (left_ne_zero_of_mul hm)
    have := monomial_le_degreeOf i h1
    simp only [Finsupp.add_apply, Finsupp.single_eq_same] at this
    omega
  rw [hq, degreeOf_mul_eq hg (right_ne_zero_of_mul (hq ▸ hne))] at hlt
  omega

/- English proof (translation)
Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Establish `hall : ∀ v, pderiv v g = 0`. Introduce and unpack `⟨i, l⟩`. Take `⟨c, hc2, hc⟩` from `hg.rename_swap 0 i`.

Establish `hinj : Function.Injective (Prod.map (Equiv.swap (0 : Fin (k + 1)) i) (id : Fin n → Fin n))` using `(Equiv.swap 0 i).injective.prodMap Function.injective_id`. Establish `h` using `pderiv_rename hinj (0, l) g`. Rewrite `h` using `[hc, pderiv_C_mul, hcon l, map_zero, Prod.map_apply, Equiv.swap_apply_left, id]`. Establish `hc0 : c ≠ 0`. Introduce and unpack `rfl`.

Simplify using `at hc2`. Conclude with `(mul_eq_zero.1 h).resolve_left fun h0 => hc0 (C_eq_zero.1 h0)`. Establish `hexp : ∀ s ∈ g.support, ∀ v, p ∣ s v`. Introduce `s hs v`. Distinguish the cases in `h0 : s v = 0`.

Simplify using `[h0]`. Establish `hle : Finsupp.single v 1 ≤ s` using `Finsupp.single_le_iff.2 (by omega)`. Establish `h1` using `congrArg (coeff (s - Finsupp.single v 1)) (hall v)`. Rewrite `h1` using `[coeff_pderiv, coeff_zero, tsub_add_cancel_of_le hle]`. Establish `h2` using `(mul_eq_zero.1 h1).resolve_left (mem_support_iff.1 hs)`.

Rewrite `h2` using `[Finsupp.tsub_apply, Finsupp.single_eq_same]`. Establish `h3 : ((s v : ℕ) : F) = 0`. Rewrite using `[← Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 h0)]`. Use `push_cast`. Conclude with `h2`.

Conclude with `(CharP.cast_eq_zero_iff F p _).1 h3`. Choose the witnesses or unpack the hypotheses as in `⟨h, hgh⟩ : ∃ h : MvPolynomial (Fin (k + 1) × Fin n) F, h ^ p = g := by`. Establish `hroot : ∀ a : F, ∃ b : F, b ^ p = a` using `fun a => IsAlgClosed.exists_pow_nat_eq a hp.out.pos`. Use `choose r hr using hroot`. Use `⟨∑ s ∈ g.support, monomial (Finsupp.mapRange (· / p) (Nat.zero_div p) s) (r (coeff s g)), ?_⟩` and prove the remaining obligations.

Rewrite using `[sum_pow_char]`. Use `conv_rhs => rw [as_sum g]`. Use `Finset.sum_congr rfl fun s hs => ?_` and prove the remaining obligations. Establish `hs' : p • Finsupp.mapRange (· / p) (Nat.zero_div p) s = s`. Use extensionality with `v`.

Simplify using `[Nat.mul_div_cancel' (hexp s hs v)]`. Rewrite using `[monomial_pow, hr, hs']`. Establish `hmem : ∀ q, q ∈ incIdeal P (k + 1) ↔ g ∣ q`. Introduce `q`. Rewrite using `[← hg.2 q, incIdeal]`.

Simplify using `only [Submodule.mem_iInf, RingHom.mem_ker]`. Establish `hprime : Prime g`. Establish `hI` using `IncIdealPrime.full F n (k + 1) P hP.isPrime hP.isRelevant`. Establish `hspan : incIdeal P (k + 1) = Ideal.span {g}`. Use extensionality with `q`.

Rewrite using `[Ideal.mem_span_singleton, hmem]`. Rewrite `hI` using `[hspan]`. Conclude with `(Ideal.span_singleton_prime hg.1).1 hI`. Establish `hh0 : h ≠ 0`. Introduce and unpack `rfl`.

Conclude with `hg.1 (by rw [← hgh, zero_pow hp.out.ne_zero])`. Take `⟨q, hq⟩` from `hprime.dvd_of_dvd_pow (show g ∣ h ^ p by rw [hgh])`. Take `⟨m, hm⟩ : ∃ m, p = m + 2` from `⟨p - 2, by have := hp.out.two_le; omega⟩`. Establish `h1 : h * (h ^ (m + 1) * q) = h * 1`. Rewrite using `[mul_one]`.

Use `conv_rhs => rw [hq, ← hgh, hm]`. Expand and normalize the polynomial expressions, which then agree. Establish `hu : IsUnit (h ^ (m + 1))` using `IsUnit.of_mul_eq_one q (mul_left_cancel₀ hh0 h1)`. Establish `hu' : IsUnit h` using `(isUnit_pow_iff (Nat.succ_ne_zero m)).1 hu`. Conclude with `hprime.not_isUnit (hgh ▸ hu'.pow p)`.
-/
theorem IsChowForm.exists_pderiv_ne_zero {F : Type} [Field F] [IsAlgClosed F] {p : ℕ} [hp : Fact p.Prime]
    [CharP F p] {n k : ℕ} {P : Ideal (MvPolynomial (Fin n) F)} (hP : IsProjPrime P)
    {g : MvPolynomial (Fin (k + 1) × Fin n) F} (hg : IsChowForm P (k + 1) g) :
    ∃ l, pderiv (0, l) g ≠ 0 := by
  classical
  by_contra hcon
  push Not at hcon

  have hall : ∀ v, pderiv v g = 0 := by
    rintro ⟨i, l⟩
    obtain ⟨c, hc2, hc⟩ := hg.rename_swap 0 i
    have hinj : Function.Injective (Prod.map (Equiv.swap (0 : Fin (k + 1)) i) (id : Fin n → Fin n)) :=
      (Equiv.swap 0 i).injective.prodMap Function.injective_id
    have h := pderiv_rename hinj (0, l) g
    rw [hc, pderiv_C_mul, hcon l, map_zero, Prod.map_apply, Equiv.swap_apply_left, id] at h
    have hc0 : c ≠ 0 := by
      rintro rfl
      simp at hc2
    exact (mul_eq_zero.1 h).resolve_left fun h0 => hc0 (C_eq_zero.1 h0)

  have hexp : ∀ s ∈ g.support, ∀ v, p ∣ s v := by
    intro s hs v
    by_cases h0 : s v = 0
    · simp [h0]
    have hle : Finsupp.single v 1 ≤ s := Finsupp.single_le_iff.2 (by omega)
    have h1 := congrArg (coeff (s - Finsupp.single v 1)) (hall v)
    rw [coeff_pderiv, coeff_zero, tsub_add_cancel_of_le hle] at h1
    have h2 := (mul_eq_zero.1 h1).resolve_left (mem_support_iff.1 hs)
    rw [Finsupp.tsub_apply, Finsupp.single_eq_same] at h2
    have h3 : ((s v : ℕ) : F) = 0 := by
      rw [← Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 h0)]
      push_cast
      exact h2
    exact (CharP.cast_eq_zero_iff F p _).1 h3

  obtain ⟨h, hgh⟩ : ∃ h : MvPolynomial (Fin (k + 1) × Fin n) F, h ^ p = g := by
    have hroot : ∀ a : F, ∃ b : F, b ^ p = a := fun a => IsAlgClosed.exists_pow_nat_eq a hp.out.pos
    choose r hr using hroot
    refine ⟨∑ s ∈ g.support, monomial (Finsupp.mapRange (· / p) (Nat.zero_div p) s) (r (coeff s g)), ?_⟩
    rw [sum_pow_char]
    conv_rhs => rw [as_sum g]
    refine Finset.sum_congr rfl fun s hs => ?_
    have hs' : p • Finsupp.mapRange (· / p) (Nat.zero_div p) s = s := by
      ext v
      simp [Nat.mul_div_cancel' (hexp s hs v)]
    rw [monomial_pow, hr, hs']

  have hmem : ∀ q, q ∈ incIdeal P (k + 1) ↔ g ∣ q := by
    intro q
    rw [← hg.2 q, incIdeal]
    simp only [Submodule.mem_iInf, RingHom.mem_ker]
  have hprime : Prime g := by
    have hI := IncIdealPrime.full F n (k + 1) P hP.isPrime hP.isRelevant
    have hspan : incIdeal P (k + 1) = Ideal.span {g} := by
      ext q
      rw [Ideal.mem_span_singleton, hmem]
    rw [hspan] at hI
    exact (Ideal.span_singleton_prime hg.1).1 hI
  have hh0 : h ≠ 0 := by
    rintro rfl
    exact hg.1 (by rw [← hgh, zero_pow hp.out.ne_zero])
  obtain ⟨q, hq⟩ := hprime.dvd_of_dvd_pow (show g ∣ h ^ p by rw [hgh])
  obtain ⟨m, hm⟩ : ∃ m, p = m + 2 := ⟨p - 2, by have := hp.out.two_le; omega⟩
  have h1 : h * (h ^ (m + 1) * q) = h * 1 := by
    rw [mul_one]
    conv_rhs => rw [hq, ← hgh, hm]
    ring
  have hu : IsUnit (h ^ (m + 1)) := IsUnit.of_mul_eq_one q (mul_left_cancel₀ hh0 h1)
  have hu' : IsUnit h := (isUnit_pow_iff (Nat.succ_ne_zero m)).1 hu
  exact hprime.not_isUnit (hgh ▸ hu'.pow p)

/- English proof (translation)
Introduce `F _ _ n k P g c hP hg hc`. Take `_ | ⟨p, hp, hch⟩` from `CharP.exists' F`. Conclude with `ChowFormBirational.full F n k P g c hP hg hc`. Use `hP.isPrime` as an intermediate fact. Establish `hmem : ∀ h, h ∈ incIdeal P (k + 1) ↔ g ∣ h`.

Introduce `h`. Rewrite using `[← hg.2 h, incIdeal]`. Simplify using `only [Submodule.mem_iInf, RingHom.mem_ker]`. Establish `hg0 : aeval (genSubst (genPt P) c) g = 0` using `(IncidenceGeneric.full F n (k + 1) P c hc g).1 ((hmem g).2 dvd_rfl)`. Establish `hA : ∀ m, aeval (genSubst (genPt P) c) (pderiv (0, m) g) = C (genPt P m) * ∑ l, aeval (genSubst (genPt P) c) (pderiv (0, l) g) * C (c l)`.

Introduce `m`. Establish `h` using `pderiv_aeval_eq_sum (genSubst (genPt P) c) (0, m) g`. Rewrite `h` using `[hg0, map_zero]`. Simplify using `only [pderiv_genSubst, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, Fintype.sum_prod_type, Fin.sum_univ_succ, Fin.succ_ne_zero, if_false, Finset.sum_const_zero, add_zero] at h`. Rewrite `h` using `[eq_comm, sub_eq_zero]`.

Rewrite using `[h, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun l _ => by ring`. Take `⟨ρ, hρ⟩ : ∃ ρ, ∀ m, aeval (genSubst (genPt P) c) (pderiv (0, m) g) = C (genPt P m) * ρ` from `⟨_, hA⟩`. Take `⟨l, hl⟩` from `IsChowForm.exists_pderiv_ne_zero (p := p) hP hg`. Use `⟨Pi.single l 1, ?_, fun m => ?_⟩` and prove the remaining obligations.

Establish `hsum : (∑ l', C ((Pi.single l (1 : F) : Fin n → F) l') * pderiv (0, l') g) = pderiv (0, l) g`. Rewrite using `[Finset.sum_eq_single l]`. Simplify using the standard rewrite rules. Introduce `b _ hb`. Simplify using `[hb]`.

Simplify using the standard rewrite rules. Rewrite using `[hsum, hmem]`. Conclude with `not_dvd_pderiv_of_pderiv_ne_zero hg.1 hl`. Simplify using `only [map_sum, map_mul, aeval_C, MvPolynomial.algebraMap_apply, hρ]`. Simplify using `only [Finset.sum_mul, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun l' _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ChowFormBirationalAlgClosed.proof : ChowFormBirationalAlgClosed.Statement := by
  intro F _ _ n k P g c hP hg hc
  obtain _ | ⟨p, hp, hch⟩ := CharP.exists' F
  · exact ChowFormBirational.full F n k P g c hP hg hc
  have := hP.isPrime
  classical

  have hmem : ∀ h, h ∈ incIdeal P (k + 1) ↔ g ∣ h := by
    intro h
    rw [← hg.2 h, incIdeal]
    simp only [Submodule.mem_iInf, RingHom.mem_ker]
  have hg0 : aeval (genSubst (genPt P) c) g = 0 :=
    (IncidenceGeneric.full F n (k + 1) P c hc g).1 ((hmem g).2 dvd_rfl)

  have hA : ∀ m, aeval (genSubst (genPt P) c) (pderiv (0, m) g) =
      C (genPt P m) * ∑ l, aeval (genSubst (genPt P) c) (pderiv (0, l) g) * C (c l) := by
    intro m
    have h := pderiv_aeval_eq_sum (genSubst (genPt P) c) (0, m) g
    rw [hg0, map_zero] at h
    simp only [pderiv_genSubst, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, Fintype.sum_prod_type, Fin.sum_univ_succ,
      Fin.succ_ne_zero, if_false, Finset.sum_const_zero, add_zero] at h
    rw [eq_comm, sub_eq_zero] at h
    rw [h, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  obtain ⟨ρ, hρ⟩ : ∃ ρ, ∀ m, aeval (genSubst (genPt P) c) (pderiv (0, m) g) = C (genPt P m) * ρ :=
    ⟨_, hA⟩

  obtain ⟨l, hl⟩ := IsChowForm.exists_pderiv_ne_zero (p := p) hP hg
  refine ⟨Pi.single l 1, ?_, fun m => ?_⟩
  · have hsum : (∑ l', C ((Pi.single l (1 : F) : Fin n → F) l') * pderiv (0, l') g) =
        pderiv (0, l) g := by
      rw [Finset.sum_eq_single l]
      · simp
      · intro b _ hb; simp [hb]
      · simp
    rw [hsum, hmem]
    exact not_dvd_pderiv_of_pderiv_ne_zero hg.1 hl
  · simp only [map_sum, map_mul, aeval_C, MvPolynomial.algebraMap_apply, hρ]
    simp only [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l' _ => ?_
    ring

end

end GroundTheory.Heights₂.Heights
