import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowForms.Imports
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

/- English proof (translation)
Proceed by induction on `g using MvPolynomial.induction_on with`. Consider the case `C a => simp [MvPolynomial.algebraMap_apply]`. Consider the case `add p q hp hq => simp only [map_add, hp, hq, add_mul, Finset.sum_add_distrib]`. Consider the case `mul_X p j hp`. Simplify using `only [map_mul, aeval_X, Derivation.leibniz, smul_eq_mul, hp, map_add, add_mul, Finset.sum_add_distrib, pderiv_X, Finset.mul_sum]`.

Use `congr 1`. Rewrite using `[Finset.sum_eq_single j]`. Simplify using the standard rewrite rules. Introduce `b _ hb`. Simplify using `[Ne.symm hb]`.

Simplify using the standard rewrite rules. Use `Finset.sum_congr rfl fun b _ => by ring` and prove the remaining obligations.
-/
theorem pderiv_aeval_eq_sum {F K : Type*} [CommRing F] [CommRing K] [Algebra F K]
    {σ τ : Type*} [Fintype σ] (ψ : σ → MvPolynomial τ K) (i : τ) (g : MvPolynomial σ F) :
    pderiv i (aeval ψ g) = ∑ j, aeval ψ (pderiv j g) * pderiv i (ψ j) := by
  classical
  induction g using MvPolynomial.induction_on with
  | C a => simp [MvPolynomial.algebraMap_apply]
  | add p q hp hq => simp only [map_add, hp, hq, add_mul, Finset.sum_add_distrib]
  | mul_X p j hp =>
    simp only [map_mul, aeval_X, Derivation.leibniz, smul_eq_mul, hp, map_add, add_mul,
      Finset.sum_add_distrib, pderiv_X, Finset.mul_sum]
    congr 1
    · rw [Finset.sum_eq_single j]
      · simp
      · intro b _ hb
        simp [Ne.symm hb]
      · simp
    · refine Finset.sum_congr rfl fun b _ => by ring

/- English proof (translation)
Take `⟨j₁, j₂⟩` from `j`. Simplify using `only [genSubst, map_sub, Derivation.leibniz, smul_eq_mul, pderiv_C, mul_zero, zero_add, map_sum, pderiv_X, Pi.single_apply, mul_zero]`. Distinguish the cases in `h : j₁ = i`. Substitute `h` using the available equality. Simplify using `[Prod.ext_iff, eq_comm, mul_comm]`.

Simplify using `[Prod.ext_iff, h]`.
-/
theorem pderiv_genSubst {K : Type*} [CommRing K] {n k : ℕ} (ζ c : Fin n → K) (i : Fin k) (m : Fin n)
    (j : Fin k × Fin n) :
    pderiv (i, m) (genSubst ζ c j) =
      (if j = (i, m) then 1 else 0) - (if j.1 = i then C (ζ m) * C (c j.2) else 0) := by
  classical
  obtain ⟨j₁, j₂⟩ := j
  simp only [genSubst, map_sub, Derivation.leibniz, smul_eq_mul, pderiv_C, mul_zero, zero_add,
    map_sum, pderiv_X, Pi.single_apply, mul_zero]
  by_cases h : j₁ = i
  · subst h
    simp [Prod.ext_iff, eq_comm, mul_comm]
  · simp [Prod.ext_iff, h]

/- English proof (translation)
Introduce and unpack `⟨q, hq⟩`. Establish `hlt : degreeOf i (pderiv i g) < degreeOf i g`. Rewrite using `[degreeOf_lt_iff hi]`. Introduce `m hm`. Rewrite `hm` using `[mem_support_iff, coeff_pderiv]`.

Establish `h1 : m + Finsupp.single i 1 ∈ g.support` using `mem_support_iff.2 (left_ne_zero_of_mul hm)`. Use `monomial_le_degreeOf i h1` as an intermediate fact. Simplify using `only [Finsupp.add_apply, Finsupp.single_eq_same] at this`. Use linear arithmetic over natural numbers and integers. Establish `hne : pderiv i g ≠ 0`.

Take `⟨s, hs, hsd⟩` from `Finset.exists_mem_eq_sup g.support (support_nonempty.2 hg) (fun m => m i)`. Rewrite `hsd` using `[← degreeOf_eq_sup]`. Establish `hle : Finsupp.single i 1 ≤ s` using `Finsupp.single_le_iff.2 (by omega)`. Introduce `h0`. Use `congrArg (coeff (s - Finsupp.single i 1)) h0` as an intermediate fact.

Rewrite `this` using `[coeff_pderiv, coeff_zero, tsub_add_cancel_of_le hle]`. Establish `hcs : coeff s g ≠ 0` using `mem_support_iff.1 hs`. Establish `hsi : (((s - Finsupp.single i 1 : σ →₀ ℕ) i : ℕ) : F) + 1 ≠ 0`. Conclude with `Nat.cast_add_one_ne_zero _`. Conclude with `mul_ne_zero hcs hsi this`.

Rewrite `hlt` using `[hq, degreeOf_mul_eq hg (right_ne_zero_of_mul (hq ▸ hne))]`. Use linear arithmetic over natural numbers and integers.
-/
theorem not_dvd_pderiv_of_degreeOf_pos {F σ : Type*} [Field F] [CharZero F] {g : MvPolynomial σ F}
    (hg : g ≠ 0) {i : σ} (hi : 0 < degreeOf i g) : ¬ g ∣ pderiv i g := by
  classical
  rintro ⟨q, hq⟩
  have hlt : degreeOf i (pderiv i g) < degreeOf i g := by
    rw [degreeOf_lt_iff hi]
    intro m hm
    rw [mem_support_iff, coeff_pderiv] at hm
    have h1 : m + Finsupp.single i 1 ∈ g.support := mem_support_iff.2 (left_ne_zero_of_mul hm)
    have := monomial_le_degreeOf i h1
    simp only [Finsupp.add_apply, Finsupp.single_eq_same] at this
    omega
  have hne : pderiv i g ≠ 0 := by
    obtain ⟨s, hs, hsd⟩ := Finset.exists_mem_eq_sup g.support (support_nonempty.2 hg) (fun m => m i)
    rw [← degreeOf_eq_sup] at hsd
    have hle : Finsupp.single i 1 ≤ s := Finsupp.single_le_iff.2 (by omega)
    intro h0
    have := congrArg (coeff (s - Finsupp.single i 1)) h0
    rw [coeff_pderiv, coeff_zero, tsub_add_cancel_of_le hle] at this
    have hcs : coeff s g ≠ 0 := mem_support_iff.1 hs
    have hsi : (((s - Finsupp.single i 1 : σ →₀ ℕ) i : ℕ) : F) + 1 ≠ 0 := by
      exact Nat.cast_add_one_ne_zero _
    exact mul_ne_zero hcs hsi this
  rw [hq, degreeOf_mul_eq hg (right_ne_zero_of_mul (hq ▸ hne))] at hlt
  omega

/- English proof (translation)
Introduce `F _ _ n k P g c hP hg hc`. Use `hP.isPrime` as an intermediate fact. Establish `hmem : ∀ h, h ∈ incIdeal P (k + 1) ↔ g ∣ h`. Introduce `h`. Rewrite using `[← hg.2 h, incIdeal]`.

Simplify using `only [Submodule.mem_iInf, RingHom.mem_ker]`. Establish `hg0 : aeval (genSubst (genPt P) c) g = 0` using `(h₁ F n (k + 1) P c hc g).1 ((hmem g).2 dvd_rfl)`. Establish `hA : ∀ m, aeval (genSubst (genPt P) c) (pderiv (0, m) g) = C (genPt P m) * ∑ l, aeval (genSubst (genPt P) c) (pderiv (0, l) g) * C (c l)`. Introduce `m`. Establish `h` using `pderiv_aeval_eq_sum (genSubst (genPt P) c) (0, m) g`.

Rewrite `h` using `[hg0, map_zero]`. Simplify using `only [pderiv_genSubst, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, Fintype.sum_prod_type, Fin.sum_univ_succ, Fin.succ_ne_zero, if_false, Finset.sum_const_zero, add_zero] at h`. Rewrite `h` using `[eq_comm, sub_eq_zero]`. Rewrite using `[h, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun l _ => by ring`.

Take `⟨δ, hδ, hhom⟩` from `h₂ F n (k + 1) P g hP hg`. Take `⟨s, hs⟩` from `support_nonempty.2 hg.1`. Choose the witnesses or unpack the hypotheses as in `⟨l, hl⟩ : ∃ l, 0 < s (0, l) := by`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`.

Establish `hw` using `congrFun (hhom (mem_support_iff.1 hs)) 0`. Establish `: (Finsupp.weight (groupWeight (k + 1) n) s) 0 = 0`. Rewrite using `[Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]`. Use `Finset.sum_eq_zero fun x _ => ?_` and prove the remaining obligations. Take `⟨x₁, x₂⟩` from `x`.

Distinguish the cases in `hx : x₁ = 0`. Substitute `hx` using the available equality. Simplify using `[Nat.le_zero.1 (hcon x₂)]`. Simplify using `[groupWeight, hx]`. Use linear arithmetic over natural numbers and integers.

Take `⟨ρ, hρ⟩ : ∃ ρ, ∀ m, aeval (genSubst (genPt P) c) (pderiv (0, m) g) = C (genPt P m) * ρ` from `⟨_, hA⟩`. Establish `hdeg : 0 < degreeOf (0, l) g` using `lt_of_lt_of_le hl (monomial_le_degreeOf _ hs)`. Use `⟨Pi.single l 1, ?_, fun m => ?_⟩` and prove the remaining obligations. Establish `hsum : (∑ l', C ((Pi.single l (1 : F) : Fin n → F) l') * pderiv (0, l') g) = pderiv (0, l) g`. Rewrite using `[Finset.sum_eq_single l]`.

Simplify using the standard rewrite rules. Introduce `b _ hb`. Simplify using `[hb]`. Simplify using the standard rewrite rules. Rewrite using `[hsum, hmem]`.

Conclude with `not_dvd_pderiv_of_degreeOf_pos hg.1 hdeg`. Simplify using `only [map_sum, map_mul, aeval_C, MvPolynomial.algebraMap_apply, hρ]`. Simplify using `only [Finset.sum_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun l' _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ChowFormBirational.proof (h₁ : IncidenceGeneric.Statement)
    (h₂ : ChowFormMultiHomog.Statement) : ChowFormBirational.Statement := by
  intro F _ _ n k P g c hP hg hc
  have := hP.isPrime
  classical

  have hmem : ∀ h, h ∈ incIdeal P (k + 1) ↔ g ∣ h := by
    intro h
    rw [← hg.2 h, incIdeal]
    simp only [Submodule.mem_iInf, RingHom.mem_ker]
  have hg0 : aeval (genSubst (genPt P) c) g = 0 :=
    (h₁ F n (k + 1) P c hc g).1 ((hmem g).2 dvd_rfl)

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

  obtain ⟨δ, hδ, hhom⟩ := h₂ F n (k + 1) P g hP hg
  obtain ⟨s, hs⟩ := support_nonempty.2 hg.1
  obtain ⟨l, hl⟩ : ∃ l, 0 < s (0, l) := by
    by_contra hcon
    push Not at hcon
    have hw := congrFun (hhom (mem_support_iff.1 hs)) 0
    have : (Finsupp.weight (groupWeight (k + 1) n) s) 0 = 0 := by
      rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]
      refine Finset.sum_eq_zero fun x _ => ?_
      obtain ⟨x₁, x₂⟩ := x
      by_cases hx : x₁ = 0
      · subst hx; simp [Nat.le_zero.1 (hcon x₂)]
      · simp [groupWeight, hx]
    omega
  obtain ⟨ρ, hρ⟩ : ∃ ρ, ∀ m, aeval (genSubst (genPt P) c) (pderiv (0, m) g) = C (genPt P m) * ρ :=
    ⟨_, hA⟩
  have hdeg : 0 < degreeOf (0, l) g := lt_of_lt_of_le hl (monomial_le_degreeOf _ hs)
  refine ⟨Pi.single l 1, ?_, fun m => ?_⟩
  · have hsum : (∑ l', C ((Pi.single l (1 : F) : Fin n → F) l') * pderiv (0, l') g) =
        pderiv (0, l) g := by
      rw [Finset.sum_eq_single l]
      · simp
      · intro b _ hb; simp [hb]
      · simp
    rw [hsum, hmem]
    exact not_dvd_pderiv_of_degreeOf_pos hg.1 hdeg
  · simp only [map_sum, map_mul, aeval_C, MvPolynomial.algebraMap_apply, hρ]
    simp only [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l' _ => ?_
    ring

end

end GroundTheory.Heights₂.Heights
