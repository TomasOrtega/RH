import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LCpeelLemmas

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

/- English proof (translation)
Unfold `peel at hd`. Rewrite `hd` using `[coeff_sum]`. Take `⟨m, hm, hne⟩` from `Finset.exists_ne_zero_of_sum_ne_zero hd`. Take `⟨hm1, hm2⟩` from `Finset.mem_filter.mp hm`. Use `⟨m, hm1, hm2, ?_⟩` and prove the remaining obligations.

Rewrite `hne` using `[coeff_monomial]`. Use `split_ifs at hne with h`. Conclude with `h.symm`. Conclude with `absurd rfl hne`.
-/
theorem lcpeel_support {B : Type*} [CommRing B] {r n : ℕ} (l j : Fin n) (a0 : Fin r) (k : ℕ)
    (g : MvPolynomial (Fin r × Fin n) B) (d : Fin r × Fin n →₀ ℕ)
    (hd : coeff d (peel l j a0 k g) ≠ 0) :
    ∃ m ∈ g.support, m (a0, l) = k ∧ d = (m.erase (a0, l)).erase (a0, j) := by
  unfold peel at hd
  rw [coeff_sum] at hd
  obtain ⟨m, hm, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hd
  obtain ⟨hm1, hm2⟩ := Finset.mem_filter.mp hm
  refine ⟨m, hm1, hm2, ?_⟩
  rw [coeff_monomial] at hne
  split_ifs at hne with h
  · exact h.symm
  · exact absurd rfl hne

/- English proof (translation)
Use `first`. Consider the case `(rw [Finsupp.weight_apply, Finsupp.sum_single_index]; exact zero_smul ℕ (w s))`. Consider the case `simp [Finsupp.weight_apply]`.
-/
private theorem weight_single_eq_nsmul {σ M : Type*} [AddCommMonoid M] (w : σ → M) (s : σ) (c : ℕ) :
    Finsupp.weight w (Finsupp.single s c) = c • w s := by
  first
    | (rw [Finsupp.weight_apply, Finsupp.sum_single_index]; exact zero_smul ℕ (w s))
    | simp [Finsupp.weight_apply]

/- English proof (translation)
Use extensionality with `⟨b, t⟩`. Simplify using `only [Finsupp.add_apply, Finsupp.erase_apply, Finsupp.single_apply, Prod.mk.injEq]`. Distinguish the cases in `hb : b = a0`. Substitute `hb` using the available equality. Distinguish the cases in `hl : t = l`.

Substitute `hl` using the available equality. Simplify using `[hlj, Ne.symm hlj]`. Distinguish the cases in `hj : t = j`. Substitute `hj` using the available equality. Simplify using `[hl, Ne.symm hl]`.

Simplify using `[hl, hj, Ne.symm hl, Ne.symm hj]`. Simplify using `[hb, Ne.symm hb]`.
-/
private theorem eq_erase_erase_add_single_add_single {r n : ℕ} (l j : Fin n) (hlj : l ≠ j) (a0 : Fin r)
    (m : Fin r × Fin n →₀ ℕ) :
    m = (m.erase (a0, l)).erase (a0, j) + Finsupp.single (a0, l) (m (a0, l)) +
      Finsupp.single (a0, j) (m (a0, j)) := by
  ext ⟨b, t⟩
  simp only [Finsupp.add_apply, Finsupp.erase_apply, Finsupp.single_apply, Prod.mk.injEq]
  by_cases hb : b = a0
  · subst hb
    by_cases hl : t = l
    · subst hl
      simp [hlj, Ne.symm hlj]
    · by_cases hj : t = j
      · subst hj
        simp [hl, Ne.symm hl]
      · simp [hl, hj, Ne.symm hl, Ne.symm hj]
  · simp [hb, Ne.symm hb]

/- English proof (translation)
Rewrite using `[Finsupp.weight_apply, Finsupp.sum_apply]`. Use `Finset.sum_eq_zero fun i hi => ?_` and prove the remaining obligations. Simplify using `only`. Establish `hi0 : d i ≠ 0` using `Finsupp.mem_support_iff.mp hi`. Take `⟨b, t⟩` from `i`.

Distinguish the cases in `ht : t = j`. Establish `hne : ¬ ((b, l) = (a0, l))`. Introduce `h`. Simplify using `only [Prod.mk.injEq] at h`. Rewrite `hi0` using `[h.1, ht]`.

Conclude with `hi0 hj`. Establish `hp : pairW (r` using `r) l j (b, t) = Finsupp.single (b, l) 1 := by`. Simplify using `[pairW, ht]`. Rewrite using `[hp, Finsupp.smul_apply, Finsupp.single_apply, if_neg hne, smul_zero]`. Establish `hne : ¬ ((b, t) = (a0, l))`.

Introduce `h`. Rewrite `hi0` using `[h]`. Conclude with `hi0 hl`. Establish `hp : pairW (r` using `r) l j (b, t) = Finsupp.single (b, t) 1 := by`. Simplify using `[pairW, ht]`.

Rewrite using `[hp, Finsupp.smul_apply, Finsupp.single_apply, if_neg hne, smul_zero]`.
-/
private theorem weight_pairW_apply_eq_zero_of_vanish {r n : ℕ} (l j : Fin n) (a0 : Fin r)
    (d : Fin r × Fin n →₀ ℕ) (hl : d (a0, l) = 0) (hj : d (a0, j) = 0) :
    Finsupp.weight (pairW l j) d (a0, l) = 0 := by
  rw [Finsupp.weight_apply, Finsupp.sum_apply]
  refine Finset.sum_eq_zero fun i hi => ?_
  dsimp only
  have hi0 : d i ≠ 0 := Finsupp.mem_support_iff.mp hi
  obtain ⟨b, t⟩ := i
  by_cases ht : t = j
  · have hne : ¬ ((b, l) = (a0, l)) := by
      intro h
      simp only [Prod.mk.injEq] at h
      rw [h.1, ht] at hi0
      exact hi0 hj
    have hp : pairW (r := r) l j (b, t) = Finsupp.single (b, l) 1 := by
      simp [pairW, ht]
    rw [hp, Finsupp.smul_apply, Finsupp.single_apply, if_neg hne, smul_zero]
  · have hne : ¬ ((b, t) = (a0, l)) := by
      intro h
      rw [h] at hi0
      exact hi0 hl
    have hp : pairW (r := r) l j (b, t) = Finsupp.single (b, t) 1 := by
      simp [pairW, ht]
    rw [hp, Finsupp.smul_apply, Finsupp.single_apply, if_neg hne, smul_zero]

/- English proof (translation)
Establish `hpl : pairW (r` using `r) l j (a0, l) = Finsupp.single (a0, l) 1 := by`. Simplify using `[pairW, hlj]`. Establish `hpj : pairW (r` using `r) l j (a0, j) = Finsupp.single (a0, l) 1 := by`. Simplify using `[pairW]`. Establish `key : ω = Finsupp.weight (pairW l j) d + Finsupp.single (a0, l) (m (a0, l) + m (a0, j))`.

Rewrite using `[← hw]`. Use `conv_lhs => rw [hsplit]`. Rewrite using `[map_add, map_add, weight_single_eq_nsmul, weight_single_eq_nsmul, hpl, hpj]`. Use `first`. Consider the case `(rw [add_assoc, ← add_smul, Finsupp.smul_single, smul_eq_mul, mul_one])`.

Consider the case `(ext y`. Simplify using `only [Finsupp.add_apply, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]`. Apply the tactic sequence `split_ifs <;> ring)`. Use extensionality with `x`. Distinguish the cases in `hx : x = (a0, l)`.

Rewrite using `[hx, Finsupp.erase_same]`. Conclude with `weight_pairW_apply_eq_zero_of_vanish l j a0 d hdl hdj`. Rewrite using `[Finsupp.erase_ne hx, key, Finsupp.add_apply, Finsupp.single_apply, if_neg (Ne.symm hx), add_zero]`.
-/
private theorem weight_pairW_eq_erase_of_split {r n : ℕ} (l j : Fin n) (hlj : l ≠ j) (a0 : Fin r)
    (m d ω : Fin r × Fin n →₀ ℕ) (hdl : d (a0, l) = 0) (hdj : d (a0, j) = 0)
    (hsplit : m = d + Finsupp.single (a0, l) (m (a0, l)) + Finsupp.single (a0, j) (m (a0, j)))
    (hw : Finsupp.weight (pairW l j) m = ω) :
    Finsupp.weight (pairW l j) d = ω.erase (a0, l) := by
  have hpl : pairW (r := r) l j (a0, l) = Finsupp.single (a0, l) 1 := by
    simp [pairW, hlj]
  have hpj : pairW (r := r) l j (a0, j) = Finsupp.single (a0, l) 1 := by
    simp [pairW]
  have key : ω = Finsupp.weight (pairW l j) d +
      Finsupp.single (a0, l) (m (a0, l) + m (a0, j)) := by
    rw [← hw]
    conv_lhs => rw [hsplit]
    rw [map_add, map_add, weight_single_eq_nsmul, weight_single_eq_nsmul, hpl, hpj]
    first
      | (rw [add_assoc, ← add_smul, Finsupp.smul_single, smul_eq_mul, mul_one])
      | (ext y
         simp only [Finsupp.add_apply, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
         split_ifs <;> ring)
  ext x
  by_cases hx : x = (a0, l)
  · rw [hx, Finsupp.erase_same]
    exact weight_pairW_apply_eq_zero_of_vanish l j a0 d hdl hdj
  · rw [Finsupp.erase_ne hx, key, Finsupp.add_apply, Finsupp.single_apply, if_neg (Ne.symm hx),
      add_zero]

/- English proof (translation)
Introduce `B _ r n l j hlj a0 ω k g hg`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `d hd`. Take `⟨m, hm, -, rfl⟩` from `lcpeel_support l j a0 k g d hd`. Conclude with `weight_pairW_eq_erase_of_split l j hlj a0 m _ ω (by simp [Finsupp.erase_apply, hlj]) (by simp [Finsupp.erase_apply]) (eq_erase_erase_add_single_add_single l j hlj a0 m) (hg (mem_support_iff.mp hm))`.

Introduce `d hd`. Take `⟨m, -, -, rfl⟩` from `lcpeel_support l j a0 k g d (mem_support_iff.mp hd)`. Conclude with `⟨by simp [Finsupp.erase_apply, hlj], by simp [Finsupp.erase_apply]⟩`.
-/
theorem sliceHomogeneous : PeelHomog := by
  intro B _ r n l j hlj a0 ω k g hg
  refine ⟨?_, ?_⟩
  · intro d hd
    obtain ⟨m, hm, -, rfl⟩ := lcpeel_support l j a0 k g d hd
    exact weight_pairW_eq_erase_of_split l j hlj a0 m _ ω
      (by simp [Finsupp.erase_apply, hlj]) (by simp [Finsupp.erase_apply])
      (eq_erase_erase_add_single_add_single l j hlj a0 m) (hg (mem_support_iff.mp hm))
  · intro d hd
    obtain ⟨m, -, -, rfl⟩ :=
      lcpeel_support l j a0 k g d (mem_support_iff.mp hd)
    exact ⟨by simp [Finsupp.erase_apply, hlj], by simp [Finsupp.erase_apply]⟩

end Formalism.GradedWeylDivisibility
