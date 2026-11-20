import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MirabolicBound.Development

namespace PI.GGMirBoundW

open Finset Matrix

noncomputable section

open Classical

/- English proof (translation)
Establish `h : ∀ s : Finset (Fin m), ψ₀ (∑ i ∈ s, g i) = ∏ i ∈ s, ψ₀ (g i)`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [AddChar.map_zero_eq_one]`. Consider the case `@insert a s ha ih`.

Rewrite using `[Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]`. Conclude with `h _`.
-/
theorem addChar_sum {F : Type} [Field F] (ψ₀ : AddChar F ℂ) {m : ℕ} (g : Fin m → F) :
    ψ₀ (∑ i, g i) = ∏ i, ψ₀ (g i) := by
  have h : ∀ s : Finset (Fin m), ψ₀ (∑ i ∈ s, g i) = ∏ i ∈ s, ψ₀ (g i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [AddChar.map_zero_eq_one]
    | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]
  exact h _

/- English proof (translation)
Use `split_ifs with ha`. Substitute `ha` using the available equality. Simplify using `[AddChar.map_zero_eq_one]`. Rewrite using `[show (∑ t : F, ψ₀ (a * t)) = ∑ t : F, ψ₀ t from Fintype.sum_equiv (Equiv.mulLeft₀ a ha) _ _ (fun t => rfl)]`. Conclude with `AddChar.sum_eq_zero_of_ne_one hψ`.
-/
theorem charSum_one {F : Type} [Field F] [Fintype F] (ψ₀ : AddChar F ℂ) (hψ : ψ₀ ≠ 1) (a : F) :
    ∑ t : F, ψ₀ (a * t) = if a = 0 then (Fintype.card F : ℂ) else 0 := by
  split_ifs with ha
  · subst ha
    simp [AddChar.map_zero_eq_one]
  · rw [show (∑ t : F, ψ₀ (a * t)) = ∑ t : F, ψ₀ t from
        Fintype.sum_equiv (Equiv.mulLeft₀ a ha) _ _ (fun t => rfl)]
    exact AddChar.sum_eq_zero_of_ne_one hψ

/- English proof (translation)
Establish `hps : ∑ c : Fin m → F, ∏ i, ψ₀ (ν i * c i) = ∏ i, ∑ t : F, ψ₀ (ν i * t)` using `by first`. Consider the case `exact (Fintype.prod_sum (fun i t => ψ₀ (ν i * t))).symm`. Consider the case `(rw [Finset.prod_univ_sum]; simp)`. Repeatedly rewrite using `[addChar_sum ψ₀]`. Rewrite using `[hps]`.

Repeatedly rewrite using `[charSum_one ψ₀ hψ]`. Use `split_ifs with hν`. Substitute `hν` using the available equality. Simplify using the standard rewrite rules. Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, ν i ≠ 0 := by`.

Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hν (funext h)`. Conclude with `Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)`.
-/
theorem charSum {F : Type} [Field F] [Fintype F] (ψ₀ : AddChar F ℂ) (hψ : ψ₀ ≠ 1) {m : ℕ} (ν : Fin m → F) :
    ∑ c : Fin m → F, ψ₀ (∑ i, ν i * c i) = if ν = 0 then (Fintype.card F : ℂ) ^ m else 0 := by
  have hps : ∑ c : Fin m → F, ∏ i, ψ₀ (ν i * c i) = ∏ i, ∑ t : F, ψ₀ (ν i * t) := by
    first
      | exact (Fintype.prod_sum (fun i t => ψ₀ (ν i * t))).symm
      | (rw [Finset.prod_univ_sum]; simp)
  simp_rw [addChar_sum ψ₀]
  rw [hps]
  simp_rw [charSum_one ψ₀ hψ]
  split_ifs with hν
  · subst hν
    simp
  · obtain ⟨i, hi⟩ : ∃ i, ν i ≠ 0 := by
      by_contra h
      push_neg at h
      exact hν (funext h)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

/- English proof (translation)
Introduce `F _ _ m ψ₀ hψ r s`. Establish `h : ∀ x : Fin m → F, ψ₀ (r ⬝ᵥ x) * ψ₀ (-(s ⬝ᵥ x)) = ψ₀ (∑ i, (r - s) i * x i)`. Introduce `x`. Rewrite using `[← AddChar.map_add_eq_mul, ← sub_eq_add_neg, ← sub_dotProduct]`. Both sides reduce to the same expression.

Repeatedly rewrite using `[h]`. Rewrite using `[charSum ψ₀ hψ (r - s)]`. Simplify using `only [sub_eq_zero]`.
-/
theorem charOrth : CharOrth := by
  intro F _ _ m ψ₀ hψ r s
  have h : ∀ x : Fin m → F, ψ₀ (r ⬝ᵥ x) * ψ₀ (-(s ⬝ᵥ x)) = ψ₀ (∑ i, (r - s) i * x i) := by
    intro x
    rw [← AddChar.map_add_eq_mul, ← sub_eq_add_neg, ← sub_dotProduct]
    rfl
  simp_rw [h]
  rw [charSum ψ₀ hψ (r - s)]
  simp only [sub_eq_zero]

/- English proof (translation)
Introduce `W _ _ X R ι _ _ _ T χ χ' N hN horth f hf hind`. Establish `hf' : ∀ x (q : R × ι), T x (f q) = χ q.1 x • f q` using `fun x q => hf x q.1 q.2`. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg p`. Take `⟨s, i⟩` from `p`.

Establish `h1 : ∑ x, χ' s x • T x (∑ q, g q • f q) = 0`. Rewrite using `[hg]`. Simplify using the standard rewrite rules. Establish `h2 : ∑ x, χ' s x • T x (∑ q, g q • f q) = ∑ q, (if q.1 = s then N * g q else 0) • f q`. Repeatedly rewrite using `[map_sum, map_smul, hf', Finset.smul_sum, smul_smul]`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_smul]`. Use `congr 1`. Establish `ho` using `horth q.1 s`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Use `_ = _ := by`.

Rewrite using `[ho]`. Apply the tactic sequence `split_ifs <;> ring`. Establish `h3 : ∑ q : R × ι, (if q.1 = s then N * g q else 0) • f q = N • ∑ j, g (s, j) • f (s, j)`. Rewrite using `[Fintype.sum_prod_type, Finset.sum_eq_single s]`. Simplify using `[Finset.smul_sum, smul_smul]`.

Introduce `r _ hr`. Simplify using `[hr]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ s) h`. Rewrite `h1` using `[h2, h3]`.

Establish `key : ∑ j, g (s, j) • f (s, j) = 0` using `(smul_eq_zero.mp h1).resolve_left hN`. Conclude with `(Fintype.linearIndependent_iff.mp (hind s)) (fun j => g (s, j)) key i`.
-/
theorem sepLemma : SepLemma := by
  intro W _ _ X R ι _ _ _ T χ χ' N hN horth f hf hind
  have hf' : ∀ x (q : R × ι), T x (f q) = χ q.1 x • f q := fun x q => hf x q.1 q.2
  rw [Fintype.linearIndependent_iff]
  intro g hg p
  obtain ⟨s, i⟩ := p
  have h1 : ∑ x, χ' s x • T x (∑ q, g q • f q) = 0 := by
    rw [hg]
    simp
  have h2 : ∑ x, χ' s x • T x (∑ q, g q • f q) =
      ∑ q, (if q.1 = s then N * g q else 0) • f q := by
    simp_rw [map_sum, map_smul, hf', Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [← Finset.sum_smul]
    congr 1
    have ho := horth q.1 s
    calc ∑ x, χ' s x * (g q * χ q.1 x) = g q * ∑ x, χ q.1 x * χ' s x := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun x _ => ?_
          ring
      _ = _ := by
          rw [ho]
          split_ifs <;> ring
  have h3 : ∑ q : R × ι, (if q.1 = s then N * g q else 0) • f q = N • ∑ j, g (s, j) • f (s, j) := by
    rw [Fintype.sum_prod_type, Finset.sum_eq_single s]
    · simp [Finset.smul_sum, smul_smul]
    · intro r _ hr
      simp [hr]
    · intro h
      exact absurd (Finset.mem_univ s) h
  rw [h2, h3] at h1
  have key : ∑ j, g (s, j) • f (s, j) = 0 := (smul_eq_zero.mp h1).resolve_left hN
  exact (Fintype.linearIndependent_iff.mp (hind s)) (fun j => g (s, j)) key i

end

end PI.GGMirBoundW
