import Mathlib

open Finset

namespace PI.QnCovHatW

/- English proof (translation)
Establish `hex : ∃ i, i ∉ Set.range c`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Establish `hs : Function.Surjective c` using `fun y => h y`. Use `Fintype.card_le_of_surjective c hs` as an intermediate fact.

Simplify using `at this`. Take `⟨i, hi⟩` from `hex`. Establish `hne : ∀ x, c x ≠ i` using `fun x hx => hi ⟨x, hx⟩`. Use `choose f hf using fun x => Fin.exists_succAbove_eq (hne x)`. Establish `finj : Function.Injective f`.

Introduce `x y hxy`. Apply `hc` to reduce the goal to its premises. Rewrite using `[← hf x, ← hf y, hxy]`. Use `⟨i, Equiv.ofBijective f (Finite.injective_iff_bijective.mp finj), ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `x`.

Simplify using `[hf]`.
-/
theorem inj_decomp {m : ℕ} (c : Fin m → Fin (m + 1)) (hc : Function.Injective c) :
    ∃ i : Fin (m + 1), ∃ σ : Equiv.Perm (Fin m), c = i.succAbove ∘ σ := by
  classical
  have hex : ∃ i, i ∉ Set.range c := by
    by_contra h
    push_neg at h
    have hs : Function.Surjective c := fun y => h y
    have := Fintype.card_le_of_surjective c hs
    simp at this
  obtain ⟨i, hi⟩ := hex
  have hne : ∀ x, c x ≠ i := fun x hx => hi ⟨x, hx⟩
  choose f hf using fun x => Fin.exists_succAbove_eq (hne x)
  have finj : Function.Injective f := by
    intro x y hxy
    apply hc
    rw [← hf x, ← hf y, hxy]
  refine ⟨i, Equiv.ofBijective f (Finite.injective_iff_bijective.mp finj), ?_⟩
  funext x
  simp [hf]

/- English proof (translation)
Establish `hi : i = i'`. Assume the negation of the conclusion as `hne`. Take `⟨z, hz⟩` from `Fin.exists_succAbove_eq hne`. Establish `hh` using `congrFun h (σ'.symm z)`. Simplify using `only [Function.comp_apply, Equiv.apply_symm_apply] at hh`.

Rewrite `hh` using `[hz]`. Conclude with `Fin.succAbove_ne _ _ hh`. Substitute `hi` using the available equality. Conclude with `⟨rfl, Equiv.ext fun x => Fin.succAbove_right_injective (congrFun h x)⟩`.
-/
theorem decomp_unique {m : ℕ} {i i' : Fin (m + 1)} {σ σ' : Equiv.Perm (Fin m)}
    (h : i.succAbove ∘ σ = i'.succAbove ∘ σ') : i = i' ∧ σ = σ' := by
  have hi : i = i' := by
    by_contra hne
    obtain ⟨z, hz⟩ := Fin.exists_succAbove_eq hne
    have hh := congrFun h (σ'.symm z)
    simp only [Function.comp_apply, Equiv.apply_symm_apply] at hh
    rw [hz] at hh
    exact Fin.succAbove_ne _ _ hh
  subst hi
  exact ⟨rfl, Equiv.ext fun x => Fin.succAbove_right_injective (congrFun h x)⟩

/- English proof (translation)
Establish `h1 : ∑ p : Fin (m + 1) × Equiv.Perm (Fin m), w (p.1.succAbove ∘ p.2) • g (p.1.succAbove ∘ p.2) = ∑ c, w c • g c`. Apply `Finset.sum_of_injOn (fun p : Fin (m + 1) × Equiv.Perm (Fin m) => p.1.succAbove ∘ p.2)` to reduce the goal to its premises. Introduce `p _ q _ hpq`. Take `⟨h1, h2⟩` from `decomp_unique hpq`. Conclude with `Prod.ext h1 h2`.

Introduce `p _`. Simplify using the standard rewrite rules. Introduce `c _ hc`. Establish `hni : ¬ Function.Injective c`. Introduce `hinj`.

Take `⟨i, σ, rfl⟩` from `inj_decomp c hinj`. Conclude with `hc ⟨(i, σ), by simp, rfl⟩`. Simplify using `[hzero c hni]`. Introduce `p _`. Both sides reduce to the same expression.

Rewrite using `[← h1, Fintype.sum_prod_type]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_smul]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[hskew i.succAbove σ, smul_smul, mul_comm]`.
-/
theorem alt_sum {M : Type*} [AddCommGroup M] [Module ℂ M] {m : ℕ}
    (g : (Fin m → Fin (m + 1)) → M)
    (hskew : ∀ c (σ : Equiv.Perm (Fin m)), g (c ∘ σ) = ((Equiv.Perm.sign σ : ℤ) : ℂ) • g c)
    (hzero : ∀ c, ¬ Function.Injective c → g c = 0)
    (w : (Fin m → Fin (m + 1)) → ℂ) :
    ∑ c, w c • g c =
      ∑ i : Fin (m + 1),
        (∑ σ : Equiv.Perm (Fin m), ((Equiv.Perm.sign σ : ℤ) : ℂ) * w (i.succAbove ∘ σ)) • g i.succAbove := by
  classical
  have h1 : ∑ p : Fin (m + 1) × Equiv.Perm (Fin m),
      w (p.1.succAbove ∘ p.2) • g (p.1.succAbove ∘ p.2) = ∑ c, w c • g c := by
    apply Finset.sum_of_injOn (fun p : Fin (m + 1) × Equiv.Perm (Fin m) => p.1.succAbove ∘ p.2)
    · intro p _ q _ hpq
      obtain ⟨h1, h2⟩ := decomp_unique hpq
      exact Prod.ext h1 h2
    · intro p _
      simp
    · intro c _ hc
      have hni : ¬ Function.Injective c := by
        intro hinj
        obtain ⟨i, σ, rfl⟩ := inj_decomp c hinj
        exact hc ⟨(i, σ), by simp, rfl⟩
      simp [hzero c hni]
    · intro p _
      rfl
  rw [← h1, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_smul]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [hskew i.succAbove σ, smul_smul, mul_comm]

end PI.QnCovHatW
