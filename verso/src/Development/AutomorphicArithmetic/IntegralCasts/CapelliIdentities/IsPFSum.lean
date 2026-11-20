import Mathlib
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IsPF

/- English proof (translation)
Introduce `A _ _ ι s f h`. Unfold `UpperTheory.Reformulated.B.PolynomialFunction₂.IsPF at h ⊢`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => exact ⟨0, fun Y => by simp⟩`. Consider the case `insert a s ha ih`.

Take `⟨p, hp⟩` from `h a (Finset.mem_insert_self a s)`. Take `⟨q, hq⟩` from `ih (fun i hi => h i (Finset.mem_insert_of_mem hi))`. Use `⟨p + q, fun Y => ?_⟩` and prove the remaining obligations. Establish `h1 : (∑ i ∈ s, f i Y) = Polynomial.eval ((algebraMap ℂ A) Y) q` using `hq Y`. Use `show (∑ i ∈ insert a s, f i Y) = Polynomial.eval ((algebraMap ℂ A) Y) (p + q)`.

Rewrite using `[Finset.sum_insert ha, hp, h1, Polynomial.eval_add]`.
-/
theorem UpperTheory.Reformulated.B.IsPFSum.isPF_sum :
    ∀ {A : Type} [inst : Ring A] [inst_1 : Algebra ℂ A] {ι : Type} (s : Finset ι) {f : ι → ℂ → A},
      (∀ i ∈ s, UpperTheory.Reformulated.B.PolynomialFunction₂.IsPF (f i)) → UpperTheory.Reformulated.B.PolynomialFunction₂.IsPF fun (Y : ℂ) ↦ ∑ i ∈ s, f i Y := by
  intro A _ _ ι s f h
  classical
  unfold UpperTheory.Reformulated.B.PolynomialFunction₂.IsPF at h ⊢
  induction s using Finset.induction_on with
  | empty => exact ⟨0, fun Y => by simp⟩
  | insert a s ha ih =>
    obtain ⟨p, hp⟩ := h a (Finset.mem_insert_self a s)
    obtain ⟨q, hq⟩ := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    refine ⟨p + q, fun Y => ?_⟩
    have h1 : (∑ i ∈ s, f i Y) = Polynomial.eval ((algebraMap ℂ A) Y) q := hq Y
    show (∑ i ∈ insert a s, f i Y) = Polynomial.eval ((algebraMap ℂ A) Y) (p + q)
    rw [Finset.sum_insert ha, hp, h1, Polynomial.eval_add]
