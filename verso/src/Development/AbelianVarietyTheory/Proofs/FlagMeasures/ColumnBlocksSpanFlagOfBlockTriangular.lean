import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SigmaFiniteOfRealSmul

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso

namespace GlobalTheory.LeviIso

/- English proof (translation)
Use `⟨fun k => ∑ i, p k i *ᵥ u i, ?_, ?_⟩` and prove the remaining obligations. Introduce `k hk`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Distinguish the cases in `hik : i < k`. Rewrite using `[hp k i hik, Matrix.zero_mulVec]`.

Establish `hki : k ≤ i` using `not_lt.mp hik`. Establish `hi : ¬ i.castSucc < l` using `fun hi => hk (lt_of_le_of_lt (Fin.castSucc_le_castSucc_iff.mpr hki) hi)`. Rewrite using `[hu i hi, Matrix.mulVec_zero]`. Repeatedly rewrite using `[hA, Matrix.sum_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_sum]`. Conclude with `Finset.sum_comm`.
-/
theorem exists_sum_mulVec_of_triangular {n a : ℕ} {j : Fin a → ℕ} (A B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ)
    (p : ∀ k i, Matrix (Fin (j k)) (Fin (j i)) ℂ) (hp : ∀ k i, i < k → p k i = 0)
    (hA : ∀ i, A i = ∑ k, B k * p k i) (l : Fin (a + 1)) (u : ∀ i, Fin (j i) → ℂ)
    (hu : ∀ i : Fin a, ¬ i.castSucc < l → u i = 0) :
    ∃ v : ∀ i, Fin (j i) → ℂ, (∀ i : Fin a, ¬ i.castSucc < l → v i = 0) ∧
      ∑ i, A i *ᵥ u i = ∑ i, B i *ᵥ v i := by
  refine ⟨fun k => ∑ i, p k i *ᵥ u i, ?_, ?_⟩
  · intro k hk
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases hik : i < k
    · rw [hp k i hik, Matrix.zero_mulVec]
    · have hki : k ≤ i := not_lt.mp hik
      have hi : ¬ i.castSucc < l := fun hi =>
        hk (lt_of_le_of_lt (Fin.castSucc_le_castSucc_iff.mpr hki) hi)
      rw [hu i hi, Matrix.mulVec_zero]
  · simp_rw [hA, Matrix.sum_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_sum]
    exact Finset.sum_comm

/- English proof (translation)
Introduce `k y`. Rewrite using `[h k y]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨u, hu, rfl⟩`. Conclude with `exists_sum_mulVec_of_triangular A B p (fun k i hik => (hpq k i hik).1) hA k u hu`.

Introduce and unpack `⟨v, hv, rfl⟩`. Take `⟨w, hw, he⟩` from `exists_sum_mulVec_of_triangular B A q (fun k i hik => (hpq k i hik).2) hB k v hv`. Conclude with `⟨w, hw, he⟩`.
-/
theorem spansFlag_of_triangular (n a : ℕ) (j : Fin a → ℕ) (A B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ)
    (p q : ∀ k i, Matrix (Fin (j k)) (Fin (j i)) ℂ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ))
    (hpq : ∀ k i, i < k → p k i = 0 ∧ q k i = 0) (hA : ∀ i, A i = ∑ k, B k * p k i)
    (hB : ∀ i, B i = ∑ k, A k * q k i) (h : SpansFlag A W) : SpansFlag B W := by
  intro k y
  rw [h k y]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact exists_sum_mulVec_of_triangular A B p (fun k i hik => (hpq k i hik).1) hA k u hu
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨w, hw, he⟩ :=
      exists_sum_mulVec_of_triangular B A q (fun k i hik => (hpq k i hik).2) hB k v hv
    exact ⟨w, hw, he⟩

end GlobalTheory.LeviIso
