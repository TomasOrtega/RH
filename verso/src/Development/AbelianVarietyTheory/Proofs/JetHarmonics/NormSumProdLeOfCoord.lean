import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift

open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne

/- English proof (translation)
Establish `key : ∀ I : Finset (Fin g), ∀ ν : Fin g → ℕ, ‖∑ j, c j * ∏ i, (if i ∈ I then G j i (ν i) else F j i (ν i))‖ ≤ B`. Introduce `I`. Proceed by induction on `I using Finset.induction_on with`. Consider the case `empty => simpa using h`. Consider the case `insert i₀ I hi ih`.

Introduce `ν`. Establish `hs` using `step i₀ (fun j => c j * ∏ i ∈ Finset.univ.erase i₀, (if i ∈ I then G j i (ν i) else F j i (ν i))) ?_ (ν i₀)`. Use `hs using 3 with j _` and compare the differences between its conclusion and the goal. Rewrite using `[← Finset.prod_erase_mul _ _ (Finset.mem_univ i₀), mul_assoc]`. Use `congr 2`.

Use `Finset.prod_congr rfl fun i hi' => ?_` and prove the remaining obligations. Simplify using `[Finset.mem_insert, Finset.ne_of_mem_erase hi']`. Simplify using the standard rewrite rules. Introduce `n`. Use `ih (Function.update ν i₀ n) using 3 with j _` and compare the differences between its conclusion and the goal.

Rewrite using `[← Finset.prod_erase_mul _ _ (Finset.mem_univ i₀), mul_assoc]`. Use `congr 2`. Use `Finset.prod_congr rfl fun i hi' => ?_` and prove the remaining obligations. Simplify using `[Function.update_of_ne (Finset.ne_of_mem_erase hi')]`. Simplify using `[hi]`.

Simplify using `using key Finset.univ ν`.
-/
theorem norm_sum_prod_le_of_coord {K : Type*} [NormedCommRing K] {g m : ℕ} (F G : Fin m → Fin g → ℕ → K)
    (c : Fin m → K) (B : ℝ)
    (step : ∀ (i : Fin g) (c' : Fin m → K), (∀ n, ‖∑ j, c' j * F j i n‖ ≤ B) → ∀ n, ‖∑ j, c' j * G j i n‖ ≤ B)
    (h : ∀ ν : Fin g → ℕ, ‖∑ j, c j * ∏ i, F j i (ν i)‖ ≤ B) (ν : Fin g → ℕ) :
    ‖∑ j, c j * ∏ i, G j i (ν i)‖ ≤ B := by
  classical
  have key : ∀ I : Finset (Fin g), ∀ ν : Fin g → ℕ,
      ‖∑ j, c j * ∏ i, (if i ∈ I then G j i (ν i) else F j i (ν i))‖ ≤ B := by
    intro I
    induction I using Finset.induction_on with
    | empty => simpa using h
    | insert i₀ I hi ih =>
      intro ν
      have hs := step i₀
        (fun j => c j * ∏ i ∈ Finset.univ.erase i₀, (if i ∈ I then G j i (ν i) else F j i (ν i))) ?_ (ν i₀)
      · convert hs using 3 with j _
        rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i₀), mul_assoc]
        congr 2
        · refine Finset.prod_congr rfl fun i hi' => ?_
          simp [Finset.mem_insert, Finset.ne_of_mem_erase hi']
        · simp
      · intro n
        convert ih (Function.update ν i₀ n) using 3 with j _
        rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i₀), mul_assoc]
        congr 2
        · refine Finset.prod_congr rfl fun i hi' => ?_
          simp [Function.update_of_ne (Finset.ne_of_mem_erase hi')]
        · simp [hi]
  simpa using key Finset.univ ν

/- English proof (translation)
Introduce `d q _ ι ω θ hθ g m a c t τ B ht hτ h`. Use `norm_sum_prod_le_of_coord (fun j i n => coeff n (hat ι (C ω * logS) (U1 d (t j i) θ) ^ a i)) (fun j i n => coeff n (hat ι (C ω * logS) (U1 d (τ i) (U1 d (t j i) θ)) ^ a i)) c B ?_ h` and prove the remaining obligations. Introduce `i c' hc n`. Use `hθ.2.2 (a i) m c' (fun j => t j i) (τ i) B (fun j => ht j i) (hτ i) (fun k => by` as an intermediate fact. Simplify `hc k) n` using `only [map_sum, coeff_C_mul]`.

Simplify `this` using `only [map_sum, coeff_C_mul]`.
-/
theorem translate_norm_prod_le : ∀ (d q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (ω : ℂ_[q]) (θ : ℂ → ℂ), ThetaLaws ι d ω θ → ∀ (g m : ℕ) (a : Fin g → ℕ) (c : Fin m → ℂ_[q]) (t : Fin m → Fin g → ℂ) (τ : Fin g → ℂ) (B : ℝ), (∀ j i, PrimeTo d q (t j i)) → (∀ i, PrimeTo d q (τ i)) → (∀ ν : Fin g → ℕ, ‖∑ j, c j * ∏ i, coeff (ν i) (hat ι (C ω * logS) (U1 d (t j i) θ) ^ a i)‖ ≤ B) → ∀ ν : Fin g → ℕ, ‖∑ j, c j * ∏ i, coeff (ν i) (hat ι (C ω * logS) (U1 d (τ i) (U1 d (t j i) θ)) ^ a i)‖ ≤ B := by
  intro d q _ ι ω θ hθ g m a c t τ B ht hτ h
  refine norm_sum_prod_le_of_coord
    (fun j i n => coeff n (hat ι (C ω * logS) (U1 d (t j i) θ) ^ a i))
    (fun j i n => coeff n (hat ι (C ω * logS) (U1 d (τ i) (U1 d (t j i) θ)) ^ a i)) c B ?_ h
  intro i c' hc n
  have := hθ.2.2 (a i) m c' (fun j => t j i) (τ i) B (fun j => ht j i) (hτ i) (fun k => by
    simpa only [map_sum, coeff_C_mul] using hc k) n
  simpa only [map_sum, coeff_C_mul] using this

end GlobalTheory.MomOne
