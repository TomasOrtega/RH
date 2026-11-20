import Mathlib
import Formalism.HermitianCurvature.StatementU
import Formalism.HermitianCurvature.StatementQ
import Formalism.HermitianCurvature.LetterProductDoubleDegreeCount
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UnitaryConjEntryAndInvEntryLinearStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliEigenSumLinearCombinationStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.InverseEntrySmulCapelliEigenfunctionSumStatement
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset

namespace GlobalTheory

/- English proof (translation)
Introduce `k r Wp Wq _ _ _ _ _ _ lam d A i j F hsep hF`. Take `⟨N₀, Fi, ν, hν, hcl, heig, hsum⟩` from `hF`. Take `⟨⟨co, hco⟩, -⟩` from `GlobalTheory.T.unitary_conj_entry_and_inv_entry_linear k r i j`. Use `GlobalTheory.T.capelliEigenSum_linearCombination k r Wp Wq lam (d + 1) (A - 1) (Fin N₀ × Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) Finset.univ (fun x => co x.2.1 x.2.2) (fun x g => g⁻¹ x.2.1 x.2.2 • Fi x.1 g) (fun g => star (g i j) • F g) ?_ ?_` and prove the remaining obligations. Introduce and unpack `⟨x, a, b⟩ -`.

Use `⟨d + 1, A - 1, le_rfl, le_rfl, ?_⟩` and prove the remaining obligations. Establish `hinj : Function.Injective (fun s => lam s + (ν x s : ℝ))`. Introduce `s t hst`. Assume the negation of the conclusion as `hne`. Establish `h1` using `hsep s t hne`.

Establish `h2 : |(ν x s : ℝ)| ≤ (d : ℝ)` using `by exact_mod_cast hν x s`. Establish `h3 : |(ν x t : ℝ)| ≤ (d : ℝ)` using `by exact_mod_cast hν x t`. Establish `h4 : lam s - lam t = (ν x t : ℝ) - (ν x s : ℝ)`. Simplify using `only at hst`. Combine the linear equalities and inequalities to obtain the conclusion.

Rewrite `h1` using `[h4]`. Establish `h5` using `abs_sub (ν x t : ℝ) (ν x s : ℝ)`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨G, hG1, hG2, hG3⟩` from `GlobalTheory.T.inverseEntry_smul_capelliEigenfunction_sum k r Wp Wq (fun s => lam s + (ν x s : ℝ)) A a b (Fi x) hinj (hcl x) (by`. Introduce `Y g hg`.

Rewrite using `[heig x Y g hg]`. Simplify using `only [add_assoc])`. Use `⟨2 * r + k + 1, G, fun t s => ν x s - if s = t then 1 else 0, ?_, hG1, ?_, hG3⟩` and prove the remaining obligations. Introduce `t s`. Establish `h` using `abs_le.mp (hν x s)`.

Rewrite using `[abs_le]`. Use `push_cast`. Apply the tactic sequence `split_ifs <;> constructor <;> omega`. Introduce `t Y g hg`. Rewrite using `[hG2 t Y g hg]`.

Use `congr 2`. Use `Finset.prod_congr rfl fun s _ => ?_` and prove the remaining obligations. Use `push_cast`. Apply the tactic sequence `split_ifs <;> ring`. Introduce `g hg beta_reduce`.

Rewrite using `[hco g hg, hsum g hg, Fintype.sum_prod_type, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Rewrite using `[Fintype.sum_prod_type, Finset.sum_smul]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_smul]`.

Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[smul_smul]`.
-/
theorem conj_entry_smul_eigenSum : ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (lam : Fin (2 * r + k + 1) → ℝ) (d : ℕ) (A : ℝ) (i j : Fin (2 * r + k + 1)) (F : B.Mat k r → (Wq →L[ℂ] Wp)), (∀ s t, s ≠ t → 2 * ((d : ℕ) : ℝ) < |lam s - lam t|) → (∃ (N₀ : ℕ) (Fi : Fin N₀ → B.Mat k r → (Wq →L[ℂ] Wp)) (ν : Fin N₀ → Fin (2 * r + k + 1) → ℤ), (∀ i s, |ν i s| ≤ ((d : ℕ) : ℤ)) ∧ (∀ i, (B.CkOn ⊤ (B.GV k r) (Fi i) ∧ ∀ m : ℕ, B.InCC (A) m (Fi i))) ∧ (∀ i, (∀ Y : ℝ, ∀ g ∈ B.GV k r, Q.CV k r (Y : ℂ) (Fi i) g = ((∏ s, (Y + lam s + (ν i s : ℝ)) : ℝ) : ℂ) • (Fi i) g)) ∧ ∀ g ∈ B.GV k r, (F) g = ∑ i, Fi i g) → (∃ (N₀ : ℕ) (Fi : Fin N₀ → B.Mat k r → (Wq →L[ℂ] Wp)) (ν : Fin N₀ → Fin (2 * r + k + 1) → ℤ), (∀ i s, |ν i s| ≤ ((d + 1 : ℕ) : ℤ)) ∧ (∀ i, (B.CkOn ⊤ (B.GV k r) (Fi i) ∧ ∀ m : ℕ, B.InCC (A - 1) m (Fi i))) ∧ (∀ i, (∀ Y : ℝ, ∀ g ∈ B.GV k r, Q.CV k r (Y : ℂ) (Fi i) g = ((∏ s, (Y + lam s + (ν i s : ℝ)) : ℝ) : ℂ) • (Fi i) g)) ∧ ∀ g ∈ B.GV k r, (fun g => star (g i j) • F g) g = ∑ i, Fi i g) := by
  intro k r Wp Wq _ _ _ _ _ _ lam d A i j F hsep hF
  obtain ⟨N₀, Fi, ν, hν, hcl, heig, hsum⟩ := hF
  obtain ⟨⟨co, hco⟩, -⟩ := GlobalTheory.T.unitary_conj_entry_and_inv_entry_linear k r i j
  refine GlobalTheory.T.capelliEigenSum_linearCombination k r Wp Wq lam (d + 1) (A - 1)
    (Fin N₀ × Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) Finset.univ
    (fun x => co x.2.1 x.2.2) (fun x g => g⁻¹ x.2.1 x.2.2 • Fi x.1 g)
    (fun g => star (g i j) • F g) ?_ ?_
  · rintro ⟨x, a, b⟩ -
    refine ⟨d + 1, A - 1, le_rfl, le_rfl, ?_⟩
    have hinj : Function.Injective (fun s => lam s + (ν x s : ℝ)) := by
      intro s t hst
      by_contra hne
      have h1 := hsep s t hne
      have h2 : |(ν x s : ℝ)| ≤ (d : ℝ) := by exact_mod_cast hν x s
      have h3 : |(ν x t : ℝ)| ≤ (d : ℝ) := by exact_mod_cast hν x t
      have h4 : lam s - lam t = (ν x t : ℝ) - (ν x s : ℝ) := by
        simp only at hst
        linarith
      rw [h4] at h1
      have h5 := abs_sub (ν x t : ℝ) (ν x s : ℝ)
      linarith
    obtain ⟨G, hG1, hG2, hG3⟩ := GlobalTheory.T.inverseEntry_smul_capelliEigenfunction_sum k r Wp Wq (fun s => lam s + (ν x s : ℝ)) A a b
      (Fi x) hinj (hcl x) (by
        intro Y g hg
        rw [heig x Y g hg]
        simp only [add_assoc])
    refine ⟨2 * r + k + 1, G, fun t s => ν x s - if s = t then 1 else 0, ?_, hG1, ?_, hG3⟩
    · intro t s
      have h := abs_le.mp (hν x s)
      rw [abs_le]
      push_cast
      split_ifs <;> constructor <;> omega
    · intro t Y g hg
      rw [hG2 t Y g hg]
      congr 2
      refine Finset.prod_congr rfl fun s _ => ?_
      push_cast
      split_ifs <;> ring
  · intro g hg
    beta_reduce
    rw [hco g hg, hsum g hg, Fintype.sum_prod_type, Finset.smul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Fintype.sum_prod_type, Finset.sum_smul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [smul_smul]

end GlobalTheory
