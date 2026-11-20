import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StConeAvoidsExists
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLeadIdealDim
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLinearFormCut
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StHomogDimZeroPow
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

variable {n : ℕ}

/- English proof (translation)
The claim follows from `Ideal.homogeneous_span _ _ (by rintro _ ⟨f, -, rfl⟩ exact ⟨f.totalDegree, (mem_homogeneousSubmodule _ _).2 (homogeneousComponent_isHomogeneous _ _)⟩)`.
-/
theorem leadIdeal_isHomogeneous (J : Ideal (MvPolynomial (Fin n) ℂ)) :
    (leadIdeal J).IsHomogeneous (homogeneousSubmodule (Fin n) ℂ) :=
  Ideal.homogeneous_span _ _ (by
    rintro _ ⟨f, -, rfl⟩
    exact ⟨f.totalDegree, (mem_homogeneousSubmodule _ _).2 (homogeneousComponent_isHomogeneous _ _)⟩)

/- English proof (translation)
The claim follows from `Ideal.homogeneous_span _ _ (by rintro _ ⟨i, rfl⟩ exact ⟨1, (mem_homogeneousSubmodule _ _).2 (IsHomogeneous.sum _ _ _ (fun j _ => (isHomogeneous_X ℂ j).C_mul (A i j)))⟩)`.
-/
theorem linIdeal_isHomogeneous {d : ℕ} (A : Matrix (Fin d) (Fin n) ℂ) :
    (linIdeal A).IsHomogeneous (homogeneousSubmodule (Fin n) ℂ) :=
  Ideal.homogeneous_span _ _ (by
    rintro _ ⟨i, rfl⟩
    exact ⟨1, (mem_homogeneousSubmodule _ _).2
      (IsHomogeneous.sum _ _ _ (fun j _ => (isHomogeneous_X ℂ j).C_mul (A i j)))⟩)

/- English proof (translation)
Establish `h : linPoly (Matrix.of (Fin.cons (B 0) A : Fin (k + 1) → Fin n → ℂ)) = Fin.cons (linPoly B 0) (linPoly A)`. Use function extensionality and compare the values at `i`. Conclude with `Fin.cases rfl (fun i => rfl) i`. Establish `hB : Set.range (linPoly B) = {linPoly B 0}`. Rewrite using `[Set.range_unique]`.

Both sides reduce to the same expression. Rewrite using `[linIdeal, linIdeal, linIdeal, h, Fin.range_cons, hB, Set.insert_eq, Ideal.span_union, sup_comm]`.
-/
theorem linIdeal_cons {k : ℕ} (A : Matrix (Fin k) (Fin n) ℂ) (B : Matrix (Fin 1) (Fin n) ℂ) :
    linIdeal (Matrix.of (Fin.cons (B 0) A : Fin (k + 1) → Fin n → ℂ)) = linIdeal A ⊔ linIdeal B := by
  have h : linPoly (Matrix.of (Fin.cons (B 0) A : Fin (k + 1) → Fin n → ℂ)) =
      Fin.cons (linPoly B 0) (linPoly A) := by
    funext i
    exact Fin.cases rfl (fun i => rfl) i
  have hB : Set.range (linPoly B) = {linPoly B 0} := by
    rw [Set.range_unique]
    rfl
  rw [linIdeal, linIdeal, linIdeal, h, Fin.range_cons, hB, Set.insert_eq, Ideal.span_union, sup_comm]

/- English proof (translation)
Introduce `n d J _ hd`. Establish `key : ∀ k, k ≤ d → ∃ A : Matrix (Fin k) (Fin n) ℂ, ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (leadIdeal J ⊔ linIdeal A)) ≤ ((d - k : ℕ) : WithBot ℕ∞)`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero`.

Introduce `_`. Use `⟨0, ?_⟩` and prove the remaining obligations. Establish `h0 : linIdeal (0 : Matrix (Fin 0) (Fin n) ℂ) = ⊥`. Rewrite using `[linIdeal, Set.range_eq_empty, Ideal.span_empty]`. Rewrite using `[h0, sup_bot_eq, Nat.sub_zero, ← hd]`.

Conclude with `hlead n J`. Consider the case `succ k ih`. Introduce `hk`. Take `⟨A, hA⟩` from `ih (by omega)`. Establish `hdk : d - k = (d - (k + 1)) + 1` using `by omega`.

Rewrite `hA` using `[hdk]`. Take `⟨B, hB⟩` from `hcut n _ _ hA`. Use `⟨Matrix.of (Fin.cons (B 0) A : Fin (k + 1) → Fin n → ℂ), ?_⟩` and prove the remaining obligations. Rewrite using `[linIdeal_cons, ← sup_assoc]`. Conclude with `hB`.

Take `⟨A, hA⟩` from `key d le_rfl`. Rewrite `hA` using `[Nat.sub_self, Nat.cast_zero]`. Take `⟨N, hN⟩` from `hpow n _ ((leadIdeal_isHomogeneous J).sup (linIdeal_isHomogeneous A)) hA`. Conclude with `⟨A, N, hN⟩`.
-/
theorem ConeAvoidsExists.proof (hlead : LeadIdealDim.Statement) (hcut : LinearFormCut.Statement)
    (hpow : HomogDimZeroPow.Statement) : ConeAvoidsExists.Statement := by
  intro n d J _ hd
  have key : ∀ k, k ≤ d → ∃ A : Matrix (Fin k) (Fin n) ℂ,
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (leadIdeal J ⊔ linIdeal A)) ≤
        ((d - k : ℕ) : WithBot ℕ∞) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨0, ?_⟩
      have h0 : linIdeal (0 : Matrix (Fin 0) (Fin n) ℂ) = ⊥ := by
        rw [linIdeal, Set.range_eq_empty, Ideal.span_empty]
      rw [h0, sup_bot_eq, Nat.sub_zero, ← hd]
      exact hlead n J
    | succ k ih =>
      intro hk
      obtain ⟨A, hA⟩ := ih (by omega)
      have hdk : d - k = (d - (k + 1)) + 1 := by omega
      rw [hdk] at hA
      obtain ⟨B, hB⟩ := hcut n _ _ hA
      refine ⟨Matrix.of (Fin.cons (B 0) A : Fin (k + 1) → Fin n → ℂ), ?_⟩
      rw [linIdeal_cons, ← sup_assoc]
      exact hB
  obtain ⟨A, hA⟩ := key d le_rfl
  rw [Nat.sub_self, Nat.cast_zero] at hA
  obtain ⟨N, hN⟩ := hpow n _ ((leadIdeal_isHomogeneous J).sup (linIdeal_isHomogeneous A)) hA
  exact ⟨A, N, hN⟩

end

end GroundTheory.Heights₂.Heights.ComplexSets
