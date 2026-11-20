import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.ResidueClassCountOfTensorBasisInclusion
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.FinrankLetter

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.LatticeSystems Formalism.GradedWeylDivisibility MvPolynomial

/- English proof (translation)
Rewrite the hypotheses and the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.
-/
theorem dualWeyl_mul (R : Type*) [CommRing R] (r n : ℕ) (ν ν' : Fin n → ℕ) {F G : MvPolynomial (Fin r × Fin n) R}
    (hF : F ∈ dualWeyl R r n ν) (hG : G ∈ dualWeyl R r n ν') : F * G ∈ dualWeyl R r n (ν + ν') := by
  rw [dualWeyl, Submodule.mem_inf] at hF hG ⊢
  refine ⟨(mem_weightedHomogeneousSubmodule _ _ _ _).2
    (((mem_weightedHomogeneousSubmodule _ _ _ _).1 hF.1).mul
      ((mem_weightedHomogeneousSubmodule _ _ _ _).1 hG.1)), ?_⟩
  have hF2 := hF.2
  have hG2 := hG.2
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, AlgHom.toLinearMap_apply,
    sub_eq_zero] at hF2 hG2 ⊢
  intro l j hlj
  rw [map_mul, map_mul, hF2 l j hlj, hG2 l j hlj]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.
-/
theorem one_mem_dualWeyl (R : Type*) [CommRing R] (r n : ℕ) : (1 : MvPolynomial (Fin r × Fin n) R) ∈ dualWeyl R r n 0 := by
  rw [dualWeyl, Submodule.mem_inf]
  refine ⟨(mem_weightedHomogeneousSubmodule _ _ _ _).2 (isWeightedHomogeneous_one _ _), ?_⟩
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, AlgHom.toLinearMap_apply,
    map_one, sub_self, implies_true]

section Ten

variable {R K : Type*} [CommRing R] [CommRing K] [Algebra R K] {S : Type*} [Fintype S] {k n : ℕ}

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components.

Reduce the claim to the hypotheses of an applicable result. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.
-/
theorem tensorLat_mul (M N L : S → Submodule R (MvPolynomial (Fin k × Fin n) K))
    (h : ∀ s, ∀ F ∈ M s, ∀ G ∈ N s, F * G ∈ L s) :
    ∀ P ∈ tensorLat R K M, ∀ Q ∈ tensorLat R K N, P * Q ∈ tensorLat R K L := by
  intro P hP Q hQ
  have hmem : P * Q ∈ tensorLat R K M * tensorLat R K N := Submodule.mul_mem_mul hP hQ
  rw [tensorLat, tensorLat, Submodule.span_mul_span] at hmem
  refine (Submodule.span_le.2 ?_) hmem
  rintro x ⟨a, ⟨F, hF, rfl⟩, b, ⟨G, hG, rfl⟩, rfl⟩
  apply Submodule.subset_span
  refine ⟨fun s => F s * G s, fun s => h s _ (hF s) _ (hG s), ?_⟩
  simp [map_mul, Finset.prod_mul_distrib]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Reduce the claim to the hypotheses of an applicable result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem tensorLat_split (M N L : S → Submodule R (MvPolynomial (Fin k × Fin n) K))
    (h : ∀ s, ∀ F ∈ L s, ∃ F₁ ∈ M s, ∃ F₂ ∈ N s, F = F₁ * F₂) :
    tensorLat R K L ≤ Submodule.span R {x | ∃ P ∈ tensorLat R K M, ∃ Q ∈ tensorLat R K N, x = P * Q} := by
  refine Submodule.span_le.2 (fun P hP => ?_)
  obtain ⟨F, hF, rfl⟩ := hP
  choose F1 hF1 F2 hF2 hF12 using fun s => h s (F s) (hF s)
  apply Submodule.subset_span
  refine ⟨∏ s, blockEmb K s (F1 s), Submodule.subset_span ⟨F1, hF1, rfl⟩,
    ∏ s, blockEmb K s (F2 s), Submodule.subset_span ⟨F2, hF2, rfl⟩, ?_⟩
  rw [← Finset.prod_mul_distrib]
  simp [hF12, map_mul]

end Ten

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.
-/
theorem nuOf_zero (m : ℕ) : nuOf (0 : Fin (m + 1) → ℤ) = 0 := by
  funext t
  simp [nuOf]

/- English proof (translation)
Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem lamAt_topW {n' m : ℕ} (TT : Finset (Fin n')) (lam0 : Fin n' → Fin (m + 1) → ℤ) (s : Fin n') :
    lamAt (topW TT lam0) s = if s ∈ TT then lamAt lam0 s else 0 := by
  simp only [lamAt, topW]
  split_ifs <;> first | rfl | (funext i; simp)

/- English proof (translation)
Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem lamAt_othW {n' m : ℕ} (TT : Finset (Fin n')) (lam0 : Fin n' → Fin (m + 1) → ℤ) (s : Fin n') :
    lamAt (othW TT lam0) s = if s ∈ TT then 0 else lamAt lam0 s := by
  simp only [lamAt, othW]
  split_ifs <;> first | rfl | (funext i; simp)

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities.
-/
theorem Vsp_eq (Kf : Type) [Field Kf] {n' m : ℕ} (lam0 : Fin n' → Fin (m + 1) → ℤ) (hdom : IsDominant lam0) :
    Vsp Kf lam0 = tensorLat Kf Kf (fun s => dualWeyl Kf (m + 1) (m + 1) (nuOf (lamAt lam0 s))) := by
  unfold Vsp
  congr 1
  funext s
  rw [if_pos (kp_lamAt_antitone lam0 hdom s)]

end Formalism.MainNotions.flipOneThree.Pf

end
