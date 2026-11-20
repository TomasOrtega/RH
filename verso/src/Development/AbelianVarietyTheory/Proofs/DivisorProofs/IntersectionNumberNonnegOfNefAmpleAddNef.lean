import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIntersectionNumberNonnegOfAmpleStatement
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPowVanishingIdealLeAnnihilator
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SupportPushforwardSubschemeSubset
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TensOfForallIsPsEff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowLeGlobalSectionsDimLineBundlePow
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

/- English proof (translation)
Take `⟨_, A, hA⟩` from `isProper_and_exists_isAmpleLB_of_isProjOver hX`. Establish `hD : DiffVanish (d + 1) (chiPic k F)` using `diffVanish_chiPic_of_isProjOver (algebraMap_eq_strHom k X) F hX hd`. Establish `key : ∀ S : Finset (Fin d), ∀ Q : Fin d → LB X, (∀ i ∈ S, IsNef k (Q i)) → (∀ i ∉ S, IsAmpleLB (Q i)) → 0 ≤ interNum k F Q`. Introduce `S`. Proceed by induction on `S using Finset.induction_on with`.

Consider the case `empty => exact fun Q _ h ↦ GlobalTheory.T.lineBundleIntersectionNumber_nonneg_of_ample k X hX d F hd Q fun i ↦ h i (by simp)`. Consider the case `insert i S hi ih`. Introduce `Q hn ha`. Establish `hi' : IsNef k (Q i)` using `hn i (Finset.mem_insert_self _ _)`. Establish `hL : ∀ j, (Q j).IsLB` using `fun j ↦ by`.

Distinguish the cases in `h : j ∈ insert i S`. Conclude with `(hn j h).isLB`. Conclude with `(ha j h).isLB`. Establish `h1 : ∀ B : LB X, IsAmpleLB B → 0 ≤ interNum k F (Function.update Q i B)`. Introduce `B hB`.

Use `ih _ (fun j hj ↦ ?_) (fun j hj ↦ ?_)` and prove the remaining obligations. Rewrite using `[Function.update_of_ne (by rintro rfl; exact hi hj)]`. Conclude with `hn j (Finset.mem_insert_of_mem hj)`. Distinguish the cases in `h : j = i`. Substitute `h` using the available equality.

Rewrite using `[Function.update_self]` and apply the resulting hypothesis. Rewrite using `[Function.update_of_ne h]`. Conclude with `ha j (by simp [h, hj])`. Establish `h2 : ∀ m : ℕ, ∃ B : LB X, IsAmpleLB B ∧ interNum k F (Function.update Q i B) = interNum k F (Function.update Q i A) + m * interNum k F Q`. Introduce `m`.

Proceed by induction on `m with`. Consider the case `zero => exact ⟨A, hA, by simp⟩`. Consider the case `succ m ihm`. Take `⟨B, hB, e⟩` from `ihm`. Use `⟨tens B (Q i), hAN _ _ hB hi', ?_⟩` and prove the remaining obligations.

Rewrite using `[hD.interNum_update_tens (by simp) hL i hB.isLB (hL i), e, Function.update_eq_self]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Assume the negation of the conclusion as `hneg`. Take `⟨B, hB, e⟩` from `h2 ((interNum k F (Function.update Q i A)).toNat + 1)`.

Establish `h3` using `h1 B hB`. Establish `h4` using `h1 A hA`. Rewrite `h3` using `[e]`. Move the coercions through the operations in `at h3`. Rewrite `h3` using `[Int.toNat_of_nonneg h4]`.

Use the polynomial consequences of the given equalities and inequalities. Conclude with `key Finset.univ P (fun i _ ↦ hP i) (fun i h ↦ absurd (Finset.mem_univ i) h)`.
-/
theorem interNum_nonneg_of_isNef_of_ample_tens_nef (k : Type) [Field k] [Infinite k]
    (X : Scheme.{0}) [Algebra k Γ(X, ⊤)] (hX : IsProjOver (strHom k X))
    (hAN : ∀ A N : LB X, IsAmpleLB A → IsNef k N → IsAmpleLB (tens A N))
    (d : ℕ) (F : X.Modules) [IsFiniteQC F] (hd : suppDim F ≤ (d : ℕ))
    (P : Fin d → LB X) (hP : ∀ i, IsNef k (P i)) : 0 ≤ interNum k F P := by
  classical
  obtain ⟨_, A, hA⟩ := isProper_and_exists_isAmpleLB_of_isProjOver hX
  have hD : DiffVanish (d + 1) (chiPic k F) :=
    diffVanish_chiPic_of_isProjOver (algebraMap_eq_strHom k X) F hX hd
  have key : ∀ S : Finset (Fin d), ∀ Q : Fin d → LB X, (∀ i ∈ S, IsNef k (Q i)) →
      (∀ i ∉ S, IsAmpleLB (Q i)) → 0 ≤ interNum k F Q := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact fun Q _ h ↦ GlobalTheory.T.lineBundleIntersectionNumber_nonneg_of_ample k X hX d F hd Q fun i ↦ h i (by simp)
    | insert i S hi ih =>
      intro Q hn ha
      have hi' : IsNef k (Q i) := hn i (Finset.mem_insert_self _ _)
      have hL : ∀ j, (Q j).IsLB := fun j ↦ by
        by_cases h : j ∈ insert i S
        · exact (hn j h).isLB
        · exact (ha j h).isLB
      have h1 : ∀ B : LB X, IsAmpleLB B → 0 ≤ interNum k F (Function.update Q i B) := by
        intro B hB
        refine ih _ (fun j hj ↦ ?_) (fun j hj ↦ ?_)
        · rw [Function.update_of_ne (by rintro rfl; exact hi hj)]
          exact hn j (Finset.mem_insert_of_mem hj)
        · by_cases h : j = i
          · subst h; rwa [Function.update_self]
          · rw [Function.update_of_ne h]
            exact ha j (by simp [h, hj])
      have h2 : ∀ m : ℕ, ∃ B : LB X, IsAmpleLB B ∧ interNum k F (Function.update Q i B) =
          interNum k F (Function.update Q i A) + m * interNum k F Q := by
        intro m
        induction m with
        | zero => exact ⟨A, hA, by simp⟩
        | succ m ihm =>
          obtain ⟨B, hB, e⟩ := ihm
          refine ⟨tens B (Q i), hAN _ _ hB hi', ?_⟩
          rw [hD.interNum_update_tens (by simp) hL i hB.isLB (hL i), e, Function.update_eq_self]
          push_cast
          ring
      by_contra hneg
      obtain ⟨B, hB, e⟩ := h2 ((interNum k F (Function.update Q i A)).toNat + 1)
      have h3 := h1 B hB
      have h4 := h1 A hA
      rw [e] at h3
      push_cast at h3
      rw [Int.toNat_of_nonneg h4] at h3
      nlinarith
  exact key Finset.univ P (fun i _ ↦ hP i) (fun i h ↦ absurd (Finset.mem_univ i) h)

end GlobalTheory
