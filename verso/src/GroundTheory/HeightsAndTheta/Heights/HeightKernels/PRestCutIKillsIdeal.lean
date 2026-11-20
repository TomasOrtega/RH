import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsRest
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

/- English proof (translation)
The claim follows from `IsHomogeneous.sum _ _ _ fun _ _ => isHomogeneous_X_pow _ _`.
-/
theorem rootPsum_isHomogeneous (f j k m : ℕ) (τ : Fin f) :
    (rootPsum f j k m τ).IsHomogeneous m :=
  IsHomogeneous.sum _ _ _ fun _ _ => isHomogeneous_X_pow _ _

/- English proof (translation)
Use `show (rename (fun p : Fin f × Fin N => (p.1, e p.2)) (map (algebraMap ℚ ℝ) A)).IsHomogeneous d`. Conclude with `(hA.map _).rename_isHomogeneous`.
-/
theorem restTransport_isHomogeneous (f j k N : ℕ) (e : Fin N ≃ Fin j ⊕ Fin k)
    {A : RestTerms.RootRing f N} {d : ℕ} (hA : A.IsHomogeneous d) :
    (restTransport f j k N e A).IsHomogeneous d := by
  show (rename (fun p : Fin f × Fin N => (p.1, e p.2)) (map (algebraMap ℚ ℝ) A)).IsHomogeneous d
  exact (hA.map _).rename_isHomogeneous

/- English proof (translation)
Introduce `f j k N e I hI A hA hhom`. Take `⟨G, hG⟩` from `h₁ f N A hA`. Establish `hT` using `restTransport_isHomogeneous f j k N e hhom`. Establish `hC` using `homogeneousComponent_of_mem (m := flagDim f j k) hT`. Rewrite `hC` using `[if_pos rfl]`.

Rewrite using `[← hC]`. Rewrite using `[hG, map_sum, map_sum, map_sum]`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, h₂, KRest.homogeneousComponent_mul_left (rootPsum_isHomogeneous f j k _ i.2)]`. Use `split_ifs with hle`.

Conclude with `hI.kills _ _ _ (Nat.succ_le_succ (Nat.zero_le _)) hle (homogeneousComponent_isHomogeneous _ _)`. Conclude with `map_zero I`.
-/
theorem RestCutIKillsIdeal.proof (h₁ : RestCutIdealSum.Statement)
    (h₂ : RestCutTransportPsum.Statement) : RestCutIKillsIdeal.Statement := by
  intro f j k N e I hI A hA hhom
  obtain ⟨G, hG⟩ := h₁ f N A hA
  have hT := restTransport_isHomogeneous f j k N e hhom
  have hC := homogeneousComponent_of_mem (m := flagDim f j k) hT
  rw [if_pos rfl] at hC
  rw [← hC]
  rw [hG, map_sum, map_sum, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [map_mul, h₂, KRest.homogeneousComponent_mul_left (rootPsum_isHomogeneous f j k _ i.2)]
  split_ifs with hle
  · exact hI.kills _ _ _ (Nat.succ_le_succ (Nat.zero_le _)) hle
      (homogeneousComponent_isHomogeneous _ _)
  · exact map_zero I

end GroundTheory.Heights₂.Heights
