import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

/- English proof (translation)
Unfold `intNum mixedDiff`. Rewrite using `[List.ofFn_get, List.ofFn_get]`. Use `haveI : LeftCommutative (diffStep (K := K)) := ⟨fun a b f => by`. Use function extensionality and compare the values at `m`. Simplify using `only [diffStep]`.

Rewrite using `[show m - a - b = m - b - a by abel]`. Use the proof step `ring⟩`. Rewrite using `[h.foldr_eq]`.
-/
private theorem intNum_get_eq_of_perm {K : Type} [DecidableEq K] {ι : K → Type} (F : Type) [Field F]
    (P : Ideal (MRing ι F)) {l l' : List (K → ℤ)} (h : l.Perm l') :
    intNum F P l.get = intNum F P l'.get := by
  unfold intNum mixedDiff
  rw [List.ofFn_get, List.ofFn_get]
  haveI : LeftCommutative (diffStep (K := K)) := ⟨fun a b f => by
    funext m
    simp only [diffStep]
    rw [show m - a - b = m - b - a by abel]
    ring⟩
  rw [h.foldr_eq]

/- English proof (translation)
Unfold `intNumL`. Conclude with `intNum_get_eq_of_perm F V h`.
-/
theorem BaseChangeColon.intNumL_perm (F : Type) [Field F] (K : Type) [DecidableEq K] (ι : K → Type)
    (V : Ideal (MRing ι F)) (l l' : List (K → ℤ)) (h : l.Perm l') :
    intNumL F V l = intNumL F V l' := by
  unfold intNumL
  exact intNum_get_eq_of_perm F V h

/- English proof (translation)
Use `⟨fun F _ K _ _ ι _ V l l' h => BaseChangeColon.intNumL_perm F K ι V l l' h, ?_⟩` and prove the remaining obligations. Introduce `O _ _ _ K _ _ ι _ Z l l' h`. Unfold `cycList`. Use `congr 1`. Use function extensionality and compare the values at `W`.

Unfold `vNumL vNum`. Conclude with `intNum_get_eq_of_perm _ _ h`.
-/
theorem BaseChangeColon.intersection_numbers_perm_invariant : (∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (V : Ideal (MRing ι F)) (l l' : List (K → ℤ)), l.Perm l' → intNumL F V l = intNumL F V l') ∧ (∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Z : Ideal (MRing ι O) → ℤ) (l l' : List (K → ℤ)), l.Perm l' → cycList Z l = cycList Z l') := by
  refine ⟨fun F _ K _ _ ι _ V l l' h => BaseChangeColon.intNumL_perm F K ι V l l' h, ?_⟩
  intro O _ _ _ K _ _ ι _ Z l l' h
  unfold cycList
  congr 1
  funext W
  unfold vNumL vNum
  exact intNum_get_eq_of_perm _ _ h
